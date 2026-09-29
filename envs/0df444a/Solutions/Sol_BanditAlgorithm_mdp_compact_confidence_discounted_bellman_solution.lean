-- Prove2me | solution 1 for BanditAlgorithm.mdp_compact_confidence_discounted_bellman_solution
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T16:32:22.334684+00:00
-- url     : https://prove2.me/submissions/7f7a2442-6412-450c-b63b-4cc2df8e5bf4

import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecificLimits.Basic

open Finset
open scoped NNReal ENNReal

/-!
The discounted Bellman optimality operator of the *extended* MDP,
`(T v)(s) = max_a (r_a(s) + γ max_{p ∈ C s a} ⟨p, v⟩)`.

The extended MDP is not a finite MDP: its actions are pairs `(a, p)` with `p`
ranging over a confidence set of transition rows, a continuum.  What replaces
finiteness is compactness: the inner maximisation is attained, and it is
`1`-Lipschitz in the supremum norm because the elements of `C s a` are
probability vectors.  Hence `T` is still a `γ`-contraction and has a fixed
point.
-/

variable {S A : ℕ}

/-- An average against a probability vector is at most any upper bound of the
integrand. -/
private lemma probVecMulLe {p u : Fin S → ℝ} {c : ℝ} (hp0 : ∀ s', 0 ≤ p s')
    (hp1 : ∑ s', p s' = 1) (h : ∀ s', u s' ≤ c) : ∑ s', p s' * u s' ≤ c := by
  calc ∑ s', p s' * u s' ≤ ∑ s', p s' * c :=
        Finset.sum_le_sum fun s' _ ↦ mul_le_mul_of_nonneg_left (h s') (hp0 s')
    _ = c := by rw [← Finset.sum_mul, hp1, one_mul]

/-- An average against a probability vector is at least any lower bound of the
integrand. -/
private lemma leProbVecMul {p u : Fin S → ℝ} {c : ℝ} (hp0 : ∀ s', 0 ≤ p s')
    (hp1 : ∑ s', p s' = 1) (h : ∀ s', c ≤ u s') : c ≤ ∑ s', p s' * u s' := by
  calc c = ∑ s', p s' * c := by rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ ∑ s', p s' * u s' :=
        Finset.sum_le_sum fun s' _ ↦ mul_le_mul_of_nonneg_left (h s') (hp0 s')

/-- The largest average `⟨p, v⟩` of `v` against a transition row `p` in the
confidence set `K`. -/
private noncomputable def optVal (K : Set (Fin S → ℝ)) (v : Fin S → ℝ) : ℝ :=
  sSup ((fun p : Fin S → ℝ ↦ ∑ s', p s' * v s') '' K)

private lemma continuousDotProd (v : Fin S → ℝ) :
    Continuous (fun p : Fin S → ℝ ↦ ∑ s', p s' * v s') :=
  continuous_finset_sum _ fun s' _ ↦ (continuous_apply s').mul continuous_const

/-- On a compact confidence set the optimistic value is attained. -/
private lemma existsEqOptVal {K : Set (Fin S → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (v : Fin S → ℝ) : ∃ p ∈ K, optVal K v = ∑ s', p s' * v s' := by
  obtain ⟨p, hp, hpe⟩ := (hK.image (continuousDotProd v)).sSup_mem (hne.image _)
  exact ⟨p, hp, hpe.symm⟩

private lemma leOptVal {K : Set (Fin S → ℝ)} (hK : IsCompact K) {p : Fin S → ℝ}
    (hp : p ∈ K) (v : Fin S → ℝ) : ∑ s', p s' * v s' ≤ optVal K v :=
  le_csSup (hK.image (continuousDotProd v)).bddAbove ⟨p, hp, rfl⟩

private lemma optValLe {K : Set (Fin S → ℝ)} (hne : K.Nonempty) {v : Fin S → ℝ} {c : ℝ}
    (h : ∀ p ∈ K, ∑ s', p s' * v s' ≤ c) : optVal K v ≤ c := by
  refine csSup_le (hne.image _) ?_
  rintro x ⟨p, hp, rfl⟩
  exact h p hp

/-- The optimistic value is `1`-Lipschitz in the supremum norm. -/
private lemma optValLeAddDist {K : Set (Fin S → ℝ)} (hK : IsCompact K) (hne : K.Nonempty)
    (hprob : ∀ p ∈ K, (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1) (u v : Fin S → ℝ) :
    optVal K u ≤ optVal K v + dist u v := by
  refine optValLe hne ?_
  intro p hp
  obtain ⟨hp0, hp1⟩ := hprob p hp
  have hcoord : ∀ s', u s' - v s' ≤ dist u v := fun s' ↦ by
    have h := dist_le_pi_dist u v s'
    rw [Real.dist_eq] at h
    exact le_trans (le_abs_self _) h
  have hsplit : ∑ s', p s' * (u s' - v s')
      = (∑ s', p s' * u s') - ∑ s', p s' * v s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ ↦ by ring
  have h1 : (∑ s', p s' * u s') - ∑ s', p s' * v s' ≤ dist u v := by
    rw [← hsplit]; exact probVecMulLe hp0 hp1 hcoord
  have h2 : ∑ s', p s' * v s' ≤ optVal K v := leOptVal hK hp v
  linarith

/-- The discounted Bellman optimality operator of the extended MDP. -/
private noncomputable def bellmanOpC (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (hne : (univ : Finset (Fin A)).Nonempty)
    (γ : ℝ) (v : Fin S → ℝ) : Fin S → ℝ :=
  fun s ↦ univ.sup' hne fun a ↦ r s a + γ * optVal (C s a) v

/-- The extended Bellman operator is a `γ`-contraction in the supremum norm. -/
private lemma bellmanOpCDistLe (r : Fin S → Fin A → ℝ)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (hCne : ∀ s a, (C s a).Nonempty)
    (hCcomp : ∀ s a, IsCompact (C s a))
    (hCprob : ∀ s a, ∀ p ∈ C s a, (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1)
    (hne : (univ : Finset (Fin A)).Nonempty) {γ : ℝ} (hγ0 : 0 ≤ γ) (u v : Fin S → ℝ) :
    dist (bellmanOpC r C hne γ u) (bellmanOpC r C hne γ v) ≤ γ * dist u v := by
  have step : ∀ u v : Fin S → ℝ, ∀ s : Fin S,
      bellmanOpC r C hne γ u s ≤ bellmanOpC r C hne γ v s + γ * dist u v := by
    intro u v s
    refine Finset.sup'_le hne _ fun a _ ↦ ?_
    have h1 : optVal (C s a) u ≤ optVal (C s a) v + dist u v :=
      optValLeAddDist (hCcomp s a) (hCne s a) (hCprob s a) u v
    have h2 : r s a + γ * optVal (C s a) v ≤ bellmanOpC r C hne γ v s :=
      Finset.le_sup' (fun a ↦ r s a + γ * optVal (C s a) v) (mem_univ a)
    nlinarith
  rw [dist_pi_le_iff (mul_nonneg hγ0 dist_nonneg)]
  intro s
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1 := step u v s
  have h2 := step v u s
  rw [dist_comm v u] at h2
  exact ⟨by linarith, by linarith⟩

theorem solution {S A : ℕ} (hS : 0 < S) (hA : 0 < A)
    (r : Fin S → Fin A → ℝ) (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1)
    (C : Fin S → Fin A → Set (Fin S → ℝ)) (hCne : ∀ s a, (C s a).Nonempty)
    (hCcomp : ∀ s a, IsCompact (C s a))
    (hCprob : ∀ s a, ∀ p ∈ C s a, (∀ s', 0 ≤ p s') ∧ ∑ s', p s' = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ (V : Fin S → ℝ) (f : Fin S → Fin A) (q : Fin S → Fin S → ℝ),
      (∀ s, V s ∈ Set.Icc (0 : ℝ) (1 / (1 - γ))) ∧
      (∀ s a, ∀ p ∈ C s a, r s a + γ * ∑ s', p s' * V s' ≤ V s) ∧
      (∀ s, q s ∈ C s (f s)) ∧
      (∀ s, V s = r s (f s) + γ * ∑ s', q s s' * V s') := by
  haveI : Nonempty (Fin A) := Fin.pos_iff_nonempty.mp hA
  haveI : Nonempty (Fin S) := Fin.pos_iff_nonempty.mp hS
  have hne : (univ : Finset (Fin A)).Nonempty := univ_nonempty
  have hcoe : ((Real.toNNReal γ : ℝ≥0) : ℝ) = γ := Real.coe_toNNReal γ hγ0
  have hlip : LipschitzWith (Real.toNNReal γ) (bellmanOpC r C hne γ) :=
    LipschitzWith.of_dist_le_mul fun u v ↦ by
      rw [hcoe]; exact bellmanOpCDistLe r C hCne hCcomp hCprob hne hγ0 u v
  have hK : Real.toNNReal γ < 1 := by
    rw [← NNReal.coe_lt_coe, hcoe, NNReal.coe_one]; exact hγ1
  have hc : ContractingWith (Real.toNNReal γ) (bellmanOpC r C hne γ) := ⟨hK, hlip⟩
  set V := hc.fixedPoint with hVdef
  have hV : bellmanOpC r C hne γ V = V := hc.fixedPoint_isFixedPt
  have hVsup : ∀ s, V s = univ.sup' hne fun a ↦ r s a + γ * optVal (C s a) V :=
    fun s ↦ (congrFun hV s).symm
  have hVle : ∀ s a, ∀ p ∈ C s a, r s a + γ * ∑ s', p s' * V s' ≤ V s := by
    intro s a p hp
    have h1 : ∑ s', p s' * V s' ≤ optVal (C s a) V := leOptVal (hCcomp s a) hp V
    have h2 : r s a + γ * optVal (C s a) V ≤ V s := by
      rw [hVsup s]
      exact Finset.le_sup' (fun a ↦ r s a + γ * optVal (C s a) V) (mem_univ a)
    nlinarith
  have hgreedy : ∀ s, ∃ a : Fin A, ∃ p : Fin S → ℝ,
      p ∈ C s a ∧ V s = r s a + γ * ∑ s', p s' * V s' := by
    intro s
    obtain ⟨a, -, ha⟩ :=
      Finset.exists_mem_eq_sup' hne fun a ↦ r s a + γ * optVal (C s a) V
    obtain ⟨p, hp, hpe⟩ := existsEqOptVal (hCcomp s a) (hCne s a) V
    exact ⟨a, p, hp, by rw [hVsup s, ha, hpe]⟩
  choose f q hq hVeq using hgreedy
  obtain ⟨smax, hsmax⟩ := Finite.exists_max V
  obtain ⟨smin, hsmin⟩ := Finite.exists_min V
  have hγpos : 0 < 1 - γ := by linarith
  have hub : V smax ≤ 1 / (1 - γ) := by
    obtain ⟨hq0, hq1⟩ := hCprob smax (f smax) (q smax) (hq smax)
    have h1 := hVeq smax
    have h2 : ∑ s', q smax s' * V s' ≤ V smax := probVecMulLe hq0 hq1 hsmax
    have h3 : r smax (f smax) ≤ 1 := (hr smax (f smax)).2
    rw [le_div_iff₀ hγpos]
    nlinarith
  have hlb : 0 ≤ V smin := by
    obtain ⟨hq0, hq1⟩ := hCprob smin (f smin) (q smin) (hq smin)
    have h1 := hVeq smin
    have h2 : V smin ≤ ∑ s', q smin s' * V s' := leProbVecMul hq0 hq1 hsmin
    have h3 : 0 ≤ r smin (f smin) := (hr smin (f smin)).1
    nlinarith
  exact ⟨V, f, q, fun s ↦ ⟨hlb.trans (hsmin s), (hsmax s).trans hub⟩, hVle, hq, hVeq⟩
