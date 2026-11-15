-- Prove2me | solution 1 for CalibeatBandit.decomposition_C_2
-- status  : ACCEPTED   (prove)
-- author  : @jasonhartline
-- created : 2026-11-14T12:46:53.110206+00:00
-- url     : https://prove2.me/submissions/b6231f7e-1a84-46a6-a048-0fd820716817

import Mathlib.Tactic
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_pseudoRewardLoss

set_option autoImplicit false

open Matrix CalibeatBandit
open scoped BigOperators

/-- **The three-part decomposition of the pseudo regrets** (§C.2, p.32). Let
`p_t = (1 − μ) x_t + μ u` with `x_t ∈ Δ(𝒜)`, `u = (1/K)·𝟏`, `0 ≤ μ ≤ 1`, rewards
`y_t ∈ [0,1]^K`, arbitrary vectors `v_t` and actions `J_t`. Then
`R^{SR,p}_T ≤ μT + max_f ∑_t (∑_i x_t(i) v_t(f(i)) − ⟨x_t, v_t⟩)
  + max_f ∑_t ∑_i x_t(i)(y_t(f(i)) − v_t(f(i))) + ∑_t ⟨x_t, v_t − y_t⟩`
and
`R^{Rec,p}_T ≤ μT + max_f ∑_t (v_t(f(J_t)) − ⟨x_t, v_t⟩) + max_f ∑_t (y_t(f(J_t)) − v_t(f(J_t)))
  + ∑_t ⟨x_t, v_t − y_t⟩`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, p.32 (the two displays before Lemma C.3).

**Formalization Note.** Deterministic: the inequalities hold for every realization. The paper
states them for the algorithm's `x_t`, `v_t` with `0 < μ ≤ 1/2`; here `x`, `v`, `J` are arbitrary
(with `x_t ∈ Δ(𝒜)`) and `0 ≤ μ ≤ 1`. Rounds are `0, …, T − 1`; `p` is only constrained on
those rounds. -/
theorem solution {K T : ℕ} (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (x v y p : ℕ → Fin K → ℝ) (J : ℕ → Fin K) (hx : ∀ t < T, IsProbVec (x t))
    (hy : ∀ t < T, ∀ j, y t j ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ t < T, ∀ j, p t j = (1 - μ) * x t j + μ / K) :
    pseudoSwapRegret T p y ≤ μ * T
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (∑ i, x t i * v t (f i) - x t ⬝ᵥ v t))
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, ∑ i, x t i * (y t (f i) - v t (f i)))
        + ∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t) ∧
    pseudoRewardLoss T p y J ≤ μ * T
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (v t (f (J t)) - x t ⬝ᵥ v t))
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (y t (f (J t)) - v t (f (J t))))
        + ∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t) := by
  have p_eq (t : ℕ) (ht : t < T) :
      p t = (1 - μ) • x t + (fun _ => μ / K) := by
    ext j
    exact hp t ht j
  have uniform_le (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      ∑ i, μ / K * (y t (f i) - y t i) ≤ μ := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin K))) fun i _ =>
      mul_le_of_le_one_right (show 0 ≤ μ / (K : ℝ) by positivity)
        (show y t (f i) - y t i ≤ 1 by linarith [(hy t ht (f i)).2, (hy t ht i).1])
    by_cases hK : K = 0
    · subst K
      simpa using hμ0
    · refine h.trans_eq ?_
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hK' : (K : ℝ) ≠ 0 := by exact_mod_cast hK
      field_simp
  have exploration (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      (∑ i, p t i * y t (f i)) - p t ⬝ᵥ y t ≤
        (1 - μ) * ((∑ i, x t i * y t (f i)) - x t ⬝ᵥ y t) + μ := by
    have expand : (∑ i, p t i * y t (f i)) - p t ⬝ᵥ y t =
        (1 - μ) * ((∑ i, x t i * y t (f i)) - x t ⬝ᵥ y t) +
          ∑ i, μ / K * (y t (f i) - y t i) := by
      simp only [p_eq t ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, add_mul,
        Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      ring_nf
    rw [expand]
    exact add_le_add_right (uniform_le t ht f) _
  have recExplore (t : ℕ) (ht : t < T) (f : Fin K → Fin K) :
      y t (f (J t)) - p t ⬝ᵥ y t ≤ y t (f (J t)) - x t ⬝ᵥ y t + μ := by
    have hupper : x t ⬝ᵥ y t ≤ 1 := by
      unfold dotProduct
      refine (Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ((hx t ht).1 i) (hy t ht i).2).trans_eq
        (hx t ht).2
    have hnonneg : 0 ≤ ∑ i, μ / K * y t i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hy t ht i).1
    have hexpand : p t ⬝ᵥ y t =
        (1 - μ) * (x t ⬝ᵥ y t) + ∑ i, μ / K * y t i := by
      simp only [p_eq t ht, Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand]
    nlinarith [mul_nonneg hμ0 (sub_nonneg.mpr hupper)]
  have sup_decompose (A B C : (Fin K → Fin K) → ℝ) (D : ℝ)
      (h : ∀ f, A f = B f + C f + D) :
      (Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ A) ≤
        (Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ B) +
        (Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ C) + D := by
    apply Finset.sup'_le
    intro f hf
    rw [h f]
    gcongr <;> exact Finset.le_sup' _ hf
  let sr : (Fin K → Fin K) → ℝ :=
    fun f => ∑ t ∈ Finset.range T, ((∑ i, x t i * y t (f i)) - x t ⬝ᵥ y t)
  let recPayoff : (Fin K → Fin K) → ℝ :=
    fun f => ∑ t ∈ Finset.range T, (y t (f (J t)) - x t ⬝ᵥ y t)
  have sr0 : 0 ≤ Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ sr := by
    have h := Finset.le_sup' sr (Finset.mem_univ (id : Fin K → Fin K))
    simpa [sr, dotProduct] using h
  have srExplore : pseudoSwapRegret T p y ≤ μ * T + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ sr := by
    unfold pseudoSwapRegret
    apply Finset.sup'_le
    intro f hf
    have h := Finset.sum_le_sum (s := Finset.range T) fun t ht =>
      exploration t (Finset.mem_range.mp ht) f
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hle : sr f ≤ Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ sr := Finset.le_sup' sr hf
    have hmul := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hμ1)
    change _ ≤ (1 - μ) * sr f + (T : ℝ) * μ at h
    nlinarith [mul_nonneg hμ0 sr0]
  have recExploreSum : pseudoRewardLoss T p y J ≤ μ * T + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ recPayoff := by
    unfold pseudoRewardLoss
    apply Finset.sup'_le
    intro f hf
    have h := Finset.sum_le_sum (s := Finset.range T) fun t ht =>
      recExplore t (Finset.mem_range.mp ht) f
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    have hle : recPayoff f ≤ Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ recPayoff :=
      Finset.le_sup' recPayoff hf
    change _ ≤ recPayoff f + (T : ℝ) * μ at h
    linarith
  constructor
  · refine srExplore.trans ?_
    have h := sup_decompose sr
      (fun f => ∑ t ∈ Finset.range T, ((∑ i, x t i * v t (f i)) - x t ⬝ᵥ v t))
      (fun f => ∑ t ∈ Finset.range T, ∑ i, x t i * (y t (f i) - v t (f i)))
      (∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t)) ?_
    · linarith
    · intro f
      simp only [sr, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring
  · refine recExploreSum.trans ?_
    have h := sup_decompose recPayoff
      (fun f => ∑ t ∈ Finset.range T, (v t (f (J t)) - x t ⬝ᵥ v t))
      (fun f => ∑ t ∈ Finset.range T, (y t (f (J t)) - v t (f (J t))))
      (∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t)) ?_
    · linarith
    · intro f
      simp only [recPayoff, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by
        simp only [dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        ring

