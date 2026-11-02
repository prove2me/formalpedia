-- Prove2me | solution 1 for DynRiskEq.Welfare.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:43:17.908205+00:00
-- url     : https://prove2.me/submissions/65a58f2c-8645-45d0-a9d4-61eebf0dba3d

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model
import Theorems.Thm_DynRiskEq_Welfare_theorem_3_i
import Theorems.Thm_DynRiskEq_Welfare_theorem_3_ii
import Theorems.Thm_DynRiskEq_Welfare_theorem_3_iv_maximizer

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare

variable {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]

lemma decomp {ι : Type} [Fintype ι] {K : ℕ} (v : Fin K → ι → ℝ) (y : ι → ℝ)
    (hy : y ∈ convexHull ℝ (Set.range v)) :
    ∃ γ : Fin K → ℝ, (∀ k, 0 ≤ γ k) ∧ ∑ k, γ k = 1 ∧ ∀ i, y i = ∑ k, γ k * v k i := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, w, hw0, hw1, rfl⟩ := hy
  refine ⟨fun k => if k ∈ s then w k else 0, ?_, ?_, ?_⟩
  · intro k; dsimp only; split_ifs with h
    · exact hw0 k h
    · exact le_rfl
  · rw [← hw1, Finset.sum_ite_mem, Finset.univ_inter]
  · intro i
    rw [Finset.affineCombination_eq_linear_combination s v w hw1]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma SE_of (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa)
    (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (γ : (n : T.Node) → Fin (K n) → ℝ)
    (h1 : ∀ n, ¬ IsLeaf T n → 0 = 1 - ∑ k, γ n k)
    (h2 : ∀ n, ¬ IsLeaf T n → ∀ k, Compl (γ n k)
      (thetaBar T θa n - ∑ m ∈ T.children n, p n k m * (∑ a, M.C a (u a m) + thetaBar T θa m)))
    (hμ : ∀ n, ¬ IsLeaf T n → ∀ m ∈ T.children n, μ m = ∑ k, γ n k * p n k m) :
    SE T M K p u x (thetaBar T θa) γ π α := by
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, hRTE.2.2.1, hRTE.2.1⟩
  · intro n hn
    unfold thetaBar
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    obtain ⟨γa, -, -, h20c, -⟩ := hRTE.1 a
    exact h20c n hn
  · intro a n
    obtain ⟨γa, -, -, -, h20d, -⟩ := hRTE.1 a
    obtain ⟨hU, w, hw, hN⟩ := h20d n
    refine ⟨hU, w, ?_, hN⟩
    set c := ⟪α a n, x a n - prevStore T M x a n - M.ω a n⟫ +
      ∑ m ∈ T.children n, μ m * W a m
    have h' := (hasGradientAt_iff_hasFDerivAt.mp hw).sub_const c
    refine hasGradientAt_iff_hasFDerivAt.mpr ?_
    have hf : (fun v => M.C a v - π n * M.g a v -
        ∑ b, ⟪α b n, Matrix.toEuclideanLin (M.Tm b a) v⟫) =
        fun v => Z T M π α μ (Function.update u a (Function.update (u a) n v)) x W a n - c := by
      funext v
      simp only [Z, Function.update_self, c]
      ring
    rw [hf]; exact h'
  · intro a n hn
    obtain ⟨γa, -, -, -, -, h20e, -⟩ := hRTE.1 a
    have : ∑ m ∈ T.children n, ∑ k, (γ n k * p n k m) • α a m =
        ∑ m ∈ T.children n, μ m • α a m := by
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [← Finset.sum_smul, ← hμ n hn m hm]
    rw [this]
    exact h20e n hn
  · intro a n hn
    obtain ⟨γa, -, -, -, -, -, h20f, -⟩ := hRTE.1 a
    exact h20f n hn

end DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare DynRiskEq.Welfare.Aux3

theorem solution {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (hprob : ∀ a, ProbGenerators T (Ka a) (pa a))
    (hA3 : ∀ n, ¬ IsLeaf T n → (socialRiskSet T Ka pa n).Nonempty)
    (Ks : T.Node → ℕ) (ps : (n : T.Node) → Fin (Ks n) → T.Node → ℝ)
    (hs : ∀ n, ¬ IsLeaf T n → riskSet T Ks ps n = socialRiskSet T Ka pa n)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    -- (i)
    (∀ n, ¬ IsLeaf T n →
      (∀ a, InRisk T (Ka a) (pa a) n μ) ∧ restrictChildren T μ n ∈ socialRiskSet T Ka pa n) ∧
    -- (ii), (24)
    (∀ n, ¬ IsLeaf T n →
      thetaBar T θa n = ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m)) ∧
    -- (iii), SE(𝒟₀) with 𝒟₀ = {μ̄}: one generator p¹₀ = μ̄ at every node
    (∃ γ : (n : T.Node) → Fin 1 → ℝ,
      SE T M (fun _ => 1) (fun _ _ => μ) u x (thetaBar T θa) γ π α ∧
      ∀ n, ¬ IsLeaf T n → ∀ m ∈ T.children n, μ m = ∑ k, γ n k * μ m) ∧
    -- (iv), SE(𝒟_s), with the closing clause μ̄(m) = Σ_k γ^k(n) p^k_s(m)
    (∃ γ : (n : T.Node) → Fin (Ks n) → ℝ,
      SE T M Ks ps u x (thetaBar T θa) γ π α ∧
      ∀ n, ¬ IsLeaf T n → ∀ m ∈ T.children n, μ m = ∑ k, γ n k * ps n k m) := by
  have hi := theorem_3_i T M Ka pa π α μ u x W θa hRTE
  have hii := theorem_3_ii T M Ka pa π α μ u x W θa hRTE
  have hiv := theorem_3_iv_maximizer T M Ka pa hprob π α μ u x W θa hRTE
  refine ⟨hi, hii, ⟨fun _ _ => 1, ?_, ?_⟩, ?_⟩
  · refine SE_of T M Ka pa π α μ u x W θa hRTE _ _ _ (fun n _ => by simp) ?_ (fun n _ m _ => by simp)
    intro n hn k
    refine ⟨zero_le_one, ?_, ?_⟩
    · rw [hii n hn]; exact le_of_eq (by ring)
    · rw [hii n hn]; ring
  · intro n _ m _; simp
  · have hex : ∀ n, ∃ g : Fin (Ks n) → ℝ, ¬ IsLeaf T n →
        (∀ k, 0 ≤ g k) ∧ ∑ k, g k = 1 ∧ ∀ m ∈ T.children n, μ m = ∑ k, g k * ps n k m := by
      intro n
      by_cases hn : IsLeaf T n
      · exact ⟨0, fun h => absurd hn h⟩
      · have hmem : restrictChildren T μ n ∈ riskSet T Ks ps n := by
          rw [hs n hn]; exact (hi n hn).2
        obtain ⟨g, g0, g1, gμ⟩ := decomp _ _ hmem
        exact ⟨g, fun _ => ⟨g0, g1, fun m hm => gμ ⟨m, hm⟩⟩⟩
    choose γ hγ using hex
    refine ⟨γ, SE_of T M Ka pa π α μ u x W θa hRTE _ _ _ ?_ ?_ ?_, ?_⟩
    · intro n hn; linarith [(hγ n hn).2.1]
    · intro n hn
      set Y := fun m => ∑ a, M.C a (u a m) + thetaBar T θa m
      have hle : ∀ k, ∑ m ∈ T.children n, ps n k m * Y m ≤ thetaBar T θa n := by
        intro k
        have hk : restrictChildren T (ps n k) n ∈ socialRiskSet T Ka pa n := by
          rw [← hs n hn]; exact subset_convexHull ℝ _ ⟨k, rfl⟩
        have := (hiv n hn).2 _ hk
        rw [← hii n hn] at this
        rw [← Finset.sum_coe_sort (T.children n) (fun m => ps n k m * Y m)]
        exact this
      have hsum : ∑ k, γ n k * (thetaBar T θa n - ∑ m ∈ T.children n, ps n k m * Y m) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hγ n hn).2.1, one_mul]
        rw [hii n hn]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine sub_eq_zero.2 (Finset.sum_congr rfl fun m hm => ?_)
        rw [(hγ n hn).2.2 m hm, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
        mul_nonneg ((hγ n hn).1 k) (sub_nonneg.2 (hle k))).1 hsum
      intro k
      exact ⟨(hγ n hn).1 k, sub_nonneg.2 (hle k), hz k (Finset.mem_univ k)⟩
    · intro n hn m hm; exact (hγ n hn).2.2 m hm
    · intro n hn m hm; exact (hγ n hn).2.2 m hm
