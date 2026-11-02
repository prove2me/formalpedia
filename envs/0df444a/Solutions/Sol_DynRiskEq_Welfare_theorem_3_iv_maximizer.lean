-- Prove2me | solution 1 for DynRiskEq.Welfare.theorem_3_iv_maximizer
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:43:17.299794+00:00
-- url     : https://prove2.me/submissions/4b3629af-14ed-477e-b2f0-14f6a71cc65f

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model
import Theorems.Thm_DynRiskEq_Welfare_theorem_2_i_value
import Theorems.Thm_DynRiskEq_Welfare_theorem_3_i
import Theorems.Thm_DynRiskEq_Welfare_theorem_3_ii

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare

variable {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]

lemma child_ne_root {n m : T.Node} (hm : m ∈ T.children n) : m ≠ T.root := by
  intro h
  simp only [Tree.children, Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have := T.root_stage
  rw [h] at hm
  omega

lemma inner_eq_zero_of_compl {d : ℕ} (y z : Vec d) (h : ∀ i, Compl (y i) (z i)) :
    ⟪y, z⟫ = 0 := by
  rw [PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm]; exact (h i).2.2

lemma sumZ (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) (m : T.Node) :
    ∑ a, Z T M π α μ u x W a m = ∑ a, M.C a (u a m) := by
  obtain ⟨-, h21, h22, h23⟩ := hRTE
  have e21 : π m * ∑ a, M.g a (u a m) = 0 := (h21 m).2.2
  have e22 : ∑ a, ⟪α a m, storageSlack T M u x a m⟫ = 0 :=
    Finset.sum_eq_zero fun a _ => inner_eq_zero_of_compl _ _ (h22 a m)
  have e23 : ∑ a, ∑ m' ∈ T.children m, μ m' * W a m' = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun m' hm' => ?_
    rw [← Finset.mul_sum]
    have := (h23 m' (child_ne_root T hm')).2.2
    rw [mul_neg] at this
    linarith
  have eslack : ∀ a, ⟪α a m, storageSlack T M u x a m⟫ =
      -⟪α a m, x a m - prevStore T M x a m - M.ω a m⟫ +
        ∑ b, ⟪α a m, Matrix.toEuclideanLin (M.Tm a b) (u b m)⟫ := by
    intro a
    have : storageSlack T M u x a m = -(x a m - prevStore T M x a m - M.ω a m) +
        ∑ b, Matrix.toEuclideanLin (M.Tm a b) (u b m) := by
      unfold storageSlack; abel
    rw [this, inner_add_right, inner_neg_right, inner_sum]
  have eswap : ∑ a, ∑ b, ⟪α a m, Matrix.toEuclideanLin (M.Tm a b) (u b m)⟫ =
      ∑ a, ∑ b, ⟪α b m, Matrix.toEuclideanLin (M.Tm b a) (u a m)⟫ := Finset.sum_comm
  simp only [Z, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, e21, e23]
  simp only [eslack, Finset.sum_add_distrib, Finset.sum_neg_distrib] at e22
  linarith

lemma bound (M : Market T A) (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ) (a : A) (γ : (n : T.Node) → Fin (K n) → ℝ)
    (hAE : AE T M K p π α μ u x W θa a γ) (n : T.Node) (hn : ¬ IsLeaf T n)
    (ν : ↥(T.children n) → ℝ) (hν : ν ∈ riskSet T K p n) :
    ∑ m : ↥(T.children n), ν m * (Z T M π α μ u x W a m - W a m + θa a m) ≤ θa a n := by
  exact (theorem_2_i_value T M K p π α μ u x W θa a γ hAE n hn).1.2 ⟨ν, hν, rfl⟩

lemma nonneg (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (hprob : ProbGenerators T K p) (n : T.Node) (hn : ¬ IsLeaf T n)
    (ν : ↥(T.children n) → ℝ) (hν : ν ∈ riskSet T K p n) : ∀ m, 0 ≤ ν m := by
  have hsub : riskSet T K p n ⊆ {ν | ∀ m, 0 ≤ ν m} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨k, rfl⟩ m
      exact (hprob n hn k).1 m m.2
    · intro ν₁ h₁ ν₂ h₂ c d hc hd hcd m
      simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
      have := h₁ m; have := h₂ m
      positivity
  exact hsub hν

lemma t3iv (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (hprob : ∀ a, ProbGenerators T (Ka a) (pa a))
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      restrictChildren T μ n ∈ socialRiskSet T Ka pa n ∧
      ∀ ν ∈ socialRiskSet T Ka pa n,
        ∑ m : ↥(T.children n), ν m * (∑ a, M.C a (u a m) + thetaBar T θa m) ≤
          ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m) := by
  intro n hn
  refine ⟨(theorem_3_i T M Ka pa π α μ u x W θa hRTE n hn).2, fun ν hν => ?_⟩
  rw [← theorem_3_ii T M Ka pa π α μ u x W θa hRTE n hn]
  have hνa : ∀ a, ν ∈ riskSet T (Ka a) (pa a) n := Set.mem_iInter.1 hν
  have hb : ∀ a, ∑ m : ↥(T.children n), ν m * (Z T M π α μ u x W a m - W a m + θa a m)
      ≤ θa a n := by
    intro a
    obtain ⟨γ, hAE⟩ := hRTE.1 a
    exact bound T M (Ka a) (pa a) π α μ u x W θa a γ hAE n hn ν (hνa a)
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => hb a
  rw [Finset.sum_comm] at hsum
  unfold thetaBar
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) hsum
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sumZ T M Ka pa π α μ u x W θa hRTE m]
  have hW : 0 ≤ - ∑ a, W a m := (hRTE.2.2.2 m (child_ne_root T m.2)).2.1
  rcases isEmpty_or_nonempty A with hA | ⟨⟨a⟩⟩
  · simp
  · have := nonneg T (Ka a) (pa a) (hprob a) n hn ν (hνa a) m
    nlinarith [mul_nonneg this hW]

end DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare DynRiskEq.Welfare.Aux3

theorem solution {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (hprob : ∀ a, ProbGenerators T (Ka a) (pa a))
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      restrictChildren T μ n ∈ socialRiskSet T Ka pa n ∧
      ∀ ν ∈ socialRiskSet T Ka pa n,
        ∑ m : ↥(T.children n), ν m * (∑ a, M.C a (u a m) + thetaBar T θa m) ≤
          ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m) := by
  exact t3iv T M Ka pa hprob π α μ u x W θa hRTE
