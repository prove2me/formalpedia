-- Prove2me | solution 1 for DynRiskEq.Welfare.theorem_3_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:42:50.09719+00:00
-- url     : https://prove2.me/submissions/fd1229c9-afc2-4c62-abbd-9eeef09434e4

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model
import Theorems.Thm_DynRiskEq_Welfare_theorem_2_i_value

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

lemma value (M : Market T A) (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ) (a : A) (γ : (n : T.Node) → Fin (K n) → ℝ)
    (hAE : AE T M K p π α μ u x W θa a γ) (n : T.Node) (hn : ¬ IsLeaf T n) :
    θa a n = ∑ m ∈ T.children n, μ m * (Z T M π α μ u x W a m - W a m + θa a m) := by
  have h := (theorem_2_i_value T M K p π α μ u x W θa a γ hAE n hn).2
  rw [h]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [show μ m = ∑ k, γ n k * p n k m by linarith [hAE.2.2.2.2.2.2 n hn m hm]]

lemma t3ii (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      thetaBar T θa n = ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m) := by
  intro n hn
  have hv : ∀ a, θa a n =
      ∑ m ∈ T.children n, μ m * (Z T M π α μ u x W a m - W a m + θa a m) := by
    intro a
    obtain ⟨γ, hAE⟩ := hRTE.1 a
    exact value T M (Ka a) (pa a) π α μ u x W θa a γ hAE n hn
  unfold thetaBar
  rw [Finset.sum_congr rfl fun a _ => hv a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.mul_sum]
  have hZ := sumZ T M Ka pa π α μ u x W θa hRTE m
  have hW : μ m * ∑ a, W a m = 0 := by
    have := (hRTE.2.2.2 m (child_ne_root T hm)).2.2
    rw [mul_neg] at this; linarith
  have hs : ∑ a, (Z T M π α μ u x W a m - W a m + θa a m) =
      ∑ a, Z T M π α μ u x W a m - ∑ a, W a m + ∑ a, θa a m := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hs, hZ]
  linear_combination -hW

end DynRiskEq.Welfare.Aux3

open DynRiskEq.Welfare DynRiskEq.Welfare.Aux3

theorem solution {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (Ka : A → T.Node → ℕ)
    (pa : (a : A) → (n : T.Node) → Fin (Ka a n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ)
    (hRTE : IsRTE T M Ka pa π α μ u x W θa) :
    ∀ n, ¬ IsLeaf T n →
      thetaBar T θa n = ∑ m ∈ T.children n, μ m * (∑ a, M.C a (u a m) + thetaBar T θa m) := by
  exact t3ii T M Ka pa π α μ u x W θa hRTE
