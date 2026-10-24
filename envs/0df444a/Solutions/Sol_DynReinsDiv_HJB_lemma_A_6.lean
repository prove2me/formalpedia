-- Prove2me | solution 1 for DynReinsDiv.HJB.lemma_A_6
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:51:51.347519+00:00
-- url     : https://prove2.me/submissions/b7d15ead-5a87-45a1-a734-8b54281e5728
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE
import Theorems.Thm_DynReinsDiv_HJB_eq_A_7_A_9
import Theorems.Thm_DynReinsDiv_HJB_lemma_A_4
import Theorems.Thm_DynReinsDiv_HJB_lemma_A_5

open DynReinsDiv.HJB

theorem solution (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 0 ≤ uxx x t := by
  obtain ⟨hAanti, hBanti, -, -, hbd, -, -⟩ := eq_A_7_A_9 M
  obtain ⟨ε₄, hε₄, h4⟩ := lemma_A_4 M L lam hL hlam hroot
  obtain ⟨ε₅, hε₅, h5⟩ := lemma_A_5 M L lam hL hlam hroot
  refine ⟨min ε₄ ε₅, lt_min hε₄ hε₅, ?_⟩
  intro ε hε hεlt β fε hβ hf u ux uxx ut hC hS hge x t hx hxL ht htT
  obtain ⟨hut, hux⟩ := h4 ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)) β fε hβ hf u ux uxx ut hC hS
    hge x t hx hxL ht htT
  have hmix := h5 ε hε (lt_of_lt_of_le hεlt (min_le_right _ _)) β fε hβ hf u ux uxx ut hC hS
    hge x t hx hxL ht htT
  have hu1 := hge x t hx hxL ht htT
  have hu0 : 0 < u x t := lt_of_lt_of_le one_pos hu1
  have heq := hS.eqn x t hx hxL ht htT
  unfold Model.Top at heq
  set y := -ux x t / u x t with hy
  -- 0 ≤ y ≤ λ
  have hy0 : 0 ≤ y := div_nonneg (by linarith) hu0.le
  have hyl : y ≤ lam := by
    rw [hy, div_le_iff₀ hu0]; linarith
  -- positivity of A(y)
  have hApos : 0 < M.A y := by
    rcases hy0.lt_or_eq with h | h
    · exact (hbd y h).1
    · rw [← h]; exact lt_of_lt_of_le (hbd 1 one_pos).1 (hAanti zero_le_one)
  -- B(y) ≥ B(λ), and γ - B(λ) = -λ A(λ)
  have hB : M.B lam ≤ M.B y := hBanti hyl
  have hf0 : M.γ - M.B lam = -lam * M.A lam := by unfold Model.fA at hroot; linarith
  have hAl : 0 < M.A lam := (hbd lam hlam).1
  -- c u + β(u-1) ≥ 0
  have hβmono : Monotone β :=
    monotone_of_deriv_nonneg (hβ.smooth.differentiable (by norm_num)) hβ.deriv_nonneg
  have hpen : 0 ≤ M.c * u x t + β (u x t - 1) := by
    have h1 : β 0 ≤ β (u x t - 1) := hβmono (by linarith)
    rw [hβ.at_zero] at h1
    have := M.c_pos
    nlinarith
  -- A(y) uxx = ut - B ux + γ ux + c u + β ≥ (γ - B(y)) ux ≥ -λ A(λ) ux ≥ 0
  have key : M.A y * uxx x t = ut x t + (M.γ - M.B y) * ux x t + (M.c * u x t + β (u x t - 1)) := by
    linear_combination (-1 : ℝ) * heq
  have h2 : 0 ≤ (M.γ - M.B y) * ux x t := by
    have : M.γ - M.B y ≤ 0 := by nlinarith
    nlinarith
  have : 0 ≤ M.A y * uxx x t := by linarith
  by_contra hc
  push Not at hc
  have := mul_neg_of_pos_of_neg hApos hc
  linarith
