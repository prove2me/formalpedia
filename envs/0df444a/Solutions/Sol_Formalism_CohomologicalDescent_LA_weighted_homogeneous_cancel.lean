-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.weighted_homogeneous_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:01:35.461827+00:00
-- url     : https://prove2.me/submissions/10e802b1-5404-4e2a-81a2-5dbdc060bbf7

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {σ : Type} {n : ℕ} (w : σ → Fin n → ℕ) (D g : MvPolynomial σ ℤ)
    (δ ν : Fin n → ℕ) (hD0 : D ≠ 0) (hD : IsWeightedHomogeneous w D δ)
    (h : IsWeightedHomogeneous w (D * g) (δ + ν)) : IsWeightedHomogeneous w g ν := by
  classical
  unfold IsWeightedHomogeneous
  intro d hd
  by_contra hne
  have key : ∀ e : σ →₀ ℕ,
      coeff e (D * weightedHomogeneousComponent w (Finsupp.weight w d) g) =
        if Finsupp.weight w e = δ + Finsupp.weight w d then coeff e (D * g) else 0 := by
    intro e
    rw [coeff_mul, coeff_mul]
    split_ifs with he
    · refine Finset.sum_congr rfl ?_
      rintro ⟨x, y⟩ hxy
      have hxy' : x + y = e := by
        first
          | simpa using hxy
          | exact Finset.mem_antidiagonal.mp hxy
          | exact Finsupp.mem_antidiagonal.mp hxy
      dsimp only
      rw [coeff_weightedHomogeneousComponent]
      split_ifs with hy
      · rfl
      · by_cases hx : coeff x D = 0
        · simp [hx]
        · exfalso
          apply hy
          have h1 := hD hx
          rw [← hxy', map_add, h1] at he
          exact add_left_cancel he
    · refine Finset.sum_eq_zero ?_
      rintro ⟨x, y⟩ hxy
      have hxy' : x + y = e := by
        first
          | simpa using hxy
          | exact Finset.mem_antidiagonal.mp hxy
          | exact Finsupp.mem_antidiagonal.mp hxy
      dsimp only
      rw [coeff_weightedHomogeneousComponent]
      split_ifs with hy
      · by_cases hx : coeff x D = 0
        · simp [hx]
        · exfalso
          apply he
          rw [← hxy', map_add, hD hx, hy]
      · simp
  have hz : D * weightedHomogeneousComponent w (Finsupp.weight w d) g = 0 := by
    ext e
    rw [key, coeff_zero]
    split_ifs with he
    · by_contra hc
      apply hne
      have h3 := h hc
      rw [he] at h3
      exact add_left_cancel h3
    · rfl
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact hD0 h0
  · apply hd
    have h4 := congrArg (coeff d) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at h4
    exact h4
end Formalism.CohomologicalDescent.LA
