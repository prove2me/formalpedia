-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.lfunction_one_le_of_siegel_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:18.97421+00:00
-- url     : https://prove2.me/submissions/4745030a-71ad-4412-961b-4429ee95568b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPos
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeA
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lfunction_deriv_near_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ),
    χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ C * Real.log (3 * M) ^ 2 * (1 - β₁) := by
  obtain ⟨C, hC⟩ := lfunction_deriv_near_one
  refine ⟨max C 0, le_max_right _ _, fun M _ χ₁ β₁ hχ hz hβ hβ1 => ?_⟩
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have hder : ∀ t ∈ Set.Icc β₁ 1,
      HasDerivWithinAt (fun t : ℝ => DirichletCharacter.LFunction χ₁ (t : ℂ))
        (deriv (DirichletCharacter.LFunction χ₁) (t : ℂ)) (Set.Icc β₁ 1) t :=
    fun t _ => ((hd (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbd : ∀ t ∈ Set.Ico β₁ 1,
      ‖deriv (DirichletCharacter.LFunction χ₁) (t : ℂ)‖ ≤ max C 0 * Real.log (3 * M) ^ 2 := by
    intro t ht
    exact (hC M χ₁ hχ t (le_trans hβ ht.1) ht.2.le).trans (by gcongr; exact le_max_left _ _)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd 1 ⟨hβ1.le, le_rfl⟩
  simp only [hz, sub_zero, ofReal_one] at this
  exact this
end Formalism.HermitianLattices.Ext.PrimesInProgressions
