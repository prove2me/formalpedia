-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_box_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.892917+00:00
-- url     : https://prove2.me/submissions/91d63e91-0a6e-42fa-8e6b-80341e62ec20

import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLemmaLfunctionZeros
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by
  calc ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ := Finset.sum_le_sum fun ρ hρ => by
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)
    _ = (∑ ρ ∈ Z, (m ρ : ℝ)) / δ := by rw [Finset.sum_div]
end Formalism.HermitianLattices.Ext.BoxTail
