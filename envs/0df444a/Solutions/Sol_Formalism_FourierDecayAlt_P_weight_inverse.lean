-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weight_inverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:04:08.35109+00:00
-- url     : https://prove2.me/submissions/3b45adb0-43cd-4e98-abfe-b4a94e0ad223

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DbarConjugationWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.WInv := by
  intro TT ζ hTT hG
  unfold C7.GGz at hG
  have hq : 0 < Complex.normSq ζ := by linarith
  have hζ : ζ ≠ 0 := by intro h; rw [h, Complex.normSq_zero] at hq; exact lt_irrefl _ hq
  have hcζ : (starRingEnd ℂ) ζ ≠ 0 := (map_ne_zero _).2 hζ
  constructor
  · unfold C7.Wz C7.GGz
    push_cast
    rw [inv_div, ← Complex.mul_conj]
    field_simp
  · have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
    rw [norm_div, norm_one, one_div]
    rw [inv_lt_inv₀ hn (Real.sqrt_pos.2 hTT), Real.sqrt_lt' hn, ← Complex.normSq_eq_norm_sq]
    linarith
end Formalism.FourierDecayAlt.P
