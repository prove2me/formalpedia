-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.root_sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:40.43326+00:00
-- url     : https://prove2.me/submissions/6b7a78c8-d5f3-48e4-be94-2119742c97a0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_one_le_mul_of_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution {s : ℕ} (hs : 0 < s) {z z' : ℂ} (h : z ^ s = z' ^ s) (hne : z ≠ z') :
    ‖z‖ ≤ (s : ℝ) * ‖z - z'‖ := by
  by_cases hz : z = 0
  · rw [hz, norm_zero]; positivity
  have h1 : (z' / z) ^ s = 1 := by rw [div_pow, ← h, div_self (pow_ne_zero _ hz)]
  have h2 : z' / z ≠ 1 := by
    intro e
    exact hne ((div_eq_one_iff_eq hz).mp e).symm
  have h3 := one_le_mul_of_root hs h1 h2
  have e : z - z' = -(z * (z' / z - 1)) := by field_simp; ring
  rw [e, norm_neg, norm_mul]
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  nlinarith
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
