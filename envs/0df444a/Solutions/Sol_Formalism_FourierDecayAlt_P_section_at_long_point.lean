-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.section_at_long_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:55:59.641998+00:00
-- url     : https://prove2.me/submissions/df12b80b-e378-4b1b-afa2-9218fb401e32

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lower_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_coordU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open G4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SectionLong := by
  intro n z hz l u hl hu
  have hk' := upperUni_conj hl
  refine ⟨coordU (wMat (n + 1) * l * wMat (n + 1) * u),
    ⟨l⁻¹, wMat (n + 1) * l * wMat (n + 1), lowerUni_inv hl, hk', ?_, lower_mul_inv hl, ?_⟩, ?_⟩
  · unfold ptLong
    rw [stab_smul hz]
    exact stab_exists hl
  · exact (upper_coordU (upperUni_mul hk' hu)).symm
  · rintro v ⟨k, k', _, _, h3, h4, h5⟩
    unfold ptLong at h3
    rw [stab_smul hz] at h3
    apply upper_injective
    rw [← h5, stab_right h4 h3, upper_coordU (upperUni_mul hk' hu)]
end Formalism.FourierDecayAlt.P
