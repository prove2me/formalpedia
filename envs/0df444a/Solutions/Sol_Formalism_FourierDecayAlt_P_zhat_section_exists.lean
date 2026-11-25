-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.zhat_section_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:46.083369+00:00
-- url     : https://prove2.me/submissions/7a4ddd99-c0ae-414a-87d9-264e94cc8e7b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2_tau_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_standard_flag_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_map_frame
import Theorems.Thm_Formalism_FourierDecayAlt_P_zhat_equivalence
import Theorems.Thm_Formalism_FourierDecayAlt_P_zhat_section_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.ZhatSection :=
  zhat_section_of_parts zhat_equivalence unipotent_map_frame c2_tau_mem standard_flag_property
end Formalism.FourierDecayAlt.P
