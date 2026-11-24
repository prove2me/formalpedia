-- Prove2me | solution 1 for Formalism.HN.degree_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:30.110668+00:00
-- url     : https://prove2.me/submissions/00f7fb7b-3db4-4fe9-bcd8-aa2d622a1167

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Theorems.Thm_Formalism_HN_degSupermod_of
import Theorems.Thm_Formalism_HN_degree_supermodular_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w
namespace Formalism.HN
theorem _root_.solution : DegSupermod := degSupermod_of degree_supermodular_integral
end Formalism.HN
