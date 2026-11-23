-- Prove2me | solution 1 for Formalism.ELL.comp_exp_coeff_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:28.107802+00:00
-- url     : https://prove2.me/submissions/b5340bac-70e7-4863-98ca-7219b99fc729

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_comp_exp_coeff_weight_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution : Formalism.ELL.CompExpWeight := Formalism.ELL.MultiplicativeWeight.comp_exp_coeff_weight_of
end Formalism.ELL
