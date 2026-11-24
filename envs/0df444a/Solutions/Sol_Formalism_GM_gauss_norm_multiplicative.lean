-- Prove2me | solution 1 for Formalism.GM.gauss_norm_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:02.800893+00:00
-- url     : https://prove2.me/submissions/75ab09ac-b7d9-42b6-970c-9da5ff2c346e

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Theorems.Thm_Formalism_GM_gaussR_mul_le
import Theorems.Thm_Formalism_GM_le_gaussR_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
namespace Formalism.GM
theorem _root_.solution : GaussMulRad := fun K _ _ ρ P Q hρ => le_antisymm (gaussR_mul_le ρ P Q) (le_gaussR_mul ρ hρ P Q)
end Formalism.GM
