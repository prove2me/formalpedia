-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.exampleZ_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:45.674067+00:00
-- url     : https://prove2.me/submissions/69695758-0652-4a67-9524-00bc630ade34

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ExampleZ
import Theorems.Thm_Formalism_HermitianLatticesTheory_exampleZ_two_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : (1 : Submodule ℤ ℚ) ⊓ Submodule.span ℤ {(2 : ℚ)} =
    Submodule.span ℤ {(2 : ℚ)} := inf_of_le_right exampleZ_two_le
end Formalism.HermitianLatticesTheory
