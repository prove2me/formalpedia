-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.mod_four_reduction_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:25.567842+00:00
-- url     : https://prove2.me/submissions/3d54595c-8834-48f1-b2c2-3bbf0a82087f

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
theorem _root_.solution (N : ℕ) (h : 4 ∣ 2 ^ N) : r4 N h (-1) = -1 := by
  show (ZMod.castHom h (ZMod 4)) (((-1 : (ZMod (2 ^ N))ˣ) : ZMod (2 ^ N))) = -1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
