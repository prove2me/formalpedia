-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.latticeCoset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:33.787736+00:00
-- url     : https://prove2.me/submissions/998164f9-a111-42fc-9007-c302f5554eab

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_latOf_le
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_of_latOf_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.LatticeCoset := by
  intro K _ R n g h
  constructor
  · intro e
    exact ⟨isInt_of_latOf_le R g h (le_of_eq e.symm), isInt_of_latOf_le R h g (le_of_eq e)⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm (latOf_le R h g h2) (latOf_le R g h h1)
end Formalism.DoubleCosetMeasures.P
