-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.neighbourConstruct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:03:21.735296+00:00
-- url     : https://prove2.me/submissions/cbbb01f8-868f-4bd6-9ff2-969426a037ab

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_NeighbourConstruct
import Theorems.Thm_Formalism_HermitianLatticesTheory_neighbourConstruct_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open nonZeroDivisors
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : NeighbourConstruct := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs _ hstar P hP hP0 L hLat hL x hx hxP hxx
  exact neighbourConstruct_main h hs hstar P hP hP0 L hLat hL x hx hxP hxx
end Formalism.HermitianLatticesTheory
