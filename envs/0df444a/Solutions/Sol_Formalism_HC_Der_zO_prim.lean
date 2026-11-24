-- Prove2me | solution 1 for Formalism.HC.Der.zO_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:31:29.083495+00:00
-- url     : https://prove2.me/submissions/ab4cfb5b-ba71-440a-b0ca-bb09f44dd5d2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (N : ℕ) [NeZero N]
namespace Formalism.HC.Der
theorem _root_.solution : IsPrimitiveRoot (zO N) N := by
  exact (Cond.z_spec N).toInteger_isPrimitiveRoot
end Formalism.HC.Der
