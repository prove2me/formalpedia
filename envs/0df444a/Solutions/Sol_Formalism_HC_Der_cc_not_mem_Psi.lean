-- Prove2me | solution 1 for Formalism.HC.Der.cc_not_mem_Psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:11.139818+00:00
-- url     : https://prove2.me/submissions/b065a241-0a74-4ef4-a1b0-16e8e67102c5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp

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
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : φ.cc ∉ φ.Psi := by
  intro h
  have h1 : φ.chD φ.cc = 1 := MonoidHom.mem_ker.mp h
  have h2 : φ.chD φ.cc = -1 := rfl
  rw [h2] at h1
  exact absurd (congrArg Units.val h1) (by norm_num)
end Formalism.HC.Der
