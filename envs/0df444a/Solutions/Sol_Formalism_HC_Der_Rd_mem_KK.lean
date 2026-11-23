-- Prove2me | solution 1 for Formalism.HC.Der.Rd.mem_KK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:17.517616+00:00
-- url     : https://prove2.me/submissions/337a3448-eec3-42fc-9c8c-072f001e26de

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution {f : ℕ} {u : (ZMod N)ˣ} : u ∈ KK N f ↔ (u : ZMod N).val ≡ 1 [MOD f] := by
  simp [KK]
end Formalism.HC.Der.Rd
