-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.additive_char_one_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:18.045416+00:00
-- url     : https://prove2.me/submissions/904c2492-27e6-4c07-86db-e78bee222ae6

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution : psi3 1 ≠ 1 := by
  intro h
  have hn : ∀ n : ℕ, psi3 (n : ZMod 3) = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, AddChar.map_add_eq_mul, ih, h, one_mul]
  have hall : ∀ a : ZMod 3, psi3 a = 1 := by
    intro a
    have := hn a.val
    rwa [ZMod.natCast_zmod_val] at this
  have hprim := ZMod.isPrimitive_stdAddChar 3
  apply hprim (a := 1) one_ne_zero
  rw [AddChar.mulShift_one]
  ext a
  exact hall a
end Formalism.L2.SG.GGMirabolic.Inhab
