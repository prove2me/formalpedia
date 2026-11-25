-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.mem_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:34.620463+00:00
-- url     : https://prove2.me/submissions/9c80753a-c355-46f3-a5c9-3d5c7c306fa3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_res_frob_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
variable {d : ℕ} [NeZero d] (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {x : OE}
    (h : em 0 x ∈ maximalIdeal R) (a : ZMod d) : em a x ∈ maximalIdeal R := by
  have hk := res_frob_pow em hfrob 0 x a.val
  rw [zero_add, ZMod.natCast_zmod_val] at hk
  rw [← residue_eq_zero_iff, hk, (residue_eq_zero_iff _).mpr h,
    zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
