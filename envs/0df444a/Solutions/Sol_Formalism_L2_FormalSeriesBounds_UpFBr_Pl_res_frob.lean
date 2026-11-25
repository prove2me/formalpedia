-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.res_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:11.525786+00:00
-- url     : https://prove2.me/submissions/e13690ce-1ad6-423f-be6f-26c5941adef2

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul

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
theorem _root_.solution (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) (a : ZMod d) (x : OE) :
    residue R (em (a + 1) x) = residue R (em a x) ^ l := by
  have h := (residue_eq_zero_iff _).mpr (hfrob a x)
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
