-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.res_frob_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:09.474958+00:00
-- url     : https://prove2.me/submissions/d507332e-1dd1-4376-bed1-b640b96dffa6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_res_frob

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
    ∀ k : ℕ, residue R (em (a + (k : ZMod d)) x) = residue R (em a x) ^ (l ^ k)
  | 0 => by simp
  | k + 1 => by
    have e : a + ((k + 1 : ℕ) : ZMod d) = (a + (k : ZMod d)) + 1 := by push_cast; ring
    rw [e, res_frob em hfrob, solution hfrob a x k, ← pow_mul, pow_succ]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
