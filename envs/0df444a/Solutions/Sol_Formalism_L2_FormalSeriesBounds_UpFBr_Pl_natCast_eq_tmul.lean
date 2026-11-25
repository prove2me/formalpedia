-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_eq_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:10.708678+00:00
-- url     : https://prove2.me/submissions/65f96afe-9748-4823-9ee0-c22ff6421d3f

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
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (k : ℕ) : ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) = (k : ℤ_[l]) ⊗ₜ (1 : OE) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, ih, Nat.cast_succ, TensorProduct.add_tmul, Algebra.TensorProduct.one_def]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
