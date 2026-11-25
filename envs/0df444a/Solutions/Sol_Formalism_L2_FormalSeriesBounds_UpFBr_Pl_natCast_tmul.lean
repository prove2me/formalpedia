-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:08.903174+00:00
-- url     : https://prove2.me/submissions/66f4fe47-3ce7-4259-b30f-5a4963d7fb72

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
theorem _root_.solution (k : ℕ) (y : OE) : (k : ℤ_[l]) ⊗ₜ[ℤ] y = (1 : ℤ_[l]) ⊗ₜ[ℤ] ((k : OE) * y) := by
  have h1 : (k : ℤ_[l]) = (k : ℤ) • (1 : ℤ_[l]) := by simp
  have h2 : ((k : OE) * y) = (k : ℤ) • y := by simp
  rw [h1, h2, TensorProduct.smul_tmul]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
