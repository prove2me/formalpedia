-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.natCast_mul_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:30.330857+00:00
-- url     : https://prove2.me/submissions/94d3f7e0-96c1-4787-9694-d8524d0d6425

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_eq_tmul

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
theorem _root_.solution (k : ℕ) (z : ℤ_[l]) (y : OE) :
    ((k : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (z ⊗ₜ y) = ((k : ℤ_[l]) * z) ⊗ₜ y := by
  rw [natCast_eq_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
