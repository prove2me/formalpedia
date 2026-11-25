-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.tauX_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:12.188841+00:00
-- url     : https://prove2.me/submissions/fa9bce1c-d711-4fcc-8295-054fe9d672e0

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
theorem _root_.solution {R : Type} [CommRing R] [Algebra ℤ_[l] R] (τ : OE →+* R) (z : ℤ_[l]) (x : OE) :
    tauX τ (z ⊗ₜ x) = algebraMap ℤ_[l] R z * τ x := by
  simp [tauX]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
