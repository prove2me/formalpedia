-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:08.0428+00:00
-- url     : https://prove2.me/submissions/604c6d83-9a60-47ef-9d4a-249734e37dc0

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
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) : chi τ s = residue R (tauX τ s) := rfl
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
