-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:07.983804+00:00
-- url     : https://prove2.me/submissions/ef9ac7ac-9f76-4a99-8c3b-a1973535114d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_tauX_tmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_apply

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
theorem _root_.solution (τ : OE →+* R) (x : OE) : chi τ ((1 : ℤ_[l]) ⊗ₜ[ℤ] x) = residue R (τ x) := by
  rw [chi_apply, tauX_tmul, map_one, one_mul]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
