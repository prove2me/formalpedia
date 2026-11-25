-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:23.895813+00:00
-- url     : https://prove2.me/submissions/d6443551-b855-4ec0-9085-d9a0c8342681

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
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
theorem _root_.solution (τ : OE →+* R) (r : ℤ_[l]) :
    chi τ (algebraMap ℤ_[l] (ℤ_[l] ⊗[ℤ] OE) r) = ((residue R).comp (algebraMap ℤ_[l] R)) r := by
  rw [chi_apply, AlgHom.commutes]
  rfl
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
