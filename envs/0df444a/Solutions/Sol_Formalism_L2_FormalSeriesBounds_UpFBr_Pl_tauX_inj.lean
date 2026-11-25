-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.tauX_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:49:10.354174+00:00
-- url     : https://prove2.me/submissions/b649f080-303c-430d-bca9-21d6a4a5b86e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP

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
open TensorProduct IsLocalRing Polynomial
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.UpFBr Formalism.L2.FormalSeriesBounds.UpFBr.Pl
variable {l : ℕ} [Fact l.Prime] {OE : Type} [CommRing OE]
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Algebra ℤ_[l] R] {d : ℕ} [NeZero d]
  (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution {τ τ' : OE →+* R} (h : ∀ s, tauX (l := l) τ s = tauX τ' s) : τ = τ' := by
  ext x
  have hx := h (1 ⊗ₜ x)
  simpa [tauX, Algebra.TensorProduct.lift_tmul] using hx
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
