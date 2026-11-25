-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:58:33.011082+00:00
-- url     : https://prove2.me/submissions/0365f0b8-0c05-42a9-b0c5-e134f9f389c3

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_e
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_hb_of
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_inj
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_card_le_of_chars
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_alg


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
theorem _root_.solution (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hsep : ∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {n : ℕ}
    (b : Module.Basis (Fin n) ℤ_[l] (LinearMap.range (LinearMap.mulLeft ℤ_[l] e))) : d ≤ n := by
  have := card_le_of_chars (F := ℤ_[l]) (fun a => chi (l := l) (em a)) (chi_inj em hsep)
    ((residue R).comp (algebraMap ℤ_[l] R)) (fun a r => chi_alg (em a) r) e (chi_e em hl hε2 he)
    (fun i => (b i : ℤ_[l] ⊗[ℤ] OE)) (hb_of e b)
  simpa [ZMod.card] using this
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
