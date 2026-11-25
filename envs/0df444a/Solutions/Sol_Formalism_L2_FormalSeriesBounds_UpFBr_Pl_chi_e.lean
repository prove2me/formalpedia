-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:46:29.440635+00:00
-- url     : https://prove2.me/submissions/eec1f29f-8618-452c-9a31-7b3efee6473a

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
theorem _root_.solution (hl : ((l : ℕ) : R) ∈ maximalIdeal R) {ε : OE} (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) (a : ZMod d) : chi (em a) e = 1 := by
  have ht : tauX (l := l) (em a) (1 ⊗ₜ ε) = em a ε := by
    simp [tauX, Algebra.TensorProduct.lift_tmul]
  have he' : e = 1 ⊗ₜ ε + ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z := sub_eq_iff_eq_add'.1 he
  change residue R (tauX (l := l) (em a) e) = 1
  have h1 : residue R ((l : ℕ) : R) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hl
  have h2 : residue R (em a ε) = 1 := by
    rw [← sub_eq_zero, ← map_one (residue R), ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hε2 a
  rw [he', map_add, map_mul, map_natCast, ht, map_add, map_mul, h1, h2, zero_mul, add_zero]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
