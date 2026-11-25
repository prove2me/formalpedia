-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.chi_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:09.90715+00:00
-- url     : https://prove2.me/submissions/84c52f75-cf42-4aff-b4c3-a5d0518c5443

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
theorem _root_.solution (hl : ((l : ℕ) : R) ∈ maximalIdeal R) (τ : OE →+* R) (s : ℤ_[l] ⊗[ℤ] OE) :
    chi τ (((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * s) = 0 := by
  have hl0 : ((l : ℕ) : ResidueField R) = 0 := by
    rw [← map_natCast (residue R), residue_eq_zero_iff]
    exact hl
  rw [map_mul, map_natCast, hl0, zero_mul]
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
