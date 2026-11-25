-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:06:08.733688+00:00
-- url     : https://prove2.me/submissions/95feaf30-3140-4d25-a1d3-06d7d196011c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CompleteOfBasis
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_DetNeZeroOfChars
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_tmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_natCast_mul_tmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_decomp
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_one_tmul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_l
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_mem_all

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
variable {d : ℕ} [NeZero d] (em : ZMod d → OE →+* R)
namespace Formalism.L2.FormalSeriesBounds.UpFBr.Pl
theorem _root_.solution (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z) {s : ℤ_[l] ⊗[ℤ] OE}
    (hs : e * s = s) (h0 : chi (em 0) s = 0) : ∃ w, s = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * w := by
  obtain ⟨x, s', hs'⟩ := decomp s
  have hx0 : em 0 x ∈ maximalIdeal R := by
    rw [hs', map_add, chi_one_tmul, chi_l hl, add_zero, residue_eq_zero_iff] at h0
    exact h0
  obtain ⟨y, hy⟩ := hε x (mem_all em hfrob hx0)
  have hkey : (1 : ℤ_[l]) ⊗ₜ[ℤ] ε * (1 ⊗ₜ x) = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * (1 ⊗ₜ y) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hy, natCast_mul_tmul, mul_one, natCast_tmul]
  refine ⟨1 ⊗ₜ y + z * (1 ⊗ₜ x) + e * s', ?_⟩
  linear_combination (-1 : ℤ_[l] ⊗[ℤ] OE) * hs + e * hs' + (1 ⊗ₜ x) * he + hkey
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
