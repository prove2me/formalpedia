-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.UpFBr.Pl.prim_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:21:02.005709+00:00
-- url     : https://prove2.me/submissions/bf1e5d81-71d2-45d6-9a24-85d48448e9fe

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NatCastMulTmul
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieUpFBrPlP
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_chi_e
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_completeA
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_idem_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_UpFBr_Pl_key


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
theorem _root_.solution [Module.Free ℤ OE] [Module.Finite ℤ OE] (hl : ((l : ℕ) : R) ∈ maximalIdeal R)
    (hfrob : ∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) {ε : OE}
    (hε2 : ∀ a, em a ε - 1 ∈ maximalIdeal R)
    (hε3 : ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y)
    {e z : ℤ_[l] ⊗[ℤ] OE} (hee : e * e = e) (he : e - 1 ⊗ₜ ε = ((l : ℕ) : ℤ_[l] ⊗[ℤ] OE) * z)
    (f : ℤ_[l] ⊗[ℤ] OE) (hf : f * f = f) (hfe : f * e = f) : f = 0 ∨ f = e := by
  have := completeA (l := l) (OE := OE)
  have hz : ∀ g : ℤ_[l] ⊗[ℤ] OE, g * g = g → e * g = g → chi (em 0) g = 0 → g = 0 := by
    intro g hg heg h0
    obtain ⟨w, hw⟩ := key em hl hfrob hε3 he heg h0
    exact idem_zero (Ideal.span {((l : ℕ) : ℤ_[l] ⊗[ℤ] OE)}) hg
      (by rw [hw]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hu : chi (em 0) f * chi (em 0) f = chi (em 0) f := by rw [← map_mul, hf]
  have hu' : chi (em 0) f * (chi (em 0) f - 1) = 0 := by linear_combination hu
  rcases mul_eq_zero.1 hu' with h | h
  · left
    exact hz f hf (by rw [mul_comm]; exact hfe) h
  · right
    have := hz (e - f) (by linear_combination hee - 2 * hfe + hf) (by linear_combination hee - hfe)
      (by rw [map_sub, chi_e em hl hε2 he 0, sub_eq_zero.1 h, sub_self])
    exact (sub_eq_zero.1 this).symm
end Formalism.L2.FormalSeriesBounds.UpFBr.Pl
