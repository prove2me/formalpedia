-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.besselK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:41.190639+00:00
-- url     : https://prove2.me/submissions/8e970422-1180-4615-919d-30a0c3d2b1c4

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_herm_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (hσ : ∀ x : K, σ (star x) = star (σ x))
    (herm : ∀ x y : U, star (h x y) = h y x) (hnn : ∀ x : U, 0 ≤ (σ (h x x)).re) {s : ℕ}
    (g : Fin s → U) (horth : ∀ a b, a ≠ b → h (g a) (g b) = 0) (hd : ∀ a, h (g a) (g a) ≠ 0) (y : U) :
    ∑ a, ‖σ (h (g a) y)‖ ^ 2 / (σ (h (g a) (g a))).re ≤ (σ (h y y)).re := by
  let c : Fin s → K := fun a => h y (g a) / h (g a) (g a)
  set y' : U := y - ∑ a, c a • g a with hy'
  have h1 : ∀ b, h y' (g b) = 0 := by
    intro b
    simp only [hy', map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single b]
    · simp only [c]; rw [div_mul_cancel₀ _ (hd b), sub_self]
    · intro a _ ha; rw [horth a b ha, mul_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  have h2 : h y' y' = h y' y := by
    conv_lhs => rw [hy', (h y').map_sub, map_sum]
    simp [h1]
  have h3 : h y' y = h y y - ∑ a, c a * h (g a) y := by
    simp only [hy', map_sub, map_sum, map_smul, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul]
  have h4 : ∀ a, (σ (c a * h (g a) y)).re = ‖σ (h (g a) y)‖ ^ 2 / (σ (h (g a) (g a))).re := by
    intro a
    simp only [c]
    rw [map_mul, map_div₀, ← herm (g a) y, hσ, herm_real σ h hσ herm (g a)]
    set v := σ (h (g a) y) with hv
    set dd := (σ (h (g a) (g a))).re with hdd
    have e : star v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have e2 : star v / (dd : ℂ) * v = ((‖v‖ ^ 2 / dd : ℝ) : ℂ) := by
      rw [div_mul_eq_mul_div, e]; push_cast; rfl
    rw [e2, Complex.ofReal_re]
    simp
  have h5 := hnn y'
  rw [h2, h3, map_sub, map_sum, Complex.sub_re, Complex.re_sum] at h5
  simp only [h4] at h5
  linarith
end Formalism.HermitianLatticeCounting.P
