-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.negperp_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:28.458506+00:00
-- url     : https://prove2.me/submissions/6556cd0b-fa16-4795-a97e-3acb28481538

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sig_norm

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
    (herm : ∀ x y : U, star (h x y) = h y x) (A N : Submodule K U)
    (hN : ∀ n ∈ N, ∀ u ∈ A, h n u = 0) (z₀ : U) (_hz₀ : z₀ ∈ A)
    (pos : ∀ w ∈ A, h w z₀ = 0 → w ∉ N → 0 < (σ (h w w)).re)
    (z : U) (hz : z ∈ A) (hzn : (σ (h z z)).re < 0) (w : U) (hw : w ∈ A) (hwz : h w z = 0)
    (hwN : w ∉ N) : 0 < (σ (h w w)).re := by
  by_contra hneg
  push_neg at hneg
  have herm0 : ∀ x y : U, h x y = 0 → h y x = 0 := fun x y hxy => by rw [← herm x y, hxy, star_zero]
  have hzz : h z z ≠ 0 := by
    intro h0
    rw [h0, map_zero, Complex.zero_re] at hzn
    exact lt_irrefl _ hzn
  have hwz' : h z w = 0 := herm0 _ _ hwz
  by_cases hz0 : h z z₀ = 0
  · have hzN : z ∉ N := fun hzN => hzz (hN z hzN z hz)
    have := pos z hz hz0 hzN
    linarith
  · obtain ⟨a, ha_def⟩ : ∃ a : K, a = h w z₀ := ⟨_, rfl⟩
    obtain ⟨b, hb_def⟩ : ∃ b : K, b = -h z z₀ := ⟨_, rfl⟩
    have hp : a • z + b • w ∈ A := A.add_mem (A.smul_mem _ hz) (A.smul_mem _ hw)
    have hpz0 : h (a • z + b • w) z₀ = 0 := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [ha_def, hb_def]
      ring
    have hb : b ≠ 0 := by
      rw [hb_def]
      exact neg_ne_zero.2 hz0
    have hpN : a • z + b • w ∉ N := by
      intro hpN
      have h1 : h (a • z + b • w) z = 0 := hN _ hpN z hz
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hwz, mul_zero,
        add_zero] at h1
      have ha : a = 0 := (mul_eq_zero.1 h1).resolve_right hzz
      apply hwN
      have hw' : w = b⁻¹ • (a • z + b • w) := by
        rw [ha, zero_smul, zero_add, smul_smul, inv_mul_cancel₀ hb, one_smul]
      rw [hw']
      exact N.smul_mem _ hpN
    have hpos := pos _ hp hpz0 hpN
    have hpp : h (a • z + b • w) (a • z + b • w) = a * star a * h z z + b * star b * h w w := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_smulₛₗ,
        starRingEnd_apply, hwz, hwz']
      ring
    rw [hpp, map_add, Complex.add_re, sig_norm σ hσ, sig_norm σ hσ] at hpos
    have h1 := Complex.normSq_nonneg (σ a)
    have h2 := Complex.normSq_nonneg (σ b)
    nlinarith [mul_nonneg h1 (neg_nonneg.2 hzn.le), mul_nonneg h2 (neg_nonneg.2 hneg)]
end Formalism.HermitianLatticeCounting.P
