-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.reverseCS_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:34.633988+00:00
-- url     : https://prove2.me/submissions/612bcbb6-949b-4614-844e-2785e598e04b

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_herm_im
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_negperp_gen

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
    (hN : ∀ n ∈ N, ∀ u ∈ A, h n u = 0) (z₀ : U) (hz₀ : z₀ ∈ A)
    (pos : ∀ w ∈ A, h w z₀ = 0 → w ∉ N → 0 < (σ (h w w)).re)
    (z : U) (hz : z ∈ A) (hzn : (σ (h z z)).re < 0) (z' : U) (hz' : z' ∈ A) :
    (σ (h z z)).re * (σ (h z' z')).re ≤ Complex.normSq (σ (h z z')) ∧
      (h z z * h z' z' = h z z' * star (h z z') → ∃ c : K, z' - c • z ∈ N) := by
  have hα : h z z ≠ 0 := by
    intro h0
    rw [h0, map_zero, Complex.zero_re] at hzn
    exact lt_irrefl _ hzn
  have hαs : star (h z z) = h z z := herm z z
  obtain ⟨β, hβdef⟩ : ∃ β : K, β = h z' z := ⟨_, rfl⟩
  have hβs : h z z' = star β := by rw [hβdef, herm]
  obtain ⟨w, hwdef⟩ : ∃ w : U, w = z' - (β / h z z) • z := ⟨_, rfl⟩
  have hwA : w ∈ A := by
    rw [hwdef]
    exact A.sub_mem hz' (A.smul_mem _ hz)
  have hwz : h w z = 0 := by
    rw [hwdef]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← hβdef, div_mul_cancel₀ β hα, sub_self]
  have hww : h z z * h w w = h z z * h z' z' - β * star β := by
    rw [hwdef]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_smulₛₗ,
      starRingEnd_apply]
    rw [← hβdef, hβs, star_div₀, hαs]
    field_simp
    ring
  have hwwre : 0 ≤ (σ (h w w)).re := by
    by_cases hwN : w ∈ N
    · rw [hN w hwN w hwA, map_zero, Complex.zero_re]
    · exact (negperp_gen σ h hσ herm A N hN z₀ hz₀ pos z hz hzn w hwA hwz hwN).le
  have him_zz := herm_im σ h hσ herm z
  have him_ww := herm_im σ h hσ herm w
  have him_z'z' := herm_im σ h hσ herm z'
  have hre_mul : ∀ p q : ℂ, p.im = 0 → q.im = 0 → (p * q).re = p.re * q.re := fun p q hp hq => by
    rw [Complex.mul_re, hp, hq, mul_zero, sub_zero]
  have hs : ∀ t : ℂ, star t = (starRingEnd ℂ) t := fun t => rfl
  have hns : (σ β * star (σ β)).re = Complex.normSq (σ β) := by
    rw [hs]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have e1 := congrArg (fun t => (σ t).re) hww
  simp only [map_mul, map_sub] at e1
  rw [hre_mul _ _ him_zz him_ww, Complex.sub_re, hre_mul _ _ him_zz him_z'z', hσ, hns] at e1
  have hnsq : Complex.normSq (σ (h z z')) = Complex.normSq (σ β) := by
    rw [hβs, hσ, hs, Complex.normSq_conj]
  constructor
  · rw [hnsq]
    have h3 : (σ (h z z)).re * (σ (h w w)).re ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hzn.le, hwwre⟩)
    linarith
  · intro heq
    have h0 : h z z * h w w = 0 := by
      rw [hww, heq, hβs, star_star]
      ring
    have hw0 : h w w = 0 := (mul_eq_zero.1 h0).resolve_left hα
    have hwN : w ∈ N := by
      by_contra hwN
      have h4 := negperp_gen σ h hσ herm A N hN z₀ hz₀ pos z hz hzn w hwA hwz hwN
      rw [hw0, map_zero, Complex.zero_re] at h4
      exact lt_irrefl _ h4
    refine ⟨β / h z z, ?_⟩
    rw [← hwdef]
    exact hwN
end Formalism.HermitianLatticeCounting.P
