-- Prove2me | solution 1 for GaussianPerimeter.uniformSphere_cap_le_capTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:55.382843+00:00
-- url     : https://prove2.me/submissions/2a7dbb38-13b9-45e9-b631-db8b82156139

module
public import Definitions.Def_GaussianPerimeter_SphereSections
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_SphereCap
public import Theorems.Thm_GaussianPerimeter_capNormalizer_pos
public import Theorems.Thm_GaussianPerimeter_capTail_eq_ballSections
public import Theorems.Thm_GaussianPerimeter_uniformSphere_cap_le_sectionRatio

section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
namespace GaussianPerimeter
private theorem sqrt_pow_eq_capProfile (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    (Real.sqrt (1 - x ^ 2)) ^ n = capProfile (n + 2) x := by
  have hx' : 0 ≤ 1 - x ^ 2 := by
    have : 0 ≤ (1 - x) * (1 + x) := mul_nonneg (by linarith [hx.2]) (by linarith [hx.1])
    nlinarith
  rw [capProfile, Nat.cast_add, Nat.cast_ofNat, add_sub_cancel_right,
    ← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hx']
  ring_nf
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n)
    {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : ‖v‖ = 1) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    uniformSphere (EuclideanSpace ℝ (Fin (n + 1)))
      {u | t ≤ ⟪v, (u : EuclideanSpace ℝ (Fin (n + 1)))⟫} ≤ ENNReal.ofReal (capTail n t) := by
  have : NeZero n := ⟨by omega⟩
  refine (uniformSphere_cap_le_sectionRatio n hv ht ht₁).trans_eq ?_
  have h₁ : (∫ x in t..1, (Real.sqrt (1 - x ^ 2)) ^ n) =
      ∫ x in t..1, capProfile (n + 2) x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ht₁.le] at hx
    exact sqrt_pow_eq_capProfile n ⟨(by linarith : (-1 : ℝ) ≤ t).trans hx.1, hx.2⟩
  have h₂ : (∫ x in (-1 : ℝ)..1, (Real.sqrt (1 - x ^ 2)) ^ n) = capNormalizer (n + 2) := by
    unfold capNormalizer
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    exact sqrt_pow_eq_capProfile n hx
  rw [sqrt_pow_eq_capProfile n ⟨by linarith, ht₁.le⟩, h₁, h₂,
    capTail_eq_ballSections hn ht.le ht₁.le, ENNReal.ofReal_div_of_pos (capNormalizer_pos (by omega))]
end GaussianPerimeter
