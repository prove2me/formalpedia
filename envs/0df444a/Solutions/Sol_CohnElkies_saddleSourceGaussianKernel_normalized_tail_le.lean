-- Prove2me | solution 1 for CohnElkies.saddleSourceGaussianKernel_normalized_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/3c5f2a07-4d0f-4c0a-b864-281cb8cebc21

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourceGaussianKernel_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_gaussian_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailSet_measurable
import Theorems.Thm_CohnElkies_saddleGaussian_cubic_tail_integral_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u z : ℝ}
    (hℓ : 0 < ℓ)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hz : 0 ≤ z)
    (hlarge : 12 ≤ ℓ * saddleSourceGaussianVariance ε ℓ u) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
          saddleSourceGaussianKernel ε ℓ u T) ≤
        4 * Real.sqrt (2 * Real.pi) *
          Real.exp (-(z ^ 2) / 8) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let k : ℝ := ℓ * V / 2
  let s : ℝ := Real.sqrt (ℓ * V)
  let R : ℝ := z / s
  have hproduct : 0 < ℓ * V := mul_pos hℓ hV
  have hs : 0 < s := by
    try dsimp [s]
    positivity
  have hk : 6 ≤ k := by
    try dsimp [k, V]
    linarith
  have hkpos : 0 < k := by linarith
  have hR : 0 ≤ R := by
    try dsimp [R]
    positivity
  have hgaussian := saddleSourceGaussianKernel_integrable hℓ hV
  have hweighted :=
    saddleGaussianTailWeight_mul_gaussian_integrable hkpos
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleSourceGaussianKernel ε ℓ u T ≤
        saddleGaussianTailWeight T * Real.exp (-k * T ^ 2) := by
    intro T hT
    have hw : 1 ≤ saddleGaussianTailWeight T := by
      unfold saddleGaussianTailWeight
      nlinarith [pow_nonneg (abs_nonneg T) 3]
    unfold saddleSourceGaussianKernel
    change Real.exp (-k * T ^ 2) ≤
      saddleGaussianTailWeight T * Real.exp (-k * T ^ 2)
    nlinarith [mul_le_mul_of_nonneg_right hw
      (Real.exp_pos (-k * T ^ 2)).le]
  have hcompare := setIntegral_mono_on
    hgaussian.integrableOn hweighted.integrableOn
      (saddleGaussianTailSet_measurable R) hpoint
  have htail := saddleGaussian_cubic_tail_integral_le hk hR
  have hexponent : (k / 4) * R ^ 2 = z ^ 2 / 8 := by
    have hsquare : s ^ 2 = ℓ * V := by
      try dsimp [s]
      exact Real.sq_sqrt hproduct.le
    try dsimp [k, R]
    field_simp [hs.ne']
    nlinarith [hsquare]
  have hroot :
      s * Real.sqrt (Real.pi / (k / 4)) =
        2 * Real.sqrt (2 * Real.pi) := by
    have hkquarter : 0 < k / 4 := by positivity
    have hratio : 0 ≤ Real.pi / (k / 4) := by positivity
    have hleft :
        0 ≤ s * Real.sqrt (Real.pi / (k / 4)) := by
      positivity
    have hright : 0 ≤ 2 * Real.sqrt (2 * Real.pi) := by
      positivity
    have hsquare :
        (s * Real.sqrt (Real.pi / (k / 4))) ^ 2 =
          (2 * Real.sqrt (2 * Real.pi)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hratio,
        Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      have hsquare' : s ^ 2 = ℓ * V := by
        try dsimp [s]
        exact Real.sq_sqrt hproduct.le
      rw [hsquare']
      try dsimp [k]
      have hV' : 0 < V := hV
      field_simp [hℓ.ne', hV'.ne']
      norm_num
    nlinarith
  have hexponent' : -(k / 4) * R ^ 2 = -(z ^ 2) / 8 := by
    nlinarith [hexponent]
  change
    s * (∫ T : ℝ in saddleGaussianTailSet R,
      saddleSourceGaussianKernel ε ℓ u T) ≤
      4 * Real.sqrt (2 * Real.pi) *
        Real.exp (-(z ^ 2) / 8)
  calc
    s * (∫ T : ℝ in saddleGaussianTailSet R,
      saddleSourceGaussianKernel ε ℓ u T) ≤
      s * (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcompare hs.le
    _ ≤ s * (2 * Real.exp (-(k / 4) * R ^ 2) *
      Real.sqrt (Real.pi / (k / 4))) := by
      exact mul_le_mul_of_nonneg_left htail hs.le
    _ = 4 * Real.sqrt (2 * Real.pi) *
      Real.exp (-(z ^ 2) / 8) := by
      rw [hexponent']
      calc
        s * (2 * Real.exp (-(z ^ 2) / 8) *
          Real.sqrt (Real.pi / (k / 4))) =
          2 * Real.exp (-(z ^ 2) / 8) *
            (s * Real.sqrt (Real.pi / (k / 4))) := by ring
        _ = 2 * Real.exp (-(z ^ 2) / 8) *
          (2 * Real.sqrt (2 * Real.pi)) := by rw [hroot]
        _ = _ := by ring
end CohnElkies
