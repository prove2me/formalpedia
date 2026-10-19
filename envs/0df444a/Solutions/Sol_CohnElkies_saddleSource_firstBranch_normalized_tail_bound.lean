-- Prove2me | solution 1 for CohnElkies.saddleSource_firstBranch_normalized_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/751b89c1-8403-41ce-854c-095209b52dc5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSource_firstBranch_weighted_tail_le
import Theorems.Thm_CohnElkies_saddleFirstBranch_normalizedGaussian_prefactor_le
import Theorems.Thm_CohnElkies_saddleFirstBranch_normalizedGaussian_exponent_le
import Theorems.Thm_CohnElkies_saddleFirstBranch_normalizedLinear_prefactor_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u z C : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hV : 0 < saddleSourceGaussianVariance ε ℓ u)
    (hC : 0 < C)
    (hupper :
      (1 + u) * saddleSourceGaussianVariance ε ℓ u ≤ C)
    (hz : 0 ≤ z)
    (hquadratic :
      6 ≤ (ε * ℓ / (2 * Real.exp 1)) / (1 + u))
    (hlinear : 6 ≤ ε * ℓ / (2 * Real.exp 1)) :
    Real.sqrt (ℓ * saddleSourceGaussianVariance ε ℓ u) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt
          (ℓ * saddleSourceGaussianVariance ε ℓ u)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt
          (Real.pi * C / (ε / (2 * Real.exp 1))) *
        Real.exp
          (-(ε / (2 * Real.exp 1) / (4 * C)) * z ^ 2) +
        (16 / (ε / (2 * Real.exp 1))) *
          Real.sqrt (C / (ℓ * (1 + u))) := by
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let η : ℝ := 1 + u
  let c : ℝ := ε / (2 * Real.exp 1)
  let R : ℝ := z / Real.sqrt (ℓ * V)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hR : 0 ≤ R := by
    try dsimp [R]
    positivity
  have htail := saddleSource_firstBranch_weighted_tail_le
    hε hεsmall hℓ hulower huupper horder hmargin
    hR hquadratic hlinear
  have hscale :
      ε * ℓ / (2 * Real.exp 1) = c * ℓ := by
    try dsimp [c]
    ring
  have hpref := saddleFirstBranch_normalizedGaussian_prefactor_le
    hℓ hV hη hc hupper
  have hexponent :=
    saddleFirstBranch_normalizedGaussian_exponent_le
      (z := z) hℓ hV hη hc hC hupper
  have hlinearPref :=
    saddleFirstBranch_normalizedLinear_prefactor_le
      hℓ hV hη hC hupper
  have hsqrt : 0 ≤ Real.sqrt (ℓ * V) :=
    Real.sqrt_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left htail hsqrt
  have hexpgaussian :
      Real.exp
          (-((c * ℓ / η) / 4) * R ^ 2) ≤
        Real.exp (-(c / (4 * C)) * z ^ 2) := by
    apply Real.exp_le_exp.mpr
    try dsimp [R]
    nlinarith [hexponent]
  have hexplinear :
      Real.exp (-((c * ℓ) / 4) * R) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hcl : 0 ≤ c * ℓ :=
      (mul_pos hc hℓ).le
    nlinarith
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt (Real.pi * C / c) *
          Real.exp (-(c / (4 * C)) * z ^ 2) +
        (16 / c) * Real.sqrt (C / (ℓ * η))
  rw [hscale] at hscaled
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      Real.sqrt (ℓ * V) *
        (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
            Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) +
          2 * Real.exp (-((c * ℓ) / 4) * R) *
            (2 / ((c * ℓ) / 4))) at hscaled
  calc
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet R,
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      Real.sqrt (ℓ * V) *
        (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
            Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) +
          2 * Real.exp (-((c * ℓ) / 4) * R) *
            (2 / ((c * ℓ) / 4))) := hscaled
    _ ≤ 4 * Real.sqrt (Real.pi * C / c) *
          Real.exp (-(c / (4 * C)) * z ^ 2) +
        (16 / c) * Real.sqrt (C / (ℓ * η)) := by
      have hfirst :
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
              Real.sqrt (Real.pi / ((c * ℓ / η) / 4))) ≤
          4 * Real.sqrt (Real.pi * C / c) *
            Real.exp (-(c / (4 * C)) * z ^ 2) := by
        calc
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ / η) / 4) * R ^ 2) *
              Real.sqrt (Real.pi / ((c * ℓ / η) / 4))) =
            2 *
              (Real.sqrt (ℓ * V) *
                Real.sqrt (Real.pi / ((c * ℓ / η) / 4))) *
              Real.exp (-((c * ℓ / η) / 4) * R ^ 2) := by
                ring
          _ ≤ 2 *
              (2 * Real.sqrt (Real.pi * C / c)) *
              Real.exp (-(c / (4 * C)) * z ^ 2) := by
                gcongr
          _ = _ := by ring
      have hsecond :
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ) / 4) * R) *
              (2 / ((c * ℓ) / 4))) ≤
          (16 / c) * Real.sqrt (C / (ℓ * η)) := by
        calc
          Real.sqrt (ℓ * V) *
            (2 * Real.exp (-((c * ℓ) / 4) * R) *
              (2 / ((c * ℓ) / 4))) =
              (16 / c) *
                (Real.sqrt (ℓ * V) / ℓ) *
                Real.exp (-((c * ℓ) / 4) * R) := by
              field_simp [hc.ne', hℓ.ne']; ring
          _ ≤ (16 / c) *
                Real.sqrt (C / (ℓ * η)) * 1 := by
                gcongr
          _ = _ := by ring
      nlinarith [hfirst, hsecond]
end CohnElkies
