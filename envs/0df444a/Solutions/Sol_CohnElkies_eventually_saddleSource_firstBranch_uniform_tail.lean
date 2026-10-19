-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_firstBranch_uniform_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/7126eeb0-5b76-4c06-8980-dd9d24e35d6a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_firstBranch_pos
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceGaussianVariance_upper_bound
import Theorems.Thm_CohnElkies_saddleSource_firstBranch_normalized_tail_bound
import Theorems.Thm_CohnElkies_saddleSourceFirstBranchVarianceCoefficient_pos
import Theorems.Thm_CohnElkies_tendsto_saddleFirstBranchTailLogMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ κ : ℝ, 0 < κ →
        ∀ᶠ ℓ : ℝ in atTop,
          ∀ u : ℝ,
            -1 < u →
            u ≤ 1 + ε / 2 →
            Real.log ℓ / 4 ≤ ℓ * (1 + u) →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance ε ℓ u) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) /
                      Real.sqrt
                        (ℓ * saddleSourceGaussianVariance ε ℓ u)),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping ε ℓ u T)) < κ := by
  have hsmall :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 / 4 := by
    have hnear : Tendsto (fun ε : ℝ => ε)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    filter_upwards
      [hnear.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with ε hε
    exact hε.le
  filter_upwards [self_mem_nhdsWithin, hsmall,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_upper_shortMargin_positive,
    eventually_saddleSourceGaussianVariance_firstBranch_pos]
    with ε hε hεsmall horder hmargin hVbranch
  change 0 < ε at hε
  intro κ hκ
  let c : ℝ := ε / (2 * Real.exp 1)
  let C : ℝ := saddleSourceFirstBranchVarianceCoefficient ε
  let U : ℝ := 2 + ε / 2
  have hc : 0 < c := by
    try dsimp [c]
    positivity
  have hC : 0 < C :=
    saddleSourceFirstBranchVarianceCoefficient_pos hε
  have hU : 0 < U := by
    try dsimp [U]
    positivity
  have hlogtop : Tendsto
      (fun ℓ : ℝ => Real.log ℓ / 4)
      atTop atTop :=
    Real.tendsto_log_atTop.atTop_div_const
      (by norm_num : (0 : ℝ) < 4)
  have hlogone := hlogtop.eventually
    (eventually_ge_atTop (1 : ℝ))
  have htail :=
    (tendsto_saddleFirstBranchTailLogMajorant
      hc hC).eventually (Iio_mem_nhds hκ)
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlogone,
    eventually_ge_atTop (6 / c),
    eventually_ge_atTop (6 * U / c),
    htail]
    with ℓ hℓ hlogoneℓ hlinbase hquadbase htailℓ
  intro u hulower huupper hlogscale
  let η : ℝ := 1 + u
  let V : ℝ := saddleSourceGaussianVariance ε ℓ u
  let z : ℝ := (ℓ * η) ^ (1 / 12 : ℝ)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hηU : η ≤ U := by
    try dsimp [η, U]
    linarith
  have hscale : 1 ≤ ℓ * η :=
    hlogoneℓ.trans hlogscale
  have hV : 0 < V := by
    try dsimp [V]
    exact hVbranch ℓ hℓ u hulower huupper
  have hmargin' :
      ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
        0 ≤ shortMargin ε a := by
    intro a ha
    have h := hmargin a ha
    linarith
  have hvariance :=
    upperFirstBranch_saddleSourceGaussianVariance_upper_bound
      hε hℓ hulower huupper horder hmargin' hscale
  have hupper : η * V ≤ C := by
    have hbound : V ≤ C / η := by
      simpa [V, η, C,
        saddleSourceFirstBranchVarianceCoefficient] using! hvariance
    calc
      η * V ≤ η * (C / η) :=
        mul_le_mul_of_nonneg_left hbound hη.le
      _ = C := by field_simp [hη.ne']
  have hlinear : 6 ≤ c * ℓ := by
    have h := (div_le_iff₀ hc).mp hlinbase
    nlinarith
  have hquadratic : 6 ≤ (c * ℓ) / η := by
    apply (le_div_iff₀ hη).mpr
    have h := (div_le_iff₀ hc).mp hquadbase
    nlinarith [mul_le_mul_of_nonneg_left hηU
      (by norm_num : (0 : ℝ) ≤ 6)]
  have hz : 0 ≤ z := by
    try dsimp [z]
    positivity
  have hsource := saddleSource_firstBranch_normalized_tail_bound
    (z := z) (C := C)
    hε hεsmall hℓ hulower huupper horder hmargin'
    hV hC hupper hz (by
      convert! hquadratic using 1; dsimp [c, η]; ring) (by
      convert! hlinear using 1; dsimp [c]; ring)
  have hlognonneg : 0 ≤ Real.log ℓ / 4 := by
    linarith
  have hpower :
      (Real.log ℓ / 4) ^ (1 / 6 : ℝ) ≤ z ^ 2 := by
    have hmono := Real.rpow_le_rpow
      hlognonneg hlogscale
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have hsquare :
        z ^ 2 = (ℓ * η) ^ (1 / 6 : ℝ) := by
      try dsimp [z]
      rw [← Real.rpow_natCast,
        ← Real.rpow_mul (mul_nonneg hℓ.le hη.le)]
      congr 1
      norm_num
    rw [hsquare]
    exact hmono
  have hrate : 0 < c / (4 * C) := by positivity
  have hexponential :
      Real.exp (-(c / (4 * C)) * z ^ 2) ≤
        Real.exp
          (-(c / (4 * C)) *
            (Real.log ℓ / 4) ^ (1 / 6 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hrate.le
      (show 0 ≤ z ^ 2 -
        (Real.log ℓ / 4) ^ (1 / 6 : ℝ) by linarith)]
  have hsqrt :
      Real.sqrt (C / (ℓ * η)) ≤
        Real.sqrt (C / (Real.log ℓ / 4)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left hC.le
      (by linarith : 0 < Real.log ℓ / 4)
      hlogscale
  change
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) < κ
  calc
    Real.sqrt (ℓ * V) *
      (∫ T : ℝ in saddleGaussianTailSet
        (z / Real.sqrt (ℓ * V)),
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      4 * Real.sqrt (Real.pi * C / c) *
        Real.exp (-(c / (4 * C)) * z ^ 2) +
          (16 / c) * Real.sqrt (C / (ℓ * η)) := by
        simpa [c, η, V] using! hsource
    _ ≤ saddleFirstBranchTailLogMajorant c C ℓ := by
      unfold saddleFirstBranchTailLogMajorant
      gcongr
    _ < κ := htailℓ
end CohnElkies
