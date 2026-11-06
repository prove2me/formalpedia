-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1750_original_full_cutoff_moving_physical_cell_L2_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:16:30.651306+00:00
-- url     : https://prove2.me/submissions/0258ecf3-d445-4e82-b4dd-b31e147e08e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- Shrinking physical time cells of the true original stopped-style jump martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (hH : ∀ k, StronglyMeasurable[𝓕.rightCont (s k)] (H k))
    (L : ℝ) (hL : 0 ≤ L) (hBound : ∀ k ω, |H k ω| ≤ L) :
    let N : ℕ → Ω → ℝ≥0∞ := fun k ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s k) (s k + T / (k : ℝ≥0)) ×ˢ
          Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℕ → ℝ := fun k =>
      ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal)
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, (H k ω * ((N k ω).toReal - r k))^2 ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by
  let N : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s k) (s k + T / (k : ℝ≥0)) ×ˢ
        Iic (-(1 / ((cut : ℝ) + 1))))
  let ν : ℝ≥0∞ := X.ν (Iic (-(1 / ((cut : ℝ) + 1))))
  let r : ℕ → ℝ := fun k =>
    ((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * ν).toReal)
  let I : ℕ → ℝ := fun k =>
    ∫ ω, (H k ω * ((N k ω).toReal - r k))^2 ∂P
  change Tendsto I atTop (nhds (0 : ℝ))
  have hBoundI (k : ℕ) : I k ≤ r k * L^2 := by
    have hIso :=
      (avram_p4_s3_interval_h_original_full_cutoff_bounded_predictable_L2_isometry_auto
        X (s k) (T / (k : ℝ≥0)) cut (H k) (hH k) L (hBound k)).2
    change I k = r k * ∫ ω, (H k ω)^2 ∂P at hIso
    rw [hIso]
    have hGlobalSM : StronglyMeasurable (H k) :=
      (hH k).mono (𝓕.rightCont.le (s k))
    have hLp : MemLp (H k) 2 P :=
      MemLp.of_bound hGlobalSM.aestronglyMeasurable L
        (Filter.Eventually.of_forall (fun ω => by
          simpa only [Real.norm_eq_abs] using hBound k ω))
    have hBdd (ω : Ω) : (H k ω)^2 ≤ L^2 := by
      have hprod : 0 ≤ (L - |H k ω|) * (L + |H k ω|) :=
        mul_nonneg (sub_nonneg.mpr (hBound k ω))
          (add_nonneg hL (abs_nonneg _))
      nlinarith [sq_abs (H k ω)]
    have hle := integral_mono (hLp.integrable_sq)
      (integrable_const (L^2)) hBdd
    have hIntBound : (∫ ω, (H k ω)^2 ∂P) ≤ L^2 := by
      simpa using hle
    exact mul_le_mul_of_nonneg_left hIntBound ENNReal.toReal_nonneg
  have hNonneg (k : ℕ) : 0 ≤ I k := by
    apply integral_nonneg
    intro ω
    exact sq_nonneg _
  have hInv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  let a : ℝ := (T : ℝ) * ν.toReal
  have hRate : Tendsto (fun k : ℕ => a / (k : ℝ))
      atTop (nhds (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => a) atTop (nhds a) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hConst.mul hInv
  have hUpperLimit : Tendsto (fun k : ℕ => L^2 * (a / (k : ℝ)))
      atTop (nhds (0 : ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => L^2) atTop (nhds (L^2)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using hConst.mul hRate
  have hUpper : ∀ᶠ k : ℕ in atTop, I k ≤ L^2 * (a / (k : ℝ)) :=
    (eventually_gt_atTop (0 : ℕ)).mono (fun k hk => by
      have hr := avram_p4_f2_physical_horizon_rate_real_div T ν k hk
      have hkNN : (k : ℝ≥0) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hk)
      have hb := hBoundI k
      change I k ≤
        (((((T / (k : ℝ≥0) : ℝ≥0) : ℝ≥0∞) * ν).toReal) * L^2)
        at hb
      rw [ENNReal.coe_div hkNN, hr] at hb
      nlinarith)
  have hLower : ∀ᶠ k : ℕ in atTop, (0 : ℝ) ≤ I k :=
    Filter.Eventually.of_forall hNonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (nhds (0 : ℝ))) hUpperLimit hLower hUpper
