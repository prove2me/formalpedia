-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_finite_activity_closed_cap_generator_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:36:22.989435+00:00
-- url     : https://prove2.me/submissions/e956e465-db3d-4fb8-b69e-aaa63aaf624c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0  := by
  classical
  have hc : 0 < C.toReal := ENNReal.toReal_pos hC.ne' hFinite
  let y : ℕ → ℝ := fun n => C.toReal - C.toReal / ((n : ℝ) + 2)
  have hreal (n : ℕ) : 0 < y n ∧ y n < C.toReal := by
    dsimp [y]
    have hn : 0 < (n : ℝ) + 2 := by positivity
    constructor
    · apply (sub_pos).2
      exact (div_lt_iff₀ hn).2 (by nlinarith)
    · have hp : 0 < C.toReal / ((n : ℝ) + 2) := div_pos hc hn
      linarith
  have hinside (n : ℕ) : 0 < y n ∧ ENNReal.ofReal (y n) < C := by
    refine ⟨(hreal n).1, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal (hreal n).1.le hFinite).2 (hreal n).2
  have hzero : Tendsto (fun n : ℕ => C.toReal / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hs :=
      (tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 2)).const_div_atTop C.toReal
    convert hs using 1
    funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_ofNat]
  have hy : Tendsto y atTop (𝓝 C.toReal) := by
    simpa only [y, sub_zero] using (tendsto_const_nhds.sub hzero)
  have hwmeas : Measurable w :=
    avram_p3_e_compensator_original_ruin_extension_value_measurable
      w hwCont hwNeg
  have hcw : ContinuousOn w (Icc (0 : ℝ) C.toReal) :=
    hwCont.mono (fun r hr => hr.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcw
  have hM0 : 0 ≤ M := (norm_nonneg (w 0)).trans
    (hM 0 ⟨le_refl _, hc.le⟩)
  have hBound (r : ℝ) (hr : r ≤ C.toReal) : ‖w r‖ ≤ M := by
    by_cases hneg : r < 0
    · simp [hwNeg r hneg, hM0]
    · exact hM r ⟨le_of_not_gt hneg, hr⟩
  let g : ℝ → ℝ := fun _ => 2 * M
  haveI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) :=
    ⟨by simpa using hActivity⟩
  have hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))) :=
    integrable_const _
  have hMeas (n : ℕ) : AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ))) := by
    exact ((hwmeas.comp (measurable_const.add measurable_id)).sub
      measurable_const).aestronglyMeasurable
  have hDom (n : ℕ) : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    have hzle : y n + z ≤ C.toReal := by
      have ht := (hreal n).2
      have : z < 0 := hz
      linarith
    calc
      ‖w (y n + z) - w (y n)‖ ≤
          ‖w (y n + z)‖ + ‖w (y n)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hBound _ hzle)
        (hBound _ (hreal n).2.le)
      _ = ‖g z‖ := by simp [g, Real.norm_eq_abs, abs_of_nonneg hM0]; ring
  exact avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
    X hStanding hBV q w C hC hFinite hwCont hwNeg
    hwGen hwGrad y hy hinside g hg hMeas hDom
