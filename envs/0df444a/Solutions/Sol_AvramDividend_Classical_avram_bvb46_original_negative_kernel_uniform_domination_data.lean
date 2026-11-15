-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb46_original_negative_kernel_uniform_domination_data
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:45:39.030367+00:00
-- url     : https://prove2.me/submissions/45276166-72f0-401e-82fa-c15558702a35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_ruin_extension_value_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    ∃ g : ℝ → ℝ,
      Integrable g (X.ν.restrict (Iio (0 : ℝ))) ∧
      (∀ n : ℕ, AEStronglyMeasurable
        (fun z : ℝ => w (C.toReal / ((n : ℝ) + 2) + z) -
          w (C.toReal / ((n : ℝ) + 2)))
        (X.ν.restrict (Iio (0 : ℝ)))) ∧
      (∀ n : ℕ, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
        ‖w (C.toReal / ((n : ℝ) + 2) + z) -
          w (C.toReal / ((n : ℝ) + 2))‖ ≤ g z)  := by
  classical
  have hc : 0 < C.toReal := ENNReal.toReal_pos hC.ne' hFinite
  let y : ℕ → ℝ := fun n => C.toReal / ((n : ℝ) + 2)
  have hreal (n : ℕ) : 0 < y n ∧ y n < C.toReal := by
    dsimp [y]
    have hn : 0 < (n : ℝ) + 2 := by positivity
    constructor
    · exact div_pos hc hn
    · apply (div_lt_iff₀ hn).2
      nlinarith
  have hwmeas : Measurable w :=
    avram_p3_e_compensator_original_ruin_extension_value_measurable
      w hwCont hwNeg
  have hcw : ContinuousOn w (Icc (0 : ℝ) C.toReal) :=
    hwCont.mono (fun r hr => hr.1)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcw
  have hM0 : 0 ≤ M :=
    (norm_nonneg (w 0)).trans (hM 0 ⟨le_refl _, hc.le⟩)
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
      ‖w (y n + z) - w (y n)‖ ≤ g z := by
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
      _ = g z := by dsimp [g]; ring
  exact ⟨g, hg, hMeas, hDom⟩
