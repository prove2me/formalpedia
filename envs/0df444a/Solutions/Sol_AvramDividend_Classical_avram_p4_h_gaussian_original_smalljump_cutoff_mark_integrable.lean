-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_smalljump_cutoff_mark_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:33:39.470079+00:00
-- url     : https://prove2.me/submissions/e106fa1e-ff49-4ec4-ba4d-d58da695cd82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original source's signed small-jump mark is integrable on every
separated finite-horizon negative band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc 0 T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))))
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
  classical
  let δ : ℝ := 1 / ((n : ℝ) + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let E : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ Ioc (-1 : ℝ) (-δ)
  have hE : MeasurableSet E := measurableSet_Ioc.prod measurableSet_Ioc
  have hsub : E ⊆ Ioc 0 T ×ˢ Iic (-δ) := by
    intro p hp
    exact ⟨hp.1, hp.2.2⟩
  have hSource : NX (Ioc 0 T ×ˢ Iic (-δ)) < ⊤ := by
    simpa only [NX, δ] using
      (avram_wave7_06_original_separated_negative_band_count_finite_every_path
        X ω T n)
  have hFin : NX E < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) hSource
  haveI : IsFiniteMeasure (NX.restrict E) :=
    isFiniteMeasure_restrict.mpr (ne_of_lt hFin)
  have hSm : AEStronglyMeasurable (fun p : ℝ≥0 × ℝ => p.2)
      (NX.restrict E) := measurable_snd.aestronglyMeasurable
  have hI : Integrable (fun p : ℝ≥0 × ℝ => p.2) (NX.restrict E) := by
    apply Integrable.of_bound hSm 1
    filter_upwards [ae_restrict_mem hE] with p hp
    have hmark : p.2 ∈ Ioc (-1 : ℝ) (-δ) := hp.2
    have hneg : p.2 ≤ 0 :=
      le_trans hmark.2 (neg_nonpos.mpr (le_of_lt hδ))
    rw [Real.norm_eq_abs, abs_of_nonpos hneg]
    linarith [hmark.1]
  exact hI
