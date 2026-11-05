-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_discounted_HJB_drift_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:42:35.142989+00:00
-- url     : https://prove2.me/submissions/67342538-3fe9-4dab-8c51-d50f9c7abeda

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
(E : Set (ℝ≥0 × Ω)) (hEmeas : MeasurableSet E)
(hUpm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) (H : ℝ → ℝ) (hHm : Measurable H) :
AEStronglyMeasurable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  have ht : Measurable (fun p : ℝ≥0 × Ω => (p.1 : ℝ)) :=
    NNReal.continuous_coe.measurable.comp measurable_fst
  have hd : Measurable (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) :=
    ((measurable_const.mul ht).neg).exp
  have hf : Measurable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) :=
    (hd.mul (hHm.comp hUpm)).ite hEmeas measurable_const
  exact hf.aestronglyMeasurable
