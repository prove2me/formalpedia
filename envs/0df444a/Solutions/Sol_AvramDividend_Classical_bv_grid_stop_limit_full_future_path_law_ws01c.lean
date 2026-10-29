-- Prove2me | solution 1 for AvramDividend.Classical.bv_grid_stop_limit_full_future_path_law_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:53:06.602469+00:00
-- url     : https://prove2.me/submissions/b17de7d1-8555-4876-8442-c98556a36f1b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw
import Theorems.Thm_AvramDividend_Classical_cross_sample_path_law_eq_of_all_finite_vector_laws
import Theorems.Thm_AvramDividend_Classical_bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_grid_right_approx_future_vector_law_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (grid : ℕ → Ω → ℝ≥0) (raw : Ω → ℝ≥0)
    (hGridTends : ∀ ω, Tendsto (fun n => grid n ω) atTop (𝓝 (raw ω)))
    (hGridAbove : ∀ ω n, raw ω ≤ grid n ω)
    (hGridStop : ∀ n s, MeasurableSet[ℱ s] {ω : Ω | grid n ω ≤ s})
    (hRawMeas : Measurable raw) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (raw ω + t) ω - X.X (raw ω) ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  haveI := X.isProbability
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X (raw ω + t) ω - X.X (raw ω) ω
  let Z : Ω → (ℝ≥0 → ℝ) :=
    fun ω t => X.X t ω
  let Ygrid : ℕ → Ω → (ℝ≥0 → ℝ) :=
    fun n ω t => X.X (grid n ω + t) ω - X.X (grid n ω) ω
  have hY : Measurable Y :=
    bv_actual_shifted_path_measurable_of_clock_measurable_ws01c
      X raw hRawMeas
  have hZ : Measurable Z := levy_wholePath_measurable X
  have hGridStopping (n : ℕ) :
      IsStoppingTime ℱ
        (fun ω : Ω => (grid n ω : WithTop ℝ≥0)) := by
    intro s
    simpa only [WithTop.coe_le_coe] using hGridStop n s
  have hGridMeas (n : ℕ) : Measurable (Ygrid n) :=
    levy_finiteStopping_stoppedFuturePath_measurable
      X (grid n) (hGridStopping n)
  have hGridLaw (n : ℕ) :
      Measure.map (Ygrid n) P = Measure.map Z P :=
    levy_finiteStopping_shiftedFuturePath_sameLaw
      X (grid n) (hGridStop n)
  have hVectorLaw (J : Finset ℝ≥0) :
      Measure.map (fun ω : Ω => fun j : J => Y ω j.1) P =
      Measure.map (fun ω : Ω => fun j : J => Z ω j.1) P := by
    let πJ : (ℝ≥0 → ℝ) → (J → ℝ) :=
      fun f j => f j.1
    have hπJ : Measurable πJ :=
      measurable_pi_iff.mpr (fun j => measurable_pi_apply j.1)
    have hVecY : Measurable (fun ω : Ω => fun j : J => Y ω j.1) :=
      hπJ.comp hY
    have hVecZ : Measurable (fun ω : Ω => fun j : J => Z ω j.1) :=
      hπJ.comp hZ
    have hVecGrid (n : ℕ) :
        Measurable (fun ω : Ω => fun j : J => Ygrid n ω j.1) :=
      hπJ.comp (hGridMeas n)
    have hGridVectorLaw (n : ℕ) :
        Measure.map (fun ω : Ω => fun j : J => Ygrid n ω j.1) P =
        Measure.map (fun ω : Ω => fun j : J => Z ω j.1) P := by
      change Measure.map (πJ ∘ Ygrid n) P =
        Measure.map (πJ ∘ Z) P
      rw [← Measure.map_map hπJ (hGridMeas n),
        ← Measure.map_map hπJ hZ]
      exact congrArg (fun μ : Measure (ℝ≥0 → ℝ) => Measure.map πJ μ)
        (hGridLaw n)
    exact bv_grid_right_approx_future_vector_law_ws01c
      X J grid raw hGridTends hGridAbove
      hVecGrid hVecY hVecZ hGridVectorLaw
  exact cross_sample_path_law_eq_of_all_finite_vector_laws
    P P Y Z hY hZ (measure_ne_top P Set.univ) hVectorLaw
