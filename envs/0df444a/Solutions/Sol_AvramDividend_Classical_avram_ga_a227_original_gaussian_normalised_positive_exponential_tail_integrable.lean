-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a227_original_gaussian_normalised_positive_exponential_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:48:29.688743+00:00
-- url     : https://prove2.me/submissions/577eb70c-b2e2-4af0-a77a-3270a28200f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (θ δ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω : Ω =>
      let Z : ℝ := ((X.X t ω - X.X s ω) -
        ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
      if δ ≤ Z then Real.exp (θ * Z) else 0) P := by
  let Z : Ω → ℝ := fun ω =>
    ((X.X t ω - X.X s ω) -
      ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
  have h0 : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have h1 : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hZm : Measurable Z :=
    ((h1.sub h0).sub measurable_const).div_const _
  have hs : MeasurableSet {ω : Ω | δ ≤ Z ω} :=
    (show MeasurableSet (Set.Ici δ : Set ℝ)
      from measurableSet_Ici).preimage hZm
  have he : Integrable (fun ω => Real.exp (θ * Z ω)) P := by
    simpa only [Z] using
      (avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
        X hν hσ s t hst θ hθ)
  have hi := he.indicator hs
  change Integrable (fun ω => if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) P
  have hEq :
      (fun ω : Ω => if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) =
      Set.indicator {ω : Ω | δ ≤ Z ω}
        (fun ω => Real.exp (θ * Z ω)) := by
    funext ω
    by_cases h : δ ≤ Z ω <;> simp [Set.indicator, h]
  rw [hEq]
  exact hi
