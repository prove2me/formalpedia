-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a228_original_raw_gaussian_positive_exponential_increment_tail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:51:41.660271+00:00
-- url     : https://prove2.me/submissions/1dc36032-a195-4f0b-9639-7a307bfb7b5a

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
      let R : ℝ := X.X t ω - X.X s ω
      if δ ≤ R then Real.exp (θ * R) else 0) P := by
  let R : Ω → ℝ := fun ω => X.X t ω - X.X s ω
  let d : ℝ := ((t - s : ℝ≥0) : ℝ) * X.c
  let Z : Ω → ℝ := fun ω => (R ω - d) / X.σ
  have hRm : Measurable R :=
    ((X.adapted t).mono (𝓕.le t) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have he : Integrable (fun ω => Real.exp ((θ * X.σ) * Z ω)) P := by
    simpa only [Z,R,d] using
      (avram_ga_a68_original_gaussian_normalised_increment_exp_integrable
        X hν hσ s t hst (θ * X.σ) (mul_nonneg hθ hσ.le))
  have hEq (ω : Ω) :
      Real.exp (θ * R ω) =
        Real.exp (θ * d) * Real.exp ((θ * X.σ) * Z ω) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [Z]
    field_simp [ne_of_gt hσ]
    ring
  have hRaw : Integrable (fun ω => Real.exp (θ * R ω)) P :=
    (he.const_mul (Real.exp (θ * d))).congr
      (Filter.Eventually.of_forall (fun ω => (hEq ω).symm))
  have hs : MeasurableSet {ω : Ω | δ ≤ R ω} :=
    (measurableSet_Ici : MeasurableSet (Set.Ici δ)).preimage hRm
  change Integrable (fun ω => if δ ≤ R ω then Real.exp (θ * R ω) else 0) P
  have hEq :
      (fun ω : Ω => if δ ≤ R ω then Real.exp (θ * R ω) else 0) =
      Set.indicator {ω : Ω | δ ≤ R ω}
        (fun ω => Real.exp (θ * R ω)) := by
    funext ω
    by_cases h : δ ≤ R ω <;> simp [Set.indicator, h]
  rw [hEq]
  exact hRaw.indicator hs
