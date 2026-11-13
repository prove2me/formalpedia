-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a29_original_interval_lindeberg_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:02:01.163824+00:00
-- url     : https://prove2.me/submissions/de47aff7-81c9-47b2-ab8d-93d45b177381

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original Gaussian increment's large-value energy obeys an explicit fourth-moment tail bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hMeas : Measurable (fun ω : Ω =>
      (X.X (t - s) ω - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
    (hMeasZ : Measurable (fun ω : Ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : Ω → ℝ := fun ω =>
      ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
    (∫⁻ ω, ENNReal.ofReal (if r ≤ |Z ω| then (Z ω) ^ 2 else 0) ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) := by
  dsimp
  let Z : Ω → ℝ := fun ω =>
    ((X.X t ω - X.X s ω) - ((t - s : ℝ≥0) : ℝ) * X.c) / X.σ
  change (∫⁻ ω, ENNReal.ofReal (if r ≤ |Z ω| then (Z ω) ^ 2 else 0) ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2))
  have hZ : Measurable Z := hMeasZ
  have hZ4 : Measurable (fun ω : Ω => ENNReal.ofReal ((Z ω) ^ 4)) := by
    fun_prop
  have hfactor (ω : Ω) :
      ENNReal.ofReal ((Z ω) ^ 4 / r ^ 2) =
        ENNReal.ofReal (1 / r ^ 2) * ENNReal.ofReal ((Z ω) ^ 4) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 : ℝ) / r ^ 2)]
    congr 1
    ring
  have h4 :
      (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 4) ∂P) ≤
        ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) := by
    exact avram_ubv_gauss13_localise_original_general_interval_fourth_moment_le_three_dt_sq
      X hν hσ s t hst hMeas
  calc
    (∫⁻ ω, ENNReal.ofReal (if r ≤ |Z ω| then (Z ω) ^ 2 else 0) ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 4 / r ^ 2) ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.ofReal_le_ofReal
            (avram_ga_a27_lindeberg_scalar_fourth_energy r (Z ω) hr)
    _ = ENNReal.ofReal (1 / r ^ 2) *
        (∫⁻ ω, ENNReal.ofReal ((Z ω) ^ 4) ∂P) := by
          simp_rw [hfactor]
          exact lintegral_const_mul _ hZ4
    _ ≤ ENNReal.ofReal (1 / r ^ 2) *
        ENNReal.ofReal (3 * (((t - s : ℝ≥0) : ℝ) ^ 2)) :=
          by
            gcongr <;> exact h4
