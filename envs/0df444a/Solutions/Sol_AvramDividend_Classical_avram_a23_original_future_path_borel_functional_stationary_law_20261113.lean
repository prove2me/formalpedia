-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_original_future_path_borel_functional_stationary_law_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:28:35.226431+00:00
-- url     : https://prove2.me/submissions/013ebd00-f498-4ef9-b534-6694f4e5b47d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Every Borel functional of the original Levy shifted future path has the initial-path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (W : (ℝ≥0 → ℝ) → ℝ) (hW : Measurable W) :
    Measure.map (fun ω : Ω => W (fun u : ℝ≥0 =>
      X.X (s + u) ω - X.X s ω)) P =
    Measure.map (fun ω : Ω => W (fun u : ℝ≥0 =>
      X.X u ω)) P := by
  let Shift : Ω → (ℝ≥0 → ℝ) := fun ω u =>
    X.X (s + u) ω - X.X s ω
  let Base : Ω → (ℝ≥0 → ℝ) := fun ω u => X.X u ω
  have hShift : Measurable Shift := by
    rw [measurable_pi_iff]
    intro u
    have ht := (X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl
    have hs := (X.adapted s).mono (𝓕.le s) le_rfl
    exact ht.sub hs
  have hBase : Measurable Base := by
    rw [measurable_pi_iff]
    intro u
    exact (X.adapted u).mono (𝓕.le u) le_rfl
  have hLaw : Measure.map Shift P = Measure.map Base P := by
    exact levy_shiftedFuturePath_stationary_law X s
  calc
    Measure.map (fun ω => W (Shift ω)) P =
      Measure.map W (Measure.map Shift P) := by
        simpa only [Function.comp_def] using
          (Measure.map_map hW hShift).symm
    _ = Measure.map W (Measure.map Base P) := by rw [hLaw]
    _ = Measure.map (fun ω => W (Base ω)) P := by
        simpa only [Function.comp_def] using
          (Measure.map_map hW hBase)
