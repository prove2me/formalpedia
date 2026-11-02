-- Prove2me | solution 1 for AvramDividend.Classical.scaledW_generator_harmonic_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:19:58.882755+00:00
-- url     : https://prove2.me/submissions/bbf328e9-8804-4baf-ae1a-cda3b9c68381

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_on_Iic_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_scaledW_boundary_smooth_fit
import Theorems.Thm_AvramDividend_Classical_generator_eq_at_barrier_of_weighted_jet
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal ∧
      X.generator (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)) (cstar W).toReal -
        q * divE (W (cstar W).toReal)
          (scaleDeriv W (cstar W).toReal) = 0 := by
  let a : ℝ := (cstar W).toReal
  let U : ℝ → ℝ := fun z => divE (W z) (scaleDeriv W a)
  have heq (z : ℝ) (hz : z ≤ a) : vcstar W z = U z := by
    simpa [a, U] using
      (vcstar_eq_scaledW_on_Iic_cstar W hW.1 z hz)
  have hjets :=
    vcstar_scaledW_boundary_smooth_fit
      X hX q hq W hW hc hcpos h_smooth
  have hder : deriv (vcstar W) a = deriv U a := by
    simpa [a, U] using hjets.1
  have hsecond :
      X.σ ^ 2 * iteratedDeriv 2 (vcstar W) a =
        X.σ ^ 2 * iteratedDeriv 2 U a := by
    simpa [a, U] using hjets.2
  have hlocal :=
    generator_eq_at_barrier_of_weighted_jet
      X (vcstar W) U a heq hder hsecond
  have hV :=
    avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
      X hX q hq W hW hc hcpos h_smooth
  have hvalue : vcstar W a = U a := heq a le_rfl
  change X.GeneratorIntegrable U a ∧
    X.generator U a - q * U a = 0
  refine ⟨hlocal.1.mp hV.1, ?_⟩
  calc
    X.generator U a - q * U a =
        X.generator (vcstar W) a - q * vcstar W a := by
          rw [← hlocal.2, ← hvalue]
    _ = 0 := hV.2
