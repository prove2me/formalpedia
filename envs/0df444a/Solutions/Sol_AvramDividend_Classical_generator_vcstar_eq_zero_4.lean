-- Prove2me | solution 4 for AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:21:49.522998+00:00
-- url     : https://prove2.me/submissions/41395bfe-1b1d-42c7-8765-22736caecd29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Transport scale-function q-harmonicity to the exact dividend candidate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
  obtain ⟨hpos, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hC1 : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_of_standing X hX q hq W hW
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hC1.differentiableOn_one x hx).differentiableAt
      (isOpen_Ioi.mem_nhds hx)
  have hfinite : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hcReal : 0 < (cstar W).toReal :=
    ENNReal.toReal_pos hc.ne' hfinite.ne
  have hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 :=
    scaleDeriv_nonzero_at_finite_cstar_of_tilted_monotone
      X hX q hq W hW hcReal hpos hdiff ⟨φ, hφ, hmono⟩
  have hscale :=
    scaleFunction_generator_q_harmonic_of_nonzero_factor
      X hX q hq W hW h_smooth hc hk
  exact vcstar_interior_harmonicity_of_scale_harmonicity
    X q W hW hcReal hscale
