-- Prove2me | solution 15 for AvramDividend.Classical.barrier_cstar_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:43:50.474397+00:00
-- url     : https://prove2.me/submissions/1b3b3e34-0a1e-48b9-8bee-9b9dccb90627
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_local_verification
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_root_optimality_of_original_verification_pair
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_positive_cap_interior_HJB
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
import Theorems.Thm_AvramDividend_Classical_avram_sweep19_vcstar_top_original_verification_hypotheses

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧
            X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  have hc : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hUpper :
      (∀ x : ℝ, 0 ≤ x →
        valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y →
        X.GeneratorIntegrable (vcstar W) y ∧
          X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
    constructor
    · by_cases hzero : cstar W = 0
      · intro x hx
        exact le_of_eq
          (avram_sweep16_zero_cstar_original_capped_optimality
            X hX q hq W hW hzero x hx)
      · have hcpos : (0 : ℝ≥0∞) < cstar W :=
          lt_of_le_of_ne bot_le (Ne.symm hzero)
        obtain ⟨hcont, hnonneg, hneg, hsmooth⟩ :=
          vcstar_local_verification_regular_of_positive_cstar
            X hX q hq W hW hc hcpos h_smooth
        have hhjb :=
          avram_sweep17_vcstar_positive_cap_interior_HJB
            X hX q hq W hW hc hcpos h_smooth
        have hlocal :=
          (local_verification X hX q hq (vcstar W) (cstar W)
            hcpos hcont hnonneg hneg hsmooth hhjb).1
        exact avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
          X hX q hq W hW hc h_smooth hlocal
    · intro hgen
      obtain ⟨hcont, hnonneg, hneg, hsmooth, hhjb⟩ :=
        avram_sweep19_vcstar_top_original_verification_hypotheses
          X hX q hq W hW hc h_smooth hgen
      have htop : (0 : ℝ≥0∞) < ⊤ := by simp
      exact (local_verification
        X hX q hq (vcstar W) ⊤ htop
        hcont hnonneg hneg hsmooth hhjb).2 rfl
  exact avram_sweep16_root_optimality_of_original_verification_pair
    X hX q hq W hW hUpper
