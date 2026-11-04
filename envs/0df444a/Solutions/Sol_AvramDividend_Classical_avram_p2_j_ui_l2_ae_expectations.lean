-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_l2_ae_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:50:53.977709+00:00
-- url     : https://prove2.me/submissions/accae851-c2c5-42e4-8af2-0f6d46e43056

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_vitali_expectations
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_uniform_l1_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_restriction_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Uniform L² and almost-everywhere convergence give convergence of expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have hL1 := avram_p2_j_ui_l2_uniform_l1_integrable P Y B hm hB
  have hlocal : ∀ n (s : Set Ω),
      eLpNorm (Y n) 1 (P.restrict s) ≤
        (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by
    intro n s
    exact avram_p2_j_ui_l2_restriction_bound P (Y n) B (hm n) (hB n) s
  have hUI : UniformIntegrable Y 1 P :=
    avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable
      P Y B hm (fun n => (hL1 n).2) hlocal
  exact avram_p2_j_ui_vitali_expectations P Y Z hUI hae
