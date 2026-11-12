-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_X_abs_plus_exp2_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:23:57.865853+00:00
-- url     : https://prove2.me/submissions/ab9f54e5-0c84-4a3c-a8c8-cea64a5d6a9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja18_standing_X_integrable_fixedtime
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original finite-time L1 norm and a two-tilted exponential moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) :
    ∀ t : ℝ≥0,
      Integrable (fun ω => |X.X t ω| + Real.exp (2 * X.X t ω)) P := by
  intro t
  have hAbs : Integrable (fun ω => |X.X t ω|) P :=
    (avram_ja18_standing_X_integrable_fixedtime X hX t).abs
  have hCent : Integrable
      (fun ω => Real.exp (2 * X.X t ω - (t : ℝ) * X.ψ 2)) P :=
    levy_compensated_exponential_integrable X t 2 (by norm_num)
  have hExp : Integrable
      (fun ω => Real.exp (2 * X.X t ω)) P := by
    have heq : (fun ω => Real.exp (2 * X.X t ω)) =
        (fun ω => Real.exp ((t : ℝ) * X.ψ 2) *
          Real.exp (2 * X.X t ω - (t : ℝ) * X.ψ 2)) := by
      funext ω
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hCent.const_mul _
  exact hAbs.add hExp
