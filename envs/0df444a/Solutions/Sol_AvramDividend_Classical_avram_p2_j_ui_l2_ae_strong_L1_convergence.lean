-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_l2_ae_strong_L1_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:29:33.461147+00:00
-- url     : https://prove2.me/submissions/71876559-7dcb-4e4a-a1b2-adf8254c0aae

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_uniform_l1_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_l2_restriction_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Vitali strengthens uniform L² a.e. convergence to genuine L¹ convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    MemLp Z 1 P ∧
      Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) := by
  have hL1 := avram_p2_j_ui_l2_uniform_l1_integrable P Y B hm hB
  have hlocal : ∀ n (s : Set Ω),
      eLpNorm (Y n) 1 (P.restrict s) ≤
        (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by
    intro n s
    exact avram_p2_j_ui_l2_restriction_bound P (Y n) B (hm n) (hB n) s
  have hUI : UniformIntegrable Y 1 P :=
    avram_p2_j_ui_quantitative_l2_modulus_to_uniform_integrable
      P Y B hm (fun n => (hL1 n).2) hlocal
  have hZ : Integrable Z P := hUI.integrable_of_ae_tendsto hae
  exact ⟨memLp_one_iff_integrable.mpr hZ,
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      (fun n => hUI.aestronglyMeasurable n)
      (memLp_one_iff_integrable.mpr hZ) hUI.unifIntegrable hae⟩
