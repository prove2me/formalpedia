-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_UI_condexp_family_original_clock_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:28:58.136114+00:00
-- url     : https://prove2.me/submissions/839560e5-6b85-4d29-b4bd-998c7e7e63d6

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hg : Integrable g P)
    (f : ℕ → Ω → ℝ) (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, f n =ᵐ[P] condExp (ℋ n) P g)
    (M : Ω → ℝ)
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => f n ω) atTop (nhds (M ω))) :
    Integrable M P ∧
      Tendsto (fun n => eLpNorm (fun ω => f n ω - M ω) 1 P)
        atTop (nhds 0) := by
  have hUIC : UniformIntegrable
      (fun n => condExp (ℋ n) P g) 1 P :=
    hg.uniformIntegrable_condExp hℋ
  have hUI : UniformIntegrable f 1 P :=
    (uniformIntegrable_congr_ae hCE).2 hUIC
  have hMI : Integrable M P :=
    hUI.integrable_of_ae_tendsto hAE
  refine ⟨hMI, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae
    (by norm_num : (1 : ℝ≥0∞) ≥ 1)
    (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    (fun n => hUI.aestronglyMeasurable n)
    (memLp_one_iff_integrable.mpr hMI)
    hUI.unifIntegrable hAE
