-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18k_subsigma_dominated_ae_limit_meas
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:43:10.805985+00:00
-- url     : https://prove2.me/submissions/2a8e1a51-86ab-46c3-b5b9-3905dac8412e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18l_dominated_real_L1_norm_limit
import Theorems.Thm_AvramDividend_Classical_avram_ja18m_subsigma_L1_closed
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original-measure sub-filtration closure follows by dominated L1
convergence and closure of the sub-sigma-algebra L1 subspace. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (hSub : m ≤ mΩ)
    (f : ℕ → Ω → ℝ) (g B : Ω → ℝ)
    (hMeas : ∀ n : ℕ, AEStronglyMeasurable[m] (f n) P)
    (hBi : Integrable B P)
    (hBound : ∀ n : ℕ, ∀ᵐ ω ∂P, ‖f n ω‖ ≤ B ω)
    (hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => f n ω) atTop (𝓝 (g ω))) :
    AEStronglyMeasurable[m] g P := by
  have hAmbient (n : ℕ) : AEStronglyMeasurable[mΩ] (f n) P :=
    AEStronglyMeasurable.mono (m' := mΩ) hSub (hMeas n)
  have hGambient : AEStronglyMeasurable[mΩ] g P :=
    aestronglyMeasurable_of_tendsto_ae atTop hAmbient hLimit
  have hBoundAll : ∀ᵐ ω ∂P, ∀ n : ℕ, ‖f n ω‖ ≤ B ω := by
    exact ae_all_iff.mpr hBound
  have hGbound : ∀ᵐ ω ∂P, ‖g ω‖ ≤ B ω := by
    filter_upwards [hLimit, hBoundAll] with ω hωlim hωbound
    exact le_of_tendsto hωlim.norm
      (Filter.Eventually.of_forall (fun n => hωbound n))
  have hfi (n : ℕ) : MemLp (f n) 1 P := by
    rw [memLp_one_iff_integrable]
    exact Integrable.mono' hBi (hAmbient n) (hBound n)
  have hgi : MemLp g 1 P := by
    rw [memLp_one_iff_integrable]
    exact Integrable.mono' hBi hGambient hGbound
  have hNorm : Tendsto (fun n : ℕ =>
      eLpNorm (f n - g) 1 P) atTop (𝓝 (0 : ℝ≥0∞)) :=
    @avram_ja18l_dominated_real_L1_norm_limit
      Ω mΩ P f g B hAmbient hBi hBound hLimit
  exact @avram_ja18m_subsigma_L1_closed
    Ω mΩ P m hSub f g hMeas hfi hgi hNorm
