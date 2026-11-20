-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_signed_physical_mesh_L1_of_ae_dominated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:30:54.148536+00:00
-- url     : https://prove2.me/submissions/3e000074-98ff-4abc-a166-78cb36f349e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (E : ℕ → Ω → ℝ)
    (hEI : ∀ k, Integrable (E k) P)
    (F : Ω → ℝ) (hFI : Integrable F P)
    (hDom : ∀ k, ∀ᵐ ω ∂P, |E k ω| ≤ F ω)
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by 
  have hMeas : ∀ k, AEStronglyMeasurable
      (fun ω => |E k ω|) P := by
    intro k
    exact (hEI k).abs.aestronglyMeasurable
  have hLimAbs : ∀ᵐ ω ∂P,
      Tendsto (fun k => |E k ω|) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAE] with ω hω
    simpa only [Function.comp_def, abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).comp hω
  have hDomAbs : ∀ k, ∀ᵐ ω ∂P, ‖|E k ω|‖ ≤ F ω := by
    intro k
    filter_upwards [hDom k] with ω hk
    simpa only [Real.norm_eq_abs, abs_abs] using hk
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence
      F hMeas hFI hDomAbs hLimAbs)
