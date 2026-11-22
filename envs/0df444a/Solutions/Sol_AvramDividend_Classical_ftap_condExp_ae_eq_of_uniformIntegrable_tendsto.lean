-- Prove2me | solution 1 for AvramDividend.Classical.ftap_condExp_ae_eq_of_uniformIntegrable_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:51:22.297455+00:00
-- url     : https://prove2.me/submissions/af9888e1-5d8a-44de-8276-c68f0cd19ec6

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42/Stochastic/Martingale/Basic/BoundedStoppingOptionalSampling.lean
Original project: https://github.com/selpoG/lean-ftap-closedness
Source commit: 8c9c46e1b6e455f7d3069062957d4363879836ce
Released under Apache-2.0.
-/
import Mathlib
open Filter MeasureTheory Set Topology
open scoped MeasureTheory NNReal

theorem solution
    {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    [SigmaFinite (μ.trim (m := m) hm)]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hfUI : UniformIntegrable f 1 μ)
    (hfg : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    (c : Ω → ℝ) (_hcMeas : AEStronglyMeasurable[m] c μ)
    (hcond : ∀ n, μ[f n | m] =ᵐ[μ] c) :
    μ[g | m] =ᵐ[μ] c := by
  have hcInt : Integrable c μ := integrable_condExp.congr (hcond 0)
  have hgInt : Integrable g μ := hfUI.integrable_of_ae_tendsto hfg
  have hLp : Tendsto (fun n => eLpNorm (f n - g) 1 μ) atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      hfUI.aestronglyMeasurable (memLp_one_iff_integrable.2 hgInt) hfUI.unifIntegrable hfg
  have hbound : ∀ n, eLpNorm (μ[g | m] - c) 1 μ ≤
      eLpNorm (f n - g) 1 μ := by
    intro n
    have hfnInt : Integrable (f n) μ :=
      (hfUI.memLp n).integrable le_rfl
    have hdiff : (μ[g | m] - c) =ᵐ[μ] μ[g - f n | m] := by
      filter_upwards [(condExp_sub hgInt hfnInt m), hcond n]
        with ω hsub hc
      change μ[g | m] ω - c ω = μ[g - f n | m] ω
      rw [← hc]
      exact hsub.symm
    rw [eLpNorm_congr_ae hdiff]
    calc
      eLpNorm μ[g - f n | m] 1 μ ≤ eLpNorm (g - f n) 1 μ :=
        eLpNorm_condExp_le_eLpNorm (g - f n) le_rfl
      _ = eLpNorm (f n - g) 1 μ := eLpNorm_sub_comm _ _ _ _
  have hzero : eLpNorm (μ[g | m] - c) 1 μ = 0 := by
    apply le_antisymm
    · exact ge_of_tendsto' hLp hbound
    · exact bot_le
  have hcondInt : Integrable (μ[g | m]) μ := integrable_condExp
  have hsubInt : Integrable (μ[g | m] - c) μ := hcondInt.sub hcInt
  have hzeroAE : (μ[g | m] - c) =ᵐ[μ] 0 :=
    (eLpNorm_eq_zero_iff hsubInt.aestronglyMeasurable one_ne_zero).1 hzero
  filter_upwards [hzeroAE] with ω hω
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hω
