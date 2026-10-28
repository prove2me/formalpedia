-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integrable_integral_of_ae_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:49.304985+00:00
-- url     : https://prove2.me/submissions/48e96c86-3de4-439a-849b-824cc0630374

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_continuous_readable

section
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/VectorItoProcessVersion.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
section VectorVersion
open LevyStochCalc.Brownian.Multidim
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {n d : ℕ} (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
variable {W ℱ hcoord H hHm hHp hHs} {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}
/-- A version's time slices are measurable. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable
/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem LevyStochCalc.Brownian.Ito.IsVectorItoVersion.measurable_uncurry
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path h.measurable
  exact hjoint.comp measurable_swap
end VectorVersion
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Integrals
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
/-- **Time integrals of bounded functionals along the cutoff Eldan process** are integrable in `ω`: for a continuous
`φ` with `|φ(p_s)| ≤ B` for all `s ≥ 0` almost surely, `ω ↦ ∫₀ᵀ φ(p_s(ω)) ds` is integrable. -/
theorem solution (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω)) P := by
  have hpcont := h.continuous_readable
  let Φ : FunctionalInequalities.KLS.BKL.Localization.Param n ≃L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) :=
    FunctionalInequalities.Probability.Diffusion.stateEquiv (FunctionalInequalities.KLS.BKL.Localization.Param n)
  change FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW
    (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ))
    (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have h1 :
      Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun ω s => Φ (p s ω)))
    exact hv.measurable_uncurry
  have hpmeas :
      Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
    have h' := Φ.symm.continuous.measurable.comp h1
    change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at h'
    simpa only [Φ.symm_apply_apply] using h'
  have hm :
      Measurable (fun z : Ω × ℝ => φ (p z.2 z.1)) :=
    hφ.measurable.comp hpmeas
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  have hmeas :
      AEStronglyMeasurable (fun z : Ω × ℝ => φ (p z.2 z.1)) (P.prod ν) :=
    hm.aestronglyMeasurable
  have hsm :
      AEStronglyMeasurable (fun ω => ∫ s, φ (p s ω) ∂ν) P :=
    hmeas.integral_prod_right'
  change Integrable (fun ω => ∫ s, φ (p s ω) ∂ν) P
  apply Integrable.of_bound hsm (B * T)
  filter_upwards [hB] with ω hω
  calc
    ‖∫ s, φ (p s ω) ∂ν‖ ≤ ∫ s, ‖φ (p s ω)‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s in Set.Ioc (0 : ℝ) T, B := by
      apply setIntegral_mono_on
      · exact ((hφ.comp (hpcont ω)).norm).integrableOn_Ioc
      · exact continuous_const.integrableOn_Ioc
      · exact measurableSet_Ioc
      · intro s hs
        simpa only [Real.norm_eq_abs] using hω s hs.1.le
    _ = B * T := by
      simp [hT]
      ring
