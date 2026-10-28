-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.dynkin_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:33:41.688981+00:00
-- url     : https://prove2.me/submissions/2c8344d9-0b4e-4062-ba08-c6c1b5e8dc49

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffCoefficients_admissible_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_IsDiffusion_dynkin_transport_readable

section
noncomputable section
open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- `𝓛_γ F = γ² 𝓛 F`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_cutoff (γ : Param n → ℝ) (F : Param n → ℝ) (p : Param n) :
    diffusionGenerator (cutoffDrift μ hc γ) (cutoffNoise μ hc γ) F p =
      γ p ^ 2 * generator μ hc F p := by
  simp only [diffusionGenerator, generator, cutoffDrift, cutoffNoise, map_smul,
    smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Process
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
/-- **Dynkin's identity for the cutoff Eldan process**: for every `C²` `F : Param n → ℝ` (no growth condition:
the cutoff coefficients have compact support), `F(p_T)` is integrable and
`E F(p_T) − F(0) = E ∫₀ᵀ γ(p_s)² 𝓛F(p_s) ds` with the uncut generator `𝓛` of (67). -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) {F : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} (hF : ContDiff ℝ 2 F)
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (p T ω)) P ∧
      ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc F (p s ω) ∂volume ∂P := by
  classical
  let Φ : FunctionalInequalities.KLS.BKL.Localization.Param n ≃L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) :=
    FunctionalInequalities.Probability.Diffusion.stateEquiv (FunctionalInequalities.KLS.BKL.Localization.Param n)
  obtain ⟨⟨_, hK, hKσ⟩, _, hbs, hσs⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.cutoffCoefficients_admissible_readable μ hc hiso hγ
  have hbc : Continuous (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ) := hK.continuous
  have hσc : ∀ k, Continuous fun p => FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ p k := by
    intro k
    exact (hKσ k).continuous
  change FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW
    (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ))
    (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (p t ω)) at h
  obtain ⟨hInt, hEq⟩ :=
    FunctionalInequalities.Probability.Diffusion.IsDiffusion.dynkin_transport_readable
      (W := W) (ℱ := ℱ) (hW := hW) (Y := p) (x₀ := 0)
      Φ hℱ0 hnull hbc hσc hbs hσs h hF hT
  refine ⟨hInt, ?_⟩
  calc
    ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
          FunctionalInequalities.Probability.Diffusion.diffusionGenerator (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ) (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ) F
            (p s ω) ∂volume ∂P := hEq
    _ = ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T,
          γ (p s ω) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc F (p s ω) ∂volume ∂P := by
            apply integral_congr_ae
            filter_upwards [] with ω
            apply integral_congr_ae
            filter_upwards [] with s
            rw [FunctionalInequalities.KLS.BKL.Localization.diffusionGenerator_cutoff]
