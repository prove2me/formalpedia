-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.exists_isEldanCutoff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:22.706748+00:00
-- url     : https://prove2.me/submissions/3c8acd2a-cb32-4e75-ac8e-1e1a59352a3c

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_cutoffCoefficients_admissible_readable
import Theorems.Thm_FunctionalInequalities_Probability_Diffusion_exists_isDiffusion_readable

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
/-- **Existence of the cutoff Eldan process** on any Brownian setup with a usual filtration, for a compactly
supported isotropic prior and an admissible cutoff. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    [ℱ.IsRightContinuous] (hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ) :
    ∃ p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n, FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p := by
  classical
  let Φ : FunctionalInequalities.KLS.BKL.Localization.Param n ≃L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) :=
    FunctionalInequalities.Probability.Diffusion.stateEquiv (FunctionalInequalities.KLS.BKL.Localization.Param n)
  obtain ⟨⟨K, hK, hKσ⟩, ⟨B, hB⟩, _, _⟩ :=
    FunctionalInequalities.KLS.BKL.Localization.cutoffCoefficients_admissible_readable μ hc hiso hγ
  let K' : ℝ≥0 :=
    ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖₊ *
      (K * ‖(Φ.symm : (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) →L[ℝ] FunctionalInequalities.KLS.BKL.Localization.Param n)‖₊)
  have hbt :
      LipschitzWith K'
        (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ)) := by
    change LipschitzWith K'
      (fun y => Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm y)))
    have he :
        (⇑(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ)) ∘
            FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ ∘
            ⇑(Φ.symm : (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) →L[ℝ] FunctionalInequalities.KLS.BKL.Localization.Param n)) =
          (fun y => Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm y))) := by
      funext y
      rfl
    rw [← he]
    exact
      (ContinuousLinearMap.lipschitz
        (Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))).comp
        (hK.comp
          (ContinuousLinearMap.lipschitz
            (Φ.symm : (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) →L[ℝ] FunctionalInequalities.KLS.BKL.Localization.Param n)))
  have hσt :
      ∀ k, LipschitzWith K'
        (fun y => FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ) y k) := by
    intro k
    change LipschitzWith K'
      (fun y => Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ (Φ.symm y) k))
    have he :
        (⇑(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ)) ∘
            (fun p => FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ p k) ∘
            ⇑(Φ.symm : (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) →L[ℝ] FunctionalInequalities.KLS.BKL.Localization.Param n)) =
          (fun y => Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ (Φ.symm y) k)) := by
      funext y
      rfl
    rw [← he]
    exact
      (ContinuousLinearMap.lipschitz
        (Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))).comp
        ((hKσ k).comp
          (ContinuousLinearMap.lipschitz
            (Φ.symm : (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ) →L[ℝ] FunctionalInequalities.KLS.BKL.Localization.Param n)))
  have hbtB :
      ∀ y, ‖FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ) y‖ ≤
        ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖ * B := by
    intro y
    calc
      ‖FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ) y‖ =
          ‖Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm y))‖ := rfl
      _ ≤ ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖ *
          ‖FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ (Φ.symm y)‖ :=
        ContinuousLinearMap.le_opNorm
          (Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ)) _
      _ ≤ ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left (hB (Φ.symm y)).1
          (norm_nonneg
            (Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ)))
  have hσtB :
      ∀ y k, ‖FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ) y k‖ ≤
        ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖ * B := by
    intro y k
    calc
      ‖FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ) y k‖ =
          ‖Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ (Φ.symm y) k)‖ := rfl
      _ ≤ ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖ *
          ‖FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ (Φ.symm y) k‖ :=
        ContinuousLinearMap.le_opNorm
          (Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ)) _
      _ ≤ ‖(Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ))‖ * B :=
        mul_le_mul_of_nonneg_left ((hB (Φ.symm y)).2 k)
          (norm_nonneg
            (Φ : FunctionalInequalities.KLS.BKL.Localization.Param n →L[ℝ] (Fin (Module.finrank ℝ (FunctionalInequalities.KLS.BKL.Localization.Param n)) → ℝ)))
  obtain ⟨Y, hY⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_isDiffusion_readable
      W ℱ hW hℱ0 hnull hbt hσt hbtB hσtB (Φ 0)
  refine ⟨fun t ω => Φ.symm (Y t ω), ?_⟩
  change FunctionalInequalities.Probability.Diffusion.IsDiffusion W ℱ hW
    (FunctionalInequalities.Probability.Diffusion.transportDrift Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffDrift μ hc γ))
    (FunctionalInequalities.Probability.Diffusion.transportNoise Φ (FunctionalInequalities.KLS.BKL.Localization.cutoffNoise μ hc γ)) (Φ 0)
    (fun t ω => Φ (Φ.symm (Y t ω)))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hY
