-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_energy_le_weighted_add_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:03.272609+00:00
-- url     : https://prove2.me/submissions/1eaa3845-271e-42eb-b7b6-62dd0ba7b41d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Cutoff_LipschitzBall
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Coefficients
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable

section
noncomputable section
open scoped NNReal
section Cutoff
variable {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
theorem FunctionalInequalities.Probability.Diffusion.ballCutoff_mem_Icc (R : ℝ) (p : V) : ballCutoff R p ∈ Set.Icc (0 : ℝ) 1 := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
theorem FunctionalInequalities.Probability.Diffusion.ballCutoff_eq_one {R : ℝ} {p : V} (hp : ‖p‖ ≤ R) : ballCutoff R p = 1 := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have h : (1 : ℝ) ≤ R + 1 - ‖p‖ := by linarith
  simp only [ballCutoff, min_eq_left h, max_eq_right zero_le_one]
theorem FunctionalInequalities.Probability.Diffusion.lipschitzWith_ballCutoff (R : ℝ) : LipschitzWith 1 (ballCutoff (V := V) R) := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  have hn : LipschitzWith 1 (fun x : V => ‖x‖) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
        abs_norm_sub_norm_le x y
  change LipschitzWith 1 (fun p : V => max 0 (min 1 (R + 1 - ‖p‖)))
  simpa only [zero_add, max_eq_right (show (0 : ℝ≥0) ≤ 1 by positivity)] using
    (LipschitzWith.const (0 : ℝ)).max
      ((LipschitzWith.const (1 : ℝ)).min ((LipschitzWith.const (R + 1)).sub hn))
theorem FunctionalInequalities.Probability.Diffusion.hasCompactSupport_ballCutoff (R : ℝ) : HasCompactSupport (ballCutoff (V := V) R) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : V) (R + 1))
  intro x hx
  have hr : R + 1 ≤ ‖x‖ :=
    le_of_lt (lt_of_not_ge (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hx))
  exact max_eq_left (le_trans (min_le_right _ _) (sub_nonpos.mpr hr))
end Cutoff
end
end

section
noncomputable section
open MeasureTheory
open scoped NNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Probability.Diffusion
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
theorem FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff (R : ℝ) : IsCutoff (ballCutoff (V := Param n) R) :=
  { lipschitz := ⟨1, lipschitzWith_ballCutoff R⟩
    compactSupport := hasCompactSupport_ballCutoff R
    mem_Icc := fun p => ballCutoff_mem_Icc R p }
end
end
end

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
end VectorVersion
end
end

noncomputable section
section S7B2BoundaryMeanValue
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
private theorem FunctionalInequalities.KLS.BKL.Localization.measurable_path
    {γ : Param n → ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW γ p) (t : ℝ) :
    Measurable (p t) := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have hm := Φ.symm.continuous.measurable.comp (hv.measurable t)
  change Measurable (fun w => Φ.symm (Φ (p t w))) at hm
  simpa only [Φ.symm_apply_apply] using hm
private theorem FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ cumulantEnergy ν d u := by
  unfold cumulantEnergy
  exact Finset.sum_nonneg fun J _ => sq_nonneg _
/-- **Splitting the boundary term** of (93) for the ball cutoff: since `γ_R = 1` on `‖q‖ ≤ R`,
`E E_{d+1}(p_t) ≤ E[γ_R(p_t)² E_{d+1}(p_t)] + C · P(‖p_t‖ > R)` whenever `E_{d+1} ≤ C` on symmetric PSD `Q`. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) {R : ℝ}
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW (FunctionalInequalities.Probability.Diffusion.ballCutoff R) p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C)
    (hcont : Continuous fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
      FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ w, FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P ≤
      (∫ w, FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 *
        FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P) +
        C * (P {w | R < ‖p t w‖}).toReal := by
  let E : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q =>
    FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let A : Set Ω := {w | R < ‖p t w‖}
  have hpt : Measurable (p t) := FunctionalInequalities.KLS.BKL.Localization.measurable_path h t
  have hEm : Measurable (fun w => E (p t w)) :=
    hcont.measurable.comp hpt
  have hAm : MeasurableSet A := by
    change MeasurableSet {w | R < ‖p t w‖}
    exact measurableSet_Ioi.preimage hpt.norm
  have hQ := h.ae_Q_posSemidef_readable hiso (FunctionalInequalities.KLS.BKL.Localization.isCutoff_ballCutoff R)
  have hEb : ∀ᵐ w ∂P, ‖E (p t w)‖ ≤ C := by
    filter_upwards [hQ] with w hw
    have he := hC (p t w) (hw t ht).1 (hw t ht).2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr
      ⟨(neg_nonpos.mpr hC0).trans (FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg _ _ _), he⟩
  have hEi : Integrable (fun w => E (p t w)) P := by
    apply Integrable.of_bound hEm.aestronglyMeasurable C
    exact hEb
  have hγm : Measurable (fun w => FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w)) :=
    (FunctionalInequalities.Probability.Diffusion.lipschitzWith_ballCutoff R).continuous.measurable.comp hpt
  have hwm :
      Measurable (fun w => FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w)) :=
    (hγm.pow_const (2 : ℕ)).mul hEm
  have hwi : Integrable (fun w => FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w)) P := by
    apply Integrable.of_bound hwm.aestronglyMeasurable C
    filter_upwards [hEb] with w hw
    have hg := FunctionalInequalities.Probability.Diffusion.ballCutoff_mem_Icc R (p t w)
    have he : 0 ≤ E (p t w) := FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg _ _ _
    have heC : E (p t w) ≤ C := (le_abs_self _).trans hw
    have h1 : 0 ≤ 1 - FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) :=
      sub_nonneg.mpr hg.2
    have h2 : 0 ≤ 1 + FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) :=
      add_nonneg zero_le_one hg.1
    have hg2 : FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg h1 h2]
    have hle :
        FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w) ≤ E (p t w) := by
      calc
        FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w) ≤ 1 * E (p t w) :=
          mul_le_mul_of_nonneg_right hg2 he
        _ = E (p t w) := one_mul _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) he)]
    exact hle.trans heC
  have hAi0 : Integrable (A.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hAi : Integrable (fun w => C * A.indicator (fun _ : Ω => (1 : ℝ)) w) P :=
    hAi0.const_mul C
  have hpoint :
      ∀ᵐ w ∂P, E (p t w) ≤
        FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w) +
          C * A.indicator (fun _ : Ω => (1 : ℝ)) w := by
    filter_upwards [hEb] with w hwC
    by_cases hwA : w ∈ A
    · have he : 0 ≤ E (p t w) := FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg _ _ _
      have heC : E (p t w) ≤ C := (le_abs_self _).trans hwC
      have hnonneg :
          0 ≤ FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w) := by
        exact mul_nonneg (sq_nonneg _) he
      have hind :
          A.indicator (fun _ : Ω => (1 : ℝ)) w = 1 := by
        simp [Set.indicator, hwA]
      rw [hind]
      linarith
    · have hwA' : ¬ R < ‖p t w‖ := by
        intro hw'
        exact hwA (by simpa [A] using hw')
      have hR : ‖p t w‖ ≤ R := le_of_not_gt hwA'
      have hγ : FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) = 1 := FunctionalInequalities.Probability.Diffusion.ballCutoff_eq_one hR
      simp [Set.indicator, hwA, hγ]
  have hind :
      ∫ w, A.indicator (fun _ : Ω => (1 : ℝ)) w ∂P = (P A).toReal := by
    rw [integral_indicator hAm, setIntegral_const]
    simp [Measure.real, smul_eq_mul]
  calc
    ∫ w, E (p t w) ∂P ≤
        ∫ w, FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w) +
          C * A.indicator (fun _ : Ω => (1 : ℝ)) w ∂P :=
      integral_mono_ae hEi (hwi.add hAi) hpoint
    _ = (∫ w, FunctionalInequalities.Probability.Diffusion.ballCutoff R (p t w) ^ 2 * E (p t w) ∂P) +
          C * (P A).toReal := by
      rw [integral_add hwi hAi, integral_const_mul, hind]
