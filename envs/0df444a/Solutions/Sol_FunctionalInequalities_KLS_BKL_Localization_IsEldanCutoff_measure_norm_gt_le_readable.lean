-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measure_norm_gt_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:42:28.384799+00:00
-- url     : https://prove2.me/submissions/801173cc-74de-483d-b4ac-7b45b860b846

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_HilbertSchmidt
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment
import Theorems.Thm_FunctionalInequalities_Analysis_opNorm_sq_le_hsNormSq_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integral_lyapunov_le_readable

section
noncomputable section
open scoped RealInnerProductSpace
section
variable {n : ℕ}
theorem FunctionalInequalities.Analysis.hsNormSq_nonneg (M : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : 0 ≤ hsNormSq M := by
  unfold hsNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
end
end
end

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
section
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
theorem FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov (p : Param n) : 1 ≤ lyapunov μ hc p := by
  unfold lyapunov
  have h₁ := sq_nonneg ‖p.1‖
  have h₂ := hsNormSq_nonneg p.2
  have h₃ := sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))
  linarith
/-- Sublevel sets are bounded: `‖p‖² ≤ 𝒱(p)`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.norm_sq_le_lyapunov (p : Param n) : ‖p‖ ^ 2 ≤ lyapunov μ hc p := by
  unfold lyapunov
  rw [Prod.norm_def]
  have hq := opNorm_sq_le_hsNormSq_readable p.2
  by_cases h : ‖p.1‖ ≤ ‖p.2‖
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖p.1‖,
      sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))]
  · rw [max_eq_left (le_of_not_ge h)]
    nlinarith [hsNormSq_nonneg p.2,
      sq_nonneg (stdTrace (Ring.inverse (cov μ hc p)))]
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc (FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc) q ≤ K * FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc q)
    {t : ℝ} (ht : 0 ≤ t) {R : ℝ} (hR : 0 < R) :
    (P {ω | R < ‖p t ω‖}).toReal ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (K * t) / R ^ 2 := by
  classical
  obtain ⟨hInt, hmean⟩ :=
    h.integral_lyapunov_le_readable hiso hγ hℱ0 hnull hK0 hK ht
  have hnonneg :
      0 ≤ᵐ[P] (fun ω => FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω)) := by
    filter_upwards [] with ω
    exact le_trans (by norm_num) (FunctionalInequalities.KLS.BKL.Localization.one_le_lyapunov μ hc _)
  have hmarkov :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hInt (R ^ 2)
  have hsub :
      {ω | R < ‖p t ω‖} ⊆
        {ω | R ^ 2 ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω)} := by
    intro ω hω
    have hsq : R ^ 2 < ‖p t ω‖ ^ 2 := by
      nlinarith [
        mul_pos (sub_pos.mpr hω)
          (add_pos_of_nonneg_of_pos (norm_nonneg (p t ω)) hR)]
    exact
      (le_of_lt hsq).trans
        (FunctionalInequalities.KLS.BKL.Localization.norm_sq_le_lyapunov μ hc (p t ω))
  have hmeasure :
      (P {ω | R < ‖p t ω‖}).toReal ≤
        (P {ω | R ^ 2 ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω)}).toReal := by
    apply ENNReal.toReal_mono
    · exact measure_ne_top P _
    · exact measure_mono hsub
  have hprob :
      (R ^ 2) *
          (P {ω | R ^ 2 ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω)}).toReal ≤
        ∫ ω, FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω) ∂P := by
    simpa only [Measure.real_def] using hmarkov
  have hprob' :
      (P {ω | R < ‖p t ω‖}).toReal * R ^ 2 ≤
        FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (K * t) := by
    calc
      (P {ω | R < ‖p t ω‖}).toReal * R ^ 2 =
          R ^ 2 * (P {ω | R < ‖p t ω‖}).toReal := by ring
      _ ≤ R ^ 2 *
          (P {ω | R ^ 2 ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc (p t ω)}).toReal :=
        mul_le_mul_of_nonneg_left hmeasure (sq_nonneg R)
      _ ≤ FunctionalInequalities.KLS.BKL.Localization.lyapunov μ hc 0 * Real.exp (K * t) := hprob.trans hmean
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  exact (le_div_iff₀ hR2).mpr hprob'
