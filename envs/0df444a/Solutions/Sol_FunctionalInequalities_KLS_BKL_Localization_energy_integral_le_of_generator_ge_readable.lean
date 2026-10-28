-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.energy_integral_le_of_generator_ge_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:37:49.386366+00:00
-- url     : https://prove2.me/submissions/4b4a5fd0-8e44-42db-9a40-311a02e424e9

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Posterior_CompactDomain
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Integral
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_dynkin_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_measurable_uncurry_path_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_ae_prod_restrict_Ioc_of_ae_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_contDiff_cumulantEnergy_posterior_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_continuous_generator_of_contDiff_three_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_cumulantEnergy_le_readable

section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- At the initial parameters the posterior is the prior. -/
theorem FunctionalInequalities.Probability.Posterior.compactPosterior_zero (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) : compactPosterior μ hc 0 0 = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change (μ : Measure E).tilted (quadraticExponent (0 : E) 0) = _
  have he : quadraticExponent (0 : E) (0 : E →L[ℝ] E) = 0 := by funext x; simp [quadraticExponent]
  rw [he, tilted_zero]
end
end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
section
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Process
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
/-- Bounded continuous functionals of the cutoff Eldan path are integrable on `P ⊗ Leb|_{(0,T]}`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integrable_prod_of_ae_bound (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s w)| ≤ B) (T : ℝ) :
    Integrable (fun z : Ω × ℝ => φ (p z.2 z.1))
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) := by
  have hm : Measurable (fun z : Ω × ℝ => φ (p z.2 z.1)) :=
    hφ.measurable.comp h.measurable_uncurry_path_readable
  refine Integrable.of_bound hm.aestronglyMeasurable B ?_
  filter_upwards [ae_prod_restrict_Ioc_of_ae_readable hB T] with z hz
  simpa only [Real.norm_eq_abs] using hz
/-- The iterated integral `E ∫₀ᵀ φ(p_s) ds` is the integral over `P ⊗ Leb|_{(0,T]}`. -/
theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_integral_eq_prod (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s w)| ≤ B) (T : ℝ) :
    ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, φ (p s w) ∂volume ∂P =
      ∫ z, φ (p z.2 z.1) ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))) :=
  (integral_prod _ (h.integrable_prod_of_ae_bound hφ hB T)).symm
end Process
end
end
end

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
section Process
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
set_option maxHeartbeats 1000000 in
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) (hLC : FunctionalInequalities.KLS.LogConcave μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 ρ)
    (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h51 : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      (1 / 2 : ℝ) * FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
        Measure (EuclideanSpace ℝ (Fin n))) (r + 1) u -
        17 * ((r : ℝ) + 1) ^ 2 * FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
            Measure (EuclideanSpace ℝ (Fin n))) r u -
        2 * ∑ K : Fin r → Fin n,
          FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
            Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
            (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)
              (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
          FunctionalInequalities.KLS.BKL.lowerDrift (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
            Measure (EuclideanSpace ℝ (Fin n)))
            (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)
              (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ≤
      FunctionalInequalities.KLS.BKL.Localization.generator μ hc
        (fun q' : FunctionalInequalities.KLS.BKL.Localization.Param n => FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q'.1 q'.2 :
            Measure (EuclideanSpace ℝ (Fin n))) r u) q)
    (hL : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      Real.sqrt (∑ K : Fin r → Fin n,
        FunctionalInequalities.KLS.BKL.lowerDrift (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
          Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q)
            (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ^ 2) ≤
        ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1) * FunctionalInequalities.KLS.BKL.cumulantEnergy
            (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 :
              Measure (EuclideanSpace ℝ (Fin n))) a u))
    {T : ℝ} (hT : 0 ≤ T) :
    FunctionalInequalities.KLS.BKL.cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) r u +
        (1 / 2 : ℝ) * FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p (r + 1) u T ≤
      (∫ w, FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p T w).1 (p T w).2 :
        Measure (EuclideanSpace ℝ (Fin n))) r u ∂P) +
        17 * ((r : ℝ) + 1) ^ 2 *
          FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p r u T +
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          (Real.sqrt (FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p r u T) *
            Real.sqrt (FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p a u T)) := by
  classical
  have _hr := hr
  -- Opaque names for the energies and the two tensor fields.
  obtain ⟨E, hE⟩ : ∃ E : ℕ → FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ, E = fun d q =>
      FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u :=
    ⟨_, rfl⟩
  obtain ⟨Tt, hTt⟩ : ∃ Tt : FunctionalInequalities.KLS.BKL.Localization.Param n → (Fin r → Fin n) → ℝ, Tt = fun q K =>
      FunctionalInequalities.Analysis.BakryEmery.cumulant (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
        (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) :=
    ⟨_, rfl⟩
  obtain ⟨Lt, hLt⟩ : ∃ Lt : FunctionalInequalities.KLS.BKL.Localization.Param n → (Fin r → Fin n) → ℝ, Lt = fun q K =>
      FunctionalInequalities.KLS.BKL.lowerDrift (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (Fin.cons u fun s => FunctionalInequalities.Analysis.inverseSqrt (FunctionalInequalities.KLS.BKL.Localization.cov μ hc q) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 :=
    ⟨_, rfl⟩
  have hEapp : ∀ d (q : FunctionalInequalities.KLS.BKL.Localization.Param n), E d q =
      FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u := by
    intro d q
    rw [hE]
  have hEnn : ∀ d (q : FunctionalInequalities.KLS.BKL.Localization.Param n), 0 ≤ E d q := by
    intro d q
    rw [hEapp]
    unfold FunctionalInequalities.KLS.BKL.cumulantEnergy
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEsmooth : ∀ d, ContDiff ℝ ∞ (E d) := by
    intro d
    rw [hE]
    exact FunctionalInequalities.KLS.BKL.Localization.contDiff_cumulantEnergy_posterior_readable μ hc hiso d u
  have hEcont : ∀ d, Continuous (E d) := fun d => (hEsmooth d).continuous
  have hE0 : FunctionalInequalities.KLS.BKL.cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) r u = E r 0 := by
    rw [hEapp]
    simp only [Prod.fst_zero, Prod.snd_zero, FunctionalInequalities.Probability.Posterior.compactPosterior_zero]
  have h51' : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      (1 / 2 : ℝ) * E (r + 1) q - 17 * ((r : ℝ) + 1) ^ 2 * E r q -
        2 * ∑ K : Fin r → Fin n, Tt q K * Lt q K ≤ FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) q := by
    intro q h1 h2
    rw [hE, hTt, hLt]
    exact h51 q h1 h2
  have hL' : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      Real.sqrt (∑ K : Fin r → Fin n, Lt q K ^ 2) ≤
        ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1) * E a q) := by
    intro q h1 h2
    rw [hE, hLt]
    exact hL q h1 h2
  have hTsq : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, ∑ K : Fin r → Fin n, Tt q K ^ 2 = E r q := by
    intro q
    rw [hEapp, hTt]
    rfl
  -- Pointwise bound on symmetric PSD parameters.
  have hpt : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      (1 / 2 : ℝ) * (γ q ^ 2 * E (r + 1) q) - 17 * ((r : ℝ) + 1) ^ 2 * (γ q ^ 2 * E r q) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          ((γ q * Real.sqrt (E r q)) * (γ q * Real.sqrt (E a q))) ≤
      γ q ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) q := by
    intro q h1 h2
    have hγ2 : 0 ≤ γ q ^ 2 := sq_nonneg _
    have hCS : ∑ K : Fin r → Fin n, Tt q K * Lt q K ≤
        Real.sqrt (∑ K : Fin r → Fin n, Tt q K ^ 2) *
          Real.sqrt (∑ K : Fin r → Fin n, Lt q K ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    rw [hTsq q] at hCS
    have hL2 := hL' q h1 h2
    have hsq : ∀ a, Real.sqrt (b (r + 1 - a + 1) * E a q) =
        Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a q) :=
      fun a => Real.sqrt_mul (hb _) _
    simp only [hsq] at hL2
    have hS : ∑ K : Fin r → Fin n, Tt q K * Lt q K ≤
        Real.sqrt (E r q) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a q)) :=
      hCS.trans (mul_le_mul_of_nonneg_left hL2 (Real.sqrt_nonneg _))
    have key := h51' q h1 h2
    have hsum : ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
        Real.sqrt (b (r + 1 - a + 1)) *
        ((γ q * Real.sqrt (E r q)) * (γ q * Real.sqrt (E a q))) =
        γ q ^ 2 * (Real.sqrt (E r q) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) *
          (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a q))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hsum]
    have hfac : (1 / 2 : ℝ) * (γ q ^ 2 * E (r + 1) q) -
        17 * ((r : ℝ) + 1) ^ 2 * (γ q ^ 2 * E r q) -
        2 * (γ q ^ 2 * (Real.sqrt (E r q) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) *
          (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a q)))) =
        γ q ^ 2 * ((1 / 2 : ℝ) * E (r + 1) q - 17 * ((r : ℝ) + 1) ^ 2 * E r q -
          2 * (Real.sqrt (E r q) * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
            ((r + 1 - 1).choose (a - 1) : ℝ) *
            (Real.sqrt (b (r + 1 - a + 1)) * Real.sqrt (E a q)))) := by
      ring
    rw [hfac]
    refine mul_le_mul_of_nonneg_left ?_ hγ2
    linarith [hS, key]
  -- Bounds along the path.
  have hQ := FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_Q_posSemidef_readable hiso hγ h
  have hγc : Continuous γ := by
    obtain ⟨K, hK⟩ := hγ.lipschitz
    exact hK.continuous
  have hγ01 : ∀ q, 0 ≤ γ q ∧ γ q ≤ 1 := fun q => hγ.mem_Icc q
  have hγabs : ∀ q, |γ q| ≤ 1 := fun q =>
    abs_le.mpr ⟨by linarith [(hγ01 q).1], (hγ01 q).2⟩
  have hEbd : ∀ d, ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → E d (p s w) ≤ C := by
    intro d
    obtain ⟨C, hC0, hC⟩ := FunctionalInequalities.KLS.BKL.Localization.exists_cumulantEnergy_le_readable μ hc hiso hLC hρ hsupp d
    refine ⟨C * ‖u‖ ^ 2, by positivity, ?_⟩
    filter_upwards [hQ] with w hw
    intro s hs
    rw [hEapp]
    exact hC (p s w) (hw s hs).1 (hw s hs).2 u
  have hGcont : ∀ d, Continuous (fun q => γ q ^ 2 * E d q) :=
    fun d => (hγc.pow 2).mul (hEcont d)
  have hGbd : ∀ d, ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |γ (p s w) ^ 2 * E d (p s w)| ≤ C := by
    intro d
    obtain ⟨C, _hC0, hC⟩ := hEbd d
    refine ⟨C, ?_⟩
    filter_upwards [hC] with w hw
    intro s hs
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hEnn d _))]
    have hg := hγ01 (p s w)
    calc γ (p s w) ^ 2 * E d (p s w) ≤ 1 * C :=
          mul_le_mul (pow_le_one₀ hg.1 hg.2) (hw s hs) (hEnn d _) zero_le_one
      _ = C := one_mul _
  have hfbd : ∀ d, ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |γ (p s w) * Real.sqrt (E d (p s w))| ≤ C := by
    intro d
    obtain ⟨C, _hC0, hC⟩ := hEbd d
    refine ⟨Real.sqrt C, ?_⟩
    filter_upwards [hC] with w hw
    intro s hs
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |γ (p s w)| * Real.sqrt (E d (p s w)) ≤ 1 * Real.sqrt C :=
          mul_le_mul (hγabs _) (Real.sqrt_le_sqrt (hw s hs)) (Real.sqrt_nonneg _) zero_le_one
      _ = Real.sqrt C := one_mul _
  have hffbd : ∀ d d', ∃ C : ℝ, ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |(γ (p s w) * Real.sqrt (E d (p s w))) * (γ (p s w) * Real.sqrt (E d' (p s w)))| ≤ C := by
    intro d d'
    obtain ⟨C, hC⟩ := hfbd d
    obtain ⟨C', hC'⟩ := hfbd d'
    refine ⟨C * C', ?_⟩
    filter_upwards [hC, hC'] with w hw hw'
    intro s hs
    rw [abs_mul]
    exact mul_le_mul (hw s hs) (hw' s hs) (abs_nonneg _) ((abs_nonneg _).trans (hw s hs))
  -- The generator term is bounded (compact support of the cutoff).
  have hF3 : ContDiff ℝ 3 (E r) := (hEsmooth r).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgen_cont : Continuous (FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r)) :=
    FunctionalInequalities.KLS.BKL.Localization.continuous_generator_of_contDiff_three_readable μ hc hiso hF3
  have hgc : Continuous (fun q => γ q ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) q) :=
    (hγc.pow 2).mul hgen_cont
  have hgsupp : HasCompactSupport (fun q => γ q ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) q) := by
    have h2 : HasCompactSupport (fun q => γ q ^ 2) :=
      hγ.compactSupport.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
    exact h2.mul_right
  obtain ⟨Bg, hBg⟩ := hgc.bounded_above_of_compact_support hgsupp
  have hgB : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s →
      |γ (p s w) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) (p s w)| ≤ Bg :=
    Filter.Eventually.of_forall fun w s _ => by
      simpa only [Real.norm_eq_abs] using hBg (p s w)
  -- Product measure.
  obtain ⟨Pr, hPr⟩ : ∃ Pr : Measure (Ω × ℝ),
      Pr = P.prod (volume.restrict (Set.Ioc (0 : ℝ) T)) := ⟨_, rfl⟩
  have : IsFiniteMeasure Pr := by
    rw [hPr]
    infer_instance
  have hprod : ∀ {φ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ}, Continuous φ → ∀ {B : ℝ},
      (∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s w)| ≤ B) →
      Integrable (fun z : Ω × ℝ => φ (p z.2 z.1)) Pr ∧
        ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, φ (p s w) ∂volume ∂P = ∫ z, φ (p z.2 z.1) ∂Pr := by
    intro φ hφ B hB
    rw [hPr]
    exact ⟨h.integrable_prod_of_ae_bound hφ hB T, h.integral_integral_eq_prod hφ hB T⟩
  have hprodae : ∀ {Q : Ω → ℝ → Prop}, (∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → Q w s) →
      ∀ᵐ z ∂Pr, Q z.1 z.2 := by
    intro Q hQ'
    rw [hPr]
    exact FunctionalInequalities.KLS.BKL.Localization.ae_prod_restrict_Ioc_of_ae_readable hQ' T
  have hae : ∀ᵐ z ∂Pr, IsSelfAdjoint (p z.2 z.1).2 ∧ ∀ x, 0 ≤ ⟪(p z.2 z.1).2 x, x⟫ :=
    hprodae hQ
  have hI : ∀ d, ∫ w, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s w) ^ 2 * E d (p s w) ∂volume ∂P =
      ∫ z, γ (p z.2 z.1) ^ 2 * E d (p z.2 z.1) ∂Pr := by
    intro d
    obtain ⟨C, hC⟩ := hGbd d
    exact (hprod (hGcont d) hC).2
  have hIint : ∀ d, Integrable (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * E d (p z.2 z.1)) Pr := by
    intro d
    obtain ⟨C, hC⟩ := hGbd d
    exact (hprod (hGcont d) hC).1
  have hfint : ∀ d, Integrable (fun z : Ω × ℝ => γ (p z.2 z.1) * Real.sqrt (E d (p z.2 z.1))) Pr := by
    intro d
    obtain ⟨C, hC⟩ := hfbd d
    exact (hprod (hγc.mul (hEcont d).sqrt) hC).1
  have hfmem : ∀ d, MemLp (fun z : Ω × ℝ => γ (p z.2 z.1) * Real.sqrt (E d (p z.2 z.1)))
      (ENNReal.ofReal 2) Pr := by
    intro d
    obtain ⟨C, hC⟩ := hfbd d
    refine MemLp.of_bound (hfint d).aestronglyMeasurable C ?_
    filter_upwards [hprodae hC] with z hz
    simpa only [Real.norm_eq_abs] using hz
  have hterm : ∀ a ∈ Finset.Icc 2 (r + 1 - 2), Integrable (fun z : Ω × ℝ =>
      ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
        ((γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
          (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))))) Pr := by
    intro a _
    obtain ⟨C, hC⟩ := hffbd r a
    exact ((hprod ((hγc.mul (hEcont r).sqrt).mul (hγc.mul (hEcont a).sqrt)) hC).1).const_mul _
  have hsumint : Integrable (fun z : Ω × ℝ => 2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
      ((r + 1 - 1).choose (a - 1) : ℝ) * Real.sqrt (b (r + 1 - a + 1)) *
        ((γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
          (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))))) Pr :=
    (integrable_finsetSum _ hterm).const_mul _
  have hGint : Integrable
      (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) (p z.2 z.1)) Pr :=
    (hprod hgc hgB).1
  have hGeq : ∫ w, ∫ s in Set.Ioc (0 : ℝ) T,
      γ (p s w) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) (p s w) ∂volume ∂P =
      ∫ z, γ (p z.2 z.1) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) (p z.2 z.1) ∂Pr :=
    (hprod hgc hgB).2
  -- Dynkin.
  have hF2 : ContDiff ℝ 2 (E r) := (hEsmooth r).of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨-, hDynkin⟩ := FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.dynkin_readable hiso hγ hℱ0 hnull h hF2 hT
  rw [hGeq] at hDynkin
  -- Integrate the pointwise bound.
  have hLHSint : Integrable (fun z : Ω × ℝ =>
      (1 / 2 : ℝ) * (γ (p z.2 z.1) ^ 2 * E (r + 1) (p z.2 z.1)) -
        17 * ((r : ℝ) + 1) ^ 2 * (γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1)) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          ((γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
            (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))))) Pr :=
    (((hIint (r + 1)).const_mul (1 / 2 : ℝ)).sub
      ((hIint r).const_mul (17 * ((r : ℝ) + 1) ^ 2))).sub hsumint
  have hmono : ∫ z, ((1 / 2 : ℝ) * (γ (p z.2 z.1) ^ 2 * E (r + 1) (p z.2 z.1)) -
        17 * ((r : ℝ) + 1) ^ 2 * (γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1)) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          ((γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
            (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))))) ∂Pr ≤
      ∫ z, γ (p z.2 z.1) ^ 2 * FunctionalInequalities.KLS.BKL.Localization.generator μ hc (E r) (p z.2 z.1) ∂Pr := by
    apply integral_mono_ae hLHSint hGint
    filter_upwards [hae] with z hz
    exact hpt (p z.2 z.1) hz.1 hz.2
  have hsplit : ∫ z, ((1 / 2 : ℝ) * (γ (p z.2 z.1) ^ 2 * E (r + 1) (p z.2 z.1)) -
        17 * ((r : ℝ) + 1) ^ 2 * (γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1)) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          ((γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
            (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))))) ∂Pr =
      (1 / 2 : ℝ) * (∫ z, γ (p z.2 z.1) ^ 2 * E (r + 1) (p z.2 z.1) ∂Pr) -
        17 * ((r : ℝ) + 1) ^ 2 * (∫ z, γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1) ∂Pr) -
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          ∫ z, (γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
            (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))) ∂Pr := by
    have hA : Integrable (fun z : Ω × ℝ =>
        (1 / 2 : ℝ) * (γ (p z.2 z.1) ^ 2 * E (r + 1) (p z.2 z.1)) -
          17 * ((r : ℝ) + 1) ^ 2 * (γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1))) Pr :=
      ((hIint (r + 1)).const_mul (1 / 2 : ℝ)).sub
        ((hIint r).const_mul (17 * ((r : ℝ) + 1) ^ 2))
    rw [integral_sub hA hsumint,
      integral_sub ((hIint (r + 1)).const_mul (1 / 2 : ℝ))
        ((hIint r).const_mul (17 * ((r : ℝ) + 1) ^ 2)),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_finsetSum _ hterm]
    simp only [integral_const_mul]
  -- Cauchy–Schwarz on the product measure.
  have hCSint : ∀ a ∈ Finset.Icc 2 (r + 1 - 2),
      ∫ z, (γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
          (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))) ∂Pr ≤
        Real.sqrt (∫ z, γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1) ∂Pr) *
          Real.sqrt (∫ z, γ (p z.2 z.1) ^ 2 * E a (p z.2 z.1) ∂Pr) := by
    intro a _
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (f := fun z : Ω × ℝ => γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1)))
      (g := fun z : Ω × ℝ => γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1)))
      (Filter.Eventually.of_forall fun z => mul_nonneg (hγ01 _).1 (Real.sqrt_nonneg _))
      (Filter.Eventually.of_forall fun z => mul_nonneg (hγ01 _).1 (Real.sqrt_nonneg _))
      (hfmem r) (hfmem a)
    have hsq : ∀ d (z : Ω × ℝ), (γ (p z.2 z.1) * Real.sqrt (E d (p z.2 z.1))) ^ (2 : ℝ) =
        γ (p z.2 z.1) ^ 2 * E d (p z.2 z.1) := by
      intro d z
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hEnn d _)]
    simp only [hsq, ← Real.sqrt_eq_rpow] at hcs
    exact hcs
  have hsum_le : ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
        Real.sqrt (b (r + 1 - a + 1)) *
        ∫ z, (γ (p z.2 z.1) * Real.sqrt (E r (p z.2 z.1))) *
          (γ (p z.2 z.1) * Real.sqrt (E a (p z.2 z.1))) ∂Pr ≤
      ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
        Real.sqrt (b (r + 1 - a + 1)) *
        (Real.sqrt (∫ z, γ (p z.2 z.1) ^ 2 * E r (p z.2 z.1) ∂Pr) *
          Real.sqrt (∫ z, γ (p z.2 z.1) ^ 2 * E a (p z.2 z.1) ∂Pr)) := by
    apply Finset.sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_left (hCSint a ha) (by positivity)
  -- Assemble.
  simp only [FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral, ← hEapp, hE0, hI]
  linarith [hmono, hsplit, hDynkin, hsum_le]
