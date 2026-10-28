-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:37:02.040396+00:00
-- url     : https://prove2.me/submissions/985588ce-ae72-4114-b19f-d4c81d1a5be0

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_VectorItoProcessVersion
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_continuous_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integrable_integral_of_ae_bound_readable
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_le_setIntegral_div_readable

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
private theorem FunctionalInequalities.KLS.BKL.Localization.measurable_path_uncurry
    {γ : Param n → ℝ}
    (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    Measurable (fun z : Ω × ℝ => p z.2 z.1) := by
  let Φ : Param n ≃L[ℝ] (Fin (Module.finrank ℝ (Param n)) → ℝ) :=
    stateEquiv (Param n)
  change IsDiffusion W ℱ hW
    (transportDrift Φ (cutoffDrift μ hc γ))
    (transportNoise Φ (cutoffNoise μ hc γ)) (Φ 0)
    (fun s ω => Φ (p s ω)) at h
  obtain ⟨_, _, _, hv⟩ := h
  have hm :
      Measurable (fun z : Ω × ℝ => Φ (p z.2 z.1)) := by
    change Measurable (Function.uncurry (fun w s => Φ (p s w)))
    exact hv.measurable_uncurry
  have hm' := Φ.symm.continuous.measurable.comp hm
  change Measurable (fun z : Ω × ℝ => Φ.symm (Φ (p z.2 z.1))) at hm'
  simpa only [Φ.symm_apply_apply] using hm'
private theorem FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg
    (ν : Measure (EuclideanSpace ℝ (Fin n))) (d : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    0 ≤ cumulantEnergy ν d u := by
  unfold cumulantEnergy
  exact Finset.sum_nonneg fun J _ => sq_nonneg _
/-- **Mean value in time** (the replacement for "let `T → ∞` along a subsequence", BKL p. 25): for a cutoff
process and a continuous energy bounded on symmetric PSD `Q`, some `t ∈ [T₀, 2T₀]` has
`E[γ(p_t)² E_{d+1}(p_t)] ≤ I_{d+1}(2T₀) / T₀`, where `I_{d+1}(T) = ∫₀ᵀ E[γ² E_{d+1}(p_s)] ds`. -/
theorem solution (hiso : FunctionalInequalities.KLS.Isotropic μ) {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} (hγ : FunctionalInequalities.KLS.BKL.Localization.IsCutoff γ)
    (h : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff μ hc W ℱ hW γ p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q : FunctionalInequalities.KLS.BKL.Localization.Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C)
    (hcont : Continuous fun q : FunctionalInequalities.KLS.BKL.Localization.Param n =>
      FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ t ∈ Set.Icc T₀ (2 * T₀),
      (∫ w, γ (p t w) ^ 2 *
        FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P) ≤
        FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by
  let E : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ := fun q =>
    FunctionalInequalities.KLS.BKL.cumulantEnergy (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u
  let F : ℝ → Ω → ℝ := fun s w => γ (p s w) ^ 2 * E (p s w)
  let f : ℝ → ℝ := fun s => ∫ w, F s w ∂P
  have hQ := h.ae_Q_posSemidef_readable hiso hγ
  obtain ⟨Kγ, hγL⟩ := hγ.lipschitz
  have hFcont : Continuous (fun q => γ q ^ 2 * E q) :=
    (hγL.continuous.pow 2).mul hcont
  have hFbound :
      ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → |F s w| ≤ C := by
    filter_upwards [hQ] with w hw
    intro s hs
    have he := hC (p s w) (hw s hs).1 (hw s hs).2
    have heC : E (p s w) ≤ C := by
      simpa [E] using he
    have he0 : 0 ≤ E (p s w) := FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg _ _ _
    have hg := hγ.mem_Icc (p s w)
    have h1 : 0 ≤ 1 - γ (p s w) :=
      sub_nonneg.mpr hg.2
    have h2 : 0 ≤ 1 + γ (p s w) :=
      add_nonneg zero_le_one hg.1
    have hg2 : γ (p s w) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg h1 h2]
    have hle : γ (p s w) ^ 2 * E (p s w) ≤ E (p s w) := by
      calc
        γ (p s w) ^ 2 * E (p s w) ≤ 1 * E (p s w) :=
          mul_le_mul_of_nonneg_right hg2 he0
        _ = E (p s w) := one_mul _
    change |γ (p s w) ^ 2 * E (p s w)| ≤ C
    exact abs_le.mpr
      ⟨(neg_nonpos.mpr hC0).trans (mul_nonneg (sq_nonneg _) he0), hle.trans heC⟩
  have hjoint :
      Measurable (fun z : Ω × ℝ => F z.2 z.1) := by
    change Measurable (fun z : Ω × ℝ => γ (p z.2 z.1) ^ 2 * E (p z.2 z.1))
    exact hFcont.measurable.comp (FunctionalInequalities.KLS.BKL.Localization.measurable_path_uncurry h)
  have hprod :
      Integrable (fun z : Ω × ℝ => F z.2 z.1)
        (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀)))) := by
    apply (integrable_prod_iff hjoint.aestronglyMeasurable).2
    constructor
    · filter_upwards [hFbound] with w hw
      apply Integrable.of_bound
        ((hFcont.comp (h.continuous_readable w)).aestronglyMeasurable) C
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simpa only [F, Function.comp_apply, Real.norm_eq_abs] using
        hw s (hT₀.le.trans hs.1.le)
    · have hnormmeas :
          AEStronglyMeasurable
            (fun w => ∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀))) P := by
        simpa only using hjoint.norm.aestronglyMeasurable.integral_prod_right'
      apply Integrable.of_bound hnormmeas (C * (2 * T₀ - T₀))
      filter_upwards [hFbound] with w hw
      have hnonneg :
          0 ≤ ∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀)) :=
        integral_nonneg (fun s => norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        (∫ s, ‖F s w‖ ∂volume.restrict (Set.Ioc T₀ (2 * T₀))) ≤
            ∫ s in Set.Ioc T₀ (2 * T₀), C := by
          apply setIntegral_mono_on
          · exact (hFcont.comp (h.continuous_readable w)).norm.integrableOn_Ioc
          · exact continuous_const.integrableOn_Ioc
          · exact measurableSet_Ioc
          · intro s hs
            simpa only [F, Function.comp_apply, Real.norm_eq_abs] using
              hw s (hT₀.le.trans hs.1.le)
        _ = C * (2 * T₀ - T₀) := by
          rw [setIntegral_const]
          simp only [smul_eq_mul]
          have hvol :
              (volume : Measure ℝ).real (Set.Ioc T₀ (2 * T₀)) = T₀ := by
            rw [Measure.real, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith)]
            ring
          rw [hvol]
          ring
  have hfint :
      Integrable f (volume.restrict (Set.Ioc T₀ (2 * T₀))) := by
    change Integrable (fun s => ∫ w, F s w ∂P)
      (volume.restrict (Set.Ioc T₀ (2 * T₀)))
    exact hprod.integral_prod_right
  obtain ⟨t, ht, htf⟩ := FunctionalInequalities.KLS.BKL.Localization.exists_le_setIntegral_div_readable hT₀ hfint
  have hprod' :
      Integrable (Function.uncurry (fun w s => F s w))
        (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀)))) := by
    change Integrable (fun z : Ω × ℝ => F z.2 z.1)
      (P.prod (volume.restrict (Set.Ioc T₀ (2 * T₀))))
    exact hprod
  have hswap := integral_integral_swap hprod'
  have hfull :
      (∫ s in Set.Ioc T₀ (2 * T₀), f s) =
        ∫ w, ∫ s in Set.Ioc T₀ (2 * T₀), F s w ∂volume ∂P := by
    simpa only [f, Function.uncurry] using hswap.symm
  have hlefti :
      Integrable
        (fun w => ∫ s in Set.Ioc T₀ (2 * T₀), F s w) P :=
    hprod.integral_prod_left
  have hrighti :
      Integrable
        (fun w => ∫ s in Set.Ioc (0 : ℝ) (2 * T₀), F s w) P := by
    simpa only [F] using
      h.integrable_integral_of_ae_bound_readable hFcont hFbound
        (T := 2 * T₀) (by linarith)
  have houter :
      (∫ w, ∫ s in Set.Ioc T₀ (2 * T₀), F s w ∂volume ∂P) ≤
        FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p d u (2 * T₀) := by
    have hmono :
        ∀ᵐ w ∂P,
          (∫ s in Set.Ioc T₀ (2 * T₀), F s w) ≤
            (∫ s in Set.Ioc (0 : ℝ) (2 * T₀), F s w) := by
      filter_upwards [] with w
      apply setIntegral_mono_set
      · exact (hFcont.comp (h.continuous_readable w)).integrableOn_Ioc
      · exact Filter.Eventually.of_forall (fun s =>
          mul_nonneg (sq_nonneg _) (FunctionalInequalities.KLS.BKL.Localization.cumulantEnergy_nonneg _ _ _))
      · exact (Set.Ioc_subset_Ioc_left (by linarith)).eventuallyLE
    have hineq := integral_mono_ae hlefti hrighti hmono
    simpa only [FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral, F, E] using hineq
  refine ⟨t, ht, ?_⟩
  calc
    ∫ w, γ (p t w) ^ 2 *
        FunctionalInequalities.KLS.BKL.cumulantEnergy
          (FunctionalInequalities.Probability.Posterior.compactPosterior μ hc (p t w).1 (p t w).2 :
            Measure (EuclideanSpace ℝ (Fin n))) d u ∂P =
        f t := by
          rfl
    _ ≤ (∫ s in Set.Ioc T₀ (2 * T₀), f s) / T₀ := htf
    _ ≤ FunctionalInequalities.KLS.BKL.Localization.weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by
      rw [hfull]
      exact div_le_div_of_nonneg_right houter hT₀.le
