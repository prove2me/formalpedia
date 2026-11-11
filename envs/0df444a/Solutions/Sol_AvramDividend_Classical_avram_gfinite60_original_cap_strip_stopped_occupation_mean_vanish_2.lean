-- Prove2me | solution 2 for AvramDividend.Classical.avram_gfinite60_original_cap_strip_stopped_occupation_mean_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:27:28.498069+00:00
-- url     : https://prove2.me/submissions/9b0bd984-44bc-4c50-85c7-662c71e52f4d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gfinite64_original_global_cap_strip_expected_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_realcap_invariant_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- The stopped strip occupies a subset of the unconditional global strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      let b : ℕ → ℝ := fun j =>
        C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Occ : ℕ → Ω → ℝ := fun j ω =>
        ∫ t in Ioo (0 : ℝ) (n : ℝ),
          if t < (ρ ω : ℝ) ∧
              b j < riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0 ∂volume
      Tendsto (fun j : ℕ => ∫ ω in A, Occ j ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let b : ℕ → ℝ := fun j => C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Occ : ℕ → Ω → ℝ := fun j ω => ∫ t in Ioo (0 : ℝ) (n : ℝ),
    if t < (ρ ω : ℝ) ∧ b j < riskProcess X x D (Real.toNNReal t) ω
    then (1 : ℝ) else 0 ∂volume
  let U : ℕ → Ω → ℝ := fun j ω => ∫ t in Ioo (0 : ℝ) (n : ℝ),
    if b j < riskProcess X x D (Real.toNNReal t) ω
    then (1 : ℝ) else 0 ∂volume
  have hc : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hCeq : ENNReal.ofReal C.toReal = C := ENNReal.ofReal_toReal hFiniteCap
  have hxc' : ENNReal.ofReal x ≤ ENNReal.ofReal C.toReal := by simpa [hCeq] using hxc
  have hD' : IsAdmissibleLe X x (ENNReal.ofReal C.toReal) D := by simpa [hCeq] using hD
  have hcap : ∀ ω (s : ℝ≥0), riskProcess X x D s ω ≤ C.toReal :=
    avram_p4_e_localise_original_finite_realcap_invariant_all_times X x C.toReal hc hxc' D hD'
  have hdiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hcut : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hUlim : Tendsto (fun j => ∫ ω, U j ω ∂P) atTop (𝓝 (0 : ℝ)) := by
    simpa only [U, b] using avram_gfinite64_original_global_cap_strip_expected_zero
      X hBV x C.toReal hcut D hdiv hcap n hn
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) (n : ℝ))
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hJoint := avram_p3_g2_original_prepayment_riskProcess_joint_measurable X x D hdiv
  have hY : Measurable (fun z : Ω × ℝ =>
      riskProcess X x D (Real.toNNReal z.2) z.1) :=
    hJoint.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hUi (j : ℕ) : Integrable (U j) P := by
    let f : Ω × ℝ → ℝ := fun z =>
      if b j < riskProcess X x D (Real.toNNReal z.2) z.1 then 1 else 0
    have hf : Integrable f (P.prod μ) :=
      (integrable_const (μ := P.prod μ) (1 : ℝ)).mono'
        (Measurable.ite (measurableSet_lt measurable_const hY) measurable_const measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun z => by dsimp [f]; split_ifs <;> norm_num))
    simpa only [U, f, μ] using hf.integral_prod_left
  have hPosOcc (j : ℕ) (ω : Ω) : 0 ≤ Occ j ω :=
    integral_nonneg (fun t => by dsimp [Occ]; split_ifs <;> norm_num)
  have hPosU (j : ℕ) (ω : Ω) : 0 ≤ U j ω :=
    integral_nonneg (fun t => by dsimp [U]; split_ifs <;> norm_num)
  have hOLe (j : ℕ) (ω : Ω) : Occ j ω ≤ U j ω := by
    have hTimeY : Measurable (fun t : ℝ => riskProcess X x D (Real.toNNReal t) ω) :=
      hJoint.comp (measurable_real_toNNReal.prodMk measurable_const)
    have hTimeInt : Integrable (fun t : ℝ => if b j < riskProcess X x D (Real.toNNReal t) ω
        then (1 : ℝ) else 0) μ :=
      (integrable_const (μ := μ) (1 : ℝ)).mono'
        (Measurable.ite (measurableSet_lt measurable_const hTimeY) measurable_const measurable_const).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun t => by split_ifs <;> norm_num))
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun t => by
        change (0 : ℝ) ≤
          (if t < (ρ ω : ℝ) ∧ b j < riskProcess X x D (Real.toNNReal t) ω
           then (1 : ℝ) else 0)
        split_ifs <;> norm_num)
    · exact hTimeInt
    · exact Filter.Eventually.of_forall (fun t => by
        by_cases ht : t < (ρ ω : ℝ)
        · simp [ht]
        · simp only [ht, false_and, ite_false]
          split_ifs <;> norm_num)
  have hLower (j : ℕ) : 0 ≤ ∫ ω in A, Occ j ω ∂P :=
    integral_nonneg (hPosOcc j)
  have hUpper (j : ℕ) : (∫ ω in A, Occ j ω ∂P) ≤ ∫ ω, U j ω ∂P := by
    have hFirst : (∫ ω in A, Occ j ω ∂P) ≤ ∫ ω in A, U j ω ∂P := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (hPosOcc j)
      · exact (hUi j).integrableOn
      · exact Filter.Eventually.of_forall (hOLe j)
    exact hFirst.trans (setIntegral_le_integral (hUi j) (Filter.Eventually.of_forall (hPosU j)))
  exact squeeze_zero hLower hUpper hUlim
