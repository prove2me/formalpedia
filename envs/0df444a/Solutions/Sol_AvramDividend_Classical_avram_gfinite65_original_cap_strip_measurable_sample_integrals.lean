-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite65_original_cap_strip_measurable_sample_integrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:34:13.756302+00:00
-- url     : https://prove2.me/submissions/04b03487-b181-4ade-a351-f76c250c2e07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
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
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
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
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
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
      (∀ j : ℕ, AEStronglyMeasurable
        (A.indicator (Occ j)) P) ∧
      (∀ j : ℕ, ∀ ω : Ω,
        IntegrableOn
          (fun t : ℝ => if t < (ρ ω : ℝ) ∧
              b j < riskProcess X x D (Real.toNNReal t) ω
            then (1 : ℝ) else 0)
          (Ioo (0 : ℝ) (n : ℝ)) volume) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let b : ℕ → ℝ := fun j =>
    C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Occ : ℕ → Ω → ℝ := fun j ω =>
    ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b j < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume
  have hAmeas : MeasurableSet A := (𝓕.rightCont.le 0) A hA
  have hPredLe : 𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro B hB
      exact (measurableSet_singleton _).prod ((𝓕.le ⊥) B hB)
    · intro i B hB
      exact measurableSet_Ioi.prod ((𝓕.le i) B hB)
  have hDJoint : Measurable (fun z : ℝ≥0 × Ω => D z.1 z.2) :=
    (avram_wave3_04_dividend_strategy_predictable 𝓕 D hD.1.1).mono
      hPredLe le_rfl
  have hXJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hRisk : Measurable
      (fun z : ℝ≥0 × Ω => riskProcess X x D z.1 z.2) := by
    convert (measurable_const.add hXJoint).sub hDJoint using 1 <;> rfl
  have hPair : Measurable
      (fun z : ℝ × Ω => (Real.toNNReal z.1, z.2)) :=
    (Measurable.real_toNNReal measurable_fst).prodMk measurable_snd
  have hRho : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
      ρ hρstop
  have hJoint (j : ℕ) : MeasurableSet
      {z : ℝ × Ω | z.1 < (ρ z.2 : ℝ) ∧
        b j < riskProcess X x D (Real.toNNReal z.1) z.2} :=
    (measurableSet_lt measurable_fst (hRho.comp measurable_snd)).inter
      (measurableSet_lt measurable_const (hRisk.comp hPair))
  have hJointMeas (j : ℕ) : Measurable
      (fun z : ℝ × Ω =>
        if z.1 < (ρ z.2 : ℝ) ∧
            b j < riskProcess X x D (Real.toNNReal z.1) z.2
        then (1 : ℝ) else 0) :=
    Measurable.ite (hJoint j) measurable_const measurable_const
  constructor
  · intro j
    have hStrong : StronglyMeasurable
        (fun z : ℝ × Ω =>
          if z.1 < (ρ z.2 : ℝ) ∧
              b j < riskProcess X x D (Real.toNNReal z.1) z.2
          then (1 : ℝ) else 0) :=
      (hJointMeas j).stronglyMeasurable
    have hOccStrong : StronglyMeasurable (Occ j) := by
      simpa only [Occ] using
        (hStrong.integral_prod_left'
          (μ := volume.restrict (Ioo (0 : ℝ) (n : ℝ))))
    exact (hOccStrong.indicator hAmeas).aestronglyMeasurable
  · intro j ω
    let f : ℝ → ℝ := fun t =>
      if t < (ρ ω : ℝ) ∧
          b j < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0
    have hfMeas : Measurable f :=
      (hJointMeas j).comp (measurable_id.prodMk measurable_const)
    have hFinite : volume (Ioo (0 : ℝ) (n : ℝ)) ≠ ⊤ := by
      simp
    have hOne : IntegrableOn (fun _ : ℝ => (1 : ℝ))
        (Ioo (0 : ℝ) (n : ℝ)) volume :=
      integrableOn_const hFinite
    have hNorm : ∀ t : ℝ,
        ‖(if t < (ρ ω : ℝ) ∧
            b j < riskProcess X x D (Real.toNNReal t) ω
          then (1 : ℝ) else 0)‖ ≤ (1 : ℝ) := by
      intro t
      by_cases ht : t < (ρ ω : ℝ) ∧
          b j < riskProcess X x D (Real.toNNReal t) ω
      · simp [f, ht]
      · simp [f, ht]
    exact hOne.mono' hfMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hNorm)
