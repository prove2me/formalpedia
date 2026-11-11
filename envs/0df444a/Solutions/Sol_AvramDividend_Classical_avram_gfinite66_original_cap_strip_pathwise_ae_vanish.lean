-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite66_original_cap_strip_pathwise_ae_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:22:57.045077+00:00
-- url     : https://prove2.me/submissions/eed838ef-e7d4-4f5c-b46e-7910951379f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_dividend_strategy_predictable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_avram_gfinite56_cap_fraction_cutoff_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gfinite68_original_real_time_cap_contact_null
import Theorems.Thm_AvramDividend_Classical_avram_gfinite69_real_time_nullcap_strip_integral_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gfinite70_nonnegative_cap_fraction_monotone
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
      ∀ᵐ ω ∂P,
        Tendsto (fun j : ℕ => A.indicator (Occ j) ω)
          atTop (𝓝 (0 : ℝ)) := by
  classical
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let b : ℕ → ℝ := fun j =>
    C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Occ : ℕ → Ω → ℝ := fun j ω =>
    ∫ t in Ioo (0 : ℝ) (n : ℝ),
      if t < (ρ ω : ℝ) ∧
          b j < riskProcess X x D (Real.toNNReal t) ω
      then (1 : ℝ) else 0 ∂volume
  have hbmono : Monotone b :=
    avram_gfinite70_nonnegative_cap_fraction_monotone
      C.toReal ENNReal.toReal_nonneg
  have hb : Tendsto b atTop (𝓝 C.toReal) :=
    avram_gfinite56_cap_fraction_cutoff_tendsto C.toReal
  have hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D s ω ≤ C.toReal := by
    intro ω s hs
    have hRange := capped_riskProcess_range_before_ruin_including_zero
      X x (le_of_lt hx) C hxc D hD ω s hs
    have hMono := ENNReal.toReal_mono hFiniteCap hRange.2
    simpa [ENNReal.toReal_ofReal hRange.1] using hMono
  have hρruin : ∀ ω,
      (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro ω
    calc
      (ρ ω : ℝ≥0∞) ≤ (σ k ω : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (hρle ω)
      _ ≤ (τ ω : ℝ≥0∞) :=
        ENNReal.coe_le_coe.mpr (hσle k ω)
      _ = (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) : ℝ≥0∞) :=
        by rw [hτeq ω]
      _ ≤ min (ruinTime X x D ω) (n : ℝ≥0∞) :=
        ENNReal.coe_toNNReal_le_self
      _ ≤ ruinTime X x D ω := min_le_left _ _
  have hCapNull := avram_gfinite68_original_real_time_cap_contact_null
    X hBV x C.toReal D hD.1.1 hCap n ρ hρruin
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
  have hU (ω : Ω) : Measurable
      (fun t : ℝ => riskProcess X x D (Real.toNNReal t) ω) :=
    hRisk.comp ((Measurable.real_toNNReal measurable_id).prodMk measurable_const)
  filter_upwards [hCapNull] with ω hωnull
  have hTend := avram_gfinite69_real_time_nullcap_strip_integral_tendsto
    n (ρ ω : ℝ) C.toReal
    (fun t : ℝ => riskProcess X x D (Real.toNNReal t) ω)
    (hU ω) b hbmono hb hωnull
  by_cases hω : ω ∈ A
  · simpa only [Occ, Set.indicator_of_mem hω] using hTend
  · simpa only [Set.indicator_of_notMem hω] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
