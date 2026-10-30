-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_stopped_rational_closed_reward_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:23:37.572812+00:00
-- url     : https://prove2.me/submissions/774ca4d0-4244-4948-bd6a-143ccfa9b7d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_random_record_shifted_rational_survival_ae_clock
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_age_fullPath_survival_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_randomAge_whole_shiftedPath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- The genuine lower-killed stopped-prefix rational future survival
has the same tilted joint mass as continuous full future survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (a : ℝ) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (A : Set Ω) (hA : MeasurableSet A) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let Bgrid : Set (Ω × ℝ) := {z |
       (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ <
           Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
         0 ≤ a + (X.X (τ z.1 + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1 -
           X.X (τ z.1) z.1)}
     let Bfull : Set (Ω × ℝ) := {z |
       (τ z.1 : ℝ) ≤ z.2 ∧ z.1 ∈ A ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal (z.2 - (τ z.1 : ℝ)) →
         0 ≤ a + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     (∫⁻ z, Bgrid.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
     (∫⁻ z, Bfull.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp)) := by
  classical
  intro Qp Bgrid Bfull
  let age : Ω × ℝ → ℝ≥0 := fun z =>
    Real.toNNReal (z.2 - (τ z.1 : ℝ))
  let Y : Ω → (ℝ≥0 → ℝ) := fun ω u =>
    X.X (τ ω + u) ω - X.X (τ ω) ω
  let H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun u f =>
    if (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < u →
       0 ≤ a + f ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)) then 1 else 0
  have hage : Measurable age := by
    dsimp [age]
    fun_prop
  have hY : Measurable Y :=
    avram_ws01e_b_randomAge_whole_shiftedPath_measurable X τ hτ
  have hH := avram_ws01h_rational_age_fullPath_survival_reward_measurable a
  have hReward : Measurable (fun z : Ω × ℝ => H (age z) (Y z.1)) :=
    hH.comp (hage.prodMk (hY.comp measurable_fst))
  have hGridTest : MeasurableSet
      {z : Ω × ℝ | ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
         0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)} := by
    have heq :
      {z : Ω × ℝ | ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
         0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)} =
      {z : Ω × ℝ | H (age z) (Y z.1) = 1} := by
       ext z
       simp [H]
    rw [heq]
    exact measurableSet_eq_fun hReward measurable_const
  have hGuard : MeasurableSet
      {z : Ω × ℝ | (τ z.1 : ℝ) ≤ z.2} :=
    measurableSet_le
      ((measurable_coe_nnreal_real.comp hτ).comp measurable_fst)
      measurable_snd
  have hPrefix : MeasurableSet {z : Ω × ℝ | z.1 ∈ A} :=
    hA.preimage measurable_fst
  have hBgrid : MeasurableSet Bgrid := by
    change MeasurableSet
      ({z : Ω × ℝ | (τ z.1 : ℝ) ≤ z.2} ∩
       ({z : Ω × ℝ | z.1 ∈ A} ∩
        {z : Ω × ℝ | ∀ n : ℕ, 0 < n → ∀ k : ℕ,
          (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < age z →
          0 ≤ a + Y z.1 ((k : ℝ≥0) * (n : ℝ≥0)⁻¹)}))
    exact hGuard.inter (hPrefix.inter hGridTest)
  have hClosed :
      MeasurableSet {z : Ω × ℝ | 0 ≤ z.2 ∧
        ∀ u : ℝ≥0, u ≤ age z →
          0 ≤ a + Y z.1 u} :=
    avram_ws01h_actual_stopped_future_closed_survival_joint_measurable
      X τ hτ a
  have hBfull : MeasurableSet Bfull := by
    have heq : Bfull =
        {z : Ω × ℝ | (τ z.1 : ℝ) ≤ z.2} ∩
         ({z : Ω × ℝ | z.1 ∈ A} ∩
          {z : Ω × ℝ | 0 ≤ z.2 ∧
            ∀ u : ℝ≥0, u ≤ age z → 0 ≤ a + Y z.1 u}) := by
      ext z
      constructor
      · rintro ⟨ht, hAz, hf⟩
        have hr0 : (0 : ℝ) ≤ z.2 :=
          (NNReal.coe_nonneg (τ z.1)).trans ht
        exact ⟨ht, hAz, hr0, hf⟩
      · rintro ⟨ht, hAz, _, hf⟩
        exact ⟨ht, hAz, hf⟩
    rw [heq]
    exact hGuard.inter (hPrefix.inter hClosed)
  have hAE (ω : Ω) : ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      Bgrid.indicator (fun _ => (1 : ℝ≥0∞)) (ω,r) =
      Bfull.indicator (fun _ => (1 : ℝ≥0∞)) (ω,r) := by
    filter_upwards
      [avram_ws01h_random_record_shifted_rational_survival_ae_clock
        X a τ ω] with r hr
    have hiff : (ω,r) ∈ Bgrid ↔ (ω,r) ∈ Bfull := by
      constructor
      · rintro ⟨hτr, hAω, hgrid⟩
        have hres : 0 ≤ r - (τ ω : ℝ) := sub_nonneg.mpr hτr
        have h := hr.mp ⟨hres, hgrid⟩
        exact ⟨hτr, hAω, h.2⟩
      · rintro ⟨hτr, hAω, hfull⟩
        have hres : 0 ≤ r - (τ ω : ℝ) := sub_nonneg.mpr hτr
        have h := hr.mpr ⟨hres, hfull⟩
        exact ⟨hτr, hAω, h.2⟩
    by_cases hb : (ω,r) ∈ Bgrid
    · have hc := hiff.mp hb
      simp [Set.indicator, hb, hc]
    · have hc : (ω,r) ∉ Bfull := fun h => hb (hiff.mpr h)
      simp [Set.indicator, hb, hc]
  exact avram_ws01h_genuine_Qp_pathwise_volume_ae_reward_transfer
    X θ p hθ hp
    (Bgrid.indicator (fun _ => (1 : ℝ≥0∞)))
    (Bfull.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hBgrid)
    (measurable_const.indicator hBfull) hAE
