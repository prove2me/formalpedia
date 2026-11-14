-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a180_original_masked_gaussian_Hessian_uniform_measurable_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:13:43.728216+00:00
-- url     : https://prove2.me/submissions/f0b0683d-c13b-4b08-bcaa-2602b2ca9d84

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Genuine stopped source Hessian mask has a uniform C2 compact bound and
measurability across every physical mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      if s < ρ ω ∧ s + Δ ≤ ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ m i, AEStronglyMeasurable (H m i) P) ∧
      (∀ m, ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m, |H m i ω| ≤ K) := by
  classical
  intro H
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
  let A : ℕ → ℕ → Ω → Prop := fun m i ω =>
    s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    x + X.X (s m i) ω - rightLimit D (s m i) ω
  have hSub : Ioi (0 : ℝ) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨hy, by simp [hTopCap]⟩
  have hwPos : ContDiffOn ℝ 2 w (Ioi (0 : ℝ)) := hw.mono hSub
  obtain ⟨K,hK,hJet⟩ :=
    avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
      X x hx D hD w C hTopCap hw ρ j hprefix
  have hρm : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hAm (m i : ℕ) : MeasurableSet {ω : Ω | A m i ω} := by
    have h1 : MeasurableSet {ω : Ω |
        (s m i : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ioi.preimage hρm
    have h2 : MeasurableSet {ω : Ω |
        ((s m i + Δ m : ℝ≥0) : WithTop ℝ≥0) ≤
          (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ici.preimage hρm
    simpa only [A,Set.setOf_and,WithTop.coe_lt_coe,WithTop.coe_le_coe] using h1.inter h2
  have hYm (m i : ℕ) : Measurable (Y m i) := by
    have hXm : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le (s m i)) le_rfl
    have hDm : Measurable (fun ω => rightLimit D (s m i) ω) :=
      dividendStrategy_rightLimit_measurable D hD (s m i)
    exact (measurable_const.add hXm).sub hDm
  have hb := avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD ρ j hprefix
  have hPos (m i : ℕ) : ∀ᵐ ω ∂P, A m i ω → 0 < Y m i ω := by
    filter_upwards [hb] with ω hω
    intro ha
    have hp := (hω (s m i) ha.1).1
    exact lt_of_lt_of_le (by positivity : 0 < (1 : ℝ) / ((j : ℝ) + 1)) hp
  have hHm (m i : ℕ) : AEStronglyMeasurable (H m i) P := by
    have h := avram_ga_a179_measurable_masked_positive_C2_Hessian_coefficient
      P w hwPos (A m i) (hAm m i) (Y m i) (hYm m i)
        (hPos m i) (Real.exp (-(q * (s m i : ℝ))))
    exact h
  refine ⟨K,hK,hHm,?_⟩
  intro m
  filter_upwards [hJet] with ω hω
  intro i hi
  by_cases ha : A m i ω
  · have hBound := (hω (s m i) ha.1).2.2
    have hEq : iteratedDeriv 2 w (Y m i ω) =
        deriv (deriv w) (Y m i ω) := by
      simp [iteratedDeriv_succ]
    have htime : 0 ≤ (s m i : ℝ) := NNReal.coe_nonneg _
    have hExp : 0 ≤ Real.exp (-(q * (s m i : ℝ))) ∧
        Real.exp (-(q * (s m i : ℝ))) ≤ 1 := by
      constructor
      · exact le_of_lt (Real.exp_pos _)
      · exact (Real.exp_le_one_iff).mpr (by nlinarith)
    have hJ : |iteratedDeriv 2 w (Y m i ω)| ≤ K := by
      simpa only [hEq] using hBound
    have hM : |Real.exp (-(q * (s m i : ℝ))) *
        iteratedDeriv 2 w (Y m i ω)| ≤ K := by
      rw [abs_mul, abs_of_nonneg hExp.1]
      nlinarith [abs_nonneg (iteratedDeriv 2 w (Y m i ω))]
    change |(if A m i ω then
      Real.exp (-(q * (s m i : ℝ))) *
        iteratedDeriv 2 w (Y m i ω) else 0)| ≤ K
    simpa only [if_pos ha] using hM
  · change |(if A m i ω then
      Real.exp (-(q * (s m i : ℝ))) *
        iteratedDeriv 2 w (Y m i ω) else 0)| ≤ K
    simpa only [if_neg ha, abs_zero] using hK
