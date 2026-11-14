-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a152_b0_original_fullcell_positive_residual_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:06:58.507294+00:00
-- url     : https://prove2.me/submissions/6e921b6a-8ce0-4c8b-a305-06fb0c282921

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a163_original_full_mesh_source_endpoint_positive
import Theorems.Thm_AvramDividend_Classical_avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact masked original physical Gaussian source measurability using the
original stopping clock, positive endpoints, and zero-jump generator law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hSigmaNonzero : X.σ ≠ 0)
    (hNuZero : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ τ ω) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    let Full : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i =>
      E (s i) * (deriv w (Y (s i)) * Z i +
        (iteratedDeriv 2 w (Y (s i)) / 2) *
          (Z i^2 - (Δ : ℝ) * X.σ^2)) +
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y (s i) + R i) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ s i + Δ ≤ ρ ω then F i else 0
    ∀ m, AEStronglyMeasurable (fun ω => max (Full m ω) 0) P := by
  classical
  intro Full m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let A : ℕ → Ω → Prop := fun i ω => s i < ρ ω ∧ s i + Δ ≤ ρ ω
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (s i) ω - rightLimit D (s i) ω
  let R : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := hopen.uniqueDiffOn
  have hSub : Ioi (0 : ℝ) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy; exact ⟨hy, by simp [hTopCap]⟩
  have h0 : ContinuousOn w (Ioi (0 : ℝ)) := hw_smooth.continuousOn.mono hSub
  have h1 : ContinuousOn (deriv w) (Ioi (0 : ℝ)) := by
    have hc := hw_smooth.continuousOn_iteratedDerivWithin (by norm_num : (1 : WithTop ENat) ≤ (2 : WithTop ENat)) hu
    have heq := iteratedDerivWithin_of_isOpen hopen (n := 1) (f := w)
    simpa only [iteratedDeriv_one] using (hc.congr heq.symm).mono hSub
  have h2 : ContinuousOn (iteratedDeriv 2 w) (Ioi (0 : ℝ)) := by
    have hc := hw_smooth.continuousOn_iteratedDerivWithin (by norm_num : (2 : WithTop ENat) ≤ (2 : WithTop ENat)) hu
    exact (hc.congr (iteratedDerivWithin_of_isOpen hopen (n := 2) (f := w)).symm).mono hSub
  have hρm : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) := (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hA (i : ℕ) : MeasurableSet {ω : Ω | A i ω} := by
    have hL : MeasurableSet {ω : Ω | (s i : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0)} := measurableSet_Ioi.preimage hρm
    have hR : MeasurableSet {ω : Ω | ((s i + Δ : ℝ≥0) : WithTop ℝ≥0) ≤ (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ici.preimage hρm
    simpa only [A, Set.setOf_and, WithTop.coe_lt_coe, WithTop.coe_le_coe] using hL.inter hR
  have hY (i : ℕ) : Measurable (Y i) := by
    have hXm := (X.adapted (s i)).mono (𝓕.le (s i)) le_rfl
    have hDm := dividendStrategy_rightLimit_measurable D hD.1.1 (s i)
    exact (measurable_const.add hXm).sub hDm
  have hR (i : ℕ) : Measurable (R i) := by
    have hXm := (X.adapted (s i)).mono (𝓕.le (s i)) le_rfl
    have hXn := (X.adapted (s i + Δ)).mono (𝓕.le (s i + Δ)) le_rfl
    exact hXn.sub hXm
  have hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω ∧ 0 < Y i ω + R i ω := by
    filter_upwards [avram_ga_a163_original_full_mesh_source_endpoint_positive
      X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
      hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
      ρ hρstop hρle j hprefix m] with ω hw
    intro i hi hh
    exact hw i hi hh
  have hMeasured := avram_ga_a167_masked_positive_C2_gaussian_source_residual_measurable
    P w h0 h1 h2 m A hA Y R hY hR hPos (Δ : ℝ) X.c X.σ
    (fun i => E (s i)) (fun i => E (s i + Δ))
  have hEq (ω : Ω) : Full m ω =
      (∑ i ∈ Finset.range m, if A i ω then
        E (s i + Δ) * (w (Y i ω + R i ω) - w (Y i ω)) -
        (E (s i) * (deriv w (Y i ω) * (R i ω - (Δ : ℝ) * X.c) +
          (iteratedDeriv 2 w (Y i ω) / 2) *
            ((R i ω - (Δ : ℝ) * X.c)^2 - (Δ : ℝ) * X.σ^2)) +
          (Δ : ℝ) * E (s i) * (X.σ^2 / 2 * iteratedDeriv 2 w (Y i ω) +
            X.c * deriv w (Y i ω)))
        else 0) := by
    dsimp [Full,A,Y,R,E,s,Δ]
    apply Finset.sum_congr rfl
    intro i hi; split_ifs <;> try rfl
    simpa only [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hNuZero w]
  have hFull : AEStronglyMeasurable (Full m) P :=
    hMeasured.congr (Filter.Eventually.of_forall (fun ω => (hEq ω).symm))
  have hc : Continuous (fun z : ℝ => max z 0) := continuous_id.max continuous_const
  simpa only [Function.comp_apply] using hc.comp_aestronglyMeasurable hFull
