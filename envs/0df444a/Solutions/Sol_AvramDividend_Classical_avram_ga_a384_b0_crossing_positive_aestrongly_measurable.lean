-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a384_b0_crossing_positive_aestrongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:10:59.940206+00:00
-- url     : https://prove2.me/submissions/fcee6a06-9722-4a83-85c9-935f84a9a8f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a386_b0_original_true_crossing_spatial_value_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a377m_masked_gaussian_C2_compensator_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a378_topcap_C2_positive_derivatives_continuousOn
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_zero_jump_generator_eq_gaussian_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option maxHeartbeats 800000

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    let Cross : ℕ → Ω → ℝ := fun m ω =>
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
    let Ccell : ℕ → ℝ := fun i =>
      E (ρ ω) * (w (Y (s i) +
        (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i))) - H i
    ∑ i ∈ Finset.range m,
      if s i < ρ ω ∧ ρ ω < s i + Δ then Ccell i else 0
    ∀ m, AEStronglyMeasurable (fun ω => max (Cross m ω) 0) P := by
  classical
  intro Cross m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let A : ℕ → Ω → Prop := fun i ω => s i < ρ ω ∧ ρ ω < s i + Δ
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (s i) ω - rightLimit D (s i) ω
  let R : ℕ → Ω → ℝ := fun i ω => X.X (s i + Δ) ω - X.X (s i) ω
  let E : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
  obtain ⟨hw1, hw2⟩ := avram_ga_a378_topcap_C2_positive_derivatives_continuousOn
    w C hTopCap hw_smooth
  have hρm : Measurable ρ := measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hA (i : ℕ) : MeasurableSet {ω : Ω | A i ω} := by
    exact ((measurableSet_Ioi : MeasurableSet (Set.Ioi (s i))).preimage hρm).inter
      ((measurableSet_Iio : MeasurableSet (Set.Iio (s i + Δ))).preimage hρm)
  have hY (i : ℕ) : Measurable (Y i) := by
    exact (measurable_const.add ((X.adapted (s i)).mono (𝓕.le _) le_rfl)).sub
      (dividendStrategy_rightLimit_measurable D hD.1.1 (s i))
  have hR (i : ℕ) : Measurable (R i) := by
    exact ((X.adapted (s i+Δ)).mono (𝓕.le _) le_rfl).sub
      ((X.adapted (s i)).mono (𝓕.le _) le_rfl)
  have hPos : ∀ᵐ ω ∂P, ∀ i ∈ Finset.range m,
      A i ω → 0 < Y i ω := by
    filter_upwards [avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD.1.1 ρ j hprefix] with ω hω
    intro i hi ha
    exact lt_of_lt_of_le
      (by positivity : (0 : ℝ) < 1 / ((j : ℝ) + 1)) (hω (s i) ha.1).1
  have hQ := avram_ga_a377m_masked_gaussian_C2_compensator_measurable
    P w hw1 hw2 m A hA Y R hY hR hPos (Δ : ℝ) X.c X.σ E
  have hV := avram_ga_a386_b0_original_true_crossing_spatial_value_measurable
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix m
  have hCrossMeas : AEStronglyMeasurable (Cross m) P := by
    convert hV.sub hQ using 1
    ext ω
    have hsum (f g : ℕ → ℝ) :
        (∑ i ∈ Finset.range m, if A i ω then f i - g i else 0) =
        (∑ i ∈ Finset.range m, if A i ω then f i else 0) -
        (∑ i ∈ Finset.range m, if A i ω then g i else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ha : A i ω <;> simp [ha]
    dsimp [Cross, Δ, s, A, Y, R, E]
    simp_rw [avram_p4_f11_zero_jump_generator_eq_gaussian_drift X hNuZero w]
    rw [hsum] <;> ring
  change ∃ z : Ω → ℝ, StronglyMeasurable z ∧
    (fun ω => max (Cross m ω) (0 : ℝ)) =ᵐ[P] z
  obtain ⟨g, hg, hEq⟩ := hCrossMeas
  refine ⟨(fun ω => max (g ω) (0 : ℝ)),
    (hg.measurable.max measurable_const).stronglyMeasurable, ?_⟩
  filter_upwards [hEq] with ω hω
  exact congrArg (fun z : ℝ => max z 0) hω
