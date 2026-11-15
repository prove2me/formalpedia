-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a386_b0_original_true_crossing_spatial_value_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T14:13:26.010193+00:00
-- url     : https://prove2.me/submissions/c51fcc6f-bc89-4118-9528-a7b78e894354

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a43_original_clipped_spatial_cell_observations
import Theorems.Thm_AvramDividend_Classical_avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    let V : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      ∑ i ∈ Finset.range m,
        if s i < ρ ω ∧ ρ ω < s i + Δ
        then E (ρ ω) * (w (Y (s i) +
          (X.X (ρ ω) ω - X.X (s i) ω)) - w (Y (s i)))
        else 0
    ∀ m, AEStronglyMeasurable (V m) P := by
  classical
  intro V m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let v : ℕ → Ω → ℝ≥0 := fun i ω => min (s i) (ρ ω)
  let E : ℕ → Ω → ℝ := fun i ω => Real.exp (-(q * (v i ω : ℝ)))
  let Y : ℕ → Ω → ℝ := fun i ω => x + X.X (v i ω) ω - rightLimit D (v i ω) ω
  let Z : ℕ → Ω → ℝ := fun i ω =>
    x + X.X (v (i+1) ω) ω - rightLimit D (v i ω) ω
  let A : ℕ → Ω → Prop := fun i ω => s i < ρ ω ∧ ρ ω < s i + Δ
  have hρ : Measurable ρ := measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hA (i : ℕ) : MeasurableSet {ω : Ω | A i ω} := by
    exact ((measurableSet_Ioi : MeasurableSet (Set.Ioi (s i))).preimage hρ).inter
      ((measurableSet_Iio : MeasurableSet (Set.Iio (s i + Δ))).preimage hρ)
  have hObs := avram_ga_a43_original_clipped_spatial_cell_observations
    X hX hBV hSigmaNonzero hNuZero q hq w C hC hTopCap
    hw_smooth hw_gen x hx hxc D hD n hn τ hτeq hτstop
    ρ hρstop hρle j hprefix m
  change (∀ i, Measurable (E i)) ∧
    (∀ i, Measurable (Y i)) ∧ (∀ i, Measurable (Z i)) ∧
    (∀ᵐ ω ∂P, ∀ i ∈ Finset.range (m + 1),
      (E (i + 1) ω = E i ω ∧ Z i ω = Y i ω) ∨
      (0 < Y i ω ∧ 0 < Z i ω)) at hObs
  obtain ⟨hE,hY,hZ,hAlt⟩ := hObs
  have hAlt' (i : ℕ) (hi : i ∈ Finset.range m) :
      ∀ᵐ ω ∂P, Y i ω = Z i ω ∨
        (0 < Y i ω ∧ 0 < Z i ω) := by
    filter_upwards [hAlt] with ω hω
    have hi' : i ∈ Finset.range (m+1) := by
      exact Finset.mem_range.mpr
        (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self m))
    rcases hω i hi' with hh | hh
    · exact Or.inl hh.2.symm
    · exact Or.inr hh
  have hE' (i : ℕ) : Measurable
      (fun ω => if A i ω then E (i+1) ω else 0) :=
    Measurable.ite (hA i) (hE (i+1)) measurable_const
  have hSpatial := avram_ga_a159_original_gaussian_finite_active_positive_domain_spatial_sum_measurable
    P w (avram_ga_a158_original_topcap_C2_value_continuous_positive_halfline
      w C hTopCap hw_smooth) m Y Z
    (fun i ω => if A i ω then E (i+1) ω else 0) hY hZ hE' hAlt'
  convert hSpatial using 1
  ext ω
  apply Finset.sum_congr rfl
  intro i hi
  change (if A i ω then
    Real.exp (-(q * (ρ ω : ℝ))) *
      (w (x + X.X (s i) ω - rightLimit D (s i) ω +
        (X.X (ρ ω) ω - X.X (s i) ω)) -
        w (x + X.X (s i) ω - rightLimit D (s i) ω))
    else 0) =
    (if A i ω then E (i+1) ω else 0) * (w (Z i ω) - w (Y i ω))
  by_cases hc : A i ω
  · have hStart : v i ω = s i := min_eq_left (le_of_lt hc.1)
    have hStep : s (i+1) = s i + Δ := by
      dsimp [s]; rw [Nat.cast_succ, add_mul, one_mul]
    have hStop : v (i+1) ω = ρ ω := by
      dsimp [v]
      rw [hStep]
      exact min_eq_right (le_of_lt hc.2)
    simp only [if_pos hc]
    dsimp [E, Y, Z]
    rw [hStart, hStop]
    have hAlgebra : x + X.X (s i) ω - rightLimit D (s i) ω +
        (X.X (ρ ω) ω - X.X (s i) ω) =
        x + X.X (ρ ω) ω - rightLimit D (s i) ω := by ring
    rw [hAlgebra]
  · simp [hc]
