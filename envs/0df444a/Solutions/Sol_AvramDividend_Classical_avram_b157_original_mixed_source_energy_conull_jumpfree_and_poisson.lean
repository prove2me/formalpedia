-- Prove2me | solution 1 for AvramDividend.Classical.avram_b157_original_mixed_source_energy_conull_jumpfree_and_poisson
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:41:22.58995+00:00
-- url     : https://prove2.me/submissions/52604ab8-617c-45c6-ae81-e1c6cc891a55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original mixed finite Gaussian and marked-grid mesh square-energy bound with only conull source count domination. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d a b : ℝ) (hab : a ≤ b) (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ))) (hJdom : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω → X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c = V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω i, i ∈ S → i ∈ J ω → |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a)
    (hEmeas : Measurable (fun ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω - ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P)
    (hDI : Integrable (fun ω => ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P) :
    let E : Ω → ℝ := fun ω => ∑ i ∈ S,
      (X.X (t i ω) ω - X.X (s i ω) ω - ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω => ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (b-a)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by 
  classical
  dsimp only
  let E : Ω → ℝ := fun ω => ∑ i ∈ S,
    (X.X (t i ω) ω - X.X (s i ω) ω - ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
  let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
  let D : Ω → ℝ := fun ω => ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
  let C : Ω → ℝ := fun ω => ((J ω).card : ℝ)
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iio (0 : ℝ))
  obtain ⟨hNI, hNmean⟩ := avram_ja35_original_negative_borel_real_count_first_moment X hFinite T (Iio (0 : ℝ)) measurableSet_Iio (Subset.refl _)
  dsimp only at hNI hNmean
  have hCI : Integrable C P := by
    apply hNI.mono_nonneg hJmeas.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _)
    · exact hJdom
  have hCmean : (∫ ω, C ω ∂P) ≤ ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
    calc
      (∫ ω, C ω ∂P) ≤ (∫ ω, (N ω).toReal ∂P) := integral_mono_ae hCI hNI hJdom
      _ = _ := hNmean
  have hContact (ω : Ω) : (∑ i ∈ S, if i ∈ J ω then (b-a)^2 else 0) = (b-a)^2 * C ω := by
    have hs : S.filter (fun i => i ∈ J ω) = J ω := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hi => ⟨hJsub ω hi, hi⟩⟩
    have hCard : (S ∩ J ω).card = (J ω).card := by rw [Finset.inter_eq_right.mpr (hJsub ω)]
    simp [Finset.sum_ite, Finset.sum_const, hs, C, mul_comm]
    exact Or.inl hCard
  let A : Set Ω := {η | ∀ i, i ∈ S → i ∉ J η →
    X.X (t i η) η - X.X (s i η) η - ((t i η - s i η : ℝ≥0) : ℝ) * X.c = V i η + d * ((t i η - s i η : ℝ≥0) : ℝ)}
  have hBound : ∀ᵐ ω ∂P, E ω ≤ 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω := by
    filter_upwards [hNoJump] with ω hω
    have hh := avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
      X S s t V J A d a b hab
      (by intro η hη i hi hj; exact hη i hi hj)
      (by intro η hη i hi hj; exact hJump η i hi hj) ω hω
    change E ω ≤ ∑ i ∈ S, (2 * (V i ω)^2 + 2 * d^2 * (((t i ω - s i ω : ℝ≥0) : ℝ))^2 + if i ∈ J ω then (b-a)^2 else 0) at hh
    calc
      E ω ≤ _ := hh
      _ = 2 * G ω + 2 * d^2 * D ω +
          (∑ i ∈ S, if i ∈ J ω then (b-a)^2 else 0) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      _ = _ := by rw [hContact ω]
  have hEnonneg (ω : Ω) : 0 ≤ E ω := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hEnvI : Integrable (fun ω => 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω) P := ((hGI.const_mul 2).add (hDI.const_mul (2 * d^2))).add (hCI.const_mul ((b-a)^2))
  have hEI : Integrable E P := hEnvI.mono_nonneg hEmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hEnonneg) (hBound)
  refine ⟨hEI, ?_⟩
  calc
    (∫ ω, E ω ∂P) ≤
        ∫ ω, (2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω) ∂P :=
      integral_mono_ae hEI hEnvI hBound
    _ = 2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (b-a)^2 * (∫ ω, C ω ∂P) := by
      calc
        (∫ ω, 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω ∂P) =
          (∫ ω, 2 * G ω + 2 * d^2 * D ω ∂P) +
          (∫ ω, (b-a)^2 * C ω ∂P) := by
            exact integral_add
              ((hGI.const_mul 2).add (hDI.const_mul (2 * d^2)))
              (hCI.const_mul ((b-a)^2))
        _ = (∫ ω, 2 * G ω ∂P) + (∫ ω, 2 * d^2 * D ω ∂P) +
            (∫ ω, (b-a)^2 * C ω ∂P) := by
            congr 1
            exact integral_add (hGI.const_mul 2) (hDI.const_mul (2 * d^2))
        _ = _ := by simp only [integral_const_mul]
    _ ≤ _ := by
      have hs : 0 ≤ (b-a)^2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hCmean hs]
