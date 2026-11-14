-- Prove2me | solution 1 for AvramDividend.Classical.avram_b78_original_event_restricted_mixed_source_square_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T13:01:57.059014+00:00
-- url     : https://prove2.me/submissions/5a1dc6ea-0cc0-4afe-9252-30d4b11fa3cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
import Theorems.Thm_AvramDividend_Classical_avram_b58_original_selected_negative_jump_cells_uniform_count_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original mixed source interior energy has a finite event-restricted estimate, even when zero-clock paths lie outside the event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (A : Set Ω) (hA : MeasurableSet A)
    (T : ℝ≥0) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d a b : ℝ) (hab : a ≤ b)
    (hJsub : ∀ ω, J ω ⊆ S)
    (hJmeas : Measurable (fun ω : Ω => ((J ω).card : ℝ)))
    (hJdom : ∀ ω : Ω, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal)
    (hNoJump : ∀ ω ∈ A, ∀ i ∈ S, i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hJump : ∀ ω ∈ A, ∀ i ∈ S, i ∈ J ω →
      |X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c| ≤ b - a)
    (hEmeas : Measurable (fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P)
    (hDI : Integrable (fun ω => ∑ i ∈ S,
      (((t i ω - s i ω : ℝ≥0) : ℝ))^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    IntegrableOn E A P ∧ (∫ ω in A, E ω ∂P) ≤
      2 * (∫ ω in A, G ω ∂P) + 2 * d^2 * (∫ ω in A, D ω ∂P) +
        (b-a)^2 * ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by 
  classical
  dsimp only
  let E : Ω → ℝ := fun ω => ∑ i ∈ S,
    (X.X (t i ω) ω - X.X (s i ω) ω - ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
  let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
  let D : Ω → ℝ := fun ω => ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
  let C : Ω → ℝ := fun ω => ((J ω).card : ℝ)
  have hC := avram_b58_original_selected_negative_jump_cells_uniform_count_L1 X hFinite T A J hJmeas hJdom
  have hCI : Integrable C P := hC.1
  have hCmean : (∫ ω in A, C ω ∂P) ≤ ((T : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := hC.2
  have hContact (ω : Ω) : (∑ i ∈ S, if i ∈ J ω then (b-a)^2 else 0) =
        (b-a)^2 * C ω := by
    have hs : S.filter (fun i => i ∈ J ω) = J ω := by
      ext i
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hi => ⟨hJsub ω hi, hi⟩⟩
    have hCard : (S ∩ J ω).card = (J ω).card := by rw [Finset.inter_eq_right.mpr (hJsub ω)]
    simp [Finset.sum_ite, Finset.sum_const, hs, C, mul_comm]
    exact Or.inl hCard
  have hBound (ω : Ω) (hω : ω ∈ A) : E ω ≤ 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω := by
    have hh := avram_b60_original_compact_jumpless_gaussian_jumpcell_square_split
      X S s t V J A d a b hab hNoJump hJump ω hω
    change E ω ≤ ∑ i ∈ S, (2 * (V i ω)^2 +
      2 * d^2 * (((t i ω - s i ω : ℝ≥0) : ℝ))^2 +
      if i ∈ J ω then (b-a)^2 else 0) at hh
    calc
      E ω ≤ _ := hh
      _ = 2 * G ω + 2 * d^2 * D ω +
          (∑ i ∈ S, if i ∈ J ω then (b-a)^2 else 0) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      _ = _ := by rw [hContact ω]
  have hEnonneg (ω : Ω) : 0 ≤ E ω := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hEnvI : Integrable (fun ω => 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω) P := ((hGI.const_mul 2).add (hDI.const_mul (2 * d^2))).add (hCI.const_mul ((b-a)^2))
  have hBoundAE : ∀ᵐ ω ∂(P.restrict A), E ω ≤ 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω := by
    filter_upwards [ae_restrict_mem hA] with ω hω; exact hBound ω hω
  have hEI : IntegrableOn E A P := hEnvI.integrableOn.mono_nonneg
    hEmeas.aestronglyMeasurable (Filter.Eventually.of_forall hEnonneg) hBoundAE
  refine ⟨hEI, ?_⟩
  calc
    (∫ ω in A, E ω ∂P) ≤
        ∫ ω in A, (2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω) ∂P :=
      integral_mono_ae hEI hEnvI.integrableOn hBoundAE
    _ = 2 * (∫ ω in A, G ω ∂P) + 2 * d^2 * (∫ ω in A, D ω ∂P) +
        (b-a)^2 * (∫ ω in A, C ω ∂P) := by
      calc
        (∫ ω in A, 2 * G ω + 2 * d^2 * D ω + (b-a)^2 * C ω ∂P) =
          (∫ ω in A, 2 * G ω + 2 * d^2 * D ω ∂P) +
          (∫ ω in A, (b-a)^2 * C ω ∂P) := by
            exact integral_add
              ((hGI.const_mul 2).add (hDI.const_mul (2 * d^2))).integrableOn (hCI.const_mul ((b-a)^2)).integrableOn
        _ = (∫ ω in A, 2 * G ω ∂P) + (∫ ω in A, 2 * d^2 * D ω ∂P) +
            (∫ ω in A, (b-a)^2 * C ω ∂P) := by
            congr 1
            exact integral_add (hGI.const_mul 2).integrableOn (hDI.const_mul (2 * d^2)).integrableOn
        _ = _ := by simp only [integral_const_mul]
    _ ≤ _ := by
      have hs : 0 ≤ (b-a)^2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hCmean hs]
