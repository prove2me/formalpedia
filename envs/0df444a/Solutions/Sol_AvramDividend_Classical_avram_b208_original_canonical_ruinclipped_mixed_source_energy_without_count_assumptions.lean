-- Prove2me | solution 1 for AvramDividend.Classical.avram_b208_original_canonical_ruinclipped_mixed_source_energy_without_count_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:06:37.331392+00:00
-- url     : https://prove2.me/submissions/813f821f-4774-413f-a6a9-e0c158499c17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
import Theorems.Thm_AvramDividend_Classical_avram_b182_original_ae_true_ruinclipped_both_conull_mixed_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Canonical true original jump-containing stopped grid gives mixed source energy without selected count premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (hx : 0 < x) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (V : ℕ → Ω → ℝ) (J : Ω → Finset ℕ)
    (d : ℝ) (grid : Ω → ℕ → ℝ≥0)
    (hGridMono : ∀ ω, Monotone (grid ω))
    (hGridMeas : ∀ i, Measurable (fun ω => grid ω i))
    (hGridBound : ∀ ω i, i ∈ S → grid ω (i + 1) ≤ (n : ℝ≥0))
    (hGridEndpoints : ∀ ω i, i ∈ S →
      s i ω = grid ω i ∧ t i ω = grid ω (i + 1))
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
    (hInterior : ∀ ω i, i ∈ S →
      s i ω ≤ t i ω ∧
      (t i ω : ℝ≥0∞) < (κ k ω : ℝ≥0∞))
    (hNoJump : ∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
      X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
          V i ω + d * ((t i ω - s i ω : ℝ≥0) : ℝ))
    (hsStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (s i ω : WithTop ℝ≥0)))
    (htStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (t i ω : WithTop ℝ≥0)))
    (hGI : Integrable (fun ω => ∑ i ∈ S, (V i ω)^2) P) :
    let E : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (X.X (t i ω) ω - X.X (s i ω) ω -
        ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c)^2
    let G : Ω → ℝ := fun ω => ∑ i ∈ S, (V i ω)^2
    let D : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (((t i ω - s i ω : ℝ≥0) : ℝ))^2
    Integrable E P ∧ (∫ ω, E ω ∂P) ≤
      2 * (∫ ω, G ω ∂P) + 2 * d^2 * (∫ ω, D ω ∂P) +
        (x + ((k : ℝ) + 1) + ((n : ℝ≥0) : ℝ) * |X.c|)^2 * (((n : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal := by
  classical
  intro E G Denergy
  have hEq (ω : Ω) :
      J ω = S.filter (fun i => ∃ u : ℝ≥0,
        grid ω i < u ∧ u ≤ grid ω (i + 1) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) := by
    ext i
    simp only [Finset.mem_filter]
    exact hJcanon ω i
  have hJsub : ∀ ω, J ω ⊆ S := by
    intro ω i hi
    exact ((hJcanon ω i).mp hi).1
  obtain ⟨hJM0, _, hJD0⟩ :=
    avram_b207_original_canonical_bounded_marked_grid_measurable_integrable_real_dom
      X hFinite n (n : ℝ≥0) le_rfl S grid hGridMono hGridMeas hGridBound
  have hJM : Measurable (fun ω => ((J ω).card : ℝ)) := by
    convert hJM0 using 1
    funext ω
    rw [hEq ω]
  have hJD : ∀ᵐ ω ∂P, ((J ω).card : ℝ) ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal := by
    filter_upwards [hJD0] with ω hω
    simpa only [hEq ω] using hω
  exact avram_b182_original_ae_true_ruinclipped_both_conull_mixed_energy
    X hFinite x hx C D hD n ρ hρbound hρclip κ hκexact
    k S s t V J d hInterior hJsub hJM hJD hNoJump hsStop htStop hGI
