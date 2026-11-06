-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:26:47.28979+00:00
-- url     : https://prove2.me/submissions/9060db06-db1e-4ead-b748-33ea21a186f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smalljump_cutoff_support_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The original Levy finite small band is a genuine finite jump sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let N : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
        (fun u : ℝ≥0 => (u, j u)))
    let E : Set (ℝ≥0 × ℝ) :=
      Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧ -1 < j u ∧
        j u ≤ -(1 / ((n : ℝ) + 1))) ∧
      (∫ p in E, p.2 ∂N) = ∑ u ∈ F, j u := by
  classical
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let N : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j u)))
  let E : Set (ℝ≥0 × ℝ) :=
    Ioc (0 : ℝ≥0) T ×ˢ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let S : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ -1 < j u ∧
    j u ≤ -(1 / ((n : ℝ) + 1))}
  have hpos1 : 0 < (n : ℝ) + 1 := by positivity
  have hpos2 : 0 < (n : ℝ) + 2 := by positivity
  have hden : -(1 / ((n : ℝ) + 1)) ≤ -(1 / ((n : ℝ) + 2)) := by
    have hdiv : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      apply (div_le_div_iff₀ hpos2 hpos1).2
      nlinarith
    linarith
  have hSfinite : S.Finite := by
    apply (avram_p4_h_gaussian_original_smalljump_cutoff_support_finite X ω T n).subset
    intro u hu
    change 0 < u ∧ u ≤ T ∧ -1 < j u ∧
      j u ≤ -(1 / ((n : ℝ) + 1)) at hu
    rcases hu with ⟨h0, hT, hlo, hhi⟩
    exact ⟨h0, hT, hlo, hhi.trans hden⟩
  let F : Finset ℝ≥0 := hSfinite.toFinset
  have hF : ∀ u : ℝ≥0, u ∈ F ↔ u ∈ S := by
    intro u
    simp [F]
  have hsum : (∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
      E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) =
      ∑ u ∈ F, j u := by
    calc
      (∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
          E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0) =
          ∑ u ∈ F, if 0 < u ∧ j u ≠ 0 then
            E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := by
        apply tsum_eq_sum
        intro u hu
        have hnot : u ∉ S := by
          intro hs
          exact hu ((hF u).2 hs)
        by_cases hc : 0 < u ∧ j u ≠ 0
        · have hnotE : (u, j u) ∉ E := by
            intro hE
            apply hnot
            change u ∈ Ioc (0 : ℝ≥0) T ∧
              j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) at hE
            rcases hE with ⟨⟨h0, hT⟩, ⟨hlo, hhi⟩⟩
            exact ⟨h0, hT, hlo, hhi⟩
          simp [hc, Set.indicator_of_notMem hnotE]
        · simp [hc]
      _ = ∑ u ∈ F, j u := by
        apply Finset.sum_congr rfl
        intro u hu
        have hs : u ∈ S := (hF u).1 hu
        change 0 < u ∧ u ≤ T ∧ -1 < j u ∧
          j u ≤ -(1 / ((n : ℝ) + 1)) at hs
        rcases hs with ⟨h0, hT, hlo, hhi⟩
        have hneg : j u < 0 := by
          have hrec : 0 < 1 / ((n : ℝ) + 1) := by positivity
          linarith
        have hE : (u, j u) ∈ E := by
          change u ∈ Ioc (0 : ℝ≥0) T ∧
            j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
          exact ⟨⟨h0, hT⟩, ⟨hlo, hhi⟩⟩
        simp [h0, ne_of_lt hneg, Set.indicator_of_mem hE]
  refine ⟨F, ?_, ?_⟩
  · intro u
    simpa only [S, Set.mem_setOf_eq, j] using (hF u)
  · exact (avram_p4_h_gaussian_original_smallband_signed_integral_eq_intrinsic_tsum
      X ω T n).trans hsum
