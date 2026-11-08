-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_finite_row_clipping_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:37:04.893344+00:00
-- url     : https://prove2.me/submissions/2ff9f6ab-ecf3-4ceb-a4ef-7918e1147b1c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every fixed original-path finite weighted raw-R mesh eventually equals
its coefficient-clipped mesh as the clipping level grows through naturals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (a : Ω → ℕ → ℝ) (ω : Ω) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    ∃ N : ℕ, ∀ k ≥ N,
      (∑ i ∈ Finset.range (n + 1),
        (if |a ω i| ≤ (k : ℝ) then a ω i else 0) *
          (R (u n i) - R (u n (i + 1)))) =
      (∑ i ∈ Finset.range (n + 1),
        a ω i * (R (u n i) - R (u n (i + 1)))) := by
  classical
  let N : ℕ → ℕ := fun i => Classical.choose (exists_nat_gt (|a ω i|))
  have hN (i : ℕ) : |a ω i| < (N i : ℝ) := by
    exact Classical.choose_spec (exists_nat_gt (|a ω i|))
  let Nmax : ℕ := (Finset.range (n + 1)).sup N
  refine ⟨Nmax, ?_⟩
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  have hb : |a ω i| ≤ (k : ℝ) := by
    have hsmall : N i ≤ Nmax := Finset.le_sup hi
    have hle : (N i : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (le_trans hsmall hk)
    exact (le_of_lt (hN i)).trans hle
  simp [hb]
