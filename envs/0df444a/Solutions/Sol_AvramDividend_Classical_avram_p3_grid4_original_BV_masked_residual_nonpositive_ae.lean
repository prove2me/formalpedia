-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_BV_masked_residual_nonpositive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:41:08.045189+00:00
-- url     : https://prove2.me/submissions/93753b27-f8e0-4284-8a26-106831f37470

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Genuine original BV residual has nonpositive weighted cell increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (a : ℕ → ℝ) (n : ℕ),
      Monotone u → (∀ i, 0 ≤ a i) →
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)
      (∑ i ∈ Finset.range n, a i *
        (R (u i) - R (u (i + 1)))) ≤ 0 := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_residual_continuous_monotone_locally_BV X hBV]
    with ω hω
  rcases hω with ⟨_, hmono, _⟩
  intro u a n hu ha
  dsimp
  apply Finset.sum_nonpos
  intro i hi
  apply mul_nonpos_of_nonneg_of_nonpos (ha i)
  exact sub_nonpos.mpr (hmono (hu (Nat.le_succ i)))
