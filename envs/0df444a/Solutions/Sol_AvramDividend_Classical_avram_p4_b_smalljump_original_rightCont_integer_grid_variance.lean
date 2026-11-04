-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_integer_grid_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:18:48.166406+00:00
-- url     : https://prove2.me/submissions/eb94a371-2537-414f-9046-be06dfd66ca4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_conditional_cross_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_orthogonal_finite_L2_square_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

/-- L² Pythagoras for increments sampled from the original source's
right-continuous filtration, conditional on genuine source centring. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j : ℕ, MemLp (V j) 2 P)
    (hadapt : ∀ j : ℕ, StronglyMeasurable[𝓕.rightCont ((j + 1 : ℕ) : ℝ≥0)] (V j))
    (hmds : ∀ j : ℕ, P[V j | 𝓕.rightCont (j : ℝ≥0)] =ᵐ[P] 0)
    (n : ℕ) :
    (∫ ω, (∑ j ∈ Finset.range n, V j ω)^2 ∂P) =
      ∑ j ∈ Finset.range n, ∫ ω, (V j ω)^2 ∂P := by
  have hpair : ∀ {i j : ℕ}, i < j →
      (∫ ω, V i ω * V j ω ∂P) = 0 := by
    intro i j hij
    have hle : ((i + 1 : ℕ) : ℝ≥0) ≤ (j : ℝ≥0) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hVi : StronglyMeasurable[𝓕.rightCont (j : ℝ≥0)] (V i) :=
      (hadapt i).mono (𝓕.rightCont.mono hle)
    exact avram_p4_b_smalljump_original_rightCont_conditional_cross_zero
      X (j : ℝ≥0) (V i) (V j) hVi (hmem i) (hmem j) (hmds j)
  have hProd : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => V i ω * V j ω) P := by
    intro i hi j hj
    exact (hmem i).integrable_mul (hmem j)
  have hOrth : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → (∫ ω, V i ω * V j ω ∂P) = 0 := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact hpair hij'
    · calc
        (∫ ω, V i ω * V j ω ∂P) =
            ∫ ω, V j ω * V i ω ∂P := by
              congr 1
              funext ω
              exact mul_comm _ _
        _ = 0 := hpair hji'
  exact avram_p4_b_smalljump_orthogonal_finite_L2_square_identity
    (Finset.range n) V hProd hOrth
