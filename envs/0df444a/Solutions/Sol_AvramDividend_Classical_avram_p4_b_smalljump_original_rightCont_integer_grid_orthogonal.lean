-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightCont_integer_grid_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:18:41.971596+00:00
-- url     : https://prove2.me/submissions/03599fbc-2681-4b7b-a715-73caa24f2f3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightCont_conditional_cross_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal NNReal

/-- The original source's right-continuous filtration sampled at integer times
gives orthogonal square-integrable martingale differences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (V : ℕ → Ω → ℝ)
    (hmem : ∀ j : ℕ, MemLp (V j) 2 P)
    (hadapt : ∀ j : ℕ, StronglyMeasurable[𝓕.rightCont ((j + 1 : ℕ) : ℝ≥0)] (V j))
    (hmds : ∀ j : ℕ, P[V j | 𝓕.rightCont (j : ℝ≥0)] =ᵐ[P] 0)
    {i j : ℕ} (hij : i < j) :
    ∫ ω, V i ω * V j ω ∂P = 0 := by
  have hle : ((i + 1 : ℕ) : ℝ≥0) ≤ (j : ℝ≥0) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hij)
  have hVi : StronglyMeasurable[𝓕.rightCont (j : ℝ≥0)] (V i) :=
    (hadapt i).mono (𝓕.rightCont.mono hle)
  exact avram_p4_b_smalljump_original_rightCont_conditional_cross_zero
    X (j : ℝ≥0) (V i) (V j) hVi (hmem i) (hmem j) (hmds j)
