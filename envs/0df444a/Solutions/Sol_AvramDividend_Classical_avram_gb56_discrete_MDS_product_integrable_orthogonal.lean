-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb56_discrete_MDS_product_integrable_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:50:35.470716+00:00
-- url     : https://prove2.me/submissions/08a0bb93-d802-476b-b142-f2ff8b4fff42

import Mathlib
import Theorems.Thm_Martingale_integral_mul_mds_eq_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal

/-- L2 martingale differences are orthogonal, with L1 products. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (𝓖 : Filtration ℕ mΩ)
    (V : ℕ → Ω → ℝ)
    (hmem : ∀ j, MemLp (V j) 2 P)
    (hadapt : ∀ j, StronglyMeasurable[𝓖 (j + 1)] (V j))
    (hmds : ∀ j, P[V j | 𝓖 j] =ᵐ[P] 0)
    (i r : ℕ) (hir : i < r) :
    Integrable (fun ω => V i ω * V r ω) P ∧
      (∫ ω, V i ω * V r ω ∂P) = 0 := by
  exact ⟨(hmem i).integrable_mul (hmem r),
    Martingale.integral_mul_mds_eq_zero P 𝓖 V hmem hadapt hmds hir⟩
