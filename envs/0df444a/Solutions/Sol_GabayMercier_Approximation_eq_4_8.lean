-- Prove2me | solution 1 for GabayMercier.Approximation.eq_4_8
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T20:47:43.606859+00:00
-- url     : https://prove2.me/submissions/45b9cdb4-d6f5-4eda-aea4-5a0d9084e266

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

open GabayMercier.Approximation


variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.8), corrected to use (2.5) on `w - x`. -/
theorem solution (A : V →L[ℝ] Y) (f₂ : Y → EReal) (α : ℝ)
    (Vh : ℕ → Submodule ℝ V) (Ah : (k : ℕ) → Vh k →L[ℝ] Y)
    (α' M : ℝ) (h : ApproxHyp A f₂ α Vh Ah α' M)
    (k : ℕ) (w : Vh k) (x : V) :
    α * ‖(w : V) - x‖ ≤ ‖A ((w : V) - x)‖ ∧
    ‖A ((w : V) - x)‖ ≤ ‖A w - Ah k w‖ + ‖Ah k w - A x‖ := by
  constructor
  · have hb := h.bddBelow ((w : V) - x)
    have hn := norm_nonneg ((w : V) - x)
    have ha := norm_nonneg (A ((w : V) - x))
    have hp := h.α_pos
    nlinarith
  · rw [map_sub]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _



#print axioms solution

