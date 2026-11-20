-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_HJB_continuous_w_has_finitecap_K
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:31:30.279523+00:00
-- url     : https://prove2.me/submissions/e206e2c0-f870-4bb2-82dd-c332da75354c

import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (C : ℝ≥0∞) :
    ∃ K : ℝ, ∀ y : ℝ,
      0 ≤ y → y ≤ C.toReal → |w y| ≤ K := by
  have hwc : ContinuousOn w (Icc (0 : ℝ) C.toReal) :=
    hw.mono (by intro y hy; exact hy.1)
  have habs : ContinuousOn (fun y : ℝ => |w y|)
      (Icc (0 : ℝ) C.toReal) := hwc.abs
  have hcompact : IsCompact ((fun y : ℝ => |w y|) ''
      Icc (0 : ℝ) C.toReal) :=
    isCompact_Icc.image_of_continuousOn habs
  obtain ⟨K, hK⟩ := hcompact.bddAbove
  refine ⟨K, ?_⟩
  intro y hy0 hyC
  exact hK (mem_image_of_mem _ ⟨hy0, hyC⟩)
