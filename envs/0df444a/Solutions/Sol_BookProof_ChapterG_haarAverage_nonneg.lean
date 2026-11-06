-- Prove2me | solution 1 for BookProof.ChapterG.haarAverage_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T14:17:13.990503+00:00
-- url     : https://prove2.me/submissions/c5ed4172-868e-4ddc-865a-2e18328eed54

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.haarAverage_nonneg
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in

theorem solution (f : X → ℝ) (hf : 0 ≤ f) :
    0 ≤ haarAverage (μG := μG) f := by
  intro x
  simp only [haarAverage, Pi.zero_apply]
  apply integral_nonneg
  intro g
  exact hf (g⁻¹ • x)
