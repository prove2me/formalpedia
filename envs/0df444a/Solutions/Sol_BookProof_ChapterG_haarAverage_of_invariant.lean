-- Prove2me | solution 1 for BookProof.ChapterG.haarAverage_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T14:17:06.165196+00:00
-- url     : https://prove2.me/submissions/91771b2f-1b03-4b13-81c1-7420f8d2dd82

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.haarAverage_of_invariant
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in

theorem solution (f : X → ℝ) (hf : ∀ g : G, ∀ x, f (g • x) = f x) :
    haarAverage (μG := μG) f = f := by
  funext x
  simp only [haarAverage]
  have : (fun g : G => f (g⁻¹ • x)) = fun _ => f x := by
    funext g; rw [hf g⁻¹ x]
  rw [this, integral_const]; simp
