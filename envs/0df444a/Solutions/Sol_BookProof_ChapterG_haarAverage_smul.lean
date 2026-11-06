-- Prove2me | solution 1 for BookProof.ChapterG.haarAverage_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T14:17:02.028003+00:00
-- url     : https://prove2.me/submissions/f6aed84b-fafd-4bf1-8e20-77c9ccf8c71f

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.haarAverage_smul
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix
open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in

theorem solution [MeasurableMul G]
    (f : X → ℝ) (g₀ : G) (x : X) :
    haarAverage (μG := μG) f (g₀ • x) = haarAverage (μG := μG) f x := by
  simp only [haarAverage]
  have key : (fun g : G => f (g⁻¹ • (g₀ • x)))
      = fun g : G => (fun h => f (h⁻¹ • x)) (g₀⁻¹ * g) := by
    funext g
    simp only [smul_smul, mul_inv_rev, inv_inv]
  rw [key]
  exact integral_mul_left_eq_self (fun h => f (h⁻¹ • x)) g₀⁻¹
