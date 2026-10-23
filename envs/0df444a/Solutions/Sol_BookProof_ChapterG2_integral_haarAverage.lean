-- Prove2me | solution 1 for BookProof.ChapterG2.integral_haarAverage
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-22T17:06:30.990169+00:00
-- url     : https://prove2.me/submissions/ba55013c-57d9-40e5-99fe-62fa9fef5c52

-- Generated from ChapterG2.lean — solution of BookProof.ChapterG2.integral_haarAverage
import Mathlib
import Definitions.Def_ChapterG2
import Definitions.Def_ChapterG
open BookProof.ChapterG2
open BookProof.ChapterG



open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : Type*} [CommRing A] (Q : A)
variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

set_option maxHeartbeats 1000000 in

theorem solution [MeasurableSpace X] [MeasurableSMul G X]
    [MeasurableMul G]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ)
    (f : X → ℝ)
    (hint : Integrable (fun p : G × X => f (p.1⁻¹ • p.2)) (μG.prod μ)) :
    ∫ x, haarAverage (μG := μG) f x ∂μ = ∫ x, f x ∂μ := by
  simp only [haarAverage]
  rw [MeasureTheory.integral_integral_swap]
  · have hcomp : ∀ g : G, ∫ x, f (g • x) ∂μ = ∫ x, f x ∂μ := by
      intro g
      have hemb : MeasurableEmbedding (fun x : X => g • x) :=
        (MeasurableEquiv.smul g).measurableEmbedding
      rw [(hμ g).integral_comp hemb]
    have hswap : (fun g : G => ∫ x, f (g⁻¹ • x) ∂μ) = fun _ : G => ∫ x, f x ∂μ := by
      funext g; exact hcomp g⁻¹
    rw [hswap, integral_const]
    simp
  · exact hint.swap
