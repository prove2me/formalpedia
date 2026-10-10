-- Prove2me | solution 1 for BookProof.ChapterLpScaleMeasure.normalized_multiplication_model
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:27:13.738433+00:00
-- url     : https://prove2.me/submissions/6712bb07-3c68-46d7-911c-f29c4bc95ff0

-- Generated from ChapterLpScaleMeasure.lean — solution of BookProof.ChapterLpScaleMeasure.normalized_multiplication_model
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
import Theorems.Thm_BookProof_ChapterLpScaleMeasure_scaleUnitary_intertwines
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure



noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

set_option maxHeartbeats 1000000 in
theorem solution [IsFiniteMeasure nu] (hne : nu Set.univ ≠ 0) :
    ∃ U : Lp ℂ 2 ((nu Set.univ)⁻¹ • nu) ≃ₗᵢ[ℂ] Lp ℂ 2 nu,
      ∀ (g : α → ℂ) (hg : MemLp g ⊤ ((nu Set.univ)⁻¹ • nu))
        (u : Lp ℂ 2 ((nu Set.univ)⁻¹ • nu)),
        (U (multOp g hg u) : α → ℂ) =ᵐ[nu] fun x => g x * (U u : α → ℂ) x := by

  have hc0 : (nu Set.univ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top nu _)
  have hctop : (nu Set.univ)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hne
  exact ⟨scaleUnitary hc0 hctop, fun g hg u => scaleUnitary_intertwines hc0 hctop hg u⟩
