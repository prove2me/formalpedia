-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:32:07.096969+00:00
-- url     : https://prove2.me/submissions/85391d87-4bd2-47fa-8866-bdd07cc18d62

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.condProb_of_bounded_dynamics
import Mathlib
import Definitions.Def_ChapterBornMeasure
import Theorems.Thm_BookProof_ChapterBornMeasure_bornMeasure_absolutelyContinuous
import Theorems.Thm_BookProof_ChapterBornMeasure_isProbabilityMeasure_bornMeasure
import Theorems.Thm_BookProof_ChapterBornMeasure_norm_evolve
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (H : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hH : IsSelfAdjoint H)
    (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) (t : ℝ) :
    IsProbabilityMeasure (bornMeasure (evolve H t psi)) ∧
      bornMeasure (evolve H t psi) ≪ μ :=
  ⟨isProbabilityMeasure_bornMeasure _ (by rw [norm_evolve H hH t psi, hpsi]),
      bornMeasure_absolutelyContinuous _⟩
