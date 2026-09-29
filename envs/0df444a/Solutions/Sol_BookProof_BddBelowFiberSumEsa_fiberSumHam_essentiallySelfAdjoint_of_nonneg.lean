-- Prove2me | solution 1 for BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:43:26.797506+00:00
-- url     : https://prove2.me/submissions/cfdfbd45-f020-4fe2-9c29-3cd7c7209ff1

-- Generated from ChapterBddBelowFiberSumEsa.lean — solution of BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_nonneg
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_essentiallySelfAdjoint_of_bddBelow
open BookProof.BddBelowFiberSumEsa












open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (hnn : ∀ i x, 0 ≤ V i x) :
    EssentiallySelfAdjointOn (fiberCore ι) (fiberSumHam V hV) :=
  fiberSumHam_essentiallySelfAdjoint_of_bddBelow V hV
      (fun i => ⟨0, fun x => by simpa using hnn i x⟩)
