-- Prove2me | solution 1 for BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:31:30.440463+00:00
-- url     : https://prove2.me/submissions/61557ef3-e233-40af-a7fe-2b8586d2732d

-- Generated from ChapterBddBelowFiberSumEsa.lean — solution of BookProof.BddBelowFiberSumEsa.fiberSumHam_essentiallySelfAdjoint_of_bddBelow'
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Theorems.Thm_BookProof_BddBelowFiberSumEsa_fiberSumHam_essentiallySelfAdjoint_of_bddBelow
open BookProof.BddBelowFiberSumEsa




open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (V : ι → ℝ → ℝ)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hbdd : ∀ i, BddBelow (Set.range (V i))) :
    EssentiallySelfAdjointOn (fiberCore ι) (fiberSumHam V hV) := by

  refine fiberSumHam_essentiallySelfAdjoint_of_bddBelow V hV (fun i => ?_)
  obtain ⟨c, hc⟩ := hbdd i
  exact ⟨-c, fun x => by simpa using hc ⟨x, rfl⟩⟩
