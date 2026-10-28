-- Prove2me | solution 1 for BookProof.BddBelowWallEsa.wallHam_essentiallySelfAdjoint_of_bddBelow_prime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:23:03.963253+00:00
-- url     : https://prove2.me/submissions/e5bc2ec4-c1ec-4fdf-8d8a-8d775071ac3e

import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterWallDeficiencyObstruction
import Definitions.Def_ChapterWeakSecondDerivative
import Definitions.Def_ChapterBddBelowWallEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.ScalaronEsa
open BookProof.ScalaronWallEsa
open BookProof.BddBelowWallEsa
open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv
noncomputable section
theorem solution (V : ℝ → ℝ)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVb : BddBelow (Set.range V)) :
    EssentiallySelfAdjointOn (ccDomain ℝ) (wallHam V hV) := by
  obtain ⟨m, hm⟩ := hVb
  exact wallHam_essentiallySelfAdjoint_of_bddBelow V hV (K := -m)
    (fun x => by simpa using hm (Set.mem_range_self x))
