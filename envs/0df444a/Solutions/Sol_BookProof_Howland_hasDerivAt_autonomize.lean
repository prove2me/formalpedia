-- Prove2me | solution 1 for BookProof.Howland.hasDerivAt_autonomize
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:09:48.462659+00:00
-- url     : https://prove2.me/submissions/b8fe522a-501a-4737-ab5d-7db533c1c318

-- Generated from ChapterHowlandAutonomization.lean — solution of BookProof.Howland.hasDerivAt_autonomize
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
open BookProof.Howland




open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (f : ℝ → E → E) (x : ℝ → E) (t : ℝ)
    (hx : HasDerivAt x (f t (x t)) t) :
    HasDerivAt (fun s : ℝ => ((s, x s) : ℝ × E)) (autonomize f (t, x t)) t := by

  simpa [autonomize] using (hasDerivAt_id t).prodMk hx
