-- Prove2me | solution 1 for ClassicalComplexWPT.norm_seriesTsum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:07:49.848836+00:00
-- url     : https://prove2.me/submissions/f6e0937d-201a-4d2f-abd4-9d2af2c08e08

import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Definitions.Def_ClassicalComplexWPT_NormalSum

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 800000
open ClassicalComplexWPT
variable {𝕜 E F I : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
omit [CompleteSpace F]
namespace ClassicalComplexWPT
theorem _root_.solution (p : I → FormalMultilinearSeries 𝕜 E F)
    (hcoeff : ∀ n, Summable (fun i ↦ ‖p i n‖)) (n : ℕ) :
    ‖seriesTsum p n‖ ≤ ∑' i, ‖p i n‖ := by
  exact norm_tsum_le_tsum_norm (hcoeff n)
end ClassicalComplexWPT
