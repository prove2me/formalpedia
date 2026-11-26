-- Prove2me | solution 1 for FirstPassageLinearTransport.barrierHitCount_le_legendre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:27.219797+00:00
-- url     : https://prove2.me/submissions/da6429cd-b1e8-4f5b-9e22-4355a34e20f6

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_barrierHitCount_le_exact_cosh

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (t θ : ℝ) (M : ℕ) (ht : 0 ≤ t) (hθ : 0 ≤ θ) :
    (barrierHitCount (2 * t * M) M 0 : ℝ) ≤
      (2 : ℝ) ^ (M + 1) *
        Real.exp (-((M : ℝ) * booleanLegendreRate t θ)) := by
  have hraw := barrierHitCount_le_exact_cosh
    (2 * t * M) θ M (by positivity) hθ
  convert hraw using 1
  unfold booleanLegendreRate
  congr 2
  ring
end FirstPassageLinearTransport
