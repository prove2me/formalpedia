-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_lower_of_maximalRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:14.513175+00:00
-- url     : https://prove2.me/submissions/0ae338a1-0e7a-4b66-bdca-198c7353b22a

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {n M H : ℕ} {h : ℝ}
    (hreg : MaximalParityRegular n M h) (hHM : H ≤ M) :
    (H : ℝ) / 2 - h ≤ oddCount n H := by
  have habs := hreg H hHM
  have hlower := (abs_le.mp habs).1
  linarith
end FirstPassageLinearTransport
