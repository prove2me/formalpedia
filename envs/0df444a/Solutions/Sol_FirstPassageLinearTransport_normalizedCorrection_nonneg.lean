-- Prove2me | solution 1 for FirstPassageLinearTransport.normalizedCorrection_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:15.418629+00:00
-- url     : https://prove2.me/submissions/9808d3cd-934c-4e58-868b-203cb63629d3

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_normalizedCorrectionTerm_nonneg

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (k n : ℕ) :
    0 ≤ normalizedCorrection k n := by
  exact Finset.sum_nonneg fun i _ => normalizedCorrectionTerm_nonneg k n i
end FirstPassageLinearTransport
