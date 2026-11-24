-- Prove2me | solution 1 for Formalism.G0.TypeIIUpP.gb_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:07.647805+00:00
-- url     : https://prove2.me/submissions/d8708fda-696f-4543-9974-35da4ba817f2

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_QVandermonde
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_SubspaceCount
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TypeIIUp
import Theorems.Thm_Formalism_G0_TypeIIUpP_qfact_pos
import Theorems.Thm_Formalism_G0_TypeIIUpP_gb_fact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.TypeIIUpP
namespace Formalism.G0.TypeIIUpP
theorem _root_.solution (q n k : ℕ) (h : k ≤ n) : gaussBinom q n k = gaussBinom q n (n - k) := by
  have h1 := gb_fact q n k h
  have h2 := gb_fact q n (n - k) (Nat.sub_le n k)
  rw [Nat.sub_sub_self h] at h2
  have hpos : 0 < qfact q k * qfact q (n - k) := Nat.mul_pos (qfact_pos q k) (qfact_pos q (n - k))
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← mul_assoc, h1, ← h2]
  ring
end Formalism.G0.TypeIIUpP
