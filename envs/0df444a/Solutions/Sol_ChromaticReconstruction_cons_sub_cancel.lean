-- Prove2me | solution 1 for ChromaticReconstruction.cons_sub_cancel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:23:55.387381+00:00
-- url     : https://prove2.me/submissions/74e192ef-e947-4c98-9bf5-33ea3a08ba35

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W P Q : Multiset ℕ} {x y : ℕ} (hP : P ≤ W) (hQ : Q ≤ W)
    (h : x ::ₘ (W - P) = y ::ₘ (W - Q)) : x ::ₘ Q = y ::ₘ P := by
  have e1 : x ::ₘ (W - P) + P = x ::ₘ W := by rw [Multiset.cons_add, tsub_add_cancel_of_le hP]
  have e2 : y ::ₘ (W - Q) + Q = y ::ₘ W := by rw [Multiset.cons_add, tsub_add_cancel_of_le hQ]
  have e : x ::ₘ W + Q = y ::ₘ W + P := by
    rw [← e1, ← e2, h, add_right_comm]
  rw [Multiset.cons_add, Multiset.cons_add, Multiset.add_comm W Q, Multiset.add_comm W P,
    ← Multiset.cons_add, ← Multiset.cons_add] at e
  exact add_right_cancel e
end ChromaticReconstruction
