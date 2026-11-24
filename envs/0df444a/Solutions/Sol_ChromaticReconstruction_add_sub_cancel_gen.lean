-- Prove2me | solution 1 for ChromaticReconstruction.add_sub_cancel_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:23:59.682746+00:00
-- url     : https://prove2.me/submissions/969d2e18-9481-4486-ae64-926a61e7eb0a

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W P Q A B : Multiset ℕ} (hP : P ≤ W) (hQ : Q ≤ W)
    (h : A + (W - P) = B + (W - Q)) : A + Q = B + P := by
  have e : A + Q + W = B + P + W := by
    calc A + Q + W = A + (W - P) + P + Q := by
          rw [add_assoc A (W - P), tsub_add_cancel_of_le hP]; abel
      _ = B + (W - Q) + Q + P := by rw [h, add_right_comm]
      _ = B + P + W := by rw [add_assoc B (W - Q), tsub_add_cancel_of_le hQ]; abel
  exact add_right_cancel e
end ChromaticReconstruction
