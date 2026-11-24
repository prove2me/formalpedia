-- Prove2me | solution 1 for ChromaticReconstruction.X_mul_fP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:22:10.195549+00:00
-- url     : https://prove2.me/submissions/adb453df-b058-4c52-aa18-dcdb3410b9d4

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_X_mul_mono

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (r : ℕ) (V : Multiset ℕ) :
    X r * fP V = ∑ c ∈ bigWeights V, C (((c - 1) * V.count c : ℕ) : ℚ) * mono (r ::ₘ lowerAt V c) := by
  unfold fP
  rw [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [← X_mul_mono]; ring
end ChromaticReconstruction
