-- Prove2me | solution 1 for ChromaticReconstruction.weightMS_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:25:11.473283+00:00
-- url     : https://prove2.me/submissions/d31b2d8e-58db-4b76-9ecd-8c5a48f6dae0

import Definitions.Def_RequestProject_Recovery
import Definitions.Def_RequestProject_RecoveryThm

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
namespace ChromaticReconstruction
theorem _root_.solution (hm : ∀ i, 1 ≤ m i) : ∀ x ∈ weightMS m, 2 ≤ x := by
  intro x hx
  unfold weightMS at hx
  obtain ⟨j, _, rfl⟩ := Multiset.mem_map.1 hx
  have := hm j
  omega
end ChromaticReconstruction
