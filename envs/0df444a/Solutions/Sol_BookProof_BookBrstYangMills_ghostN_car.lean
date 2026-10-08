-- Prove2me | solution 1 for BookProof.BookBrstYangMills.ghostN_car
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:42:58.180742+00:00
-- url     : https://prove2.me/submissions/a6a0d9a1-da58-4097-b220-5b2bc6670bc7

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.ghostN_car
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution : GhostCAR (ghostCreN (N := N)) (ghostAnnN (N := N)) := by

  constructor
  · intro a b
    refine LinearMap.ext fun x => ?_
    simp only [ghostCreN, LinearMap.add_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
      LinearMap.zero_apply, ← mul_assoc]
    rw [← add_mul, CliffordAlgebra.ι_mul_ι_add_swap]
    simp [QuadraticMap.polar]
  · intro a b
    refine LinearMap.ext fun x => ?_
    simp only [ghostAnnN, LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply]
    rw [CliffordAlgebra.contractLeft_comm, neg_add_cancel]
  · intro a b
    refine LinearMap.ext fun x => ?_
    simp only [ghostCreN, ghostAnnN, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.mulLeft_apply, CliffordAlgebra.contractLeft_ι_mul]
    by_cases h : a = b
    · subst h; simp
    · simp [h]
