-- Prove2me | solution 1 for BookProof.DirectSumEsa.dsOp_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:49:44.279972+00:00
-- url     : https://prove2.me/submissions/de37a97d-cd84-42ed-bd9e-02d9eccf3848

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.dsOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution (H : ∀ i, D i →ₗ[ℂ] G i) (hsym : ∀ i, SymmetricOn (D i) (H i)) :
    SymmetricOn (dsCore D) (dsOp H) := by

  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  exact hsym i ⟨(x : lp G 2) i, x.2.2 i⟩ ⟨(y : lp G 2) i, y.2.2 i⟩
