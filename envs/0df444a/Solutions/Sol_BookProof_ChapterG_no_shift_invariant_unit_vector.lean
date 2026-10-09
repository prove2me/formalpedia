-- Prove2me | solution 1 for BookProof.ChapterG.no_shift_invariant_unit_vector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:18:06.450265+00:00
-- url     : https://prove2.me/submissions/dac9c5ab-96ee-490d-9b8e-e75016145ed2

-- Generated from ChapterG.lean — solution of BookProof.ChapterG.no_shift_invariant_unit_vector
import Mathlib
import Definitions.Def_ChapterG
import Theorems.Thm_BookProof_ChapterG_shift_invariant_l2_eq_zero
open BookProof.ChapterG



open scoped ComplexConjugate InnerProductSpace Matrix

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ Ψ : lp (fun _ : ℤ => ℂ) 2, ‖Ψ‖ = 1 ∧ ∀ k, Ψ (k + 1) = Ψ k := by

  rintro ⟨Ψ, hnorm, hinv⟩
  have h0 := shift_invariant_l2_eq_zero Ψ hinv
  rw [h0] at hnorm
  simp at hnorm
