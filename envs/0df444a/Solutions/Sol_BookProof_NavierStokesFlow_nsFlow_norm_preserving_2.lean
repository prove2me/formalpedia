-- Prove2me | solution 2 for BookProof.NavierStokesFlow.nsFlow_norm_preserving
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:58:30.673413+00:00
-- url     : https://prove2.me/submissions/d23ab91f-8bf6-45b9-8077-6cd14aaa46ac

import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.ChapterContinuityUnitary BookProof.NavierStokesFlow Matrix in
theorem nsNP3889_adv_herm {n : ℕ} (d : NSTruncation n) (i : Fin 3) :
    (nsAdvection d i)ᴴ = nsAdvection d i := by
  unfold nsAdvection nsVelocity nsGradVelocity nsLapVelocity
  rw [conjTranspose_sub, conjTranspose_sum, conjTranspose_smul, d.u_herm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_mul, d.u_herm, d.u_herm, d.u_comm]
  · simp [Complex.conj_ofReal]

open BookProof.ChapterContinuityUnitary BookProof.NavierStokesFlow Matrix in
theorem nsNP3889_ham_herm {n : ℕ} (d : NSTruncation n) :
    (nsHamiltonian d)ᴴ = nsHamiltonian d := by
  unfold nsHamiltonian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, d.mom_herm,
    nsNP3889_adv_herm, add_comm]

open BookProof.ChapterContinuityUnitary BookProof.NavierStokesFlow Matrix in
theorem solution {n : ℕ} (d : NSTruncation n) (t : ℝ) (psi : Fin n → ℂ) :
    ∑ a, ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2 = ∑ a, ‖psi a‖ ^ 2 := by
  exact unitary_preserves_normSq _ (exp_smul_I_unitary _ (nsNP3889_ham_herm d) t) psi
