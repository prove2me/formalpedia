-- Prove2me | solution 1 for BookProof.NavierStokesFlow.nsFlow_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T11:43:57.185534+00:00
-- url     : https://prove2.me/submissions/1eaa2e16-62af-403d-b063-c9a0600f02e6

import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.ChapterContinuityUnitary BookProof.NavierStokesFlow Matrix in
theorem nsFlow628e_adv_herm {n : ℕ} (d : NSTruncation n) (i : Fin 3) :
    (nsAdvection d i)ᴴ = nsAdvection d i := by
  unfold nsAdvection nsVelocity nsGradVelocity nsLapVelocity
  rw [conjTranspose_sub, conjTranspose_sum, conjTranspose_smul, d.u_herm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_mul, d.u_herm, d.u_herm, d.u_comm]
  · simp [Complex.conj_ofReal]

open BookProof.ChapterContinuityUnitary BookProof.NavierStokesFlow Matrix in
theorem nsFlow628e_ham_herm {n : ℕ} (d : NSTruncation n) :
    (nsHamiltonian d)ᴴ = nsHamiltonian d := by
  unfold nsHamiltonian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, d.mom_herm,
    nsFlow628e_adv_herm, add_comm]

open BookProof.ChapterContinuityUnitary BookProof.NavierStokesFlow Matrix in
theorem solution {n : ℕ} (d : NSTruncation n) (t : ℝ) : (nsFlowUnitary d t)ᴴ * nsFlowUnitary d t = 1 := by
  exact exp_smul_I_unitary _ (nsFlow628e_ham_herm d) t
