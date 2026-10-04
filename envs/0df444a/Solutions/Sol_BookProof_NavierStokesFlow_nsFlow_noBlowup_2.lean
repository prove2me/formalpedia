-- Prove2me | solution 2 for BookProof.NavierStokesFlow.nsFlow_noBlowup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:11:02.913045+00:00
-- url     : https://prove2.me/submissions/6dd31d4e-0788-4bde-ba40-4ef479d8f21d

import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

open BookProof.NavierStokesFlow in
theorem nsFB036_herm {n : ℕ} (d : NSTruncation n) :
    (nsHamiltonian d)ᴴ = nsHamiltonian d := by
  have hu : ∀ k, (d.u k)ᴴ = d.u k := d.u_herm
  have hA : ∀ i, (nsAdvection d i)ᴴ = nsAdvection d i := by
    intro i
    simp only [nsAdvection, nsVelocity, nsGradVelocity, nsLapVelocity,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_smul, hu, Complex.star_def, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact d.u_comm _ _
  simp only [nsHamiltonian, Matrix.conjTranspose_sum, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, hA, d.mom_herm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm]

theorem nsFB036_sumsq {n : ℕ} (v : Fin n → ℂ) :
    ((∑ a, ‖v a‖ ^ 2 : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

open BookProof.NavierStokesFlow in
theorem nsFB036_unitary {n : ℕ} (d : NSTruncation n) (t : ℝ) :
    (nsFlowUnitary d t)ᴴ * nsFlowUnitary d t = 1 := by
  unfold nsFlowUnitary
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, nsFB036_herm,
    ← Matrix.exp_add_of_commute]
  · have : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      simp
    rw [this, neg_smul, neg_add_cancel, NormedSpace.exp_zero]
  · have : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      simp
    rw [this, neg_smul]
    exact (Commute.refl _).neg_left

open BookProof.NavierStokesFlow in
theorem nsFB036_norm {n : ℕ} (d : NSTruncation n) (t : ℝ) (psi : Fin n → ℂ) :
    ∑ a, ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2 = ∑ a, ‖psi a‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [nsFB036_sumsq, nsFB036_sumsq, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, nsFB036_unitary, Matrix.one_mulVec]

open BookProof.NavierStokesFlow Matrix in
theorem solution {n : ℕ} (d : NSTruncation n) (t : ℝ) (psi : Fin n → ℂ) (k : Fin n) :
    ‖(nsFlowUnitary d t *ᵥ psi) k‖ ^ 2 ≤ ∑ a, ‖psi a‖ ^ 2 := by
  rw [← nsFB036_norm d t psi]
  exact Finset.single_le_sum (f := fun a => ‖(nsFlowUnitary d t *ᵥ psi) a‖ ^ 2)
    (fun a _ => by positivity) (Finset.mem_univ k)
