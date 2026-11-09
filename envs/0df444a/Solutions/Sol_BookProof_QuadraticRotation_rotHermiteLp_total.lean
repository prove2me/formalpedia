-- Prove2me | solution 1 for BookProof.QuadraticRotation.rotHermiteLp_total
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T07:06:55.518398+00:00
-- url     : https://prove2.me/submissions/de7d2687-3c16-4dc7-aaa9-958445150a01

-- Generated from ChapterQuadraticRotationEsa.lean — solution of BookProof.QuadraticRotation.rotHermiteLp_total
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Theorems.Thm_BookProof_QuadraticRotation_span_rotHermiteLp
import Theorems.Thm_BookProof_QuadraticRotation_eq_zero_of_inner_core
open BookProof.QuadraticRotation




open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (w : L2d d)
    (h : ∀ a, (inner ℂ (rotHermiteLp (d := d) O a) w : ℂ) = 0) : w = 0 := by

  refine eq_zero_of_inner_core w fun u hu => ?_
  rw [← span_rotHermiteLp hO] at hu
  induction hu using Submodule.span_induction with
  | mem z hz => obtain ⟨a, rfl⟩ := hz; exact h a
  | zero => simp
  | add z z' _ _ ihz ihz' => rw [inner_add_left, ihz, ihz']; ring
  | smul r z _ ih => rw [inner_smul_left, ih]; ring
