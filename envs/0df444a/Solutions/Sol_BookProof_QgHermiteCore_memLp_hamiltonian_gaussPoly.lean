-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:37.960049+00:00
-- url     : https://prove2.me/submissions/6a469009-86d6-49a7-b3c5-4f96e5298541

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.memLp_hamiltonian_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_memLp_gaussPoly
import Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_gaussPoly_of_expBounded
import Theorems.Thm_BookProof_QgHermiteCore_deriv2_gaussPoly
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution {W : ℝ → ℝ} (hW : Continuous W) (hWb : ExpBounded W)
    (p : Polynomial ℝ) :
    MemLp (fun x : ℝ =>
        ((-deriv (deriv (gaussPoly p)) x + W x * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) := by

  have h1 : MemLp (fun x : ℝ =>
      ((-gaussPoly (gaussPolyDeriv (gaussPolyDeriv p)) x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
    have hneg := (memLp_gaussPoly (gaussPolyDeriv (gaussPolyDeriv p))).neg
    refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).mp hneg
    simp only [Pi.neg_apply, Complex.ofReal_neg]
  have h2 := memLp_mul_gaussPoly_of_expBounded hW hWb p
  have hsum := h1.add h2
  refine (memLp_congr_ae (Filter.Eventually.of_forall fun x => ?_)).mp hsum
  rw [deriv2_gaussPoly]
  simp only [Pi.add_apply]
  push_cast
  ring
