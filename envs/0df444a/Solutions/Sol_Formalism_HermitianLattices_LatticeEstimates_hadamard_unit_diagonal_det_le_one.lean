-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.hadamard_unit_diagonal_det_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.600838+00:00
-- url     : https://prove2.me/submissions/0ebb3c34-b2cf-4050-966d-7a60689f0f5a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution (N : ℕ) (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.PosSemidef) (hd : ∀ c, H c c = 1) :
    H.det.re ≤ 1 := by
  have hh := hH.isHermitian
  have hdet := hh.det_eq_prod_eigenvalues
  have htr := hh.trace_eq_sum_eigenvalues
  have hnn := hH.eigenvalues_nonneg
  have htr' : ∑ i, hh.eigenvalues i = N := by
    have h1 : (H.trace) = (N : ℂ) := by simp [Matrix.trace, hd]
    rw [h1] at htr
    have h2 : ((N : ℝ) : ℂ) = ((∑ i, hh.eigenvalues i : ℝ) : ℂ) := by
      push_cast; simpa using htr
    exact_mod_cast h2.symm
  rw [hdet]
  have h3 : (∏ i, ((hh.eigenvalues i : ℝ) : ℂ)).re = ∏ i, hh.eigenvalues i := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  have h4 : (∏ i, (RCLike.ofReal (hh.eigenvalues i) : ℂ)).re = ∏ i, hh.eigenvalues i := by
    simpa using h3
  rw [h4]
  calc ∏ i, hh.eigenvalues i ≤ ∏ i, Real.exp (hh.eigenvalues i - 1) :=
        Finset.prod_le_prod (fun i _ => hnn i)
          (fun i _ => by linarith [Real.add_one_le_exp (hh.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hh.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by rw [Finset.sum_sub_distrib, htr']; simp
end Formalism.HermitianLattices.LatticeEstimates
