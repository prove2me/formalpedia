-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.third_zeta_arithmetic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:44.388394+00:00
-- url     : https://prove2.me/submissions/a59462cb-1e9b-48bf-abb8-9e752e0b65d8

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
theorem _root_.solution : InterlacingLogSquareBound := by
  intro n lam nu T c rho hI hT hc hcb hr hrb
  have hT0 : 0 < T := by linarith
  have hz : 0 < T ^ (-(degZ lam nu)) := zpow_pos hT0 _
  have hd : 0 < weylDim lam := (mul_pos_iff_of_pos_left hz).1 (lt_of_lt_of_le (by positivity) hrb)
  have hmin : ∀ i, 0 ≤ min (len lam i) (B0 lam nu) := by
    intro i
    refine le_min ?_ ?_
    · unfold len; have := hI.1 (Fin.castSucc_le_succ i); linarith
    · unfold B0; exact Finset.sum_nonneg fun j _ => by have := (hI.2 j).1; linarith
  have hsum : ((∑ i, (min (len lam i) (B0 lam nu)).toNat : ℕ) : ℝ)
      = ∑ i, ((min (len lam i) (B0 lam nu) : ℤ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Int.toNat_of_nonneg (hmin i)
    exact_mod_cast this
  have e1 : Real.log ((c * rho) ^ 2) = 2 * Real.log |c| + Real.log (rho ^ 2) := by
    rw [mul_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_abs]; push_cast; ring
  have e2 : Real.log |c| ≤ ((n * ∑ i, (min (len lam i) (B0 lam nu)).toNat : ℕ) : ℝ) * Real.log (Wnum lam : ℝ) := by
    have := Real.log_le_log (abs_pos.2 hc) hcb
    rwa [Real.log_pow] at this
  have e3 : Real.log (rho ^ 2) ≤ -(degZ lam nu : ℝ) * Real.log T + Real.log (weylDim lam) := by
    have := Real.log_le_log (by positivity) hrb
    rw [Real.log_mul hz.ne' hd.ne', Real.log_zpow] at this
    push_cast at this; exact this
  rw [Nat.cast_mul, hsum] at e2
  unfold MeanSquareTwistBound
  rw [e1]; nlinarith
end Formalism.HermitianLattices.LatticeEstimates
