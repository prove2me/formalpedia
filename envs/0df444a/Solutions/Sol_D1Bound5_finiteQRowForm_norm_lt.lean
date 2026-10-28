-- Prove2me | solution 1 for D1Bound5.finiteQRowForm_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:48:31.592698+00:00
-- url     : https://prove2.me/submissions/00045b96-4f53-4cd2-9fb1-1e1cad0c663d

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteQMatrix_Definitions
import Definitions.Def_D1Bound5_FiniteQRowBound_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_finiteQDividedMatrix_root_height
import Theorems.Thm_D1Bound5_finiteQRowResidual_norm_lt
import Theorems.Thm_D1Bound5_finite_row_root_transfer_norm_lt

section
namespace D1Bound5







theorem finiteQRowForm_eq_root_sum
    (a b s t c z rA rB rS rT : ℂ) (i : Fin 5) :
    finiteQRowForm a b s t c z rA rB rS rT i =
      finiteQDividedMatrix a b s t c i 0*z +
        ∑ j : Fin 4, finiteQDividedMatrix a b s t c i j.succ * ![rA,rB,rS,rT] j := by
  simp [finiteQRowForm, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]

/-- The actual Q row has coefficient54 after the signed-root transfer.
Only the root error estimates are intermediate hypotheses here; its height
and residual estimates are derived from the constructed family. -/
theorem _root_.solution
    (a b s t c z rA rB rS rT : ℂ) (A T : ℝ) (hA : 0 < A) (hz : z ≠ 0)
    (hlower : ∀ j, A ≤ ‖finiteQAnchors a b s t j‖)
    (hupper : ∀ j, ‖finiteQAnchors a b s t j‖ ≤ T)
    (hAC : 1000 ≤ A*‖c‖)
    (herr : ∀ j : Fin 4,
      ‖((1+1/(finiteQAnchors a b s t j*c))^(1/2 : ℂ)) -
        ![rA,rB,rS,rT] j/(finiteQAnchors a b s t j*z)‖ ≤
          (3/2 : ℝ)*‖c‖/(‖finiteQAnchors a b s t j‖*‖z‖^2)) (i : Fin 5) :
    ‖finiteQRowForm a b s t c z rA rB rS rT i‖ <
      54*T^3*‖c‖^2/‖z‖+3*T*‖z‖/(2*A^2*‖c‖^4) := by
  have hT : 0 < T := (hA.trans_le (hlower 0)).trans_le (hupper 0)
  have hAT : A ≤ T := (hlower 0).trans (hupper 0)
  have hTC : 1 ≤ T*‖c‖ := by
    have hm := mul_le_mul_of_nonneg_right hAT (norm_nonneg c)
    linarith
  have ha (j : Fin 4) : finiteQAnchors a b s t j ≠ 0 :=
    norm_pos_iff.mp (hA.trans_le (hlower j))
  have hheight := finiteQDividedMatrix_root_height a b s t c T ‖c‖ hT.le
    (norm_nonneg c) (hupper 0) (hupper 1) (hupper 2) (hupper 3) le_rfl hTC i
  have hres := finiteQRowResidual_norm_lt a b s t c A T hA hlower hupper hAC i
  have h := finite_row_root_transfer_norm_lt
    (finiteQDividedMatrix a b s t c i 0) z (finiteQAnchors a b s t)
    (fun j => finiteQDividedMatrix a b s t c i j.succ)
    (fun j => (1+1/(finiteQAnchors a b s t j*c))^(1/2 : ℂ))
    ![rA,rB,rS,rT] ha hz ((3/2 : ℝ)*‖c‖) (36*T^3*‖c‖)
    (3*T/(2*A^2*‖c‖^4)) (by positivity) herr hheight hres
  rw [finiteQRowForm_eq_root_sum]
  convert h using 1 <;> ring

end D1Bound5
end
