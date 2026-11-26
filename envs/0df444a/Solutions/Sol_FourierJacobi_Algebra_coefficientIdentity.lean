-- Prove2me | solution 1 for FourierJacobi.Algebra.coefficientIdentity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:20:09.16081+00:00
-- url     : https://prove2.me/submissions/ae866492-2f38-4652-9e81-73cb16f1cf7e

import Definitions.Def_FourierJacobi_Algebra_WeylCoefficient10
import Definitions.Def_FourierJacobi_Algebra_WeylSum
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity0
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity1
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity10
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity2
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity3
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity4
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity5
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity6
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity7
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity8
import Theorems.Thm_FourierJacobi_Algebra_coefficientIdentity9


set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Algebra
variable {K : Type*} [Field K]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace FourierJacobi.Algebra
theorem _root_.solution (t a b : K) (k : Fin 11) :
    (∑ i : Fin 8, allWeylCoefficients t a b i k) =
      if k = 5 then weylTargetCoefficient t a b else 0 := by
  fin_cases k
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity0 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity1 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity2 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity3 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity4 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity5 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity6 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity7 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity8 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity9 t a b
  · simpa only [allWeylCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val, Fin.reduceFinMk, Fin.val_zero, Fin.val_succ, wcCoeffs0, wcCoeffs1, wcCoeffs2, wcCoeffs3, wcCoeffs4, wcCoeffs5, wcCoeffs6, wcCoeffs7, ite_true, ite_false, Fin.reduceEq, add_zero, add_assoc] using coefficientIdentity10 t a b
end FourierJacobi.Algebra
