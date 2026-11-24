-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_eval_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:36.920727+00:00
-- url     : https://prove2.me/submissions/c4cbf74f-3dd2-4b8e-9769-aca1e473d02b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (a b : Fin n) (t : ℚ) (f : MvPolynomial (Fin n × Fin n) ℚ) :
    (rowGen ℚ a b f).eval (C t) = rowAct ℚ (1 + Matrix.single b a t) f := by
  have h : ((Polynomial.aeval (R := MvPolynomial (Fin n × Fin n) ℚ) (C t : MvPolynomial (Fin n × Fin n) ℚ)).restrictScalars
      ℚ).comp (rowGen ℚ a b) = rowAct ℚ (1 + Matrix.single b a t) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply, rowGen_X, rowAct, aeval_X]
    simp only [AlgHom.restrictScalars_apply, map_add, Polynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
      Matrix.add_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply, Matrix.single_apply]
    congr 1
    · simp
    · split_ifs with hv
      · simp only [hv, true_and, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_self,
          RingHom.id_apply]
        rw [Finset.sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
        simp
      · simp [Ne.symm hv]
  have := congrArg (fun φ => φ f) h
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using this
end Formalism.InvariantFactorPaths.ColumnFamilies
