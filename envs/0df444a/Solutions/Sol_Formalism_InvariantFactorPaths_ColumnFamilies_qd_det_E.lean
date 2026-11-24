-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_det_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:19.064814+00:00
-- url     : https://prove2.me/submissions/2caaeb74-c6fe-40ba-9e86-7e8cbe45fb2b

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
theorem _root_.solution (a b : Fin n) (t : ℕ) : IsUnit (1 + Matrix.single b a (t : ℚ)).det := by
  by_cases hab : b = a
  · subst hab
    have : (1 + Matrix.single b b (t : ℚ)) = Matrix.diagonal (fun i => if i = b then (1 + t : ℚ) else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        by_cases hi : i = b <;> simp [hi, Matrix.single_apply]
        intro h; exact absurd h.symm hi
      · simp [Matrix.one_apply_ne hij, Matrix.diagonal_apply_ne _ hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [this, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp only [mem_univ, if_true]
    exact isUnit_iff_ne_zero.2 (by positivity)
  · have : (1 + Matrix.single b a (t : ℚ)) = Matrix.transvection b a (t : ℚ) := rfl
    rw [this, Matrix.det_transvection_of_ne _ _ hab]
    exact isUnit_one
end Formalism.InvariantFactorPaths.ColumnFamilies
