-- Prove2me | solution 1 for Formalism.UG.P.wlocal_rowAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:42.327036+00:00
-- url     : https://prove2.me/submissions/805f0695-a772-4a73-8ea8-2338e6752af3

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
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
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R : Type} [CommRing R]
namespace Formalism.UG.P
theorem _root_.solution {r n : ℕ} (A B : Matrix (Fin r) (Fin r) R) :
    rowAct R (n := n) (A * B) = (rowAct R B).comp (rowAct R A) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring
end Formalism.UG.P
