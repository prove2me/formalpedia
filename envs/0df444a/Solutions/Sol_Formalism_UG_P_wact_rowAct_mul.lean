-- Prove2me | solution 1 for Formalism.UG.P.wact_rowAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:40:55.316001+00:00
-- url     : https://prove2.me/submissions/bc18b401-a803-4e81-938e-b4281b2d907d

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_DualWeylModuleStable
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
open MvPolynomial
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution (R : Type) [CommRing R] (r n : ℕ) (A B : Matrix (Fin r) (Fin r) R) :
    Formalism.GradedWeylDivisibility.rowAct R (n := n) (A * B) = (Formalism.GradedWeylDivisibility.rowAct R (n := n) B).comp (Formalism.GradedWeylDivisibility.rowAct R A) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  simp only [Formalism.GradedWeylDivisibility.rowAct, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  first
  | exact Finset.sum_comm
  | (rw [Finset.sum_comm])
end Formalism.UG.P
