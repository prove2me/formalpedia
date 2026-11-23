-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:19.698804+00:00
-- url     : https://prove2.me/submissions/4a922542-d68f-4830-a15d-595c93d02325

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Theorems.Thm_Formalism_L2_G_Model_Dop_X
import Theorems.Thm_Formalism_L2_G_Model_sw_rowGen_X
import Theorems.Thm_Formalism_L2_G_Model_sw_rowGen_C
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
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
variable (R : Type) [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model
theorem _root_.solution (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    (1 + if a = b then Polynomial.X else 0) * Polynomial.derivative (rowGen R a b f) =
      rowGen R a b (Dop R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [sw_rowGen_C, Polynomial.derivative_C, mul_zero, MvPolynomial.derivation_C, map_zero]
  | add p q hp hq =>
    rw [map_add, map_add, map_add, map_add, mul_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.derivative_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add,
      map_mul, map_mul, ← hp, Dop_X, sw_rowGen_X]
    by_cases h1 : v.1 = b <;> by_cases h2 : a = b <;>
      simp only [h1, h2, if_true, if_false, sw_rowGen_X, map_zero, mul_zero, zero_mul, add_zero,
        Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
        Polynomial.derivative_X, zero_add, one_mul, mul_one, Polynomial.derivative_zero] <;> ring
end Formalism.L2.G.Model
