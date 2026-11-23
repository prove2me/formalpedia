-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_rowDiv_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:11.085808+00:00
-- url     : https://prove2.me/submissions/5fbdc235-855b-4c6f-81f9-4777eac62473

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
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
theorem _root_.solution (a b : Fin r) (g : MvPolynomial (Fin r × Fin n) R) : rowDiv R a b 0 g = g := by
  unfold rowDiv
  induction g using MvPolynomial.induction_on with
  | C c => rw [sw_rowGen_C, Polynomial.coeff_C_zero]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.mul_coeff_zero, hp, sw_rowGen_X]
    split_ifs <;> simp
end Formalism.L2.G.Model
