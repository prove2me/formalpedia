-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_step_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:27.929277+00:00
-- url     : https://prove2.me/submissions/f3afc37d-16c7-4800-9b13-57296906da5f

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Theorems.Thm_Formalism_L2_G_Model_sw_deriv
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
theorem _root_.solution (a b : Fin r) (hab : a ≠ b) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a b (k + 1) f = rowDiv R a b k (Dop R a b f) := by
  have h := sw_deriv R a b f
  rw [if_neg hab, add_zero, one_mul] at h
  unfold rowDiv
  rw [← h, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 1
  simp
end Formalism.L2.G.Model
