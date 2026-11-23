-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_step_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:27.929739+00:00
-- url     : https://prove2.me/submissions/61f250ab-ed37-46be-8359-c8ead453f403

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
theorem _root_.solution (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
      rowDiv R a a k (Dop R a a f) - (k : R) • rowDiv R a a k f := by
  have h := sw_deriv R a a f
  rw [if_pos rfl] at h
  unfold rowDiv
  rw [← h, add_mul, one_mul, Polynomial.coeff_add]
  cases k with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, add_zero, Polynomial.coeff_derivative]
    simp [MvPolynomial.smul_eq_C_mul, mul_comm]
  | succ k =>
    rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    simp only [MvPolynomial.smul_eq_C_mul]
    push_cast
    simp only [map_add, map_natCast, map_one]
    ring
end Formalism.L2.G.Model
