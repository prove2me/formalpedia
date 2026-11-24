-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:00:25.864801+00:00
-- url     : https://prove2.me/submissions/ad49a723-6eb1-429d-941c-4a2445e6001b

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Theorems.Thm_Formalism_L2_G_Model_DL_apply
import Theorems.Thm_Formalism_L2_G_Model_sw_rowDiv_zero
import Theorems.Thm_Formalism_L2_G_Model_sw_step_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
    ((k.factorial : ℕ) : R) • rowDiv R a a k f =
      (((List.range k).map fun j : ℕ => DL R (n := n) a a -
        (j : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))).prod) f := by
  induction k generalizing f with
  | zero => simp [sw_rowDiv_zero]
  | succ k ih =>
    have step : ((k + 1 : ℕ) : R) • rowDiv R a a (k + 1) f =
        rowDiv R a a k ((DL R (n := n) a a - (k : R) • (1 : Module.End R (MvPolynomial (Fin r × Fin n) R))) f) := by
      rw [sw_step_eq R a k f, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, DL_apply,
        sub_eq_add_neg ((Dop R a a) f), rowDiv_add, ← neg_smul, rowDiv_smul, neg_smul, sub_eq_add_neg]
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, mul_smul, step, ih, List.range_succ,
      List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, Module.End.mul_apply]
end Formalism.L2.G.Model
