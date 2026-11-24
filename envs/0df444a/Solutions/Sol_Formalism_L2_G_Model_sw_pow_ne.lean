-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_pow_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:00:49.494016+00:00
-- url     : https://prove2.me/submissions/e9231de0-3e8f-4e06-96d7-d36d96a1c8ac

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Theorems.Thm_Formalism_L2_G_Model_DL_apply
import Theorems.Thm_Formalism_L2_G_Model_sw_rowDiv_zero
import Theorems.Thm_Formalism_L2_G_Model_sw_step_ne
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
    ((k.factorial : ℕ) : R) • rowDiv R a b k f = (DL R a b ^ k) f := by
  induction k generalizing f with
  | zero => simp [sw_rowDiv_zero]
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, mul_comm, mul_smul, sw_step_ne R a b hab k f, ih,
      pow_succ, Module.End.mul_apply, DL_apply]
end Formalism.L2.G.Model
