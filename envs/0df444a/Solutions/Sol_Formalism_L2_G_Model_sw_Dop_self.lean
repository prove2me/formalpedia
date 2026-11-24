-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_Dop_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:33.94504+00:00
-- url     : https://prove2.me/submissions/44f5c987-f34d-4dd8-83bc-b3e65f7733cb

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_G_Model_sw_rowDiv_zero
import Theorems.Thm_Formalism_L2_G_Model_sw_step_eq
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
namespace Formalism.L2.G.Model
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    Dop R a a f = rowDiv R a a 1 f := by
  have h := sw_step_eq R a 0 f
  simp only [zero_add, Nat.cast_one, one_smul, Nat.cast_zero, zero_smul, sub_zero, sw_rowDiv_zero] at h
  exact h.symm
end Formalism.L2.G.Model
