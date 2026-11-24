-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_Dop_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:00:52.286813+00:00
-- url     : https://prove2.me/submissions/ad2da033-d63b-4c4e-a578-1c8d086fe7ab

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_L2_G_Model_sw_rowDiv_zero
import Theorems.Thm_Formalism_L2_G_Model_sw_step_ne
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
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r) (hab : a ≠ b)
    (f : MvPolynomial (Fin r × Fin n) R) : Dop R a b f = rowDiv R a b 1 f := by
  have h := sw_step_ne R a b hab 0 f
  simp only [zero_add, Nat.cast_one, one_smul, sw_rowDiv_zero] at h
  exact h.symm
end Formalism.L2.G.Model
