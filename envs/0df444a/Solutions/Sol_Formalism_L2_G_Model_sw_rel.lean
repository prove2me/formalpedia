-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:00:50.486801+00:00
-- url     : https://prove2.me/submissions/52630c63-2afc-4dca-a395-4923bcb71424

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Theorems.Thm_Formalism_L2_G_Model_Dop_X
import Theorems.Thm_Formalism_L2_G_Model_DL_apply
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
theorem _root_.solution (a b c d : Fin r) :
    DL R (n := n) a b * DL R c d - DL R c d * DL R a b =
      (if b = c then DL R a d else 0) - (if d = a then DL R c b else 0) := by
  have hder : ⁅Dop R (n := n) a b, Dop R (n := n) c d⁆ =
      (if b = c then Dop R (n := n) a d else 0) - (if d = a then Dop R (n := n) c b else 0) := by
    apply MvPolynomial.derivation_ext
    intro v
    rw [Derivation.commutator_apply, Dop_X, Dop_X, apply_ite (Dop R (n := n) a b),
      apply_ite (Dop R (n := n) c d), map_zero, map_zero, Dop_X, Dop_X]
    by_cases h1 : v.1 = d <;> by_cases h2 : v.1 = b <;> by_cases h3 : b = c <;>
      by_cases h4 : d = a <;> simp [h1, h2, h3, h4, Dop_X, @eq_comm _ c b, @eq_comm _ a d]
  refine LinearMap.ext fun f => ?_
  have h := congrArg (fun D : Derivation R _ _ => D f) hder
  simp only [Derivation.commutator_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, DL_apply]
  rw [h]
  split_ifs <;> simp [DL_apply]
end Formalism.L2.G.Model
