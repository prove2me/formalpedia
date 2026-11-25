-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.incl_z_twist_by_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:56:54.828266+00:00
-- url     : https://prove2.me/submissions/00d3b264-1822-4a82-a3b5-9c6e86acf6e3

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Theorems.Thm_Formalism_CohomologicalDescent_LA_incl_z_shift_by_one_iff
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : InclZTwist := by
  unfold InclZTwist
  intro r ν c l e hν hl
  induction c with
  | zero => simp
  | succ c ih =>
    have hνc : Antitone (fun a => ν a + c) := fun a b hab => Nat.add_le_add_right (hν hab) c
    have he : (fun a => ν a + (c + 1)) = (fun a => (fun a => ν a + c) a + 1) := by
      funext a
      show ν a + (c + 1) = ν a + c + 1
      omega
    rw [he]
    exact (incl_z_shift_by_one_iff r (fun a => ν a + c) l e hνc).trans ih
end Formalism.CohomologicalDescent.LA
