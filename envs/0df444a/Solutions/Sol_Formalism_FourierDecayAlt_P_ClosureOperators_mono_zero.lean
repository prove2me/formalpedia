-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.mono_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:33:53.616547+00:00
-- url     : https://prove2.me/submissions/1894416c-6f70-4ab4-ac53-be5c1458d8e9

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
import Theorems.Thm_Formalism_FourierDecayAlt_P_ClosureOperators_mono_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ClosureOperators
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.ClosureOperators
theorem _root_.solution : ∀ {n : ℕ} (f : Fin n → Module.End ℂ V), mono f (fun _ => 0) = 1 := by
  intro n
  induction n with
  | zero => intro f; simp [mono]
  | succ k ih =>
    intro f
    rw [mono_succ]
    simp only [pow_zero, one_mul]
    exact ih _
end Formalism.FourierDecayAlt.P.ClosureOperators
