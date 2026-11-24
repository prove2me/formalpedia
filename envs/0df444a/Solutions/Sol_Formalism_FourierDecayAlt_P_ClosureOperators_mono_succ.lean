-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ClosureOperators.mono_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:14:20.368815+00:00
-- url     : https://prove2.me/submissions/fa75ce46-2fe7-4c6c-bd62-51b825eb6ce6

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ClosureOperators
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
theorem _root_.solution {n : ℕ} (f : Fin (n + 1) → Module.End ℂ V) (a : Fin (n + 1) → ℕ) :
    mono f a = f 0 ^ a 0 * mono (fun x => f x.succ) (fun x => a x.succ) := by
  simp only [mono, List.ofFn_succ, List.prod_cons]
end Formalism.FourierDecayAlt.P.ClosureOperators
