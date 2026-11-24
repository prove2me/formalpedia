-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FreeActionExpansion.comm_ins_uinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:20:57.74745+00:00
-- url     : https://prove2.me/submissions/564fa1cb-340d-4de2-84d0-72a2635ec40d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionUpdateSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeActionExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_comm_io_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_FreeActionExpansion_uinv_alg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FreeActionExpansion
open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion
theorem _root_.solution {a : S} {C : SlopeTestRemainingChoices S A} (hC : FreeOf a C) (s : ℂ) :
    Commute C (ins a (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s))) := by
  refine Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ C hC fun i j => ?_
  obtain ⟨c, hc⟩ := uinv_alg (A := A) s i j
  simp only [lift0, Matrix.map_apply, hc]
  exact comm_io_alg C c
end Formalism.FourierDecayAlt.P.FreeActionExpansion
