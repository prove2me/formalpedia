-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.cc_vlet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:49.510042+00:00
-- url     : https://prove2.me/submissions/ae554a6c-a4bf-4435-b16c-2543dd83e0a8

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_vlet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution {σ τ : Site A} (h : SitesCommute σ τ) (l : Letter K S) :
    CC τ (vlet σ l : SlopeTestRemainingChoices S A) := fun x hx => io_comm_vlet σ x (fun y hy => h y hy x hx) l
end Formalism.FourierDecayAlt.P.Wd8
