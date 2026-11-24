-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBF.pr_one_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:55:10.3679+00:00
-- url     : https://prove2.me/submissions/6d0d248d-d10d-4549-9ef5-16ce87da2720

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.PBF
theorem _root_.solution : (1 : Q.Pr V).1 = 1 := rfl
end Formalism.FourierDecayAlt.P.PBF
