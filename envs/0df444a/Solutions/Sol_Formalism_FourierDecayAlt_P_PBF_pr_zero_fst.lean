-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBF.pr_zero_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:13.938963+00:00
-- url     : https://prove2.me/submissions/fe76188d-fa2e-4ca8-8f78-84004f7ed251

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
theorem _root_.solution : (0 : Q.Pr V).1 = 0 := rfl
end Formalism.FourierDecayAlt.P.PBF
