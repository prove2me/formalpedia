-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBF.blockMulVec_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:36:10.492018+00:00
-- url     : https://prove2.me/submissions/e37a5a23-128a-43e9-858f-4d43f5c4e9a3

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
theorem _root_.solution (M : SlopeTestRemainingChoices S (Q.Pr V)) (X Y : Ix S → V) : actP M (X + Y) = actP M X + actP M Y := by
  funext a
  simp only [actP, Pi.add_apply, map_add, Finset.sum_add_distrib]
end Formalism.FourierDecayAlt.P.PBF
