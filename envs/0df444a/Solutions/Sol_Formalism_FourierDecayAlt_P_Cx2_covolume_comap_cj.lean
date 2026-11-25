-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx2.covolume_comap_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:49.824473+00:00
-- url     : https://prove2.me/submissions/48cf6a70-f6e0-4d14-b3e5-f4a75c2ad630

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_cj_mp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {Wp Wq : InfinitePlace E → Type} [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.Cx2
theorem _root_.solution (S : HidaSetting E Wp Wq) (L : Submodule ℤ E) [DiscreteTopology (J.eLat E L 1)]
    [IsZLattice ℝ (J.eLat E L 1)] :
    ZLattice.covolume (ZLattice.comap ℝ (J.eLat E L 1) (cj S).toLinearEquiv.toLinearMap) =
      ZLattice.covolume (J.eLat E L 1) :=
  ZLattice.covolume_comap (J.eLat E L 1) volume volume (e := (cj S).toContinuousLinearEquiv) (cj_mp S)
end Formalism.FourierDecayAlt.P.Cx2
