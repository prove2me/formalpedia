-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.map_invP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:02:32.586956+00:00
-- url     : https://prove2.me/submissions/4c2d34a6-32cf-46be-9f10-9f1919a15a5f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_map_invM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarW
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_invM_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_radical_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_weyl_subgroup_closed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    D.μSS.map invP = D.μSS := by
  have hm := B2x1.invM_meas (k := k) (r := r)
  have hW := map_invM_eq (weyl_subgroup_closed k r D.z) D.haarW
  have hN := map_invM_eq (unipotent_radical_closed k r) D.haarN
  have hW' := map_invM_eq (weyl_subgroup_closed k r D.z') D.haarW'
  show ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)).map
      (Prod.map (Prod.map B2.invM B2.invM) (Prod.map B2.invM B2.invM)) = (D.μW.prod D.μN).prod (D.μW'.prod D.μN)
  rw [← Measure.map_prod_map _ _ (hm.prodMap hm) (hm.prodMap hm), ← Measure.map_prod_map _ _ hm hm,
    ← Measure.map_prod_map _ _ hm hm, hW, hN, hW']
end Formalism.FourierDecayAlt.P.S3dx4
