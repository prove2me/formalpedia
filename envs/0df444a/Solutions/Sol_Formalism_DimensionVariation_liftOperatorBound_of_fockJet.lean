-- Prove2me | solution 1 for Formalism.DimensionVariation.liftOperatorBound_of_fockJet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:11.293241+00:00
-- url     : https://prove2.me/submissions/03e6d6ac-5d6d-448c-b4c1-d934bf006d40

import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_Assembly
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_ClassSchur
import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementD
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementE
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Theorems.Thm_Formalism_DimensionVariation_blockBound_of_fockJet
import Theorems.Thm_Formalism_DimensionVariation_weightedSchurBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (hF : FockJet) : LiftOperatorBound := by
  intro Pl ι Cl Cl' _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S γ γ' ε hν hn hs hs2 hTh hc hS hRc hRs
    hOm hlam hγ hγ' hε
  have hB := blockBound_of_fockJet hF
  unfold liftNormSq
  apply csInf_le ⟨0, fun X hX => hX.1⟩
  refine ⟨?_, fun fn => ?_⟩
  · exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg S) (Finset.prod_nonneg fun τ _ =>
      mul_nonneg (pow_nonneg (inv_nonneg.2 (hOm τ).le) _) (by positivity)))
  · exact weightedSchurBound Cl Cl' A B γ γ' ε (fun L L' => liftBlock (c L L') Rc lam) _ fn hγ hγ' hε
      (fun L L' => hB Pl ι (A →L[ℂ] B) r ν n s (Th L L') (c L L') Rc lam Om S hν hn hs hs2 (hTh L L')
        (hc L L') (hS L L') hRc hRs hOm hlam)
end Formalism.DimensionVariation
