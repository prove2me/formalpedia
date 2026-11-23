-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.frame_jet_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:41.402922+00:00
-- url     : https://prove2.me/submissions/b3a64b03-c4bb-4207-8786-90ecbc4cd52f

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_eval__jetPairPoly_5113198bcf9c
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_ringMap_minorProd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_thetaZ
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_theta_subst
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_frameM_idM
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_frameM_row
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jet_pair_linearity


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : FrameJetEval := by
  intro F K _ _ _ _ φ d N0 N1 _ g U ε be hg hbe colN p hp I x
  unfold frameJet
  have hbe' : MvPowerSeries.constantCoeff (MvPowerSeries.map φ be) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hbe, map_zero]
  rw [eval₂_jetPairPoly, map_thetaZ φ g U ε be hg hbe,
    theta_subst idM (frameM x) (fun i y => frameM x y i) (fun z i => frameM_idM x z i) _ _ _ hbe',
    jet_pair_linearity K]
  unfold thetaZ
  congr 1
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ringMap_minorProd]
  symm
  refine (ringMap_minorProd (MvPolynomial.aeval _).toRingHom _ _ _ _).trans ?_
  congr 1
  funext i b
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
  rw [sum_frameM_row]
  simp [MvPolynomial.map_C, MvPolynomial.map_X]
end Formalism.DworkPowerSeriesWeights
