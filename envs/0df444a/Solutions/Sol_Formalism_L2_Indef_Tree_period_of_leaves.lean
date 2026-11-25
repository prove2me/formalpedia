-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.period_of_leaves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:46.825366+00:00
-- url     : https://prove2.me/submissions/9a8d800b-10c4-474d-8ef8-62cf029d26ca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_DimensionVariation_periodValue
import Theorems.Thm_Formalism_ExtensionFiltration_periodBound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (P : SlopeBoundParameters) (hKL : LeafKL P) (hCN : LeafCN P) (hFE : LeafFE P) (hDi : LeafDiff P)
    (hNo : LeafNorm P) (hv : 0 < P.v) (hrd : 2 * P.v = P.rd) (h4 : 4 ≤ P.rd) (hLc : |P.Lc| ≤ P.L)
    (hx : 1 ≤ P.x) :
    P.logOm = Real.eulerMascheroniConstant + Real.log (Real.pi / P.v) - P.Lc ∧ |P.logOm| ≤ P.La := by
  have hd : 0 < P.dK := by
    unfold SlopeBoundParameters.dK; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P.dN)
  have hval := (Formalism.DimensionVariation.periodValue P.dK P.v P.rd P.A1 P.Z P.L0 P.Lc P.logOmK P.logOm hd hv hrd.symm
    hKL hCN hFE hDi hNo).2.2
  exact ⟨hval, Formalism.ExtensionFiltration.periodBound P.logOm P.v P.rd P.Lc P.L P.x P.b P.a hval hrd h4 hLc hx rfl rfl⟩
end Formalism.L2.Indef.Tree
