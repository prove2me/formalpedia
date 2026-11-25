-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.scaleTies_some_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:15.935265+00:00
-- url     : https://prove2.me/submissions/ec91cd65-8342-485d-9fcd-bbc9f923a47f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι
namespace Formalism.L2.Indef.Tree
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} (Zs : IndefScale Bs)
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) (hT : ScaleTies Zs P F) (hm : 2 ≤ P.m) :
    ∃ j, (F j).q' ≠ 0 := by
  obtain ⟨-, -, hcard, -, -, hinj, -⟩ := hT
  have h2 : 1 < Fintype.card Bs.J := by
    have : (2 : ℝ) ≤ Fintype.card Bs.J := by rw [hcard]; exact hm
    exact_mod_cast (show (1 : ℝ) < Fintype.card Bs.J by linarith)
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card h2
  by_contra h
  simp only [ne_eq, not_exists, not_not] at h
  exact hab (hinj (show (F a).q' = (F b).q' by rw [h a, h b]))
end Formalism.L2.Indef.Tree
