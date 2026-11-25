-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.scaleTies_unique_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:13:19.602547+00:00
-- url     : https://prove2.me/submissions/f6198415-4e80-425a-9f0f-12334968d4e3

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
    (P : SlopeBoundParameters) (F : Bs.J → SlopeBoundLiftData K P) (hT : ScaleTies Zs P F) (hm : 1 ≤ P.m) :
    ∃! j, (F j).q' = 0 := by
  obtain ⟨-, -, hcard, -, -, hinj, hq⟩ := hT
  have hlt : ∀ j, (F j).q' < Fintype.card Bs.J := by
    intro j
    have h1 := (hq j).1
    rw [← hcard] at h1
    exact_mod_cast (show ((F j).q' : ℝ) < (Fintype.card Bs.J : ℝ) by linarith)
  let g : Bs.J → Fin (Fintype.card Bs.J) := fun j => ⟨(F j).q', hlt j⟩
  have hg : Function.Injective g := fun a b h => hinj (show (F a).q' = (F b).q' from congrArg Fin.val h)
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hg, by simp⟩
  have hpos : 0 < Fintype.card Bs.J := by
    have : (1 : ℝ) ≤ Fintype.card Bs.J := by rw [hcard]; exact hm
    exact_mod_cast (show (0 : ℝ) < Fintype.card Bs.J by linarith)
  obtain ⟨j, hj⟩ := hbij.2 ⟨0, hpos⟩
  have hj0 : (F j).q' = 0 := congrArg Fin.val hj
  exact ⟨j, hj0, fun j' hj' => hinj (show (F j').q' = (F j).q' by rw [hj', hj0])⟩
end Formalism.L2.Indef.Tree
