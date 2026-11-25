-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.on_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:03:57.587906+00:00
-- url     : https://prove2.me/submissions/15cb79a1-2f97-4d19-ad7a-ed88f9d9acf2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsWeightedConditional
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditions
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ErrSum
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_UnipotentNumeric
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef.Tree
theorem _root_.solution (c : OnConst) : ∃ CE : ℝ, CE = c.CE ∧
    ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [StarRing K₁] (Bs : DefBase K₁) (Df : DefSide Bs) (R : IndefRows Df),
      Df.WF → ∀ (N : IndefNum Bs) (P : Type) [Group P] [Finite P] (O : OnObj R.toIndefData P c),
      LeafMackey O → LeafSup O → LeafProj O → TieCoord O → LeafSpan O → LeafLemmaS O → LatticeIndexBoundAtPairs O → LeafData O →
      LeafRankJ O → LeafIdentity O → LeafTW2 O → LeafTW1 O → LeafShareI O → LeafIndexU O → LeafBadShare O →
      LeafUnip O → LeafDepthGood N O → LeafDepthRam N O → LeafDepth2 N O → LeafDepthLevel N O → LeafPage O →
      LeafSizes O → LeafX O → LeafBad O → LeafJSum O → LeafJExp N O → ErrorConstantMatchesDefinition N O CE → TieErr O →
      R.toIndefData.ON N := by
  refine ⟨c.CE, rfl, ?_⟩
  intro K₁ _ _ _ Bs Df R wf N P _ _ O hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE tE1 tErr
  exact on_of_rows N R wf O c.CE hMk hSup hProj hC hSp hS hT0 hD hJ hI h2 h1 hSh hIU hBS hUn hG hR h2p hL
    hPg hSz hX hBad hJS hJE le_rfl tE1 tErr
end Formalism.L2.Indef.Tree
