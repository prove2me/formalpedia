-- Prove2me | solution 1 for Formalism.L2.Indef.Tree.cut_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:22:06.078296+00:00
-- url     : https://prove2.me/submissions/9606cdf7-ff75-4dcf-8009-23d8b89b739f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
import Theorems.Thm_Formalism_ExtensionFiltration_goodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_rkK_pos


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
theorem _root_.solution (K V2 ι2 : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V2] [Module K V2] [Module (𝓞 K) V2] [IsScalarTower (𝓞 K) K V2] [Fintype ι2] [DecidableEq ι2]
    (b2 : Basis ι2 K V2) (X2 : InfinitePlace K → Matrix ι2 ι2 ℂ) (hX2 : ∀ v, IsUnit (X2 v).det)
    (N Mb : Submodule (𝓞 K) V2) (e : V2 →ₗ[K] V2) (g : ℕ)
    (hN : N.FG) (hMb : Mb.FG) (hN0 : N ≠ ⊥) (hg : 1 ≤ g) (hee : e ∘ₗ e = e)
    (hsa : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b2 X2 v (e x) y = Formalism.HermitianLatticesTheory.majAt b2 X2 v x (e y))
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) (hNM : N ≤ Mb) :
    (0 : ℝ) < (rkK N : ℝ) ∧
    (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (0 : ℝ) ≤ (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (rkK N : ℝ) * muDef b2 X2 N ≤
      (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) *
        muDef b2 X2 (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * (muMaxDef b2 X2 Mb + 2 * Real.log g) := by
  obtain ⟨hr, hdeg, hmax⟩ := Formalism.ExtensionFiltration.goodBadCut K V2 ι2 b2 X2 hX2 e g N hN hg hee hsa hint
  have hmax' := hmax Mb hMb hNM
  have hrN : (0 : ℝ) < (rkK N : ℝ) := by exact_mod_cast Formalism.ExtensionFiltration.rkK_pos b2 N hN0
  have hsum : (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) := by exact_mod_cast hr.symm
  refine ⟨hrN, hsum, by positivity, by nlinarith⟩
end Formalism.L2.Indef.Tree
