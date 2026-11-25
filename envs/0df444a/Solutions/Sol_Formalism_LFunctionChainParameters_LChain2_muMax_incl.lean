-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.muMax_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:43.014803+00:00
-- url     : https://prove2.me/submissions/b11009dc-f124-42b9-8b3b-81584bf15cb9

import Definitions.Def_Formalism_SizeWindowBrackets_Chain2aCoreNoAnalytic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PChain
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_OneLeThresholdMulPowers
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ProjectiveLines
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_inclL_ht
import Theorems.Thm_Formalism_HN_slope_inequality_mean
import Theorems.Thm_Formalism_LFunctionChainParameters_ProjectiveLineModels_standard_lattice_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain2
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat inclMat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] [DecidableEq κ] [DecidableEq κ₁] [Nonempty κ] :
    muMaxDef (Pi.basisFun K κ) (fun _ => 1) (stdLat K κ)
      ≤ muMaxDef (Pi.basisFun K (κ ⊕ κ₁)) (fun _ => 1) (stdLat K (κ ⊕ κ₁)) := by
  have hinj : Function.Injective (inclL K κ κ₁) := by
    intro x y hxy
    ext a
    exact congrFun hxy (Sum.inl a)
  have hmap : (stdLat K κ).map ((inclL K κ κ₁).restrictScalars (𝓞 K)) ≤ stdLat K (κ ⊕ κ₁) := by
    unfold stdLat
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨Sum.inl k, ?_⟩
    ext (a | a) <;> simp [inclL, Pi.single_apply]
  have hne : (stdLat K κ).map ((inclL K κ κ₁).restrictScalars (𝓞 K)) ≠ ⊥ := by
    intro h0
    obtain ⟨k⟩ := (inferInstance : Nonempty κ)
    have h1 : (inclL K κ κ₁) (Pi.basisFun K κ k) ∈
        (stdLat K κ).map ((inclL K κ κ₁).restrictScalars (𝓞 K)) :=
      ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
    rw [h0, Submodule.mem_bot] at h1
    exact (Pi.basisFun K κ).ne_zero k (hinj (h1.trans (map_zero _).symm))
  have h := ((slope_inequality_mean K (κ → K) κ (κ ⊕ κ₁ → K) (κ ⊕ κ₁) (Pi.basisFun K κ) (fun _ => 1)
    (Pi.basisFun K (κ ⊕ κ₁)) (fun _ => 1) (by simp) (by simp) (inclL K κ κ₁) (stdLat K κ)
    (ProjectiveLineModels.standard_lattice_fg K κ) hne).2 (stdLat K (κ ⊕ κ₁)) (ProjectiveLineModels.standard_lattice_fg K _) hmap).2 hinj.injOn
  have := inclL_ht K κ κ₁
  linarith
end Formalism.LFunctionChainParameters.LChain2
