-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.std_T_slopes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:05.094827+00:00
-- url     : https://prove2.me/submissions/29183e4d-7c7c-4db4-84f2-2bab3bc80323

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_rank_one
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_orth
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_T_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_T_cons
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_T_ne
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_T_single
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_polygon_slope_sum


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
open Formalism.LFunctionChainParameters.ProjectiveLineModels (stdLat)
variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  (n : Type) [Fintype n] [DecidableEq n]
variable {K n}
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (s : Finset n) (hs : s.Nonempty) :
    muMaxDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n s) = 0 ∧
    muMinDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n s) = 0 := by
  have hX : ∀ v : InfinitePlace K, IsUnit ((1 : Matrix n n ℂ)).det := by simp
  have hone : ∀ a : n, muMaxDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 0 ∧
      muMinDef (Pi.basisFun K n) (fun _ => 1) (standardSpanAlt K n {a}) = 0 := by
    intro a
    obtain ⟨h1, h2⟩ := std_T_single (K := K) a
    obtain ⟨h3, h4⟩ := std_rank_one (Pi.basisFun K n) (fun _ => 1) hX (std_T_fg {a}) h1
    unfold muDef at h2
    unfold muMaxDef muMinDef
    rw [h3, h4]
    exact ⟨h2, h2⟩
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => exact hone a
  | cons a s ha hs ih =>
    have hA := (place_lattice_structure K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX _ (std_T_fg (K := K) {a})).1
    have hB := (place_lattice_structure K (n → K) n (Pi.basisFun K n) (fun _ => 1) hX _ (std_T_fg (K := K) s)).1
    obtain ⟨m1, m2⟩ := ((polygon_slope_sum.{0, 0, 0, 0} (𝓞 K) (n → K) _
      (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ)))).2 _ _ hA hB
      (fun x hx y hy => std_orth ha hx hy)).2.2 (std_T_ne (Finset.singleton_nonempty a)) (std_T_ne hs)
    obtain ⟨o1, o2⟩ := hone a
    obtain ⟨i1, i2⟩ := ih
    rw [std_T_cons]
    unfold muMaxDef at o1 i1 ⊢
    unfold muMinDef at o2 i2 ⊢
    rw [m1, m2]
    constructor
    · rcases max_choice (muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n {a}))
        (muMax (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n s)) with h | h
      · rw [h]; exact o1
      · rw [h]; exact i1
    · rcases min_choice (muMin (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n {a}))
        (muMin (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K n) (fun _ => (1 : Matrix n n ℂ))) (standardSpanAlt K n s)) with h | h
      · rw [h]; exact o2
      · rw [h]; exact i2
end Formalism.LFunctionChainParameters.LChain2
