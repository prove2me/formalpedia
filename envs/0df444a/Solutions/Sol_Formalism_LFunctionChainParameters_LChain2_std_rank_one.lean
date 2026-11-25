-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.std_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:59:59.58105+00:00
-- url     : https://prove2.me/submissions/c961bbce-c14f-4560-9ad3-924d1beea412

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_deg_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_std_deg_bot_le
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_HN_hnSum_rk_bot
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_slope_characterization
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_index
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_landauIteratedDerivatives_key


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
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    {L : Submodule (𝓞 K) V} (hL : L.FG) (hrk : rkK L = 1) :
    muMax (Formalism.HermitianLatticesTheory.realize b X) L = slope (Formalism.HermitianLatticesTheory.realize b X) L ∧
    muMin (Formalism.HermitianLatticesTheory.realize b X) L = slope (Formalism.HermitianLatticesTheory.realize b X) L := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hL0 : L ≠ ⊥ := by
    rintro rfl
    have h0 : rkK (⊥ : Submodule (𝓞 K) V) = 0 := by
      unfold rkK
      rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]
    omega
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hrkL := (place_lattice_structure K V ι b X hX L hL).2.1
  obtain ⟨c1, c2, -, c4, c5⟩ := slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat hL0
  have hbot := std_deg_bot_le b X hX hL hL0
  have hfr : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hr0 : rk (Formalism.HermitianLatticesTheory.realize b X) L ≠ 0 := by
    rw [hrkL, hrk]; omega
  have hdegL := std_deg_eq b X L hr0
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ L → N ≠ ⊥ →
      rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) L ∧
      deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ deg (Formalism.HermitianLatticesTheory.realize b X) L := by
    intro N hN hN0
    have hNfg : N.FG := Submodule.FG.of_le hL hN
    have hrkN : rkK N = 1 := by
      have h1 : rkK N ≤ rkK L := Submodule.finrank_mono (Submodule.span_mono hN)
      have h2 := slopeLatticeData.rkK_pos (K := K) hN0
      omega
    have hr := (place_lattice_structure K V ι b X hX N hNfg).2.1
    have hrr : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) L := by rw [hr, hrkL, hrkN, hrk]
    have hmu := slopeLatticeData.muDef_index b X hX hL hN hN0 (hrkN.trans hrk.symm)
    have hlog : 0 ≤ Real.log (N.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) := Real.log_natCast_nonneg _
    have hq : 0 ≤ 2 * Real.log (N.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) /
        ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by positivity
    have hsl : slope (Formalism.HermitianLatticesTheory.realize b X) N ≤ slope (Formalism.HermitianLatticesTheory.realize b X) L := by
      unfold muDef at hmu
      linarith
    refine ⟨hrr, ?_⟩
    rw [std_deg_eq b X N (by rw [hrr]; exact hr0), hdegL, hrr]
    exact mul_le_mul_of_nonneg_right hsl (Nat.cast_nonneg _)
  constructor
  · refine le_antisymm ((c1 _).2 fun N hN => ?_) c5
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [hnSum_rk_bot]
      simpa using hbot
    · obtain ⟨k1, k2⟩ := key N hN hN0
      rw [k1, ← hdegL]
      exact k2
  · refine le_antisymm c4 ((c2 _).2 fun N hN => ?_)
    by_cases hN0 : N = ⊥
    · subst hN0
      rw [hnSum_rk_bot, ← sub_nonneg]
      have : deg (Formalism.HermitianLatticesTheory.realize b X) L - deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V)
          - slope (Formalism.HermitianLatticesTheory.realize b X) L * ((rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) - ((0 : ℕ) : ℝ))
          = - deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) := by
        rw [hdegL]; push_cast; ring
      rw [this]
      linarith
    · obtain ⟨k1, k2⟩ := key N hN hN0
      rw [k1, sub_self, mul_zero]
      linarith
end Formalism.LFunctionChainParameters.LChain2
