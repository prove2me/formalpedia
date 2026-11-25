-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.Fam.slopeRel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:16.463301+00:00
-- url     : https://prove2.me/submissions/710da4be-ebd1-42e7-9fe4-d546f5fccd25

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_ramE_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_Fam_rk_M
import Theorems.Thm_Formalism_LFunctionChainParameters_LatticeToWeightTransfer_slope_formula_transfer


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
open Formalism.LFunctionChainParameters.LChain2.Fam
variable {I : Type} {m : ℕ} (F : Fam I m)
namespace Formalism.LFunctionChainParameters.LChain2.Fam
theorem _root_.solution (u : I) (f : ℕ) (bb : ℝ) (hX : ∀ v, IsUnit (F.X u v).det) (hd : 0 < F.du u)
    (hP : F.PlaceHyp f bb) :
    muMaxDef (F.b u) (F.X u) (F.N' u) ≤
      muMaxDef (F.b u) (F.X u) (F.M u) + UnitWeightPartition.Sg F.S lE (F.sgR u) F.tauR ∧
    muDef (F.b u) (F.X u) (F.N' u) =
      muDef (F.b u) (F.X u) (F.M u) + UnitWeightPartition.Sg F.S lE (F.sgR u) F.tauR
        - UnitWeightPartition.BeSum F.S lE (F.du u) (F.lenR u) F.tauR := by
  obtain ⟨-, hτ0, -, -, -, hu⟩ := hP
  obtain ⟨hFG, hspan, -, -, hle, hrkN, hoff, -⟩ := hu u
  have hrk := F.rk_M u hspan
  have hne : F.M u ≠ ⊥ := by
    intro h0
    have h1 : rkK (F.M u) = 0 := by
      unfold rkK
      rw [h0]
      simp
    rw [h1] at hrk
    simp only [Nat.cast_zero] at hrk
    exact absurd hrk hd.ne
  have h := LatticeToWeightTransfer.slope_formula_transfer F.K (F.V u) (F.ι u) (F.b u) (F.X u) hX (F.σ u) F.τ (F.M u) (F.N0 u)
    (fun w => (F.lenN u w : ℝ) / F.du u) hFG hne hle hrkN
    (fun w => by
      rw [hrk]
      show (F.lenN u w : ℝ) = _
      field_simp)
    F.S ramE lE (F.sgR u) F.tauR (F.lenR u)
    (fun w hw => ⟨(hoff w hw).1, hτ0 w hw, by
      show (F.lenN u w : ℝ) / F.du u = 0
      rw [(hoff w hw).2]; simp⟩)
    (fun w _ => ramE_pos w) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun w _ => by
      rw [hrk]
      unfold Fam.lenR
      congr 1
      field_simp)
  rw [hrk] at h
  exact h
end Formalism.LFunctionChainParameters.LChain2.Fam
