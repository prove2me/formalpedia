-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.mem_plOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:26:12.37773+00:00
-- url     : https://prove2.me/submissions/a0fe4f2d-f4e9-436b-9217-7a049819ed21

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_prBelow_iff

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
variable {K}
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution {p : ℕ} (hp : p.Prime) (w : slopeLatticeData.FinPl K) : w ∈ plOver K p ↔ prBelow w = p := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hPprime : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hPne : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simpa using hpZ.ne_zero
  have hPmax : (Ideal.span {(p : ℤ)}).IsMaximal := hPprime.isMaximal hPne
  have hfin : {w : slopeLatticeData.FinPl K | prBelow w = p}.Finite := by
    have : Finite {w : slopeLatticeData.FinPl K | prBelow w = p} :=
      Finite.of_injective
        (fun w : {w : slopeLatticeData.FinPl K | prBelow w = p} =>
          (⟨w.1.1, w.1.2.isPrime, (prBelow_iff w.1 p).1 w.2⟩ : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K)))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun q => q.1) hab)))
    exact Set.toFinite _
  unfold plOver
  rw [dif_pos hfin]
  simp
end Formalism.LFunctionChainParameters.LChain2
