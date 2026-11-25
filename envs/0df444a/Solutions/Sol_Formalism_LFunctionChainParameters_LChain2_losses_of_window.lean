-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain2.losses_of_window
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:07:06.164795+00:00
-- url     : https://prove2.me/submissions/493a4105-7a15-4812-bffd-e14a615a995b

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain2_log_derivative_identity
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_losses_of_setting


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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}
variable [Fintype Ω] [∀ o u0, Fintype (W o u0)]
namespace Formalism.LFunctionChainParameters.LChain2
theorem _root_.solution : LossesOfWindow (H := H) (Ω := Ω) (W := W) (m := m) := by
  intro D hD ell G C N TT T2 a w Fm Lp P π s sB BAD Sig Cord eW KW o hL hx1 hC
  obtain ⟨px, pε, -, pd, -, hWin, -, hio, hc, he⟩ := hL
  obtain ⟨hε0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC0, -⟩ := hWin
  have hId := fun u0 => log_derivative_identity D hD N TT a w Fm Lp u0 o
  have h := PrimeWindowSizeBounds.losses_of_setting P (PlAll Fm) (Fin m) H H H Ω (inertPs D N) s Finset.univ TT
    (fun u0 p o => (Fm o u0).iop p) (ldOf D N a w Fm Lp) o id
    ({ mkData G C.cHH D ell N TT T2 (a o) (w o) (Fm o) with
        IO := fun u0 => ∑ p ∈ s, Real.log (p : ℝ) * (Fm o u0).iop p }) C hC (px ▸ hx1) hε0.le hC0 px.symm pε.symm
    (by show bTx G.x G.ε = bTx P.x P.ε; rw [px, pε]) (Fintype.card_coe TT) (by simp)
    (fun u0 => by rw [pd]; exact ((hId u0).1).symm) (fun u0 => ((hId u0).2).symm) (fun _ => rfl) hc he
  intro u0
  refine ⟨(h u0).1, le_trans ?_ (h u0).2⟩
  show ∑ p ∈ (Fm o u0).Pr, Real.log (p : ℝ) * (Fm o u0).iop p ≤ ∑ p ∈ s, Real.log (p : ℝ) * (Fm o u0).iop p
  calc ∑ p ∈ (Fm o u0).Pr, Real.log (p : ℝ) * (Fm o u0).iop p
      = ∑ p ∈ (Fm o u0).Pr.filter (fun p => p ∈ s), Real.log (p : ℝ) * (Fm o u0).iop p := by
        refine (Finset.sum_filter_of_ne fun p hp hne => ?_).symm
        by_contra hps
        exact hne (by rw [(hio o u0).1 p hp hps, mul_zero])
    _ ≤ ∑ p ∈ s, Real.log (p : ℝ) * (Fm o u0).iop p :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => (Finset.mem_filter.1 hp).2)
          (fun p hp _ => mul_nonneg (Real.log_natCast_nonneg p) ((hio o u0).2 p hp))
end Formalism.LFunctionChainParameters.LChain2
