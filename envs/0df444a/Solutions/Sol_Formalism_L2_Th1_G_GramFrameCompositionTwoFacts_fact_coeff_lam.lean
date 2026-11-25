-- Prove2me | solution 1 for Formalism.L2.Th1.G.GramFrameCompositionTwoFacts.fact_coeff_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:08:21.285225+00:00
-- url     : https://prove2.me/submissions/e4f609d6-8f3e-4844-986c-287a025540ca

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_Hurwitz
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_CurveSecondLogDerivative
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_BridgeTwoMore
import Definitions.Def_Formalism_GaussJetBounds_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_ThetaZeroJetsCurveHolds
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
open Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
theorem _root_.solution (e : PowerSeries K) (s2 : K) (n : ℕ) :
    (((n + 2).factorial : ℕ) : K) * PowerSeries.coeff (n + 2) (lam e s2) =
      ((n.factorial : ℕ) : K) * PowerSeries.coeff n e + if n = 0 then s2 else 0 := by
  have h1 : ((n : K) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  have h2 : ((n : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h3 : ¬ (n + 2 < 2) := by omega
  rw [lam, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, dblInt, PowerSeries.coeff_mk,
    if_neg h3, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ]
  by_cases h0 : n = 0
  · subst h0
    simp
    field_simp
    ring
  · have h4 : n + 2 ≠ 2 := by omega
    have h5 : ((n : K) + 2 - 1) = (n : K) + 1 := by ring
    rw [if_neg h0, if_neg h4]
    push_cast
    rw [h5]
    field_simp
    ring
end Formalism.L2.Th1.G.GramFrameCompositionTwoFacts
