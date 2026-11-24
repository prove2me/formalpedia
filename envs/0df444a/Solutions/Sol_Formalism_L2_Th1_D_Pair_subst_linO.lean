-- Prove2me | solution 1 for Formalism.L2.Th1.D.Pair.subst_linO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:41.107889+00:00
-- url     : https://prove2.me/submissions/00f4ee82-5951-4791-9aed-f2ddc0402359

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum
import Theorems.Thm_P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
namespace Pair
section Alg
variable {K : Type} [Field K]
end Alg
section NormedLin
variable {K : Type} [NormedField K]
private theorem subst_C_mul_X_eq_C_mul {ι τ : Type} {L : ι → MvPowerSeries τ K} (hL : HasSubst L) (x : K)
    (s : ι) : subst L (C x * X s) = C x * L s := by
  first
  | (simp only [← MvPowerSeries.smul_eq_C_mul]; rw [MvPowerSeries.subst_smul hL, subst_X hL])
  | (rw [← coe_substAlgHom hL, map_mul, coe_substAlgHom hL, subst_X hL]; congr 1; simp)
  | simp [subst_X hL, MvPowerSeries.subst_mul hL]
end NormedLin
section Normed
variable {K : Type} [NormedField K] [CharZero K]
end Normed
end Pair
open Pair
end Formalism.L2.Th1.D
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Formalism.L2.Th1.D.Pair
variable {K : Type} [NormedField K]
namespace Formalism.L2.Th1.D.Pair
theorem _root_.solution {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) {τ : Type}
    {L : ZMod d → MvPowerSeries τ K} (hL : HasSubst L) :
    subst L (linO σ c) = linOL σ c L := by
  unfold linO linOL
  rw [subst_sum hL]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> first | exact subst_zero' hL | exact subst_C_mul_X_eq_C_mul hL _ s
end Formalism.L2.Th1.D.Pair
