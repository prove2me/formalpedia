-- Prove2me | solution 1 for Formalism.L2.Th1.D.subst_tilde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:39.633775+00:00
-- url     : https://prove2.me/submissions/38906928-df8d-44b3-a25f-2005545aec1b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst2_comp
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_linE
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_linO
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_linE
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_linO
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
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
end Alg
section NormedLin
variable {K : Type} [NormedField K]
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
open Pair
namespace Formalism.L2.Th1.D
theorem _root_.solution : SubstTil := by
  unfold SubstTil
  intro K _ l d _ σ _hl be0 ι _ om oms τ _ L hL0
  have hL : HasSubst L := hasSubst_finite_of_constantCoeff_eq_zero hL0
  unfold beTil
  rw [subst_sum hL]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [subst2_comp hL (cc_linE σ (oms r)) (cc_linO σ (om r)), subst_linE σ (oms r) hL,
    subst_linO σ (om r) hL]
end Formalism.L2.Th1.D
