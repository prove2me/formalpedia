-- Prove2me | solution 1 for Formalism.L2.Th1.D.third_mean_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:52:53.667362+00:00
-- url     : https://prove2.me/submissions/96bdb110-3954-4a17-a035-582e92f80629

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_divAB_addC
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_beMean
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_wt_pow
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_geom_zero
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_pair_degO
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_pair_degE
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_wt_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (torus lw degE degO NoLowBidegree)
open Formalism.InvariantFactorPaths.G7 (lgF at1 DivAB)
open TorusDerivation
namespace Formalism.L2.Th1.D
theorem _root_.solution : MeanNoLowBidegreeTerms := by
  intro K _ _ l d _ σ hl _ _ be0 hbe ι _ om oms ζ hζ n hn
  rw [coeff_beMean] at hn
  have hG := divAB_addC l hbe
  have hT : MvPowerSeries.coeff n (beTil l σ be0 om oms) ≠ 0 := by
    intro h
    apply hn
    rw [h, mul_zero, mul_zero]
  have hS : ∑ k ∈ Finset.range (l ^ d - 1), wt l ζ n ^ k ≠ 0 := by
    intro h
    apply hn
    rw [h, zero_mul, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · refine Nat.pos_of_ne_zero fun h => hT ?_
    unfold beTil
    rw [map_sum]
    exact Finset.sum_eq_zero fun r _ => coeff_pair_degE hG σ _ _ h
  · refine Nat.pos_of_ne_zero fun h => hT ?_
    unfold beTil
    rw [map_sum]
    exact Finset.sum_eq_zero fun r _ => coeff_pair_degO hG σ _ _ h
  · rintro ⟨hE, hO⟩
    exact hS (geom_zero (wt_pow hζ.pow_eq_one n) (wt_ne_one hl hζ hE hO))
end Formalism.L2.Th1.D
