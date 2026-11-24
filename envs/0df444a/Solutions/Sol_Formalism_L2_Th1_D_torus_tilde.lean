-- Prove2me | solution 1 for Formalism.L2.Th1.D.torus_tilde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:35:22.663818+00:00
-- url     : https://prove2.me/submissions/fc134860-a700-41b6-baa2-e0e731d6b409

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_scale
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_sum
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_pair
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_linE
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_linO
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_scale_linE
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_scale_linO
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_iter_pow

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
theorem _root_.solution : TorusTil := by
  intro K _ l d _ σ _ be0 ι _ om oms u hu hσ
  have hs : MvPowerSeries.HasSubst (torus (d := d) l u) := hasSubst_scale (fun s => u ^ lw l s)
  unfold beTil
  rw [subst_sum hs]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [subst_pair (constantCoeff_linE _ _) (constantCoeff_linO _ _) hs]
  have hE : MvPowerSeries.subst (torus (d := d) l u) (linE σ (oms r)) = linE σ (u * oms r) := by
    refine (subst_scale_linE σ (oms r) (fun s => u ^ lw l s)).trans ?_
    unfold linE
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · have e : σ^[s.val] (oms r) * u ^ lw l s = σ^[s.val] (u * oms r) := by
        rw [← RingHom.coe_pow, map_mul, RingHom.coe_pow, iter_pow σ hσ, lw, if_pos h, one_mul,
          ← Nat.cast_pow, zpow_natCast, mul_comm]
      rw [e]
    · rfl
  have hO : MvPowerSeries.subst (torus (d := d) l u) (linO σ (om r)) = linO σ (u⁻¹ * om r) := by
    refine (subst_scale_linO σ (om r) (fun s => u ^ lw l s)).trans ?_
    unfold linO
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · have e : σ^[s.val] (om r) * u ^ lw l s = σ^[s.val] (u⁻¹ * om r) := by
        rw [← RingHom.coe_pow, map_mul, map_inv₀, RingHom.coe_pow, iter_pow σ hσ, lw, if_neg h,
          neg_one_mul, zpow_neg, ← Nat.cast_pow, zpow_natCast, mul_comm]
      rw [e]
  rw [hE, hO]
end Formalism.L2.Th1.D
