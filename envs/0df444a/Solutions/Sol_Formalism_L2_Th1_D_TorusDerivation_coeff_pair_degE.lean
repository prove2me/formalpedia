-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.coeff_pair_degE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:14.045485+00:00
-- url     : https://prove2.me/submissions/d5c1e050-912f-4b35-9f3f-a72201064ac7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_subst_scale
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_scale
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_pair
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_left_zero
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_linE
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_linO
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_scale_linE
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_scale_linO

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
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution {G : MvPowerSeries (Fin 2) K} (hG : DivAB G) (σ : K →+* K) (c c' : K)
    {n : ZMod d →₀ ℕ} (hn : degE n = 0) :
    MvPowerSeries.coeff n (MvPowerSeries.subst ![linE σ c, linO σ c'] G) = 0 := by
  set a : ZMod d → K := fun s => if s.val % 2 = 0 then 0 else 1 with ha
  have h := coeff_subst_scale a (MvPowerSeries.subst ![linE σ c, linO σ c'] G) n
  have hp : ∏ s, a s ^ n s = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    by_cases hs : s.val % 2 = 0
    · have := (Finset.sum_eq_zero_iff.1 hn) s (Finset.mem_univ s)
      rw [if_pos hs] at this
      rw [this, pow_zero]
    · simp [ha, hs]
  have hE : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linE (d := d) σ c) = 0 := by
    rw [subst_scale_linE]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · simp [ha, hs]
    · rfl
  have hO : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linO (d := d) σ c') = linO σ c' := by
    rw [subst_scale_linO]
    unfold linO
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hs
    · rfl
    · simp [ha, hs]
  rw [hp, one_mul, subst_pair (constantCoeff_linE _ _) (constantCoeff_linO _ _) (hasSubst_scale a),
    hO, hE, subst_left_zero hG (constantCoeff_linO _ _), map_zero] at h
  exact h.symm
end Formalism.L2.Th1.D.TorusDerivation
