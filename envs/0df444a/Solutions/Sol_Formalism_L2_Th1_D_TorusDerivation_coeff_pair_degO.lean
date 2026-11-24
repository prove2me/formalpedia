-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.coeff_pair_degO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:14.746794+00:00
-- url     : https://prove2.me/submissions/4a567f04-c7de-4137-a2a1-190d77ddcb1d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_coeff_subst_scale
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_scale
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_pair
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_right_zero
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
    {n : ZMod d →₀ ℕ} (hn : degO n = 0) :
    MvPowerSeries.coeff n (MvPowerSeries.subst ![linE σ c, linO σ c'] G) = 0 := by
  set a : ZMod d → K := fun s => if s.val % 2 = 0 then 1 else 0 with ha
  have h := coeff_subst_scale a (MvPowerSeries.subst ![linE σ c, linO σ c'] G) n
  have hp : ∏ s, a s ^ n s = 1 := by
    refine Finset.prod_eq_one fun s _ => ?_
    by_cases hs : s.val % 2 = 0
    · simp [ha, hs]
    · have := (Finset.sum_eq_zero_iff.1 hn) s (Finset.mem_univ s)
      rw [if_neg hs] at this
      rw [this, pow_zero]
  have hO : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linO (d := d) σ c') = 0 := by
    rw [subst_scale_linO]
    refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · rfl
    · simp [ha, hs]
  have hE : MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s)
      (linE (d := d) σ c) = linE σ c := by
    rw [subst_scale_linE]
    unfold linE
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with hs
    · simp [ha, hs]
    · rfl
  rw [hp, one_mul, subst_pair (constantCoeff_linE _ _) (constantCoeff_linO _ _) (hasSubst_scale a),
    hO, hE, subst_right_zero hG (constantCoeff_linE _ _), map_zero] at h
  exact h.symm
end Formalism.L2.Th1.D.TorusDerivation
