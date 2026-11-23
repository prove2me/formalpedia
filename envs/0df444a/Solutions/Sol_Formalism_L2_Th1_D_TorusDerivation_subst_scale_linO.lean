-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.subst_scale_linO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:36.876275+00:00
-- url     : https://prove2.me/submissions/934ea3b0-8f46-40ef-92c2-3f9a2efea310

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_scale
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_sum
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_C_mul
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_zero

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
open Formalism.L2.Th1.D.TorusDerivation
variable {K : Type} [Field K]
variable {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution (σ : K →+* K) (c : K) (a : ZMod d → K) :
    MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) (linO (d := d) σ c) =
      ∑ s : ZMod d, if s.val % 2 = 0 then 0
        else MvPowerSeries.C (σ^[s.val] c * a s) * MvPowerSeries.X s := by
  have hs := hasSubst_scale a
  unfold linO
  rw [subst_sum hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · exact subst_zero hs
  · rw [subst_C_mul hs, MvPowerSeries.subst_X hs, map_mul, mul_assoc]
end Formalism.L2.Th1.D.TorusDerivation
