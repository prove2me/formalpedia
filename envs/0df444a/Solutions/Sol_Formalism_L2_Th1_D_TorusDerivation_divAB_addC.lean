-- Prove2me | solution 1 for Formalism.L2.Th1.D.TorusDerivation.divAB_addC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:44.27713+00:00
-- url     : https://prove2.me/submissions/e2980ca7-401d-46b2-83fd-74f6428abbb9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstZeroOfConstantCoeff
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_hasSubst_pair
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_pair
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_right_zero
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_left_zero
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_divAB_of_axes
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_expF
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_constantCoeff_inVar
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_subst_zero_of_constantCoeff

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
namespace Formalism.L2.Th1.D.TorusDerivation
theorem _root_.solution (l : ℕ) {be0 : MvPowerSeries (Fin 2) K} (h : DivAB be0) :
    DivAB (addC l be0) := by
  have hE := constantCoeff_expF (K := K) l
  have h0 := constantCoeff_inVar (0 : Fin 2) _ hE
  have h1 := constantCoeff_inVar (1 : Fin 2) _ hE
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  refine divAB_of_axes ?_ ?_
  · have hb := hasSubst_pair hX0 (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K)))
    unfold addC
    rw [subst_pair h0 h1 hb, subst_single_var hb, subst_single_var hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [subst_zero_of_constantCoeff _ hE]
    exact subst_right_zero h (PowerSeries.constantCoeff_subst_eq_zero hX0 _ hE)
  · have hb := hasSubst_pair (map_zero (MvPowerSeries.constantCoeff (σ := Fin 2) (R := K))) hX1
    unfold addC
    rw [subst_pair h0 h1 hb, subst_single_var hb, subst_single_var hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [subst_zero_of_constantCoeff _ hE]
    exact subst_left_zero h (PowerSeries.constantCoeff_subst_eq_zero hX1 _ hE)
end Formalism.L2.Th1.D.TorusDerivation
