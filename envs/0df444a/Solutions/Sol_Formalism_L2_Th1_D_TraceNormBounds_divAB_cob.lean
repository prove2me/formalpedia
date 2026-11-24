-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceNormBounds.divAB_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:08.854255+00:00
-- url     : https://prove2.me/submissions/22c1b3c0-215e-4d31-adf2-ca819b8efef8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_NormLeInvOfLtOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_CoboundaryCommutesHomomorphism
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_law_right_zero
import Theorems.Thm_Formalism_L2_Th1_D_TraceNormBounds_law_left_zero
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_subst1
import Theorems.Thm_Formalism_L2_Th1_D_TorusDerivation_divAB_of_axes
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog frobVar)
open MvPowerSeries
open Formalism.L2.Th1.D.TraceNormBounds
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.D.TraceNormBounds
theorem _root_.solution {l : ℕ} (hl : 2 ≤ l) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) (hF : cob F (lgF K l) = 0) {ph : PowerSeries K}
    (hph : PowerSeries.constantCoeff ph = 0) : DivAB (cob F ph) := by
  have hX0 : constantCoeff (X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : constantCoeff (X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hz := map_zero (constantCoeff (σ := Fin 2) (R := K))
  refine TorusDerivation.divAB_of_axes ?_ ?_
  · have hs := Pair.hs2 hX0 hz
    unfold cob
    rw [subst_sub hs, subst_sub hs,
      Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
      Pair.subst_single_var hs, Pair.subst_single_var hs, law_right_zero hl hF0 hF hX0]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [TorusDerivation.subst_zero_of_constantCoeff _ hph, sub_self, sub_zero]
  · have hs := Pair.hs2 hz hX1
    unfold cob
    rw [subst_sub hs, subst_sub hs,
      Pair.subst_subst1 hs (PowerSeries.HasSubst.of_constantCoeff_zero hF0),
      Pair.subst_single_var hs, Pair.subst_single_var hs, law_left_zero hl hF0 hF hX1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [TorusDerivation.subst_zero_of_constantCoeff _ hph, sub_zero, sub_self]
end Formalism.L2.Th1.D.TraceNormBounds
