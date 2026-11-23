-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts.subst_zero_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:02.943343+00:00
-- url     : https://prove2.me/submissions/52b760bb-0514-41ff-bcee-861e291f0950

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ConstantCoeffLawFirstTwoOfThree
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_single_variable
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
open MvPowerSeries
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
theorem _root_.solution {τ : Type} (G : MvPowerSeries (Fin 2) K)
    {w : MvPowerSeries τ K} (hw : constantCoeff w = 0) :
    subst ![0, w] (pderiv K 0 G) = PowerSeries.subst w (fLin G) := by
  have hd : (X 0 : MvPowerSeries (Fin 2) K) ∣ pderiv K 0 G - at1 1 (fLin G) := by
    refine X_dvd_iff.2 fun m hm => ?_
    have hm1 : m = Finsupp.single 1 (m 1) := by
      ext i
      fin_cases i <;> simp [hm]
    rw [map_sub, coeff_pderiv, coeff_single_variable_series, if_pos hm1, hm, fLin, PowerSeries.coeff_mk,
      add_comm (Finsupp.single 0 1), ← hm1]
    simp
  obtain ⟨Q, hQ⟩ := hd
  have e : pderiv K 0 G = at1 1 (fLin G) + X 0 * Q := by rw [← hQ]; ring
  have h := hs2 (map_zero _) hw
  rw [e, subst_add h, subst_mul h, subst_X h, subst_single_variable h]
  simp
end Formalism.InvariantFactorPaths.G7.GramFrameCompositionLinFacts
