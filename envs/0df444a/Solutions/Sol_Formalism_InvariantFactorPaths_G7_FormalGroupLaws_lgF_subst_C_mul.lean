-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.lgF_subst_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:15.363351+00:00
-- url     : https://prove2.me/submissions/0901437f-ff0a-4436-857b-8ac90fcbe8d8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_rescale_lgF

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
open Formalism.InvariantFactorPaths.G7.FormalGroupLaws
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.FormalGroupLaws
theorem _root_.solution {ι : Type} {ζ : K} {p : ℕ} (hζ : ζ ^ (p ^ 2 - 1) = 1) (hp : 2 ≤ p)
    (G : MvPowerSeries ι K) (hG : MvPowerSeries.constantCoeff G = 0) :
    PowerSeries.subst (MvPowerSeries.C ζ * G) (lgF K p) =
      MvPowerSeries.C ζ * PowerSeries.subst G (lgF K p) := by
  have hG' : PowerSeries.HasSubst G := PowerSeries.HasSubst.of_constantCoeff_zero hG
  have hX : PowerSeries.HasSubst (ζ • PowerSeries.X : PowerSeries K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp; exact Or.inr PowerSeries.constantCoeff_X)
  have h1 : PowerSeries.subst G (ζ • PowerSeries.X : PowerSeries K) = MvPowerSeries.C ζ * G := by
    rw [PowerSeries.subst_smul hG', PowerSeries.subst_X hG', MvPowerSeries.smul_eq_C_mul]
  rw [← h1, ← PowerSeries.subst_comp_subst_apply hX hG', ← PowerSeries.rescale_eq_subst,
    rescale_lgF hζ hp, ← PowerSeries.smul_eq_C_mul, PowerSeries.subst_smul hG',
    MvPowerSeries.smul_eq_C_mul]
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
