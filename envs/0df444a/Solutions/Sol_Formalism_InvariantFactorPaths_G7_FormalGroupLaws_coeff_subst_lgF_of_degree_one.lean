-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_subst_lgF_of_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:06.560297+00:00
-- url     : https://prove2.me/submissions/e5f82cf3-c2c5-4a0a-8836-8070f66f2542

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_one_lgF

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
theorem _root_.solution {ι : Type} (p : ℕ) (hp : 2 ≤ p) (F : MvPowerSeries ι K)
    (hF : MvPowerSeries.constantCoeff F = 0) (n : ι →₀ ℕ) (hn : n.degree = 1) :
    MvPowerSeries.coeff n (PowerSeries.subst F (lgF K p)) = MvPowerSeries.coeff n F := by
  classical
  have hdvd : (PowerSeries.X : PowerSeries K) ^ 2 ∣ lgF K p - PowerSeries.X := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lgF p hp]
    · simp [coeff_one_lgF p hp]
  obtain ⟨r, hr⟩ := hdvd
  have hF' : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have hl : lgF K p = PowerSeries.X + PowerSeries.X ^ 2 * r := by rw [← hr]; ring
  rw [hl, PowerSeries.subst_add hF', PowerSeries.subst_mul hF', PowerSeries.subst_pow hF',
    PowerSeries.subst_X hF', map_add]
  suffices h : MvPowerSeries.coeff n (F ^ 2 * PowerSeries.subst F r) = 0 by rw [h, add_zero]
  rw [pow_two, mul_assoc, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  by_cases hi : i = 0
  · subst hi
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
  · have hj : j = 0 := by
      have h1 := congrArg Finsupp.degree hij
      rw [map_add, hn] at h1
      have h2 : i.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff i).mp h)
      exact (Finsupp.degree_eq_zero_iff j).mp (by omega)
    subst hj
    simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
end Formalism.InvariantFactorPaths.G7.FormalGroupLaws
