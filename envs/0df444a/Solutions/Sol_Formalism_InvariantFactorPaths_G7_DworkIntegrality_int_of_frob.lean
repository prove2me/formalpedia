-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.DworkIntegrality.int_of_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:01:32.901828+00:00
-- url     : https://prove2.me/submissions/43c29d37-c63b-476f-ac3a-74a6e30bdc98

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LocalComponentGL
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_sm_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_sub_truncD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_truncD_self
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_constantCoeff_truncD
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_coeff_eq_of_low
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_induct
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_low_PhiH
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero


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
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
open Formalism.InvariantFactorPaths.G7.DworkIntegrality
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [Finite ι] {p : ℕ} {σ : K →+* K}
namespace Formalism.InvariantFactorPaths.G7.DworkIntegrality
theorem _root_.solution (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ p‖ ≤ (p : ℝ)⁻¹) {Fo Ga : MvPowerSeries ι K}
    (hF : MvPowerSeries.constantCoeff Fo = 1) (hG0 : MvPowerSeries.constantCoeff Ga = 1)
    (hG : Bd (p : ℝ)⁻¹ (Ga - 1)) (hrel : PhiH hp.ne_zero σ Fo = Fo ^ p * Ga) : Bd 1 Fo := by
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by have := hp.pos; positivity
  refine bd_induct zero_le_one Fo fun d hl m hm => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
    rw [hm0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]
    simp
  have hFh : Low d (Fo - truncD d Fo) := low_sub_truncD d Fo
  have hFl1 : MvPowerSeries.constantCoeff (truncD d Fo) = 1 := by
    rw [constantCoeff_truncD hd, hF]
  have hFlm : MvPowerSeries.coeff m (truncD d Fo) = 0 := coeff_truncD_self Fo hm
  generalize truncD d Fo = Fl at hl hFh hFl1 hFlm
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion Fl (Fo - Fl) p
  rw [add_sub_cancel] at hk
  obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow Fo Fl p
  have hB := frob_congr hp hnp hσ hl
  have hY : Bd (p : ℝ)⁻¹ (-(Fl ^ p - PhiH hp.ne_zero σ Fl) - (Ga - 1) * Fl ^ p) :=
    bd_sub (bd_neg hB) (sm_mul hpos.le hG (int_pow hl p))
  have hG1 : Low 1 (Ga - 1) := (low_one_iff _).2 (by rw [map_sub, hG0]; simp)
  have hFp : Low 1 (Fl ^ (p - 1) - 1) := (low_one_iff _).2 (by rw [map_sub, map_pow, hFl1]; simp)
  have hlow : Low (d + 1) (MvPowerSeries.C (p : K) * Fo -
      (-(Fl ^ p - PhiH hp.ne_zero σ Fl) - (Ga - 1) * Fl ^ p + MvPowerSeries.C (p : K) * Fl)) := by
    have e : MvPowerSeries.C (p : K) * Fo -
        (-(Fl ^ p - PhiH hp.ne_zero σ Fl) - (Ga - 1) * Fl ^ p + MvPowerSeries.C (p : K) * Fl) =
        PhiH hp.ne_zero σ (Fo - Fl) - MvPowerSeries.C (p : K) * ((Fl ^ (p - 1) - 1) * (Fo - Fl)) -
          k * ((Fo - Fl) * (Fo - Fl)) - (Fo - Fl) * r * (Ga - 1) := by
      rw [map_sub, map_natCast]
      linear_combination -hrel - hk - (Ga - 1) * hr
    rw [e]
    have h2 := hp.two_le
    refine low_sub (low_sub (low_sub ?_ ?_) ?_) ?_
    · exact low_mono (by nlinarith) (low_PhiH hp.ne_zero σ hFh)
    · exact low_mono (by omega) (low_mul (low_zero (MvPowerSeries.C (p : K))) (low_mul hFp hFh))
    · exact low_mono (by omega) (low_mul (low_zero k) (low_mul hFh hFh))
    · exact low_mono (by omega) (low_mul (low_mul hFh (low_zero r)) hG1)
  have h1 := coeff_eq_of_low hlow hm
  rw [map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, hFlm, mul_zero, add_zero] at h1
  have h2 := hY m
  rw [← h1, norm_mul, hnp] at h2
  exact le_of_mul_le_mul_left (by simpa using h2) hpos
end Formalism.InvariantFactorPaths.G7.DworkIntegrality
