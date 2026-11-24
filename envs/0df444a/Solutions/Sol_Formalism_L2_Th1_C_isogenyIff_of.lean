-- Prove2me | solution 1 for Formalism.L2.Th1.C.isogenyIff_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:51:11.218899+00:00
-- url     : https://prove2.me/submissions/a100b785-6473-4a86-8518-f43fc19f9419

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_ChordSecondLogDeriv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_HasSecondLogDerivPowerSeriesExp
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_pExp
import Theorems.Thm_Formalism_L2_Th1_C_derivative_pExp
import Theorems.Thm_Formalism_L2_Th1_C_hasSecondLogDeriv_prod
import Theorems.Thm_Formalism_L2_Th1_C_hasSecondLogDeriv_powerSeriesExp
import Theorems.Thm_Formalism_L2_Th1_C_hasSecondLogDeriv_right_unique
import Theorems.Thm_Formalism_L2_Th1_C_hasSecondLogDeriv_left_unique
import Theorems.Thm_Formalism_L2_Th1_C_derivative_rescale
import Theorems.Thm_Formalism_L2_Th1_C_rescale_C_eq
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_rescale_eq
import Theorems.Thm_Formalism_L2_Th1_C_derivative2_lam
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_lam
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_derivative_lam
import Theorems.Thm_Formalism_L2_Th1_C_prod_wpShift_form
import Theorems.Thm_Formalism_L2_Th1_C_isogenyReduce_of

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
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
namespace Formalism.L2.Th1.C
theorem _root_.solution (hE : MvExpLaws) : IsogenyIff := by
  intro K _ _ e s2 ι _ neg c w al hal hendo
  obtain ⟨hneg, hD, hend⟩ := hendo
  rw [isogenyReduce_of hE K e s2 ι c al hal]
  change pExp _ = _ ↔ _
  have hL : constantCoeff (lam e s2) = 0 := constantCoeff_lam e s2
  set Φ := (2 * ((Fintype.card ι : K) + 1)) • lam e s2 - (2 : K) • rescale al (lam e s2) with hΦdef
  have hΦ : constantCoeff Φ = 0 := by
    rw [hΦdef]
    simp [PowerSeries.smul_eq_C_mul, constantCoeff_rescale_eq, hL]
  have hΦ1 : constantCoeff (derivative K Φ) = 0 := by
    rw [hΦdef]
    simp [PowerSeries.smul_eq_C_mul, derivative_rescale, Derivation.map_smul, constantCoeff_rescale_eq,
      constantCoeff_derivative_lam]
  set W := ∏ P, wpShift e (c P) with hWdef
  set g := ∑ P, (2 * e - w P - w (neg P)) with hgdef
  have hWg : HasSecondLogDeriv W g := hasSecondLogDeriv_prod _ _ _ fun P _ => hD P
  have hEg : HasSecondLogDeriv (pExp Φ) (derivative K (derivative K Φ)) := hasSecondLogDeriv_powerSeriesExp Φ hΦ
  have hsum_neg : ∑ P, w (neg P) = ∑ P, w P := Equiv.sum_comp (Function.Involutive.toPerm neg hneg) w
  have hg : g = (Fintype.card ι : PowerSeries K) * (2 * e) - 2 * ∑ P, w P := by
    rw [hgdef, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum_neg, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hend' : C al ^ 2 * rescale al e = e + ∑ P, w P - C (∑ P, c P) := by
    rw [← map_pow, hend, Finset.sum_sub_distrib, map_sum]
    ring
  have hd : derivative K (derivative K Φ) = g + C (2 * (∑ P, c P - (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2)) := by
    rw [hΦdef, map_sub, map_sub, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul, Derivation.map_smul,
      derivative_rescale, Derivation.map_smul, derivative_rescale, derivative2_lam, map_add, rescale_C_eq, hg]
    simp only [PowerSeries.smul_eq_C_mul, map_mul, map_sub, map_add, map_pow, map_natCast, map_one, map_ofNat]
    linear_combination (-2 : PowerSeries K) * hend'
  constructor
  · intro h
    have hW0 : W ≠ 0 := by
      intro h0
      have h3 := constantCoeff_pExp hE Φ hΦ
      rw [h, h0, map_zero] at h3
      exact zero_ne_one h3
    have hEg' := hEg
    rw [h] at hEg'
    have h1 := hasSecondLogDeriv_right_unique hW0 hEg' hWg
    rw [hd] at h1
    have h2 : C (2 * (∑ P, c P - (al ^ 2 - ((Fintype.card ι : K) + 1)) * s2)) = 0 := by
      linear_combination h1
    have h3 := congrArg constantCoeff h2
    rw [PowerSeries.constantCoeff_C, map_zero] at h3
    have h4 := (mul_eq_zero.1 h3).resolve_left two_ne_zero
    linear_combination -1 * h4
  · intro h
    have hΦg : derivative K (derivative K Φ) = g := by
      rw [hd, ← h, sub_self, mul_zero, map_zero, add_zero]
    obtain ⟨r, hr⟩ := prod_wpShift_form Finset.univ e c
    have hW1 : constantCoeff W = 1 := by
      rw [hWdef, hr]
      simp
    have hW2 : constantCoeff (derivative K W) = 0 := by
      rw [hWdef, hr, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
      simp [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
    have hWg' : HasSecondLogDeriv W (derivative K (derivative K Φ)) := by rw [hΦg]; exact hWg
    exact hasSecondLogDeriv_left_unique (constantCoeff_pExp hE Φ hΦ) hW1
      (by rw [derivative_pExp Φ hΦ, map_mul, hΦ1, mul_zero, hW2]) hEg hWg'
end Formalism.L2.Th1.C
