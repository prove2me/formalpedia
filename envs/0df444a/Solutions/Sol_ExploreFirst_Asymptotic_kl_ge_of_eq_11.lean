-- Prove2me | solution 1 for ExploreFirst.Asymptotic.kl_ge_of_eq_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:52:27.329481+00:00
-- url     : https://prove2.me/submissions/008f522a-b69a-47a8-9f31-e13dd7defa6c

import Mathlib
import Definitions.Def_ExploreFirst_Asymptotic_Setting

namespace Aux_ExploreFirst_Asymptotic_kl_ge_of_eq_11
open MeasureTheory InformationTheory
open ExploreFirst.FundIneq

lemma ber_finite (p : ℝ) : IsFiniteMeasure (bernoulliLaw p) := by
  constructor
  simp [bernoulliLaw]

lemma ber_one (p : ℝ) : bernoulliLaw p {1} = ENNReal.ofReal p := by
  simp [bernoulliLaw, Measure.dirac_apply]

lemma ber_zero (p : ℝ) : bernoulliLaw p {0} = ENNReal.ofReal (1 - p) := by
  simp [bernoulliLaw, Measure.dirac_apply]

lemma ber_lintegral (q : ℝ) (f : ℝ → ENNReal) :
    ∫⁻ x, f x ∂(bernoulliLaw q) = ENNReal.ofReal q * f 1 + ENNReal.ofReal (1 - q) * f 0 := by
  simp [bernoulliLaw, lintegral_add_measure, lintegral_smul_measure]

end Aux_ExploreFirst_Asymptotic_kl_ge_of_eq_11

open MeasureTheory InformationTheory ExploreFirst.FundIneq
  Aux_ExploreFirst_Asymptotic_kl_ge_of_eq_11 in
theorem solution (p q : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (if q = 1 ∧ p < 1 then (⊤ : ENNReal)
      else ENNReal.ofReal ((1 - p) * Real.log (1 / (1 - q)) - Real.log 2)) ≤
      ExploreFirst.FundIneq.klBer p q := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  haveI := ber_finite p
  haveI := ber_finite q
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  by_cases htop : q = 1 ∧ p < 1
  · rw [if_pos htop]
    have hnac : ¬ bernoulliLaw p ≪ bernoulliLaw q := by
      intro hac
      have h0 : bernoulliLaw q {0} = 0 := by
        rw [ber_zero, htop.1, sub_self, ENNReal.ofReal_zero]
      have h1 := hac h0
      rw [ber_zero, ENNReal.ofReal_eq_zero] at h1
      linarith [htop.2]
    rw [klBer, klDiv_of_not_ac hnac]
  · rw [if_neg htop]
    set R := (1 - p) * Real.log (1 / (1 - q)) - Real.log 2 with hR
    by_cases hRle : R ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hRle]
      exact zero_le
    push_neg at hRle
    have hqpos : 0 < q := by
      by_contra hc
      have hq' : q = 0 := le_antisymm (not_lt.mp hc) hq0
      rw [hR, hq', sub_zero, div_one, Real.log_one, mul_zero] at hRle
      linarith
    have hqlt : q < 1 := by
      by_contra hc
      have hq' : q = 1 := le_antisymm hq1 (not_lt.mp hc)
      have hp' : p = 1 := by
        by_contra hpne
        exact htop ⟨hq', lt_of_le_of_ne hp1 hpne⟩
      rw [hR, hp', sub_self, zero_mul, zero_sub] at hRle
      linarith
    by_cases hac : bernoulliLaw p ≪ bernoulliLaw q
    swap
    · rw [klBer, klDiv_of_not_ac hac]
      exact le_top
    rw [klBer, klDiv_eq_lintegral_klFun_of_ac hac, ber_lintegral]
    set r := (bernoulliLaw p).rnDeriv (bernoulliLaw q) with hr
    have hr1 : (r 1).toReal = p / q := by
      have h := Measure.setLIntegral_rnDeriv hac {1}
      rw [lintegral_singleton, ber_one, ber_one] at h
      have : r 1 = ENNReal.ofReal p / ENNReal.ofReal q := by
        rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hqpos).ne' ENNReal.ofReal_ne_top, mul_comm]
        exact h
      rw [this, ENNReal.toReal_div, ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hq0]
    have hr0 : (r 0).toReal = (1 - p) / (1 - q) := by
      have h := Measure.setLIntegral_rnDeriv hac {0}
      rw [lintegral_singleton, ber_zero, ber_zero] at h
      have : r 0 = ENNReal.ofReal (1 - p) / ENNReal.ofReal (1 - q) := by
        rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top,
          mul_comm]
        exact h
      rw [this, ENNReal.toReal_div, ENNReal.toReal_ofReal (by linarith),
        ENNReal.toReal_ofReal (by linarith)]
    rw [hr1, hr0]
    have hk1 : 0 ≤ klFun (p / q) := klFun_nonneg (div_nonneg hp0 hq0)
    have hk0 : 0 ≤ klFun ((1 - p) / (1 - q)) := klFun_nonneg (div_nonneg (by linarith) (by linarith))
    rw [← ENNReal.ofReal_mul hq0, ← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg hq0 hk1) (mul_nonneg (by linarith) hk0)]
    apply ENNReal.ofReal_le_ofReal
    set A := Real.log (p / q) with hA
    set B := Real.log ((1 - p) / (1 - q)) with hB
    have e1 : q * klFun (p / q) = p * A + q - p := by
      have : q * (p / q) = p := mul_div_cancel₀ p hqpos.ne'
      rw [klFun_apply]
      linear_combination (A + 1 - 1) * this - this
    have e0 : (1 - q) * klFun ((1 - p) / (1 - q)) = (1 - p) * B + (1 - q) - (1 - p) := by
      have : (1 - q) * ((1 - p) / (1 - q)) = 1 - p := mul_div_cancel₀ (1 - p) (by linarith)
      rw [klFun_apply]
      linear_combination (B + 1 - 1) * this - this
    rw [e1, e0]
    have hA' : p * Real.log p ≤ p * A := by
      by_cases hpz : p = 0
      · rw [hpz, zero_mul, zero_mul]
      · rw [hA, Real.log_div hpz hqpos.ne']
        have : Real.log q ≤ 0 := Real.log_nonpos hq0 hq1
        nlinarith
    have hB' : (1 - p) * B = (1 - p) * Real.log (1 - p) + (1 - p) * Real.log (1 / (1 - q)) := by
      by_cases hpz : 1 - p = 0
      · rw [hpz, zero_mul, zero_mul, zero_mul, add_zero]
      · rw [hB, Real.log_div hpz (by linarith), one_div, Real.log_inv]
        ring
    have hent := Real.binEntropy_le_log_two (p := p)
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog] at hent
    rw [hB']
    linarith
