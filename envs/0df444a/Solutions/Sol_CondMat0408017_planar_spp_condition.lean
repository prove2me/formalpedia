-- Prove2me | solution 1 for CondMat0408017.planar_spp_condition
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:30:23.677742+00:00
-- url     : https://prove2.me/submissions/1106dc29-3a5d-49a8-a1dc-0332c8afd97c

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

private lemma deriv_planarModeUpper (A : ℂ) (β k x1 : ℝ) :
    deriv (planarModeUpper A β k x1) 0 = -(β : ℂ) * A * cexp (I * k * x1) := by
  have h1 : HasDerivAt (fun z : ℂ => -(β : ℂ) * z) (-(β : ℂ)) (0 : ℂ) := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-(β : ℂ))
  have h2 : HasDerivAt (fun z : ℂ => A * cexp (-(β : ℂ) * z) * cexp (I * k * x1))
      (A * (cexp (-(β : ℂ) * 0) * -(β : ℂ)) * cexp (I * k * x1)) (0 : ℂ) :=
    ((h1.cexp).const_mul A).mul_const (cexp (I * k * x1))
  have h3 : HasDerivAt (planarModeUpper A β k x1)
      (A * (cexp (-(β : ℂ) * 0) * -(β : ℂ)) * cexp (I * k * x1)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h2' := hasDerivAt_iff_tendsto_slope_zero.mp h2.comp_ofReal
    simpa [planarModeUpper, Complex.real_smul] using h2'
  rw [h3.deriv]
  simp only [mul_zero, Complex.exp_zero, one_mul]
  ring

private lemma deriv_planarModeLower (A : ℂ) (β k x1 : ℝ) :
    deriv (planarModeLower A β k x1) 0 = (β : ℂ) * A * cexp (I * k * x1) := by
  have h1 : HasDerivAt (fun z : ℂ => (β : ℂ) * z) (β : ℂ) (0 : ℂ) := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (β : ℂ)
  have h2 : HasDerivAt (fun z : ℂ => A * cexp ((β : ℂ) * z) * cexp (I * k * x1))
      (A * (cexp ((β : ℂ) * 0) * (β : ℂ)) * cexp (I * k * x1)) (0 : ℂ) :=
    ((h1.cexp).const_mul A).mul_const (cexp (I * k * x1))
  have h3 : HasDerivAt (planarModeLower A β k x1)
      (A * (cexp ((β : ℂ) * 0) * (β : ℂ)) * cexp (I * k * x1)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h2' := hasDerivAt_iff_tendsto_slope_zero.mp h2.comp_ofReal
    simpa [planarModeLower, Complex.real_smul] using h2'
  rw [h3.deriv]
  simp only [mul_zero, Complex.exp_zero, one_mul]
  ring

theorem solution (epsP epsM k ω c : ℝ) (hc : 0 < c) (hω : 0 < ω)
    (hP : 0 < k ^ 2 - epsP * (ω / c) ^ 2) (hM : 0 < k ^ 2 - epsM * (ω / c) ^ 2) :
    (∀ κP κM AP AM : ℂ, κP ≠ 0 → κM ≠ 0 →
      (FlatInterfaceBC κP κM (planarModeUpper AP (decayConst epsP k ω c) k)
          (planarModeLower AM (decayConst epsM k ω c) k) ↔
        AP = AM ∧
          ((decayConst epsP k ω c : ℂ) / κP + (decayConst epsM k ω c : ℂ) / κM) * AP = 0)) ∧
    (∀ (μ0 : ℝ) (AP AM : ℂ), 0 < μ0 →
      FlatInterfaceBC (μ0 : ℂ) (μ0 : ℂ) (planarModeUpper AP (decayConst epsP k ω c) k)
          (planarModeLower AM (decayConst epsM k ω c) k) → AP = 0 ∧ AM = 0) ∧
    (epsP ≠ 0 → epsM ≠ 0 →
      ((∃ AP AM : ℂ, (AP ≠ 0 ∨ AM ≠ 0) ∧
          FlatInterfaceBC (epsP : ℂ) (epsM : ℂ) (planarModeUpper AP (decayConst epsP k ω c) k)
            (planarModeLower AM (decayConst epsM k ω c) k)) ↔
        epsP / epsM = -(decayConst epsP k ω c / decayConst epsM k ω c)) ∧
      (epsP / epsM = -(decayConst epsP k ω c / decayConst epsM k ω c) ↔
        epsP * epsM < 0 ∧ epsP + epsM ≠ 0 ∧
          (k = Real.sqrt (epsP * epsM / (epsP + epsM)) * (ω / c) ∨
            k = -(Real.sqrt (epsP * epsM / (epsP + epsM)) * (ω / c))))) := by
  have hβP : 0 < decayConst epsP k ω c := Real.sqrt_pos.mpr hP
  have hβM : 0 < decayConst epsM k ω c := Real.sqrt_pos.mpr hM
  have hβP_sq : decayConst epsP k ω c ^ 2 = k ^ 2 - epsP * (ω / c) ^ 2 :=
    Real.sq_sqrt hP.le
  have hβM_sq : decayConst epsM k ω c ^ 2 = k ^ 2 - epsM * (ω / c) ^ 2 :=
    Real.sq_sqrt hM.le
  have hpart1 : ∀ κP κM AP AM : ℂ, κP ≠ 0 → κM ≠ 0 →
      (FlatInterfaceBC κP κM (planarModeUpper AP (decayConst epsP k ω c) k)
          (planarModeLower AM (decayConst epsM k ω c) k) ↔
        AP = AM ∧
          ((decayConst epsP k ω c : ℂ) / κP + (decayConst epsM k ω c : ℂ) / κM) * AP = 0) := by
    intro κP κM AP AM hκP hκM
    simp only [FlatInterfaceBC, planarModeUpper, planarModeLower, deriv_planarModeUpper,
      deriv_planarModeLower, ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    constructor
    · intro h
      obtain ⟨hval, hder⟩ := h 0
      simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hval hder
      refine ⟨hval, ?_⟩
      rw [← hval] at hder
      field_simp [hκP, hκM] at hder ⊢
      linear_combination -hder
    · rintro ⟨hA, hsum⟩ x1
      refine ⟨by rw [hA], ?_⟩
      rw [← hA]
      have hsum' : ((decayConst epsP k ω c : ℂ) * κM + κP * (decayConst epsM k ω c : ℂ)) * AP = 0 := by
        field_simp [hκP, hκM] at hsum
        linear_combination hsum
      field_simp [hκP, hκM]
      linear_combination -hsum'
  refine ⟨hpart1, ?_, ?_⟩
  · intro μ0 AP AM hμ0 hbc
    have hμc : (μ0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ0.ne'
    obtain ⟨hA, hsum⟩ := (hpart1 (μ0 : ℂ) (μ0 : ℂ) AP AM hμc hμc).mp hbc
    have hpos : 0 < decayConst epsP k ω c / μ0 + decayConst epsM k ω c / μ0 := by positivity
    have hne : (decayConst epsP k ω c : ℂ) / (μ0 : ℂ) + (decayConst epsM k ω c : ℂ) / (μ0 : ℂ) ≠ 0 := by
      have : (decayConst epsP k ω c : ℂ) / (μ0 : ℂ) + (decayConst epsM k ω c : ℂ) / (μ0 : ℂ) =
          ((decayConst epsP k ω c / μ0 + decayConst epsM k ω c / μ0 : ℝ) : ℂ) := by push_cast; rfl
      rw [this]
      exact Complex.ofReal_ne_zero.mpr hpos.ne'
    have hAP0 : AP = 0 := (mul_eq_zero.mp hsum).resolve_left hne
    exact ⟨hAP0, hA ▸ hAP0⟩
  · intro heP heM
    have hePc : (epsP : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr heP
    have heMc : (epsM : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr heM
    constructor
    · constructor
      · rintro ⟨AP, AM, hnz, hbc⟩
        obtain ⟨hA, hsum⟩ := (hpart1 (epsP : ℂ) (epsM : ℂ) AP AM hePc heMc).mp hbc
        have hAPnz : AP ≠ 0 := by
          rcases hnz with h | h
          · exact h
          · exact hA ▸ h
        have hzero : (decayConst epsP k ω c : ℂ) / (epsP : ℂ) +
            (decayConst epsM k ω c : ℂ) / (epsM : ℂ) = 0 :=
          (mul_eq_zero.mp hsum).resolve_right hAPnz
        have hreal : decayConst epsP k ω c / epsP + decayConst epsM k ω c / epsM = 0 := by
          apply Complex.ofReal_injective
          push_cast
          exact hzero
        field_simp [heP, heM, hβM.ne'] at hreal ⊢
        linarith
      · intro hdisp
        refine ⟨1, 1, Or.inl one_ne_zero, (hpart1 (epsP : ℂ) (epsM : ℂ) 1 1 hePc heMc).mpr ⟨rfl, ?_⟩⟩
        rw [mul_one]
        have hreal : decayConst epsP k ω c / epsP + decayConst epsM k ω c / epsM = 0 := by
          field_simp [heP, heM, hβM.ne'] at hdisp ⊢
          linarith
        have : (decayConst epsP k ω c : ℂ) / (epsP : ℂ) + (decayConst epsM k ω c : ℂ) / (epsM : ℂ) =
            ((decayConst epsP k ω c / epsP + decayConst epsM k ω c / epsM : ℝ) : ℂ) := by
          push_cast; rfl
        rw [this, hreal, ofReal_zero]
    · have hwc : 0 < ω / c := div_pos hω hc
      constructor
      · intro hdisp
        have hdiv_neg : epsP / epsM < 0 := by
          rw [hdisp]
          have : 0 < decayConst epsP k ω c / decayConst epsM k ω c := div_pos hβP hβM
          linarith
        have hprod_neg : epsP * epsM < 0 := by
          have : epsP * epsM = (epsP / epsM) * epsM ^ 2 := by field_simp [heM]
          rw [this]
          exact mul_neg_of_neg_of_pos hdiv_neg (sq_pos_of_ne_zero heM)
        have hne_diff : epsP - epsM ≠ 0 := by
          intro h
          have : epsP = epsM := sub_eq_zero.mp h
          rw [this] at hprod_neg
          nlinarith [sq_nonneg epsM]
        have hsq : (epsP / epsM) ^ 2 = (decayConst epsP k ω c / decayConst epsM k ω c) ^ 2 := by
          rw [hdisp, neg_sq]
        have hsq' : epsP ^ 2 * (k ^ 2 - epsM * (ω / c) ^ 2) =
            epsM ^ 2 * (k ^ 2 - epsP * (ω / c) ^ 2) := by
          rw [div_pow, div_pow, hβP_sq, hβM_sq] at hsq
          have h1 : epsM ^ 2 ≠ 0 := pow_ne_zero 2 heM
          have h2 : k ^ 2 - epsM * (ω / c) ^ 2 ≠ 0 := hM.ne'
          linear_combination (div_eq_div_iff h1 h2).mp hsq
        have hfac : (epsP - epsM) * ((epsP + epsM) * k ^ 2 - epsP * epsM * (ω / c) ^ 2) = 0 := by
          linarith
        have hlin : (epsP + epsM) * k ^ 2 = epsP * epsM * (ω / c) ^ 2 := by
          have := (mul_eq_zero.mp hfac).resolve_left hne_diff
          linarith
        have hsum_ne : epsP + epsM ≠ 0 := by
          intro hsum0
          rw [hsum0, zero_mul] at hlin
          have : epsP * epsM * (ω / c) ^ 2 < 0 := mul_neg_of_neg_of_pos hprod_neg (sq_pos_of_pos hwc)
          linarith
        have hksq_raw : k ^ 2 = epsP * epsM / (epsP + epsM) * (ω / c) ^ 2 := by
          rw [div_mul_eq_mul_div, eq_div_iff hsum_ne]
          linarith
        have hfrac_nonneg : 0 ≤ epsP * epsM / (epsP + epsM) := by
          have h0 : 0 ≤ epsP * epsM / (epsP + epsM) * (ω / c) ^ 2 := hksq_raw ▸ sq_nonneg k
          exact nonneg_of_mul_nonneg_left h0 (sq_pos_of_pos hwc)
        have hksq : k ^ 2 = (Real.sqrt (epsP * epsM / (epsP + epsM)) * (ω / c)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hfrac_nonneg, hksq_raw]
        exact ⟨hprod_neg, hsum_ne, sq_eq_sq_iff_eq_or_eq_neg.mp hksq⟩
      · rintro ⟨hprod_neg, hsum_ne, hk⟩
        have hdiv_neg : epsP / epsM < 0 := by
          have : epsP / epsM = (epsP * epsM) / epsM ^ 2 := by field_simp [heM]
          rw [this]
          exact div_neg_of_neg_of_pos hprod_neg (sq_pos_of_ne_zero heM)
        have hksq : k ^ 2 = epsP * epsM / (epsP + epsM) * (ω / c) ^ 2 := by
          have hnonneg : 0 ≤ epsP * epsM / (epsP + epsM) := by
            by_contra hlt
            push Not at hlt
            have h0 : Real.sqrt (epsP * epsM / (epsP + epsM)) = 0 := Real.sqrt_eq_zero_of_nonpos hlt.le
            have hk0 : k = 0 := by
              rcases hk with h | h <;> rw [h, h0, zero_mul] <;> ring
            rw [hk0, zero_pow two_ne_zero, zero_sub] at hP hM
            have hP' : epsP < 0 := by nlinarith [sq_pos_of_pos hwc]
            have hM' : epsM < 0 := by nlinarith [sq_pos_of_pos hwc]
            nlinarith
          rcases hk with h | h
          · rw [h, mul_pow, Real.sq_sqrt hnonneg]
          · rw [h, neg_sq, mul_pow, Real.sq_sqrt hnonneg]
        have hsq : (epsP / epsM) ^ 2 = (-(decayConst epsP k ω c / decayConst epsM k ω c)) ^ 2 := by
          rw [neg_sq, div_pow, div_pow, hβP_sq, hβM_sq, hksq]
          have h1 : epsM ^ 2 ≠ 0 := pow_ne_zero 2 heM
          have h2 : epsP * epsM / (epsP + epsM) * (ω / c) ^ 2 - epsM * (ω / c) ^ 2 ≠ 0 := by
            rw [← hksq]; exact hM.ne'
          rw [div_eq_div_iff h1 h2]
          field_simp [hsum_ne]
          ring
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
        · exact h
        · exfalso
          have hpos : 0 < decayConst epsP k ω c / decayConst epsM k ω c := div_pos hβP hβM
          linarith
