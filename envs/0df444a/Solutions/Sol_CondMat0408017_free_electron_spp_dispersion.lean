-- Prove2me | solution 1 for CondMat0408017.free_electron_spp_dispersion
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:35:35.0538+00:00
-- url     : https://prove2.me/submissions/5f8d6d87-bd0f-4199-afb2-ddbe08c86373

import Mathlib
import Definitions.Def_CondMat0408017_Basic
import Theorems.Thm_CondMat0408017_planar_spp_condition

open MeasureTheory Filter Topology Complex CondMat0408017

private lemma omegaSP_disc_pos (epsInf ωp c k : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) (hk : 0 < k) :
    0 < (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 - 4 * k ^ 2 * c ^ 2 * ωp ^ 2 := by
  have h1 : (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 - 4 * k ^ 2 * c ^ 2 * ωp ^ 2 =
      (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) - ωp ^ 2) ^ 2 +
        4 * k ^ 2 * c ^ 2 * ωp ^ 2 / epsInf := by
    field_simp [he.ne']
    ring
  rw [h1]
  have hpos : 0 < 4 * k ^ 2 * c ^ 2 * ωp ^ 2 / epsInf := by positivity
  linarith [sq_nonneg (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) - ωp ^ 2)]

private lemma omegaSP_inner_pos (epsInf ωp c k : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) (hk : 0 < k) :
    0 < 1 / 2 * (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) -
      1 / 2 * Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
        4 * k ^ 2 * c ^ 2 * ωp ^ 2) := by
  set B := k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2
  set D := 4 * k ^ 2 * c ^ 2 * ωp ^ 2
  have hB : 0 < B := by positivity
  have hD : 0 < D := by positivity
  have hlt : Real.sqrt (B ^ 2 - D) < B := by
    rw [Real.sqrt_lt' hB]
    linarith
  linarith

private lemma omegaSP_inner_eq_div (epsInf ωp c k : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) (hk : 0 < k) :
    1 / 2 * (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) -
        1 / 2 * Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
          4 * k ^ 2 * c ^ 2 * ωp ^ 2) =
      2 * k ^ 2 * c ^ 2 * ωp ^ 2 /
        ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) +
          Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
            4 * k ^ 2 * c ^ 2 * ωp ^ 2)) := by
  set B := k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2
  set D := 4 * k ^ 2 * c ^ 2 * ωp ^ 2
  have hdisc : 0 ≤ B ^ 2 - D := (omegaSP_disc_pos epsInf ωp c k he hp hc hk).le
  have hB : 0 < B := by positivity
  have hden : 0 < B + Real.sqrt (B ^ 2 - D) := by positivity
  have hsq : Real.sqrt (B ^ 2 - D) ^ 2 = B ^ 2 - D := Real.sq_sqrt hdisc
  have hD_eq : 2 * k ^ 2 * c ^ 2 * ωp ^ 2 = D / 2 := by simp only [D]; ring
  rw [hD_eq]
  field_simp [hden.ne']
  nlinarith

private lemma omegaSP_sq (epsInf ωp c k : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) (hk : 0 < k) :
    omegaSP epsInf ωp c k ^ 2 =
      1 / 2 * (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) -
        1 / 2 * Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
          4 * k ^ 2 * c ^ 2 * ωp ^ 2) :=
  Real.sq_sqrt (omegaSP_inner_pos epsInf ωp c k he hp hc hk).le

private lemma omegaSP_sq_lt_kc_sq (epsInf ωp c k : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) (hk : 0 < k) :
    omegaSP epsInf ωp c k ^ 2 < (k * c) ^ 2 := by
  rw [omegaSP_sq epsInf ωp c k he hp hc hk]
  set B := k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2
  set D := 4 * k ^ 2 * c ^ 2 * ωp ^ 2
  have hdisc : 0 < B ^ 2 - D := omegaSP_disc_pos epsInf ωp c k he hp hc hk
  have hP : (B - 2 * k ^ 2 * c ^ 2) ^ 2 < B ^ 2 - D := by
    have hcalc : (B ^ 2 - D) - (B - 2 * k ^ 2 * c ^ 2) ^ 2 = 4 * k ^ 4 * c ^ 4 / epsInf := by
      simp only [B, D]
      field_simp [he.ne']
      ring
    have hpos : 0 < 4 * k ^ 4 * c ^ 4 / epsInf := by positivity
    linarith
  have hsqrt : B - 2 * k ^ 2 * c ^ 2 < Real.sqrt (B ^ 2 - D) := by
    by_cases hle : B - 2 * k ^ 2 * c ^ 2 ≤ 0
    · linarith [Real.sqrt_pos.mpr hdisc]
    · push Not at hle
      rw [← Real.sqrt_sq hle.le]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hP
  have hkc : (k * c) ^ 2 = k ^ 2 * c ^ 2 := by ring
  linarith

private lemma omegaSP_sq_lt_asymp (epsInf ωp c k : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) (hk : 0 < k) :
    omegaSP epsInf ωp c k ^ 2 < epsInf / (epsInf + 1) * ωp ^ 2 := by
  rw [omegaSP_sq epsInf ωp c k he hp hc hk]
  set B := k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2
  set D := 4 * k ^ 2 * c ^ 2 * ωp ^ 2
  set L := epsInf / (epsInf + 1) * ωp ^ 2
  have he1 : 0 < epsInf + 1 := by linarith
  have hdisc : 0 < B ^ 2 - D := omegaSP_disc_pos epsInf ωp c k he hp hc hk
  have hP : (B - 2 * L) ^ 2 < B ^ 2 - D := by
    have hcalc : (B ^ 2 - D) - (B - 2 * L) ^ 2 =
        4 * epsInf / (epsInf + 1) ^ 2 * ωp ^ 4 := by
      simp only [B, D, L]
      field_simp [he.ne', he1.ne']
      ring
    have hpos : 0 < 4 * epsInf / (epsInf + 1) ^ 2 * ωp ^ 4 := by positivity
    linarith
  have hsqrt : B - 2 * L < Real.sqrt (B ^ 2 - D) := by
    by_cases hle : B - 2 * L ≤ 0
    · linarith [Real.sqrt_pos.mpr hdisc]
    · push Not at hle
      rw [← Real.sqrt_sq hle.le]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hP
  linarith

theorem solution (epsInf ωp c : ℝ) (he : 0 < epsInf) (hp : 0 < ωp)
    (hc : 0 < c) :
    (∀ k ω : ℝ, 0 < k → 0 < ω →
      (IsPlanarSPP 1 (freeElectronEps epsInf ωp ω) k ω c ↔ ω = omegaSP epsInf ωp c k)) ∧
    Tendsto (fun k => omegaSP epsInf ωp c k / (k * c)) (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (omegaSP epsInf ωp c) atTop (𝓝 (Real.sqrt (epsInf / (epsInf + 1)) * ωp)) ∧
    ∀ k : ℝ, 0 < k → omegaSP epsInf ωp c k < k * c := by
  have he1 : 0 < epsInf + 1 := by linarith
  have hpart4 : ∀ k : ℝ, 0 < k → omegaSP epsInf ωp c k < k * c := by
    intro k hk
    have hlt := omegaSP_sq_lt_kc_sq epsInf ωp c k he hp hc hk
    have hkc : 0 < k * c := mul_pos hk hc
    have hnn : 0 ≤ omegaSP epsInf ωp c k := Real.sqrt_nonneg _
    nlinarith
  refine ⟨?_, ?_, ?_, hpart4⟩
  · -- Part 1: IsPlanarSPP ↔ ω = omegaSP
    intro k ω hk hω
    set epsM := freeElectronEps epsInf ωp ω
    set B := k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2
    set D := 4 * k ^ 2 * c ^ 2 * ωp ^ 2
    have hdisc : 0 < B ^ 2 - D := omegaSP_disc_pos epsInf ωp c k he hp hc hk
    have hinner : 0 < 1 / 2 * B - 1 / 2 * Real.sqrt (B ^ 2 - D) :=
      omegaSP_inner_pos epsInf ωp c k he hp hc hk
    have hquad_equiv :
        (1 + epsM ≠ 0 ∧ k ^ 2 = epsM / (1 + epsM) * (ω / c) ^ 2) ↔
          (1 + epsM ≠ 0 ∧ (ω ^ 2) ^ 2 - B * ω ^ 2 + k ^ 2 * c ^ 2 * ωp ^ 2 = 0) := by
      constructor <;> rintro ⟨h1e, heq⟩ <;> refine ⟨h1e, ?_⟩
      · have h1e' : (1 + epsInf) * ω ^ 2 - epsInf * ωp ^ 2 ≠ 0 := by
          intro h0
          apply h1e
          simp only [epsM, freeElectronEps]
          field_simp [hω.ne']
          linarith
        have h1e'' : ω ^ 2 + epsInf * (ω ^ 2 - ωp ^ 2) ≠ 0 := by
          intro h0; exact h1e' (by linarith)
        simp only [epsM, freeElectronEps] at heq
        field_simp [h1e, h1e', h1e'', hω.ne', hc.ne', he.ne'] at heq ⊢
        simp only [B]
        field_simp [he.ne']
        nlinarith
      · simp only [epsM, freeElectronEps]
        simp only [B] at heq
        have h1e' : (1 + epsInf) * ω ^ 2 - epsInf * ωp ^ 2 ≠ 0 := by
          intro h0
          apply h1e
          simp only [epsM, freeElectronEps]
          field_simp [hω.ne']
          linarith
        have h1e'' : ω ^ 2 + epsInf * (ω ^ 2 - ωp ^ 2) ≠ 0 := by
          intro h0; exact h1e' (by linarith)
        field_simp [h1e, h1e', h1e'', hω.ne', hc.ne', he.ne'] at heq ⊢
        nlinarith
    constructor
    · rintro ⟨hP, hM, hex⟩
      have hcond := (planar_spp_condition 1 epsM k ω c hc hω hP hM).2.2
      have heM_ne : epsM ≠ 0 := by
        intro h0
        obtain ⟨AP, AM, hnz, hbc⟩ := hex
        have hβP : 0 < decayConst 1 k ω c := Real.sqrt_pos.mpr hP
        obtain ⟨hval, hder⟩ := hbc 0
        simp only [planarModeUpper, planarModeLower, ofReal_zero, mul_zero, Complex.exp_zero,
          mul_one, h0, div_zero, ofReal_one, div_one] at hval hder
        have hdu : deriv (planarModeUpper AP (decayConst 1 k ω c) k 0) 0 =
            -(decayConst 1 k ω c : ℂ) * AP := by
          have hd1 : HasDerivAt (fun z : ℂ => -(decayConst 1 k ω c : ℂ) * z)
              (-(decayConst 1 k ω c : ℂ)) (0 : ℂ) := by
            simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-(decayConst 1 k ω c : ℂ))
          have hd2 : HasDerivAt (fun z : ℂ => AP * cexp (-(decayConst 1 k ω c : ℂ) * z) *
              cexp (I * (k : ℂ) * (0 : ℝ)))
              (AP * (cexp (-(decayConst 1 k ω c : ℂ) * 0) * -(decayConst 1 k ω c : ℂ)) *
                cexp (I * (k : ℂ) * (0 : ℝ))) (0 : ℂ) :=
            ((hd1.cexp).const_mul AP).mul_const (cexp (I * (k : ℂ) * (0 : ℝ)))
          have hd3 : HasDerivAt (planarModeUpper AP (decayConst 1 k ω c) k 0)
              (AP * (cexp (-(decayConst 1 k ω c : ℂ) * 0) * -(decayConst 1 k ω c : ℂ)) *
                cexp (I * (k : ℂ) * (0 : ℝ))) 0 := by
            rw [hasDerivAt_iff_tendsto_slope_zero]
            have h2' := hasDerivAt_iff_tendsto_slope_zero.mp hd2.comp_ofReal
            simpa [planarModeUpper, Complex.real_smul] using h2'
          rw [hd3.deriv]
          simp only [ofReal_zero, mul_zero, Complex.exp_zero, one_mul, mul_one]
          ring
        rw [hdu] at hder
        have hne : -(decayConst 1 k ω c : ℂ) ≠ 0 :=
          neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hβP.ne')
        have hAP0 : AP = 0 := (mul_eq_zero.mp hder).resolve_left hne
        exact hnz.elim (· hAP0) (· (hval ▸ hAP0))
      have ⟨h1, h2⟩ := hcond one_ne_zero heM_ne
      obtain ⟨hprod, hsum, hk_eq⟩ := h2.mp (h1.mp hex)
      have heM_neg : epsM < 0 := by linarith
      have h1e_neg : 1 + epsM < 0 := by
        by_contra hge
        push Not at hge
        have hpos : 0 < 1 + epsM := lt_of_le_of_ne hge hsum.symm
        have hneg : 1 * epsM / (1 + epsM) < 0 := div_neg_of_neg_of_pos hprod hpos
        have hsqrt0 : Real.sqrt (1 * epsM / (1 + epsM)) = 0 :=
          Real.sqrt_eq_zero_of_nonpos hneg.le
        rcases hk_eq with h | h <;> rw [hsqrt0, zero_mul] at h <;> linarith
      have hksq : k ^ 2 = epsM / (1 + epsM) * (ω / c) ^ 2 := by
        have hnn : 0 ≤ 1 * epsM / (1 + epsM) := by
          rw [one_mul]
          exact div_nonneg_of_nonpos heM_neg.le h1e_neg.le
        rcases hk_eq with h | h
        · rw [h, mul_pow, Real.sq_sqrt hnn, one_mul]
        · rw [h, neg_sq, mul_pow, Real.sq_sqrt hnn, one_mul]
      have hquad : (ω ^ 2) ^ 2 - B * ω ^ 2 + k ^ 2 * c ^ 2 * ωp ^ 2 = 0 :=
        (hquad_equiv.mp ⟨hsum, hksq⟩).2
      have hω_lt : ω ^ 2 < epsInf / (epsInf + 1) * ωp ^ 2 := by
        simp only [epsM, freeElectronEps] at h1e_neg
        have h1 : (1 + epsInf) * ω ^ 2 < epsInf * ωp ^ 2 := by
          have : 1 + epsInf * (1 - ωp ^ 2 / ω ^ 2) =
              ((1 + epsInf) * ω ^ 2 - epsInf * ωp ^ 2) / ω ^ 2 := by
            field_simp [hω.ne']; ring
          rw [this] at h1e_neg
          have := (div_neg_iff.mp h1e_neg).resolve_left (by intro h; linarith [sq_pos_of_pos hω])
          linarith
        rw [div_mul_eq_mul_div, lt_div_iff₀ he1]
        linarith
      have hsq_eq : (2 * ω ^ 2 - B) ^ 2 = B ^ 2 - D := by
        have hD : D = 4 * (k ^ 2 * c ^ 2 * ωp ^ 2) := by simp only [D]; ring
        linarith
      have hroot : 2 * ω ^ 2 - B = Real.sqrt (B ^ 2 - D) ∨
          2 * ω ^ 2 - B = -Real.sqrt (B ^ 2 - D) := by
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        rw [hsq_eq, Real.sq_sqrt hdisc.le]
      rcases hroot with hplus | hminus
      · exfalso
        have hP : (B - 2 * (epsInf / (epsInf + 1) * ωp ^ 2)) ^ 2 < B ^ 2 - D := by
          have hcalc : (B ^ 2 - D) - (B - 2 * (epsInf / (epsInf + 1) * ωp ^ 2)) ^ 2 =
              4 * epsInf / (epsInf + 1) ^ 2 * ωp ^ 4 := by
            simp only [B, D]; field_simp [he.ne', he1.ne']; ring
          have hpos : 0 < 4 * epsInf / (epsInf + 1) ^ 2 * ωp ^ 4 := by positivity
          linarith
        have hsqrt_gt : 2 * (epsInf / (epsInf + 1) * ωp ^ 2) - B < Real.sqrt (B ^ 2 - D) := by
          by_cases hle : 2 * (epsInf / (epsInf + 1) * ωp ^ 2) - B ≤ 0
          · linarith [Real.sqrt_pos.mpr hdisc]
          · push Not at hle
            rw [← Real.sqrt_sq hle.le]
            apply Real.sqrt_lt_sqrt (sq_nonneg _)
            have : (2 * (epsInf / (epsInf + 1) * ωp ^ 2) - B) ^ 2 =
                (B - 2 * (epsInf / (epsInf + 1) * ωp ^ 2)) ^ 2 := by ring
            rw [this]
            exact hP
        linarith
      · have hωsq : ω ^ 2 = omegaSP epsInf ωp c k ^ 2 := by
          rw [omegaSP_sq epsInf ωp c k he hp hc hk]
          change ω ^ 2 = 1 / 2 * B - 1 / 2 * Real.sqrt (B ^ 2 - D)
          linarith
        have hsp_pos : 0 < omegaSP epsInf ωp c k := Real.sqrt_pos.mpr hinner
        exact (sq_eq_sq₀ hω.le hsp_pos.le).mp hωsq
    · intro hωeq
      subst hωeq
      have hω_sq : omegaSP epsInf ωp c k ^ 2 = 1 / 2 * B - 1 / 2 * Real.sqrt (B ^ 2 - D) :=
        omegaSP_sq epsInf ωp c k he hp hc hk
      have hω_lt_kc := omegaSP_sq_lt_kc_sq epsInf ωp c k he hp hc hk
      have hω_lt_as := omegaSP_sq_lt_asymp epsInf ωp c k he hp hc hk
      have h1e_neg : 1 + epsM < 0 := by
        simp only [epsM, freeElectronEps]
        have h1 : (1 + epsInf) * omegaSP epsInf ωp c k ^ 2 < epsInf * ωp ^ 2 := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ he1] at hω_lt_as
          linarith
        have : 1 + epsInf * (1 - ωp ^ 2 / omegaSP epsInf ωp c k ^ 2) =
            ((1 + epsInf) * omegaSP epsInf ωp c k ^ 2 - epsInf * ωp ^ 2) /
              omegaSP epsInf ωp c k ^ 2 := by
          field_simp [hω.ne']; ring
        rw [this]
        exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hω)
      have heM_neg : epsM < 0 := by linarith
      have hP : 0 < k ^ 2 - 1 * (omegaSP epsInf ωp c k / c) ^ 2 := by
        rw [one_mul, div_pow]
        have : k ^ 2 - omegaSP epsInf ωp c k ^ 2 / c ^ 2 =
            ((k * c) ^ 2 - omegaSP epsInf ωp c k ^ 2) / c ^ 2 := by
          field_simp [hc.ne']
        rw [this]
        exact div_pos (by linarith) (sq_pos_of_pos hc)
      have hM : 0 < k ^ 2 - epsM * (omegaSP epsInf ωp c k / c) ^ 2 := by
        have : epsM * (omegaSP epsInf ωp c k / c) ^ 2 < 0 :=
          mul_neg_of_neg_of_pos heM_neg (sq_pos_of_pos (div_pos hω hc))
        nlinarith [sq_pos_of_pos hk]
      refine ⟨hP, hM, ?_⟩
      have ⟨h1, h2⟩ := (planar_spp_condition 1 epsM k (omegaSP epsInf ωp c k) c hc hω hP hM).2.2
        one_ne_zero heM_neg.ne
      apply h1.mpr
      apply h2.mpr
      refine ⟨by linarith, h1e_neg.ne, Or.inl ?_⟩
      have hquad : (omegaSP epsInf ωp c k ^ 2) ^ 2 - B * omegaSP epsInf ωp c k ^ 2 +
          k ^ 2 * c ^ 2 * ωp ^ 2 = 0 := by
        rw [hω_sq]
        have hsq : Real.sqrt (B ^ 2 - D) ^ 2 = B ^ 2 - D := Real.sq_sqrt hdisc.le
        have hD : D = 4 * (k ^ 2 * c ^ 2 * ωp ^ 2) := by simp only [D]; ring
        nlinarith
      have hksq : k ^ 2 = epsM / (1 + epsM) * (omegaSP epsInf ωp c k / c) ^ 2 :=
        (hquad_equiv.mpr ⟨h1e_neg.ne, hquad⟩).2
      have hnn : 0 ≤ 1 * epsM / (1 + epsM) := by
        rw [one_mul]; exact div_nonneg_of_nonpos heM_neg.le h1e_neg.le
      have hrhs_pos : 0 ≤ Real.sqrt (1 * epsM / (1 + epsM)) * (omegaSP epsInf ωp c k / c) := by
        positivity
      have hsq_eq : k ^ 2 = (Real.sqrt (1 * epsM / (1 + epsM)) * (omegaSP epsInf ωp c k / c)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hnn, one_mul, hksq]
      exact (sq_eq_sq₀ hk.le hrhs_pos).mp hsq_eq
  · -- Part 2: k → 0+ limit
    let g : ℝ → ℝ := fun k =>
      Real.sqrt (2 * ωp ^ 2 /
        ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) +
          Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
            4 * k ^ 2 * c ^ 2 * ωp ^ 2)))
    have hcont : ContinuousAt g 0 := by
      have hden0 : ((0 : ℝ) ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) +
          Real.sqrt (((0 : ℝ) ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
            4 * (0 : ℝ) ^ 2 * c ^ 2 * ωp ^ 2) ≠ 0 := by
        simp only [zero_pow two_ne_zero, zero_mul, mul_zero, zero_div, zero_add, sub_zero,
          Real.sqrt_sq (sq_nonneg ωp)]
        positivity
      fun_prop (disch := assumption)
    have hg0 : g 0 = 1 := by
      simp only [g, zero_pow two_ne_zero, zero_mul, mul_zero, zero_div, zero_add, sub_zero,
        Real.sqrt_sq (sq_nonneg ωp)]
      have : 2 * ωp ^ 2 / (ωp ^ 2 + ωp ^ 2) = 1 := by
        field_simp [hp.ne']
        ring
      rw [this, Real.sqrt_one]
    have htend : Tendsto g (𝓝[>] 0) (𝓝 1) := by
      rw [← hg0]
      exact hcont.tendsto.mono_left nhdsWithin_le_nhds
    refine htend.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with k hk
    change 0 < k at hk
    have hkc : 0 < k * c := mul_pos hk hc
    have hinner_eq := omegaSP_inner_eq_div epsInf ωp c k he hp hc hk
    simp only [g, omegaSP]
    rw [hinner_eq, ← Real.sqrt_sq hkc.le, ← Real.sqrt_div (by positivity)]
    congr 1
    field_simp [hkc.ne']
  · -- Part 3: k → ∞ limit
    let h : ℝ → ℝ := fun u =>
      Real.sqrt (2 * ωp ^ 2 /
        (((1 + epsInf) / epsInf + u) +
          Real.sqrt (((1 + epsInf) / epsInf + u) ^ 2 - 4 * u)))
    have hcont : ContinuousAt h 0 := by
      have hden0 : ((1 + epsInf) / epsInf + (0 : ℝ)) +
          Real.sqrt (((1 + epsInf) / epsInf + (0 : ℝ)) ^ 2 - 4 * (0 : ℝ)) ≠ 0 := by
        simp only [add_zero, mul_zero, sub_zero]
        have hpos : 0 < (1 + epsInf) / epsInf := by positivity
        rw [Real.sqrt_sq hpos.le]
        linarith
      fun_prop (disch := assumption)
    have hh0 : h 0 = Real.sqrt (epsInf / (epsInf + 1)) * ωp := by
      simp only [h, add_zero, mul_zero, sub_zero]
      have hpos : 0 < (1 + epsInf) / epsInf := by positivity
      rw [Real.sqrt_sq hpos.le]
      have heq : 2 * ωp ^ 2 / ((1 + epsInf) / epsInf + (1 + epsInf) / epsInf) =
          epsInf / (epsInf + 1) * ωp ^ 2 := by
        field_simp [he.ne', he1.ne']
        ring
      rw [heq, Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le]
    have hu : Tendsto (fun k : ℝ => ωp ^ 2 / (k ^ 2 * c ^ 2)) atTop (𝓝 0) := by
      have hkc : Tendsto (fun k : ℝ => k ^ 2 * c ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).atTop_mul_const (sq_pos_of_pos hc)
      exact tendsto_const_nhds.div_atTop hkc
    have htend : Tendsto (fun k => h (ωp ^ 2 / (k ^ 2 * c ^ 2))) atTop
        (𝓝 (Real.sqrt (epsInf / (epsInf + 1)) * ωp)) := by
      rw [← hh0]
      exact hcont.tendsto.comp hu
    refine htend.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hinner_eq := omegaSP_inner_eq_div epsInf ωp c k he hp hc hk
    simp only [h, omegaSP]
    rw [hinner_eq]
    congr 1
    have hk2c2 : 0 < k ^ 2 * c ^ 2 := by positivity
    have hrad : Real.sqrt (((1 + epsInf) / epsInf + ωp ^ 2 / (k ^ 2 * c ^ 2)) ^ 2 -
        4 * (ωp ^ 2 / (k ^ 2 * c ^ 2))) =
        Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
          4 * k ^ 2 * c ^ 2 * ωp ^ 2) / (k ^ 2 * c ^ 2) := by
      have hdiv : Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
          4 * k ^ 2 * c ^ 2 * ωp ^ 2) / (k ^ 2 * c ^ 2) =
          Real.sqrt (((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
            4 * k ^ 2 * c ^ 2 * ωp ^ 2) / (k ^ 2 * c ^ 2) ^ 2) := by
        rw [Real.sqrt_div (omegaSP_disc_pos epsInf ωp c k he hp hc hk).le, Real.sqrt_sq hk2c2.le]
      rw [hdiv]
      congr 1
      field_simp [hk2c2.ne', he.ne']
    rw [hrad]
    have hden : 0 < (k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) +
        Real.sqrt ((k ^ 2 * c ^ 2 / epsInf * (1 + epsInf) + ωp ^ 2) ^ 2 -
          4 * k ^ 2 * c ^ 2 * ωp ^ 2) := by positivity
    field_simp [hk2c2.ne', he.ne', hden.ne']
