-- Prove2me | solution 1 for CompOpacity.Disclosure.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:42:23.150373+00:00
-- url     : https://prove2.me/submissions/6ea9ea51-f3e7-4ecc-b7ee-653018f8e11d

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model

open CompOpacity.Disclosure in
theorem solution (a q n thetaBar : ℝ) (m : Fin 2 → ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 2) (hq : 0 < q) (hn : 0 < n) (hθ : 0 < thetaBar) (hm : ∀ i, 0 ≤ m i) (s : LinStrat) : IsLinEq a 0 q n thetaBar m s ↔ ∀ i : Fin 2, s.beta i = n / (q + m i + (1 - a) * n) ∧ s.gamma i = m i / ((1 - a) * (q + m i + (1 - a) * n)) ∧ s.h i = q * thetaBar / ((1 - a) * (q + m i + (1 - a) * n)) := by
  have key : IsLinEq a 0 q n thetaBar m s ↔ ∀ i (zz xx : ℝ),
      s.beta i * xx + s.gamma i * zz + s.h i =
        postMean q n thetaBar (m i) zz xx +
          a * (s.beta i * postMean q n thetaBar (m i) zz xx + s.gamma i * zz + s.h i) := by
    constructor
    · intro H i zz xx
      have := H (fun _ => zz) (fun _ => xx) i
      simp only [invest, expK, zero_mul, sub_zero] at this
      exact this
    · intro H z x i
      simp only [invest, expK, zero_mul, sub_zero]
      exact H i (z i) (x i)
  rw [key]
  have h1a : 0 < 1 - a := by linarith
  apply forall_congr'
  intro i
  have hmi := hm i
  set β := s.beta i
  set γ := s.gamma i
  set h := s.h i
  set D := m i + n + q with hD
  set E := q + m i + (1 - a) * n with hE
  have hDp : 0 < D := by rw [hD]; linarith
  have hEp : 0 < E := by rw [hE]; nlinarith
  have hDne : D ≠ 0 := hDp.ne'
  have hEne : E ≠ 0 := hEp.ne'
  have h1ane : (1 - a) ≠ 0 := h1a.ne'
  have hP : ∀ zz xx, postMean q n thetaBar (m i) zz xx * D = m i * zz + n * xx + q * thetaBar := by
    intro zz xx; unfold postMean; rw [← hD]; field_simp
  constructor
  · intro H
    have hpoly : ∀ zz xx, (β * xx + γ * zz + h) * D =
        (1 + a * β) * (m i * zz + n * xx + q * thetaBar) + (a * γ * zz + a * h) * D := by
      intro zz xx
      linear_combination D * H zz xx + (1 + a * β) * hP zz xx
    have e00 := hpoly 0 0
    have e01 := hpoly 0 1
    have e10 := hpoly 1 0
    have hβ : β * E = n := by rw [hE]; rw [hD] at e00 e01; linear_combination e01 - e00
    have hγ' : γ * (1 - a) * D = (1 + a * β) * m i := by linear_combination e10 - e00
    have hh' : h * (1 - a) * D = (1 + a * β) * (q * thetaBar) := by linear_combination e00
    have h1aβ : (1 + a * β) * E = D := by rw [hE, hD]; rw [hE] at hβ; linear_combination a * hβ
    have hγ0 : D * (γ * (1 - a) * E - m i) = 0 := by linear_combination E * hγ' + m i * h1aβ
    have hh0 : D * (h * (1 - a) * E - q * thetaBar) = 0 := by
      linear_combination E * hh' + (q * thetaBar) * h1aβ
    have hγ : γ * (1 - a) * E = m i := by
      have := (mul_eq_zero.1 hγ0).resolve_left hDp.ne'; linarith
    have hh : h * (1 - a) * E = q * thetaBar := by
      have := (mul_eq_zero.1 hh0).resolve_left hDp.ne'; linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [eq_div_iff hEp.ne']; exact hβ
    · rw [eq_div_iff (mul_pos h1a hEp).ne']; linear_combination hγ
    · rw [eq_div_iff (mul_pos h1a hEp).ne']; linear_combination hh
  · rintro ⟨hβ, hγ, hh⟩ zz xx
    have hβ' : β * E = n := by rw [hβ]; field_simp
    have hγ' : γ * ((1 - a) * E) = m i := by rw [hγ]; field_simp
    have hh' : h * ((1 - a) * E) = q * thetaBar := by rw [hh]; field_simp
    have h1aβ : (1 + a * β) * E = D := by rw [hE, hD]; rw [hE] at hβ'; linear_combination a * hβ'
    -- reduce to polynomial identity times D * E
    have hP' := hP zz xx
    set P := postMean q n thetaBar (m i) zz xx
    have goalE : (β * xx + γ * zz + h - (P + a * (β * P + γ * zz + h))) * (D * ((1 - a) * E)) = 0 := by
      have e1 : P * D = m i * zz + n * xx + q * thetaBar := hP'
      linear_combination (D * (1 - a) * xx) * hβ' + ((1 - a) * D * zz) * hγ' + ((1 - a) * D) * hh'
        - ((1 - a) * P * D) * h1aβ - ((1 - a) * D) * e1
    have hne : D * ((1 - a) * E) ≠ 0 := (mul_pos hDp (mul_pos h1a hEp)).ne'
    have := (mul_eq_zero.1 goalE).resolve_right hne
    linarith
