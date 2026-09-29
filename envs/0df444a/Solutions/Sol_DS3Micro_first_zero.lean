-- Prove2me | solution 1 for DS3Micro.first_zero
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:08:32.415485+00:00
-- url     : https://prove2.me/submissions/ebd5fc03-69b6-4eb5-8977-8be6f91cc51a

import Mathlib
import Definitions.Def_dS3_microstates

open Complex

namespace DS3Micro

theorem aux_fz_E0 (b : ℂ) (β : ℝ) (hβ : 0 < β) (hb : b ^ 2 = Complex.I * (β : ℂ)) :
    E0 b = ((2 * Real.cosh (Real.pi / β) : ℝ) : ℂ) := by
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have h1 : (Real.pi : ℂ) * (b ^ 2)⁻¹ = ((-(Real.pi / β) : ℝ) : ℂ) * Complex.I := by
    rw [hb]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  unfold E0
  rw [h1, Complex.cos_mul_I, ← Complex.ofReal_cosh, Real.cosh_neg]
  push_cast
  ring

theorem aux_fz_rho (b : ℂ) (β : ℝ) (hb : b ^ 2 = Complex.I * (β : ℂ)) (E : ℝ) :
    rho0 b E = ((2 / Real.pi * Real.sinh (Real.pi * β) *
      Real.sin (β * Real.arcosh (E / 2)) : ℝ) : ℂ) := by
  have h1 : -Complex.I * (Real.pi : ℂ) * b ^ 2 = ((Real.pi * β : ℝ) : ℂ) := by
    rw [hb]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have h2 : -Complex.I * b ^ 2 * (Real.arcosh (E / 2) : ℂ) =
      ((β * Real.arcosh (E / 2) : ℝ) : ℂ) := by
    rw [hb]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  unfold rho0
  rw [h1, h2, ← Complex.ofReal_sinh, ← Complex.ofReal_sin]
  push_cast
  ring

end DS3Micro

open DS3Micro

theorem solution (b : ℂ) (hb : InRegime b) :
    (E0 b).im = 0 ∧ 2 < (E0 b).re ∧ rho0 b (E0 b).re = 0 ∧
      ∀ E : ℝ, 2 < E → E < (E0 b).re → (rho0 b E).im = 0 ∧ 0 < (rho0 b E).re := by
  obtain ⟨β, hβ, hb2⟩ := hb
  have hE0 := aux_fz_E0 b β hβ hb2
  have hρ := aux_fz_rho b β hb2
  have hq : 0 < Real.pi / β := div_pos Real.pi_pos hβ
  have hcosh : 1 < Real.cosh (Real.pi / β) := Real.one_lt_cosh.mpr hq.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hE0, Complex.ofReal_im]
  · rw [hE0, Complex.ofReal_re]; linarith
  · rw [hE0, Complex.ofReal_re, hρ]
    have : (2 * Real.cosh (Real.pi / β)) / 2 = Real.cosh (Real.pi / β) := by ring
    rw [this, Real.arcosh_cosh hq.le]
    have : β * (Real.pi / β) = Real.pi := by field_simp
    rw [this, Real.sin_pi]
    simp
  · intro E hE2 hEE0
    rw [hE0, Complex.ofReal_re] at hEE0
    rw [hρ, Complex.ofReal_im, Complex.ofReal_re]
    refine ⟨rfl, ?_⟩
    have ha0 : 0 < Real.arcosh (E / 2) := Real.arcosh_pos (by linarith)
    have ha1 : Real.arcosh (E / 2) < Real.pi / β := by
      have h := (Real.arcosh_lt_arcosh (x := E / 2) (y := Real.cosh (Real.pi / β))
        (by linarith) (by linarith)).mpr (by linarith)
      rwa [Real.arcosh_cosh hq.le] at h
    have hs1 : 0 < β * Real.arcosh (E / 2) := mul_pos hβ ha0
    have hs2 : β * Real.arcosh (E / 2) < Real.pi := by
      have := mul_lt_mul_of_pos_left ha1 hβ
      rwa [show β * (Real.pi / β) = Real.pi by field_simp] at this
    have hsin : 0 < Real.sin (β * Real.arcosh (E / 2)) := Real.sin_pos_of_pos_of_lt_pi hs1 hs2
    have hsinh : 0 < Real.sinh (Real.pi * β) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hβ)
    have : 0 < 2 / Real.pi := div_pos two_pos Real.pi_pos
    positivity
