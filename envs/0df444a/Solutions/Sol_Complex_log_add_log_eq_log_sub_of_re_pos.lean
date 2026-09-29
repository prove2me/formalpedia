-- Prove2me | solution 1 for Complex.log_add_log_eq_log_sub_of_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1c6092e1-a17a-5dc8-b15d-50083b5ba3d8

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_log_add_log_eq_log_sub_of_re_pos

set_option autoImplicit false

noncomputable section

open Complex

open scoped Real

namespace DedekindEtaLog

lemma exp_inj_of_im {x y : ℂ} (hx1 : -π < x.im) (hx2 : x.im ≤ π) (hy1 : -π < y.im) (hy2 : y.im ≤ π)
    (h : exp x = exp y) : x = y := by
  rw [← log_exp hx1 hx2, ← log_exp hy1 hy2, h]

lemma arg_mem_of_re_pos {u : ℂ} (hu : 0 < u.re) : -(π / 2) < arg u ∧ arg u < π / 2 :=
  abs_lt.1 (abs_arg_lt_pi_div_two_iff.2 (Or.inl hu))

theorem log_add_log_eq {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re)
    (h : u * v = -I * w) : log u + log v = log w - π * I / 2 := by
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hv0 : v ≠ 0 := fun h0 => by simp [h0] at hv
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw
  obtain ⟨hu1, hu2⟩ := arg_mem_of_re_pos hu
  obtain ⟨hv1, hv2⟩ := arg_mem_of_re_pos hv
  obtain ⟨hw1, hw2⟩ := arg_mem_of_re_pos hw
  have hpi := Real.pi_pos
  refine exp_inj_of_im ?_ ?_ ?_ ?_ ?_
  · simp only [add_im, log_im]; linarith
  · simp only [add_im, log_im]; linarith
  · simp only [sub_im, log_im, div_ofNat_im, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re]; linarith
  · simp only [sub_im, log_im, div_ofNat_im, mul_im, ofReal_re, Complex.I_im, ofReal_im, Complex.I_re]; linarith
  · rw [exp_add, exp_log hu0, exp_log hv0, exp_sub, exp_log hw0, h,
      show π * I / 2 = (π / 2 : ℂ) * I by ring, exp_mul_I]
    have hc : Complex.cos (π / 2 : ℂ) = 0 := by exact_mod_cast Complex.cos_pi_div_two
    have hs : Complex.sin (π / 2 : ℂ) = 1 := by exact_mod_cast Complex.sin_pi_div_two
    rw [hc, hs]
    field_simp
    ring_nf
    simp

end DedekindEtaLog

end

theorem solution {u v w : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (hw : 0 < w.re) (h : u * v = -Complex.I * w) : Complex.log u + Complex.log v = Complex.log w - Real.pi * Complex.I / 2 :=
  DedekindEtaLog.log_add_log_eq hu hv hw h

end S_Complex_log_add_log_eq_log_sub_of_re_pos
end P2MW
export P2MW.S_Complex_log_add_log_eq_log_sub_of_re_pos (solution)
