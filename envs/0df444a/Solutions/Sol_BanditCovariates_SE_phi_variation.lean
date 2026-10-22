-- Prove2me | solution 1 for BanditCovariates.SE.phi_variation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:32:47.425603+00:00
-- url     : https://prove2.me/submissions/1c0e671a-acb5-431c-b352-27dce497ccef

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

set_option autoImplicit false

theorem log_le_div_e (t : ℝ) (ht : 0 < t) : Real.log t ≤ t / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < t / Real.exp 1 by positivity)
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

theorem g_var (t' t : ℝ) (ht' : 0 < t') (htt : t' ≤ t) :
    max (2 * Real.log t) 1 / t ≤ 2 / Real.exp (1 / 2) * (max (2 * Real.log t') 1 / t') := by
  have ht : 0 < t := lt_of_lt_of_le ht' htt
  set E := Real.exp (1 / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : E * E = Real.exp 1 := by rw [hE, ← Real.exp_add]; norm_num
  have hEle : E ≤ 2 := by
    have : E * E < 4 := by rw [hE2]; have := Real.exp_one_lt_d9; linarith
    nlinarith
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by norm_num)
  have hgnn : 0 ≤ max (2 * Real.log t') 1 / t' := by positivity
  by_cases hbig : Real.exp 1 ≤ t'
  · -- both beyond e
    have h1 : Real.log t / t ≤ Real.log t' / t' :=
      Real.log_div_self_antitoneOn (show t' ∈ Set.Ici (Real.exp 1) from hbig)
        (show t ∈ Set.Ici (Real.exp 1) from hbig.trans htt) htt
    have hlog1 : 1 ≤ Real.log t' := by
      have := Real.log_le_log (Real.exp_pos 1) hbig
      rwa [Real.log_exp] at this
    have hlogt : 1 ≤ Real.log t := by linarith [Real.log_le_log ht' htt]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    have : 2 * Real.log t / t ≤ 2 * Real.log t' / t' := by
      rw [mul_div_assoc, mul_div_assoc]; linarith
    have h2 : 1 ≤ 2 / E := by rw [le_div_iff₀ hEpos]; linarith
    calc 2 * Real.log t / t ≤ 2 * Real.log t' / t' := this
      _ = 1 * (2 * Real.log t' / t') := by ring
      _ ≤ 2 / E * (2 * Real.log t' / t') := by
        apply mul_le_mul_of_nonneg_right h2
        have : 0 ≤ 2 * Real.log t' := by linarith
        positivity
  · push_neg at hbig
    by_cases hsmall : 2 * Real.log t ≤ 1
    · rw [max_eq_right hsmall]
      have h1 : 1 / t ≤ 1 / t' := one_div_le_one_div_of_le ht' htt
      have h2 : 1 / t' ≤ max (2 * Real.log t') 1 / t' :=
        div_le_div_of_nonneg_right (le_max_right _ _) ht'.le
      have h3 : 1 ≤ 2 / E := by rw [le_div_iff₀ hEpos]; linarith
      calc 1 / t ≤ max (2 * Real.log t') 1 / t' := h1.trans h2
        _ = 1 * (max (2 * Real.log t') 1 / t') := by ring
        _ ≤ 2 / E * (max (2 * Real.log t') 1 / t') := mul_le_mul_of_nonneg_right h3 hgnn
    · push_neg at hsmall
      rw [max_eq_left hsmall.le]
      have hA : 2 * Real.log t / t ≤ 2 / Real.exp 1 := by
        rw [div_le_div_iff₀ ht (Real.exp_pos 1)]
        have := log_le_div_e t ht
        rw [le_div_iff₀ (Real.exp_pos 1)] at this
        nlinarith
      -- lower bound g(t') ≥ 1/E
      have hB : 1 / E ≤ max (2 * Real.log t') 1 / t' := by
        rw [div_le_div_iff₀ hEpos ht']
        by_cases hle : t' ≤ E
        · have := le_max_right (2 * Real.log t') 1
          nlinarith
        · push_neg at hle
          have hlog : Real.log (t' / E) ≥ 1 - E / t' := by
            have := Real.one_sub_inv_le_log_of_pos (show 0 < t' / E by positivity)
            rw [inv_div] at this
            exact this
          rw [Real.log_div ht'.ne' hEpos.ne', hE, Real.log_exp] at hlog
          have hlog2 : 2 * Real.log t' ≥ 3 - 2 * E / t' := by
            have : 2 * (Real.log t' - 1 / 2) ≥ 2 * (1 - Real.exp (1/2) / t') := by linarith
            rw [← hE] at this
            have h' : 2 * E / t' = 2 * (E / t') := by ring
            rw [h']; linarith
          have hE2' : t' < E * E := by rw [hE2]; exact hbig
          have h5 : t' * t' ≤ E * (3 * t' - 2 * E) := by
            nlinarith [mul_nonneg (sub_nonneg.2 hle.le) (show 0 ≤ 2 * E - t' by nlinarith)]
          have h6 : t' ≤ E * (3 - 2 * E / t') := by
            rw [show E * (3 - 2 * E / t') = E * (3 * t' - 2 * E) / t' by field_simp]
            rw [le_div_iff₀ ht']
            nlinarith
          have h7 : E * (3 - 2 * E / t') ≤ E * max (2 * Real.log t') 1 :=
            mul_le_mul_of_nonneg_left (hlog2.le.trans (le_max_left _ _)) hEpos.le
          nlinarith
      calc 2 * Real.log t / t ≤ 2 / Real.exp 1 := hA
        _ = 2 / E * (1 / E) := by rw [← hE2]; field_simp
        _ ≤ 2 / E * (max (2 * Real.log t') 1 / t') := by
          apply mul_le_mul_of_nonneg_left hB (by positivity)

theorem solution (a x x' : ℝ) (ha : 0 < a) (hx' : 0 < x')
    (hxx' : x' ≤ x) :
    BanditCovariates.SE.phi a x ≤ 2 * Real.exp (-(1 / 2 : ℝ)) * BanditCovariates.SE.phi a x' := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have key : ∀ y : ℝ, 0 < y → BanditCovariates.SE.phi a y =
      Real.sqrt a * (max (2 * Real.log (Real.sqrt a * y)) 1 / (Real.sqrt a * y)) := by
    intro y hy
    unfold BanditCovariates.SE.phi BanditCovariates.SE.logbar
    have h1 : Real.log (a * y ^ 2) = 2 * Real.log (Real.sqrt a * y) := by
      have : a * y ^ 2 = (Real.sqrt a * y) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ha.le]
      rw [this, Real.log_pow]; norm_num
    rw [h1]
    field_simp
  rw [key x hx, key x' hx']
  have hg := g_var (Real.sqrt a * x') (Real.sqrt a * x) (by positivity)
    (mul_le_mul_of_nonneg_left hxx' hs.le)
  have : 2 * Real.exp (-(1 / 2 : ℝ)) = 2 / Real.exp (1 / 2) := by
    rw [Real.exp_neg]; ring
  rw [this]
  calc Real.sqrt a * (max (2 * Real.log (Real.sqrt a * x)) 1 / (Real.sqrt a * x))
      ≤ Real.sqrt a * (2 / Real.exp (1 / 2) * (max (2 * Real.log (Real.sqrt a * x')) 1 / (Real.sqrt a * x'))) :=
        mul_le_mul_of_nonneg_left hg hs.le
    _ = 2 / Real.exp (1 / 2) * (Real.sqrt a * (max (2 * Real.log (Real.sqrt a * x')) 1 / (Real.sqrt a * x'))) := by ring
