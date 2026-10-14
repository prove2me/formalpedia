-- Prove2me | solution 2 for ExplicitPNT.kadiri_zero_free_region_569693
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-12T12:48:07.625934+00:00
-- url     : https://prove2.me/submissions/6376f9f7-5638-4899-a2a6-5c031bb5172c

import Definitions.Def_PNT_Kadiri_HeckeBridge_433_0010
import Theorems.Thm_OAI_SevenEighths_HeckeFamily_LFunction_ne_zero_of_seven_eighths_lt_re

set_option maxHeartbeats 800000
open scoped BigOperators
open Real Complex Set MeasureTheory

namespace RSLocal

lemma exp_neg_three_lt : Real.exp (-3) < (1 / 20 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have h20 : (20 : ℝ) < Real.exp 3 := by linarith
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 3)).2
  linarith

lemma log_region_gt_half (t β : ℝ) (ht : 2 ≤ t)
    (hβ : 1 - 1 / ((9645908801 / 1000000000 : ℝ) * Real.log t) ≤ β) :
    1 / 2 < β := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log t :=
    h2.trans (Real.log_le_log (by norm_num) ht)
  have hden : (2 : ℝ) < (9645908801 / 1000000000) * Real.log t := by nlinarith
  have hinv : 1 / ((9645908801 / 1000000000 : ℝ) * Real.log t) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (9645908801 / 1000000000) * Real.log t)).2
    linarith
  linarith

lemma log_region_gt_seven_eighths (t β : ℝ) (ht : 4 ≤ t)
    (hβ : 1 - 1 / ((9645908801 / 1000000000 : ℝ) * Real.log t) ≤ β) :
    7 / 8 < β := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h4 : (1 : ℝ) ≤ Real.log 4 := by
    have hp := Real.log_pow (2 : ℝ) 2
    norm_num at hp
    linarith
  have hlog : (1 : ℝ) ≤ Real.log t :=
    h4.trans (Real.log_le_log (by norm_num) ht)
  have hden : (8 : ℝ) < (9645908801 / 1000000000) * Real.log t := by nlinarith
  have hinv : 1 / ((9645908801 / 1000000000 : ℝ) * Real.log t) < (1 / 8 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (9645908801 / 1000000000) * Real.log t)).2
    linarith
  linarith

lemma theta_kernel_bound (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ HurwitzZeta.evenKernel 0 x - 1 ∧
    HurwitzZeta.evenKernel 0 x - 1 ≤ (9 / 4 : ℝ) * Real.exp (-3 * x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have htheta : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x))
      (HurwitzZeta.evenKernel 0 x - 1) := by
    simpa [zero_mul, mul_zero, Real.cos_zero, mul_one,
      HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
      HurwitzZeta.hasSum_nat_cosKernel₀ 0 hx0
  let q := Real.exp (-3 * x)
  have hq0 : 0 < q := Real.exp_pos _
  have hq20 : q < (1 / 20 : ℝ) :=
    (Real.exp_le_exp.mpr (by linarith : -3 * x ≤ -3)).trans_lt exp_neg_three_lt
  have hq1 : q < 1 := by linarith
  have hgeo := (hasSum_geometric_of_lt_one hq0.le hq1).mul_left (2 * q)
  have hterm (n : ℕ) :
      2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x) ≤
      (2 * q) * q^n := by
    have hn : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hsq : (n + 1 : ℝ) ≤ (n + 1 : ℝ)^2 := by nlinarith
    have hp : 3 * (n + 1 : ℝ) ≤ Real.pi * (n + 1 : ℝ)^2 := by
      nlinarith [Real.pi_gt_three]
    have he : -Real.pi * (n + 1 : ℝ)^2 * x ≤ (n + 1 : ℝ) * (-3 * x) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) hx0.le]
    calc
      2 * Real.exp (-Real.pi * (n + 1 : ℝ)^2 * x) ≤
          2 * Real.exp ((n + 1 : ℝ) * (-3 * x)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) zero_le_two
      _ = (2 * q) * q^n := by
        rw [show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, Real.exp_nat_mul]
        simp only [q, pow_succ]
        ring
  have hsum := htheta.summable.tsum_le_tsum hterm hgeo.summable
  rw [htheta.tsum_eq, hgeo.tsum_eq] at hsum
  constructor
  · rw [← htheta.tsum_eq]
    exact tsum_nonneg (fun n => mul_nonneg zero_le_two (Real.exp_pos _).le)
  · apply hsum.trans
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ (by linarith : 0 < 1 - q)).2
    nlinarith

noncomputable def upperKernel : ℝ → ℂ :=
  (Ioi 1).indicator (fun x => (HurwitzZeta.evenKernel 0 x : ℂ) - 1)

lemma upper_integrand_bound (z : ℂ) (hz : z.re ≤ 1) (x : ℝ) (hx : 1 < x) :
    ‖(x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)‖ ≤
      (9 / 4 : ℝ) * Real.exp (-3 * x) := by
  have hx0 : 0 < x := by linarith
  have hk := theta_kernel_bound x hx.le
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hp : x ^ (z - 1).re ≤ (1 : ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos hx.le (by simpa using sub_nonpos.mpr hz)
  have hn : ‖(HurwitzZeta.evenKernel 0 x : ℂ) - 1‖ =
      HurwitzZeta.evenKernel 0 x - 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hk.1]
  rw [hn]
  exact (mul_le_of_le_one_left hk.1 hp).trans hk.2

lemma upper_integrand_integrable (z : ℂ) (hz : z.re ≤ 1) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)) (Ioi 1) := by
  have hd : IntegrableOn (fun x : ℝ => (9 / 4 : ℝ) * Real.exp (-3 * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 1).const_mul (9 / 4)
  have hc : ContinuousOn (fun x : ℝ =>
      (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1)) (Ioi 1) := by
    have hpow : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (z - 1)) (Ioi 1) := by
      apply continuousOn_of_forall_continuousAt
      intro x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      exact Complex.continuousAt_ofReal_cpow_const x (z - 1) (Or.inr hx0.ne')
    have hk : ContinuousOn (fun x : ℝ => (HurwitzZeta.evenKernel 0 x : ℂ) - 1) (Ioi 1) :=
      (Complex.continuous_ofReal.comp_continuousOn
        ((HurwitzZeta.continuousOn_evenKernel 0).mono
          (fun x hx => by simp only [mem_Ioi] at *; linarith))).sub continuousOn_const
    exact hpow.smul hk
  exact hd.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => upper_integrand_bound z hz x hx)

lemma upper_mellin_convergent (z : ℂ) (hz : z.re ≤ 1) :
    MellinConvergent upperKernel z := by
  unfold MellinConvergent upperKernel
  simp_rw [← indicator_smul]
  exact ((upper_integrand_integrable z hz).integrable_indicator measurableSet_Ioi).integrableOn

lemma upper_mellin_bound (z : ℂ) (hz : z.re ≤ 1) :
    ‖mellin upperKernel z‖ ≤ (3 / 80 : ℝ) := by
  have hd : IntegrableOn (fun x : ℝ => (9 / 4 : ℝ) * Real.exp (-3 * x)) (Ioi 1) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 1).const_mul (9 / 4)
  have hle := norm_integral_le_of_norm_le hd
    (ae_restrict_mem measurableSet_Ioi |>.mono fun x hx => upper_integrand_bound z hz x hx)
  have hrepr : mellin upperKernel z =
      ∫ x : ℝ in Ioi 1, (x : ℂ) ^ (z - 1) • ((HurwitzZeta.evenKernel 0 x : ℂ) - 1) := by
    unfold mellin upperKernel
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioi]
    rw [inter_eq_right.mpr (show Ioi (1 : ℝ) ⊆ Ioi 0 by
      intro x hx
      simp only [mem_Ioi] at *
      linarith)]
  rw [hrepr]
  apply hle.trans
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 1]
  have he := exp_neg_three_lt
  norm_num at *
  linarith

lemma modif_sub_upper (x : ℝ) (hx : 0 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x - upperKernel x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) • upperKernel (x⁻¹) := by
  rcases lt_trichotomy 1 x with h | h | h
  · have hi : x⁻¹ ≤ 1 := (inv_le_one₀ hx).2 h.le
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, upperKernel,
      h, not_lt.mpr hi, not_lt.mpr h.le]
  · subst x
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, upperKernel]
  · have hi : 1 < x⁻¹ := (one_lt_inv₀ hx).2 h
    simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair, upperKernel,
      Pi.add_apply, Function.comp_apply, ite_true, one_mul, smul_eq_mul, mul_one]
    simp only [indicator_of_notMem (show x ∉ Ioi (1 : ℝ) from not_lt.mpr h.le),
      indicator_of_mem (show x ∈ Ioo 0 1 from ⟨hx, h⟩),
      indicator_of_mem (show x⁻¹ ∈ Ioi (1 : ℝ) from hi)]
    simp only [zero_add, sub_zero]
    have hf : (HurwitzZeta.evenKernel 0 x : ℂ) =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * (HurwitzZeta.evenKernel 0 (x⁻¹) : ℂ) := by
      rw [HurwitzZeta.evenKernel_functional_equation, ← HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
      push_cast
      have hc : ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) = (x : ℂ) ^ (1 / 2 : ℂ) := by
        simpa using Complex.ofReal_cpow hx.le (1 / 2 : ℝ)
      simpa only [one_div, Complex.cpow_neg] using!
        congrArg (fun w : ℂ => w⁻¹ * (HurwitzZeta.evenKernel 0 (x⁻¹) : ℂ)) hc
    have hp : ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
      simpa using Complex.ofReal_cpow hx.le (-(1 / 2 : ℝ))
    rw [hf, hp]
    ring

lemma completed_mellin_split (s : ℂ) (hσ : s.re ≤ 1) :
    completedRiemannZeta₀ s =
      (mellin upperKernel (s / 2) + mellin upperKernel ((1 - s) / 2)) / 2 := by
  have hz : (s / 2).re ≤ 1 := by simp; linarith
  have hc : MellinConvergent (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (s / 2) :=
    ((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (s / 2)).1
  have hm := (hasMellin_sub hc (upper_mellin_convergent (s / 2) hz)).2
  have he :
      mellin (fun x => (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x - upperKernel x) (s / 2) =
        mellin upperKernel ((1 - s) / 2) := by
    calc
      _ = mellin (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) • upperKernel (x⁻¹)) (s / 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [modif_sub_upper x hx]
      _ = mellin (fun x : ℝ => upperKernel (x⁻¹)) (s / 2 + -(1 / 2 : ℂ)) :=
        mellin_cpow_smul _ _ _
      _ = mellin upperKernel (-(s / 2 + -(1 / 2 : ℂ))) := mellin_comp_inv _ _
      _ = _ := by congr 1; ring
  rw [he] at hm
  unfold completedRiemannZeta₀ HurwitzZeta.completedHurwitzZetaEven₀ WeakFEPair.Λ₀
  congr 1
  linear_combination -hm

lemma completed_entire_bound (s : ℂ) (hσ0 : 0 ≤ s.re) (hσ1 : s.re ≤ 1) :
    ‖completedRiemannZeta₀ s‖ ≤ (3 / 80 : ℝ) := by
  rw [completed_mellin_split s hσ1, norm_div]
  have h1 := upper_mellin_bound (s / 2) (by simp; linarith)
  have h2 := upper_mellin_bound ((1 - s) / 2) (by simp; linarith)
  have hn := norm_add_le (mellin upperKernel (s / 2)) (mellin upperKernel ((1 - s) / 2))
  norm_num
  linarith

theorem zeta_nonzero_small_height (s : ℂ) (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1)
    (ht0 : 0 < s.im) (ht4 : s.im ≤ 4) : riemannZeta s ≠ 0 := by
  have hs : s ≠ 0 := by intro h; subst s; simp at ht0
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hn1 : ‖s‖ ≤ 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_nonneg hσ0.le, abs_of_nonneg ht0.le] at h
    linarith
  have hn2 : ‖1 - s‖ ≤ 5 := by
    have h := Complex.norm_le_abs_re_add_abs_im (1 - s)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hσ1), abs_of_nonneg ht0.le] at h
    linarith
  intro hz
  have hzC : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs] at hz
    rcases (div_eq_zero_iff).mp hz with h | h
    · exact h
    · exact (Complex.Gammaℝ_ne_zero_of_re_pos hσ0 h).elim
  have hid : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [hzC] at h
    linear_combination -h
  have he : s * (1 - s) * completedRiemannZeta₀ s = 1 := by
    rw [hid]
    field_simp
    ring
  have hsmall := completed_entire_bound s hσ0.le hσ1
  have hn : ‖s * (1 - s) * completedRiemannZeta₀ s‖ < 1 := by
    calc
      _ = ‖s‖ * ‖1 - s‖ * ‖completedRiemannZeta₀ s‖ := by rw [norm_mul, norm_mul]
      _ ≤ 5 * 5 * (3 / 80 : ℝ) := by gcongr
      _ < 1 := by norm_num
  rw [he] at hn
  norm_num at hn

end RSLocal














theorem kadiri_hecke_zeta_nonzero (s : ℂ) (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  apply OAI.SevenEighths.HeckeDirichlet.zeta_seven_eighths_of_hecke _ s hs
  intro η z hz hpole
  apply OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re η hz
  rintro ⟨hη, hz1⟩
  rcases hpole with h | h
  · exact h hz1
  · exact h hη

namespace KadiriLocal

lemma log_nine_halves_lower : (141 / 100 : ℝ) ≤ Real.log (9 / 2 : ℝ) := by
  have h5 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (5 / 4 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h5
  norm_num at h5
  have h6 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (6 / 5 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h6
  norm_num at h6
  have h7 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (7 / 6 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h7
  norm_num at h7
  have h8 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (8 / 7 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h8
  norm_num at h8
  have h9 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (9 / 8 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h9
  norm_num at h9
  have h10 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (10 / 9 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h10
  norm_num at h10
  have h11 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (11 / 10 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h11
  norm_num at h11
  have h12 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (12 / 11 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h12
  norm_num at h12
  have h13 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (13 / 12 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h13
  norm_num at h13
  have h14 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (14 / 13 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h14
  norm_num at h14
  have h15 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (15 / 14 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h15
  norm_num at h15
  have h16 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (16 / 15 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h16
  norm_num at h16
  have h17 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (17 / 16 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h17
  norm_num at h17
  have h18 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (18 / 17 : ℝ))
  rw [Real.log_div (by norm_num) (by norm_num)] at h18
  norm_num at h18
  have hh : (141 / 100 : ℝ) ≤ Real.log 18 - Real.log 4 := by
    linarith
  rw [← Real.log_div (by norm_num : (18 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)] at hh
  norm_num at hh ⊢
  exact hh

lemma log_region_gt_half (t β : ℝ) (ht : 2 ≤ t)
    (hβ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log t) ≤ β) :
    1 / 2 < β := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : (1 / 2 : ℝ) ≤ Real.log t :=
    h2.trans (Real.log_le_log (by norm_num) ht)
  have hden : (2 : ℝ) < (569693 / 100000) * Real.log t := by nlinarith
  have hinv : 1 / ((569693 / 100000 : ℝ) * Real.log t) < (1 / 2 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (569693 / 100000) * Real.log t)).2
    linarith
  linarith

lemma log_region_gt_seven_eighths (t β : ℝ) (ht : 9 / 2 ≤ t)
    (hβ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log t) ≤ β) :
    7 / 8 < β := by
  have hlog : (141 / 100 : ℝ) ≤ Real.log t :=
    log_nine_halves_lower.trans (Real.log_le_log (by norm_num) ht)
  have hden : (8 : ℝ) < (569693 / 100000) * Real.log t := by nlinarith
  have hinv : 1 / ((569693 / 100000 : ℝ) * Real.log t) < (1 / 8 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (569693 / 100000) * Real.log t)).2
    linarith
  linarith

theorem zeta_nonzero_small_height (s : ℂ) (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1)
    (ht0 : 0 < s.im) (ht4 : s.im ≤ 9 / 2) : riemannZeta s ≠ 0 := by
  have hs : s ≠ 0 := by intro h; subst s; simp at ht0
  have hs1 : 1 - s ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  have hresq : s.re ^ 2 ≤ 1 := by nlinarith
  have himsq : s.im ^ 2 ≤ 81 / 4 := by nlinarith
  have hresq2 : (1 - s.re) ^ 2 ≤ 1 := by nlinarith
  have hn1 : ‖s‖ ≤ 5 := by
    have h := Complex.sq_norm_sub_sq_re s
    nlinarith [norm_nonneg s]
  have hn2 : ‖1 - s‖ ≤ 5 := by
    have h := Complex.sq_norm_sub_sq_re (1 - s)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at h
    nlinarith [norm_nonneg (1 - s)]
  intro hz
  have hzC : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs] at hz
    rcases (div_eq_zero_iff).mp hz with h | h
    · exact h
    · exact (Complex.Gammaℝ_ne_zero_of_re_pos hσ0 h).elim
  have hid : completedRiemannZeta₀ s = 1 / s + 1 / (1 - s) := by
    have h := completedRiemannZeta_eq s
    rw [hzC] at h
    linear_combination -h
  have he : s * (1 - s) * completedRiemannZeta₀ s = 1 := by
    rw [hid]
    field_simp
    ring
  have hsmall := RSLocal.completed_entire_bound s hσ0.le hσ1
  have hn : ‖s * (1 - s) * completedRiemannZeta₀ s‖ < 1 := by
    calc
      _ = ‖s‖ * ‖1 - s‖ * ‖completedRiemannZeta₀ s‖ := by rw [norm_mul, norm_mul]
      _ ≤ 5 * 5 * (3 / 80 : ℝ) := by gcongr
      _ < 1 := by norm_num
  rw [he] at hn
  norm_num at hn

theorem zeta_nonzero_positive_height (s : ℂ)
    (ht : 2 ≤ s.im)
    (hσ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log s.im) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  by_cases h4 : 9 / 2 ≤ s.im
  · exact kadiri_hecke_zeta_nonzero s
      (log_region_gt_seven_eighths s.im s.re h4 hσ)
  · by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1
    · exact zeta_nonzero_small_height s
        (by linarith [log_region_gt_half s.im s.re ht hσ])
        (le_of_not_ge h1) (by linarith) (le_of_not_ge h4)

end KadiriLocal

namespace ExplicitPNT
theorem kadiri_zero_free_region_569693 (s : ℂ)
    (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0 := by
  by_cases hpos : 0 ≤ s.im
  · rw [abs_of_nonneg hpos] at ht hσ
    exact KadiriLocal.zeta_nonzero_positive_height s ht hσ
  · have him : (star s).im = |s.im| := by
      simp only [Complex.star_def, Complex.conj_im]
      rw [abs_of_neg (lt_of_not_ge hpos)]
    have hre : (star s).re = s.re := by simp
    have hn := KadiriLocal.zeta_nonzero_positive_height (star s)
      (by simpa only [him] using ht) (by simpa only [him, hre] using hσ)
    intro hz
    apply hn
    change riemannZeta ((starRingEnd ℂ) s) = 0
    rw [riemannZeta_conj, hz, map_zero]
end ExplicitPNT

theorem solution (s : ℂ) (ht : 2 ≤ |s.im|)
    (hσ : 1 - 1 / ((569693 / 100000 : ℝ) * Real.log |s.im|) ≤ s.re) :
    riemannZeta s ≠ 0 :=
  ExplicitPNT.kadiri_zero_free_region_569693 s ht hσ

#print axioms KadiriLocal.log_nine_halves_lower
#print axioms KadiriLocal.zeta_nonzero_small_height
#print axioms ExplicitPNT.kadiri_zero_free_region_569693
#print axioms solution

