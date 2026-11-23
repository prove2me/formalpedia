-- Prove2me | solution 1 for BroughanRH.mszZeta
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:55:37.980808+00:00
-- url     : https://prove2.me/submissions/0c1ac9ac-3f26-407a-9798-e75dc2a35297
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_XiHadamardPortPublished_concrete_xi_no_real_zeros
import Theorems.Thm_Zeta23_StirlingVert_digamma_eq
import Theorems.Thm_Zeta23_StirlingVert_norm_eps_le
import Theorems.Thm_ExplicitFormula_digamma_one_sub_sub_digamma

open Complex

/-- Telescoping tail bound. -/
lemma msz_tsum_norm_le (f : ℕ → ℂ) {c K : ℝ} (hc : 1 < c) (hK : 0 ≤ K)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ K / ((n:ℝ) + c) ^ 2) : ‖∑' n, f n‖ ≤ K / (c - 1) := by
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, K / ((n:ℝ) + c) ^ 2 ≤ K / (c - 1) - K / ((N:ℝ) + c - 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hN : (0:ℝ) ≤ N := N.cast_nonneg
      have h1 : 0 < (N:ℝ) + c - 1 := by linarith
      have h2 : 0 < (N:ℝ) + c := by linarith
      have : K / ((N:ℝ) + c) ^ 2 ≤ K / ((N:ℝ) + c - 1) - K / (((N+1:ℕ):ℝ) + c - 1) := by
        push_cast
        have e : (N:ℝ) + 1 + c - 1 = (N:ℝ) + c := by ring
        rw [e, div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg hK (mul_pos h1 h2).le]
      linarith
  have hb : ∀ N : ℕ, ∑ n ∈ Finset.range N, K / ((n:ℝ) + c) ^ 2 ≤ K / (c - 1) := by
    intro N
    have : 0 ≤ K / ((N:ℝ) + c - 1) := div_nonneg hK (by have := (N.cast_nonneg : (0:ℝ) ≤ N); linarith)
    linarith [hpart N]
  have hg0 : ∀ n : ℕ, 0 ≤ K / ((n:ℝ) + c) ^ 2 := fun n => by positivity
  have hgs : Summable (fun n : ℕ => K / ((n:ℝ) + c) ^ 2) := summable_of_sum_range_le hg0 hb
  have hfs : Summable (fun n => ‖f n‖) := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hf hgs
  calc ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' n : ℕ, K / ((n:ℝ) + c) ^ 2 := hfs.tsum_le_tsum hf hgs
    _ ≤ K / (c - 1) := Real.tsum_le_of_sum_range_le hg0 hb

lemma msz_normsq_shift (w : ℂ) (n : ℕ) (k : ℝ) :
    ‖(n:ℂ) + k + w‖ ^ 2 = ((n:ℝ) + k + w.re) ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp; ring

/-- Lower bound for `Re ψ(w)` from the exact Stirling-type formula. -/
lemma msz_re_digamma_lower {w : ℂ} (ha : 0 < w.re) (hy : 4 ≤ |w.im|) :
    Real.log ‖1 + w‖ - w.re / (w.re ^ 2 + w.im ^ 2)
      - (1/2) * ((1 + w.re) / ((1 + w.re) ^ 2 + w.im ^ 2)) - 5 / (3 * w.im ^ 2)
      ≤ (Complex.digamma w).re := by
  have hy' : 1/2 ≤ |w.im| := by linarith
  rw [Zeta23.StirlingVert.digamma_eq ha hy']
  set a := w.re with ha_def
  set y := |w.im| with hy_def
  have hy2 : w.im ^ 2 = y ^ 2 := (sq_abs _).symm
  have hypos : 0 < y := by linarith
  -- lower bound on the norms
  have hz : ∀ n : ℕ, ((n:ℝ) + (1 + a + y)) ^ 2 / 2 ≤ ‖(n:ℂ) + 1 + w‖ ^ 2 := by
    intro n
    have := msz_normsq_shift w n 1
    push_cast at this
    rw [this, hy2]
    nlinarith [sq_nonneg ((n:ℝ) + 1 + a - y)]
  have hzpos : ∀ n : ℕ, 0 < ((n:ℝ) + (1 + a + y)) := fun n => by
    have := (n.cast_nonneg : (0:ℝ) ≤ n); linarith
  have hρ : ‖∑' n, Zeta23.StirlingVert.rho w n‖ ≤ (2 / y) / ((1 + a + y) - 1) := by
    apply msz_tsum_norm_le _ (by linarith) (by positivity)
    intro n
    unfold Zeta23.StirlingVert.rho
    rw [norm_div, norm_one, norm_mul, norm_pow]
    have h2 : y ≤ ‖(n:ℂ) + 2 + w‖ := by
      have := Complex.abs_im_le_norm ((n:ℂ) + 2 + w)
      simpa using this
    have hzn := hz n
    have hp := hzpos n
    have hq : 0 < ‖(n:ℂ) + 1 + w‖ ^ 2 := by nlinarith
    calc 1 / (‖(n:ℂ) + 1 + w‖ ^ 2 * ‖(n:ℂ) + 2 + w‖) ≤ 1 / (‖(n:ℂ) + 1 + w‖ ^ 2 * y) :=
          one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left h2 hq.le)
      _ ≤ 2 / y / ((n:ℝ) + (1 + a + y)) ^ 2 := by
          rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hzn hypos.le]
  have hε : ‖∑' n : ℕ, Zeta23.StirlingVert.eps w ((n:ℝ) + 1)‖ ≤ (2 / (3 * y)) / ((1 + a + y) - 1) := by
    apply msz_tsum_norm_le _ (by linarith) (by positivity)
    intro n
    have he := Zeta23.StirlingVert.norm_eps_le ha hy' (m := (n:ℝ) + 1) (by positivity)
    have hc : (((n:ℝ) + 1 : ℝ) : ℂ) + w = (n:ℂ) + 1 + w := by push_cast; ring
    rw [hc] at he
    rw [← hy_def] at he
    refine he.trans ?_
    have hzn := hz n
    have hp := hzpos n
    have hq : 0 < ‖(n:ℂ) + 1 + w‖ ^ 2 := by nlinarith
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hzn hypos.le]
  -- real parts
  have hlog : (Complex.log (1 + w)).re = Real.log ‖1 + w‖ := Complex.log_re _
  have hinv : (1 / w).re = a / (a ^ 2 + w.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]; ring
  have hinv2 : ((1 / 2 : ℂ) * (1 + w)⁻¹).re = (1/2) * ((1 + a) / ((1 + a) ^ 2 + w.im ^ 2)) := by
    rw [show ((1 / 2 : ℂ) * (1 + w)⁻¹).re = (1/2) * ((1 + w)⁻¹).re by simp [Complex.mul_re]]
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
    ring
  have hρre : (((1 / 2 : ℂ)) * ∑' n, Zeta23.StirlingVert.rho w n).re ≤ (1/2) * ‖∑' n, Zeta23.StirlingVert.rho w n‖ := by
    have : ((1 / 2 : ℂ) * ∑' n, Zeta23.StirlingVert.rho w n).re = (1/2) * (∑' n, Zeta23.StirlingVert.rho w n).re := by
      simp [Complex.mul_re]
    rw [this]
    have := Complex.re_le_norm (∑' n, Zeta23.StirlingVert.rho w n)
    linarith
  have hεre : -‖∑' n : ℕ, Zeta23.StirlingVert.eps w ((n:ℝ) + 1)‖ ≤ (∑' n : ℕ, Zeta23.StirlingVert.eps w ((n:ℝ) + 1)).re := by
    have := Complex.abs_re_le_norm (∑' n : ℕ, Zeta23.StirlingVert.eps w ((n:ℝ) + 1))
    rw [abs_le] at this; linarith
  simp only [Complex.add_re, Complex.sub_re]
  rw [hlog, hinv, hinv2]
  have hfin : (1/2) * ((2 / y) / ((1 + a + y) - 1)) + (2 / (3 * y)) / ((1 + a + y) - 1) ≤ 5 / (3 * w.im ^ 2) := by
    rw [hy2]
    have e : (1 + a + y) - 1 = a + y := by ring
    rw [e]
    have hay : 0 < a + y := by linarith
    have : (1/2) * ((2 / y) / (a + y)) + (2 / (3 * y)) / (a + y) = 5 / (3 * (y * (a + y))) := by
      field_simp; ring
    rw [this]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  nlinarith [hρ, hε, hρre, hεre, hfin]

lemma msz_sin_re (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  rw [Complex.sin_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.mul_re, Complex.mul_im]
lemma msz_sin_im (z : ℂ) : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  rw [Complex.sin_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.mul_re, Complex.mul_im]
lemma msz_cos_re (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.mul_re, Complex.mul_im]
lemma msz_cos_im (z : ℂ) : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  rw [Complex.cos_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.mul_re, Complex.mul_im]

lemma msz_sinh_ge (Y : ℝ) (hY : 0 ≤ Y) : Y ^ 2 / 4 ≤ Real.sinh Y := by
  rw [Real.sinh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg hY
  have h2 : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

lemma msz_cot_re {z : ℂ} (hz : 4 ≤ z.im) :
    |((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)).re| ≤ 1 / 400 := by
  have hZim : ((Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  set Z := (Real.pi : ℂ) * z with hZ
  set X := Z.re
  set Y := Z.im
  have hpi := Real.pi_gt_d2
  have hY : 4 * Real.pi ≤ Y := by rw [hZim]; nlinarith [Real.pi_pos]
  have hsinh : 39 ≤ Real.sinh Y := by
    have := msz_sinh_ge Y (by linarith [Real.pi_pos])
    nlinarith
  have hden : (Real.sin X * Real.cosh Y) * (Real.sin X * Real.cosh Y)
      + (Real.cos X * Real.sinh Y) * (Real.cos X * Real.sinh Y) = Real.sin X ^ 2 + Real.sinh Y ^ 2 := by
    have hc := Real.cosh_sq Y
    have hs := Real.sin_sq_add_cos_sq X
    linear_combination (Real.sin X ^ 2) * hc + (Real.sinh Y ^ 2) * hs
  have hre : (Complex.cot Z).re = Real.sin X * Real.cos X / (Real.sin X ^ 2 + Real.sinh Y ^ 2) := by
    rw [Complex.cot_eq_cos_div_sin, Complex.div_re, msz_cos_re, msz_cos_im, msz_sin_re,
      msz_sin_im, Complex.normSq_apply, msz_sin_re, msz_sin_im, hden, ← add_div]
    congr 1
    have hc := Real.cosh_sq Y
    linear_combination (Real.sin X * Real.cos X) * hc
  rw [Complex.re_ofReal_mul, hre, abs_mul, abs_of_pos Real.pi_pos, abs_div,
    abs_of_pos (by positivity : (0:ℝ) < Real.sin X ^ 2 + Real.sinh Y ^ 2)]
  have hsc : |Real.sin X * Real.cos X| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one X) (abs_nonneg _) (Real.abs_cos_le_one X)
  have hD : 1521 ≤ Real.sin X ^ 2 + Real.sinh Y ^ 2 := by nlinarith [sq_nonneg (Real.sin X)]
  have hpi4 := Real.pi_lt_d2
  calc Real.pi * (|Real.sin X * Real.cos X| / (Real.sin X ^ 2 + Real.sinh Y ^ 2))
      ≤ 3.15 * (1 / 1521) := by
        apply mul_le_mul (by linarith) _ (by positivity) (by norm_num)
        exact div_le_div₀ (by norm_num) hsc (by norm_num) hD
    _ ≤ 1 / 400 := by norm_num

lemma msz_rat_neg (σ : ℝ) (hσ : σ ≤ 0) :
    0 < σ/(σ^2+64) + (σ-1)/((σ-1)^2+64) + ((2-σ/2)^2/16)/(2*((2-σ/2)^2/16+2))
      - (1-σ/2)/(2*((1-σ/2)^2+16)) - (2-σ/2)/(4*((2-σ/2)^2+16)) - 5/96 - 1/800
      + (1 - 3.1416/4)/2 := by
  obtain ⟨p, hp, rfl⟩ : ∃ p : ℝ, 0 ≤ p ∧ σ = -p := ⟨-σ, by linarith, by ring⟩
  have h1 : (-p)^2+64 ≠ 0 := by positivity
  have h2 : (-p-1)^2+64 ≠ 0 := by positivity
  have h3 : (2-(-p)/2)^2/16+2 ≠ 0 := by positivity
  have h4 : (1-(-p)/2)^2+16 ≠ 0 := by positivity
  have h5 : (2-(-p)/2)^2+16 ≠ 0 := by positivity
  have key : 0 < (16619:ℝ)*p^10 + (260618:ℝ)*p^9 + (5708591:ℝ)*p^8 + (46877020:ℝ)*p^7 + (546935084:ℝ)*p^6 + (2129538592:ℝ)*p^5 + (18184258304:ℝ)*p^4 + (-6605734400:ℝ)*p^3 + (214600123392:ℝ)*p^2 + (-1254493143040:ℝ)*p + (3883730534400:ℝ) := by
    nlinarith [sq_nonneg (p - 3), sq_nonneg (p^2 - p), mul_nonneg hp (sq_nonneg (p-3)), pow_nonneg hp 3,
      pow_nonneg hp 5, pow_nonneg hp 6, pow_nonneg hp 7, pow_nonneg hp 8, pow_nonneg hp 9, pow_nonneg hp 10,
      mul_nonneg (pow_nonneg hp 2) (sq_nonneg (p-1))]
  have hD : 0 < (30000:ℝ)*p^10 + (660000:ℝ)*p^9 + (17670000:ℝ)*p^8 + (227400000:ℝ)*p^7 + (3217080000:ℝ)*p^6 + (27047040000:ℝ)*p^5 + (249588480000:ℝ)*p^4 + (1347072000000:ℝ)*p^3 + (8452823040000:ℝ)*p^2 + (23966515200000:ℝ)*p + (97763328000000:ℝ) := by
    positivity
  have e : (-p)/((-p)^2+64) + ((-p)-1)/(((-p)-1)^2+64) + ((2-(-p)/2)^2/16)/(2*((2-(-p)/2)^2/16+2))
      - (1-(-p)/2)/(2*((1-(-p)/2)^2+16)) - (2-(-p)/2)/(4*((2-(-p)/2)^2+16)) - 5/96 - 1/800
      + (1 - 3.1416/4)/2 = ((16619:ℝ)*p^10 + (260618:ℝ)*p^9 + (5708591:ℝ)*p^8 + (46877020:ℝ)*p^7 + (546935084:ℝ)*p^6 + (2129538592:ℝ)*p^5 + (18184258304:ℝ)*p^4 + (-6605734400:ℝ)*p^3 + (214600123392:ℝ)*p^2 + (-1254493143040:ℝ)*p + (3883730534400:ℝ)) / ((30000:ℝ)*p^10 + (660000:ℝ)*p^9 + (17670000:ℝ)*p^8 + (227400000:ℝ)*p^7 + (3217080000:ℝ)*p^6 + (27047040000:ℝ)*p^5 + (249588480000:ℝ)*p^4 + (1347072000000:ℝ)*p^3 + (8452823040000:ℝ)*p^2 + (23966515200000:ℝ)*p + (97763328000000:ℝ)) := by
    rw [eq_div_iff hD.ne']
    field_simp
    ring
  rw [e]
  exact div_pos key hD

lemma msz_rat_pos (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1/2) :
    0 < (p-1)/((p-1)^2+64) + ((2-p/2)^2/16)/(2*((2-p/2)^2/16+2))
      - (1-p/2)/(2*((1-p/2)^2+16)) - (2-p/2)/(4*((2-p/2)^2+16)) - 5/96 - 1/800
      + (1 - 3.1416/4)/2 := by
  have hp := hp0
  have h2 : (p-1)^2+64 ≠ 0 := by positivity
  have h3 : (2-p/2)^2/16+2 ≠ 0 := by positivity
  have h4 : (1-p/2)^2+16 ≠ 0 := by positivity
  have h5 : (2-p/2)^2+16 ≠ 0 := by positivity
  have hp1 : p ≤ 1 := by linarith
  have hpk : ∀ k : ℕ, p ^ k ≤ 1 := fun k => pow_le_one₀ hp hp1
  have key : 0 < (16619:ℝ)*p^8 + (-290618:ℝ)*p^7 + (5304975:ℝ)*p^6 + (-44027468:ℝ)*p^5 + (392576684:ℝ)*p^4 + (-1520860640:ℝ)*p^3 + (8256150528:ℝ)*p^2 + (-4266544640:ℝ)*p + (60683289600:ℝ) := by
    nlinarith [hpk 7, hpk 5, hpk 3, hpk 1, pow_nonneg hp 8, pow_nonneg hp 6, pow_nonneg hp 4, pow_nonneg hp 2]
  have hD : 0 < (30000:ℝ)*p^8 + (-660000:ℝ)*p^7 + (15750000:ℝ)*p^6 + (-185160000:ℝ)*p^5 + (2209080000:ℝ)*p^4 + (-15196800000:ℝ)*p^3 + (108207360000:ℝ)*p^2 + (-374476800000:ℝ)*p + (1527552000000:ℝ) := by
    nlinarith [hpk 7, hpk 5, hpk 3, hpk 1, pow_nonneg hp 8, pow_nonneg hp 6, pow_nonneg hp 4, pow_nonneg hp 2]
  have e : (p-1)/((p-1)^2+64) + ((2-p/2)^2/16)/(2*((2-p/2)^2/16+2))
      - (1-p/2)/(2*((1-p/2)^2+16)) - (2-p/2)/(4*((2-p/2)^2+16)) - 5/96 - 1/800
      + (1 - 3.1416/4)/2 = ((16619:ℝ)*p^8 + (-290618:ℝ)*p^7 + (5304975:ℝ)*p^6 + (-44027468:ℝ)*p^5 + (392576684:ℝ)*p^4 + (-1520860640:ℝ)*p^3 + (8256150528:ℝ)*p^2 + (-4266544640:ℝ)*p + (60683289600:ℝ)) / ((30000:ℝ)*p^8 + (-660000:ℝ)*p^7 + (15750000:ℝ)*p^6 + (-185160000:ℝ)*p^5 + (2209080000:ℝ)*p^4 + (-15196800000:ℝ)*p^3 + (108207360000:ℝ)*p^2 + (-374476800000:ℝ)*p + (1527552000000:ℝ)) := by
    rw [eq_div_iff hD.ne']
    field_simp
    ring
  rw [e]
  exact div_pos key hD

set_option maxHeartbeats 1000000 in
lemma msz_L_pos (σ t : ℝ) (hσ : σ ≤ 1/2) (ht : 8 ≤ t) :
    0 < σ/(σ^2+t^2) + (σ-1)/((σ-1)^2+t^2) - Real.log Real.pi / 2
      + (1/2) * (Complex.digamma (((σ:ℂ) + (t:ℂ) * Complex.I) / 2)).re := by
  set z : ℂ := ((σ:ℂ) + (t:ℂ) * Complex.I) / 2 with hz_def
  have hzre : z.re = σ / 2 := by simp [z]
  have hzim : z.im = t / 2 := by simp [z]
  have hz : ∀ n : ℤ, z ≠ n := by
    intro n h
    have := congrArg Complex.im h
    rw [hzim] at this
    simp at this
    linarith
  have hrefl := ExplicitFormula.digamma_one_sub_sub_digamma z hz
  have hψ : (Complex.digamma z).re = (Complex.digamma (1 - z)).re
      - ((Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z)).re := by
    have : Complex.digamma z = Complex.digamma (1 - z) - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) := by
      linear_combination (-1:ℂ) * hrefl
    rw [this, Complex.sub_re]
  have hcot := msz_cot_re (z := z) (by rw [hzim]; linarith)
  rw [abs_le] at hcot
  set w : ℂ := 1 - z with hw_def
  have hwre : w.re = 1 - σ/2 := by simp [w, hzre]
  have hwim : w.im = -(t/2) := by simp [w, hzim]
  have hwim2 : w.im ^ 2 = t ^ 2 / 4 := by rw [hwim]; ring
  have hB := msz_re_digamma_lower (w := w) (by rw [hwre]; linarith)
    (by rw [hwim, abs_neg, abs_of_pos (by linarith)]; linarith)
  rw [hwre, hwim2] at hB
  -- the logarithm
  have hn2 : ‖1 + w‖ ^ 2 = (2 - σ/2) ^ 2 + t ^ 2 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, hwre, hwim]
    ring
  have hlogn : Real.log ‖1 + w‖ = Real.log ((2 - σ/2) ^ 2 + t ^ 2 / 4) / 2 := by
    rw [← hn2, Real.log_pow]; push_cast; ring
  have hl1 : Real.log ((2 - σ/2) ^ 2 + 16) ≤ Real.log ((2 - σ/2) ^ 2 + t ^ 2 / 4) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hl2 : Real.log ((2 - σ/2) ^ 2 + 16) = Real.log 16 + Real.log (1 + (2 - σ/2) ^ 2 / 16) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
  have hl3 := Real.le_log_one_add_of_nonneg (x := (2 - σ/2) ^ 2 / 16) (by positivity)
  have hl16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; ring
  have hpi : Real.log Real.pi - 2 * Real.log 2 ≤ Real.pi / 4 - 1 := by
    have h := Real.log_le_sub_one_of_pos (x := Real.pi / 4) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num), show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
    push_cast at h
    linarith
  have hpi4 := Real.pi_lt_d4
  -- monotonicity in t
  have ht2 : 64 ≤ t ^ 2 := by nlinarith
  have hT2 : (σ-1)/((σ-1)^2+64) ≤ (σ-1)/((σ-1)^2+t^2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ 1-σ by linarith) (show 0 ≤ t^2-64 by linarith)]
  have hA : (1-σ/2)/((1-σ/2)^2+t^2/4) ≤ (1-σ/2)/((1-σ/2)^2+16) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ 1-σ/2 by linarith) (show 0 ≤ t^2/4-16 by linarith)]
  have hU : (1 + (1-σ/2))/((1 + (1-σ/2))^2+t^2/4) ≤ (2-σ/2)/((2-σ/2)^2+16) := by
    rw [show 1 + (1-σ/2) = 2 - σ/2 by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ 2-σ/2 by linarith) (show 0 ≤ t^2/4-16 by linarith)]
  have hE : 5 / (3 * (t^2/4)) ≤ 5 / 48 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  have r1 : (1-σ/2)/(2*((1-σ/2)^2+16)) = (1/2) * ((1-σ/2)/((1-σ/2)^2+16)) := by
    rw [mul_comm (2:ℝ), ← div_div]; ring
  have r2 : (2-σ/2)/(4*((2-σ/2)^2+16)) = (1/4) * ((2-σ/2)/((2-σ/2)^2+16)) := by
    rw [mul_comm (4:ℝ), ← div_div]; ring
  have r3 : ((2-σ/2)^2/16)/(2*((2-σ/2)^2/16+2)) = (1/4) * (2 * ((2-σ/2)^2/16) / ((2-σ/2)^2/16 + 2)) := by
    rw [mul_comm (2:ℝ) ((2-σ/2)^2/16+2), ← div_div]; ring
  rw [hψ]
  rcases le_total σ 0 with h0 | h0
  · have hT1 : σ/(σ^2+64) ≤ σ/(σ^2+t^2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (show 0 ≤ -σ by linarith) (show 0 ≤ t^2-64 by linarith)]
    have key := msz_rat_neg σ h0
    rw [r1, r2, r3] at key
    linarith
  · have hT1 : 0 ≤ σ/(σ^2+t^2) := by positivity
    have key := msz_rat_pos σ h0 hσ
    rw [r1, r2, r3] at key
    linarith

noncomputable def mszF (s : ℂ) : ℂ := s * (s - 1) * Complex.Gammaℝ s

lemma msz_pole {s : ℂ} (hs : s.im ≠ 0) : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.im h
  simp at this
  exact hs this

lemma msz_F_ne {s : ℂ} (hs : s.im ≠ 0) : mszF s ≠ 0 := by
  unfold mszF
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s - 1 ≠ 0 := by intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hG : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h; exfalso; exact Real.pi_ne_zero (by exact_mod_cast h)
    · exact Complex.Gamma_ne_zero (msz_pole hs)
  exact mul_ne_zero (mul_ne_zero h0 h1) hG

lemma msz_F_hasDerivAt {s : ℂ} (hs : s.im ≠ 0) :
    HasDerivAt mszF (mszF s * (1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2
      + (1 / 2) * Complex.digamma (s / 2)))) s := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s - 1 ≠ 0 := by intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero (msz_pole hs)
  have hd1 : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
    simpa using this
  have hd2 : HasDerivAt (fun s : ℂ => Complex.Gamma (s / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    exact (Complex.differentiableAt_Gamma (s / 2) (msz_pole hs)).hasDerivAt.comp s
      ((hasDerivAt_id' s).div_const 2)
  have hdg : deriv Complex.Gamma (s / 2) = Complex.Gamma (s / 2) * Complex.digamma (s / 2) := by
    rw [Complex.digamma_def, logDeriv_apply]; field_simp
  have hpoly : HasDerivAt (fun s : ℂ => s * (s - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  have hfun : mszF = fun s : ℂ => s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) := by
    funext x; rw [mszF, Complex.Gammaℝ_def]
  rw [hfun]
  refine (hpoly.mul (hd1.mul hd2)).congr_deriv ?_
  simp only [Pi.mul_apply]
  rw [hdg, ← Complex.ofReal_log Real.pi_pos.le]
  field_simp

lemma msz_line_hasDerivAt (t σ : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => ‖mszF ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2)
      (2 * (Complex.normSq (mszF ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        (σ/(σ^2+t^2) + (σ-1)/((σ-1)^2+t^2) - Real.log Real.pi / 2
          + (1/2) * (Complex.digamma (((σ:ℂ) + (t:ℂ) * Complex.I) / 2)).re))) σ := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs_def
  have hsim : s.im = t := by simp [s]
  have hsre : s.re = σ := by simp [s]
  have hF := msz_F_hasDerivAt (s := s) (by rw [hsim]; exact ht)
  have hF' : HasDerivAt (fun z : ℂ => mszF (z + (t : ℂ) * Complex.I)) _ (σ : ℂ) :=
    HasDerivAt.comp_add_const (σ : ℂ) ((t : ℂ) * Complex.I) hF
  have hR := hF'.comp_ofReal.norm_sq
  convert hR using 1
  rw [Complex.inner]
  congr 1
  rw [show mszF s * (1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2)))
      * (starRingEnd ℂ) (mszF s) = (Complex.normSq (mszF s) : ℂ) *
      (1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2))) by
    rw [Complex.normSq_eq_conj_mul_self]; ring]
  rw [Complex.re_ofReal_mul]
  congr 1
  simp only [Complex.add_re, one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    hsre, hsim, Complex.one_re, Complex.one_im, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]
  have : ((2:ℂ)⁻¹ * Complex.digamma (s/2)).re = 2⁻¹ * (Complex.digamma (s/2)).re := by
    simp [Complex.mul_re]
  rw [this]
  ring

lemma msz_F_mono (t : ℝ) (ht : 8 ≤ t) :
    MonotoneOn (fun x : ℝ => ‖mszF ((x : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2) (Set.Iic (1/2)) := by
  have ht0 : t ≠ 0 := by linarith
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic _)
    (f' := fun σ => 2 * (Complex.normSq (mszF ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        (σ/(σ^2+t^2) + (σ-1)/((σ-1)^2+t^2) - Real.log Real.pi / 2
          + (1/2) * (Complex.digamma (((σ:ℂ) + (t:ℂ) * Complex.I) / 2)).re)))
  · intro x _
    exact (msz_line_hasDerivAt t x ht0).continuousAt.continuousWithinAt
  · intro x _
    exact (msz_line_hasDerivAt t x ht0).hasDerivWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    have := msz_L_pos x t (le_of_lt hx) ht
    exact mul_nonneg (by norm_num) (mul_nonneg (Complex.normSq_nonneg _) this.le)

lemma msz_xi_eq (s : ℂ) (hs : s.im ≠ 0) :
    (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2 = mszF s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s - 1 ≠ 0 := by intro h; apply hs; have := congrArg Complex.im h; simpa using this
  have h1' : 1 - s ≠ 0 := by intro h; apply h1; linear_combination -h
  have hF := msz_F_ne hs
  have hG : Complex.Gammaℝ s ≠ 0 := by intro h; apply hF; rw [mszF, h, mul_zero]
  rw [riemannZeta_def_of_ne_zero h0, completedRiemannZeta_eq, mszF]
  field_simp
  ring


open Filter Topology

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
private lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

private noncomputable def xiM (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

/-- Under RH, zeros of `xiM` lie on the critical line. -/
private lemma xiM_zero_re {s : ℂ} (hx' : xiM s = 0) : s.re = 1/2 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiM at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    linear_combination (-1 : ℂ) * hx
  rcases le_or_gt 1 s.re with h | h
  · exact absurd hΛ (completed_ne_zero_of_one_le_re h hs1)
  rcases le_or_gt s.re 0 with h' | h'
  · have : 1 ≤ (1 - s).re := by simp; linarith
    refine absurd ?_ (completed_ne_zero_of_one_le_re this ?_)
    · rw [completedRiemannZeta_one_sub]; exact hΛ
    · intro h2; apply hs0; linear_combination -h2
  have hζ : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]
  apply riemann_hypothesis s hζ
  · rintro ⟨n, hn⟩
    rw [hn] at h'
    simp at h'
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · exact hs1

private noncomputable def FP (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

private lemma FP_eq (z : ℂ) : FP z = xiM (z + 1/2) := by
  unfold FP xiM; ring

private lemma FP_ne_zero {w : ℂ} (hw : w.re ≠ 0) : FP w ≠ 0 := by
  rw [FP_eq]
  intro h
  have := xiM_zero_re h
  simp at this
  exact hw this

private lemma FP_zero_ne : FP 0 ≠ 0 := by
  have := XiHadamardPortPublished.concrete_xi_no_real_zeros (1/2 : ℝ)
  rw [FP_eq, xiM]
  simpa using this

private lemma xiM_two : xiM 2 = (Real.pi : ℂ) / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hG : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    rw [Complex.Gammaℝ_def]
    norm_num [Complex.cpow_neg_one]
  have h2 : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
    have := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
    rw [riemannZeta_two, hG, div_inv_eq_mul] at this
    have h3 : completedRiemannZeta 2 * Real.pi = (Real.pi : ℂ) / 6 * Real.pi := by
      rw [← this]; ring
    exact mul_right_cancel₀ hpi h3
  have h0 := completedRiemannZeta_eq 2
  rw [h2] at h0
  unfold xiM
  have : completedRiemannZeta₀ 2 = (Real.pi : ℂ) / 6 + 1/2 + 1/(1-2) := by
    linear_combination -h0
  rw [this]; norm_num; ring

private lemma factor_lt {a wa wb : ℂ} (hre : a.re = 0) (hpos : 0 < a.im)
    (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖1 + wa ^ 2 / (-a ^ 2)‖ < ‖1 + wb ^ 2 / (-a ^ 2)‖ := by
  have ha : -a ^ 2 = ((a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, hre]
  have hc : (0:ℝ) < a.im ^ 2 := by positivity
  have hc' : ((a.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrw : ∀ w : ℂ, 1 + w ^ 2 / (-a ^ 2) = (((a.im ^ 2 : ℝ) : ℂ) + w ^ 2) / ((a.im ^ 2 : ℝ) : ℂ) := by
    intro w; rw [ha]; field_simp
  rw [hrw, hrw, norm_div, norm_div]
  apply div_lt_div_of_pos_right _ (by simpa using hc)
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im, zero_add]
  rw [him] at *
  have hX' : wa.re * wa.re < wb.re * wb.re := by nlinarith
  have hpos2 : 0 < 2 * (a.im * a.im) + 2 * (wb.im * wb.im) + wa.re * wa.re + wb.re * wb.re := by
    nlinarith [mul_self_nonneg wb.im, mul_self_nonneg wa.re, mul_self_nonneg wb.re]
  nlinarith [mul_pos (sub_pos.mpr hX') hpos2]

private lemma zero_re_of_order {a : ℂ} (h : analyticOrderNatAt FP a ≠ 0) : a.re = 0 := by
  have h1 : analyticOrderAt FP a ≠ 0 := by
    intro h0; apply h; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FP_eq] at h2
  have := xiM_zero_re h2
  simpa using this

private lemma main_lt {wa wb : ℂ} (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖FP wa‖ < ‖FP wb‖ := by
  let U : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FP z.val)
  have key : ∀ w : ℂ, Multipliable (fun p : U => 1+w^2/(-p.1.val^2)) ∧
      FP w / FP 0 = ∏' p : U, (1+w^2/(-p.1.val^2)) :=
    XiPairingPublished.concrete_upper_paired_product
  have h0 := FP_zero_ne
  have hwb : wb.re ≠ 0 := by
    intro h; rw [h] at hX; nlinarith [sq_nonneg wa.re]
  have hFb := FP_ne_zero hwb
  have hP : ∀ w, FP w = FP 0 * ∏' p : U, (1+w^2/(-p.1.val^2)) := by
    intro w; rw [← (key w).2]; field_simp
  -- nonempty
  have hne : Nonempty U := by
    by_contra hU
    rw [not_nonempty_iff] at hU
    have hc : ∀ w, FP w = FP 0 := by intro w; rw [hP w, tprod_empty, mul_one]
    have e1 : FP (-1/2) = 1/2 := by unfold FP; ring_nf
    have e2 : FP (3/2) = (Real.pi : ℂ) / 6 := by
      rw [FP_eq]; norm_num; exact xiM_two
    have := (hc (3/2)).trans (hc (-1/2)).symm
    rw [e1, e2] at this
    have h3 : (Real.pi : ℂ) = 3 := by linear_combination 6 * this
    have : Real.pi = 3 := by exact_mod_cast h3
    linarith [Real.pi_gt_three]
  obtain ⟨p0⟩ := hne
  set g : U → ℂ → ℂ := fun p w => 1+w^2/(-p.1.val^2) with hg
  have hgle : ∀ p : U, ‖g p wa‖ < ‖g p wb‖ := by
    intro p
    have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
      intro h; have := p.2.isLt; omega
    exact factor_lt (zero_re_of_order hord) p.1.2 him hX
  set Pa := ‖∏' p : U, g p wa‖
  set Pb := ‖∏' p : U, g p wb‖
  have hTa := (key wa).1.hasProd.norm
  have hTb := (key wb).1.hasProd.norm
  have hlim : ‖g p0 wb‖ * Pa ≤ ‖g p0 wa‖ * Pb := by
    apply le_of_tendsto_of_tendsto (hTa.const_mul _) (hTb.const_mul _)
    filter_upwards [Filter.eventually_ge_atTop {p0}] with S hS
    have hp0 : p0 ∈ S := Finset.singleton_subset_iff.mp hS
    rw [← Finset.mul_prod_erase S _ hp0, ← Finset.mul_prod_erase S (fun p => ‖g p wb‖) hp0]
    have : ∏ x ∈ S.erase p0, ‖g x wa‖ ≤ ∏ x ∈ S.erase p0, ‖g x wb‖ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => (hgle i).le)
    have hn : 0 ≤ ‖g p0 wb‖ * ‖g p0 wa‖ := by positivity
    calc ‖g p0 wb‖ * (‖g p0 wa‖ * ∏ x ∈ S.erase p0, ‖g x wa‖)
        = (‖g p0 wb‖ * ‖g p0 wa‖) * ∏ x ∈ S.erase p0, ‖g x wa‖ := by ring
      _ ≤ (‖g p0 wb‖ * ‖g p0 wa‖) * ∏ x ∈ S.erase p0, ‖g x wb‖ :=
          mul_le_mul_of_nonneg_left this hn
      _ = ‖g p0 wa‖ * (‖g p0 wb‖ * ∏ x ∈ S.erase p0, ‖g x wb‖) := by ring
  have hna : ‖FP wa‖ = ‖FP 0‖ * Pa := by rw [hP wa, norm_mul]
  have hnb : ‖FP wb‖ = ‖FP 0‖ * Pb := by rw [hP wb, norm_mul]
  have hF0 : 0 < ‖FP 0‖ := norm_pos_iff.mpr h0
  rw [hna, hnb]
  apply mul_lt_mul_of_pos_left _ hF0
  have hPb : 0 < Pb := by
    have : 0 < ‖FP wb‖ := norm_pos_iff.mpr hFb
    rw [hnb] at this
    exact pos_of_mul_pos_right this hF0.le
  rcases (norm_nonneg (∏' p : U, g p wa)).eq_or_lt with hPa | hPa
  · change 0 = Pa at hPa
    rw [← hPa]; exact hPb
  change 0 < Pa at hPa
  have hA := norm_nonneg (g p0 wa)
  have hAB := hgle p0
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon hA, mul_lt_mul_of_pos_right hAB hPa]

private lemma xi_eq_FP (σ t : ℝ) :
    (1 + ((σ : ℂ) + (t : ℂ) * Complex.I) * (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) *
      completedRiemannZeta₀ ((σ : ℂ) + (t : ℂ) * Complex.I)) / 2 =
      FP (((σ - 1/2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  rw [FP_eq, xiM]; push_cast; ring_nf

private lemma xi_lt_of_sq {σ₁ σ₂ t : ℝ} (h : (σ₁ - 1/2) ^ 2 < (σ₂ - 1/2) ^ 2) :
    ‖(1 + ((σ₁ : ℂ) + (t : ℂ) * Complex.I) * (((σ₁ : ℂ) + (t : ℂ) * Complex.I) - 1) *
      completedRiemannZeta₀ ((σ₁ : ℂ) + (t : ℂ) * Complex.I)) / 2‖ <
    ‖(1 + ((σ₂ : ℂ) + (t : ℂ) * Complex.I) * (((σ₂ : ℂ) + (t : ℂ) * Complex.I) - 1) *
      completedRiemannZeta₀ ((σ₂ : ℂ) + (t : ℂ) * Complex.I)) / 2‖ := by
  rw [xi_eq_FP, xi_eq_FP]
  apply main_lt
  · simp
  · simpa using h


theorem solution :
    ∀ t : ℝ, 8 ≤ t → StrictAntiOn (fun σ : ℝ => ‖riemannZeta ((σ : ℂ)+(t : ℂ)*Complex.I)‖) (Set.Iic (1/2 : ℝ)) := by
  intro t ht a ha b hb hab
  simp only [Set.mem_Iic] at ha hb
  have ht0 : t ≠ 0 := by linarith
  have him : ∀ σ : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I).im ≠ 0 := fun σ => by simpa using ht0
  have hz : ∀ σ : ℝ, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ =
      2 * ‖(1 + ((σ : ℂ) + (t : ℂ) * Complex.I) * (((σ : ℂ) + (t : ℂ) * Complex.I) - 1) *
        completedRiemannZeta₀ ((σ : ℂ) + (t : ℂ) * Complex.I)) / 2‖ /
        ‖mszF ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    intro σ
    rw [msz_xi_eq _ (him σ), norm_div, norm_mul]
    have hF : 0 < ‖mszF ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr (msz_F_ne (him σ))
    field_simp
    simp
  have hxi := xi_lt_of_sq (σ₁ := b) (σ₂ := a) (t := t) (by nlinarith)
  have hFa : 0 < ‖mszF ((a : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr (msz_F_ne (him a))
  have hFb : 0 < ‖mszF ((b : ℂ) + (t : ℂ) * Complex.I)‖ := norm_pos_iff.mpr (msz_F_ne (him b))
  have hmono := msz_F_mono t ht (Set.mem_Iic.mpr ha) (Set.mem_Iic.mpr hb) hab.le
  simp only at hmono
  have hFab : ‖mszF ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ ‖mszF ((b : ℂ) + (t : ℂ) * Complex.I)‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hmono
  show ‖riemannZeta ((b : ℂ) + (t : ℂ) * Complex.I)‖ < ‖riemannZeta ((a : ℂ) + (t : ℂ) * Complex.I)‖
  rw [hz a, hz b]
  set Xa := ‖(1 + ((a : ℂ) + (t : ℂ) * Complex.I) * (((a : ℂ) + (t : ℂ) * Complex.I) - 1) *
        completedRiemannZeta₀ ((a : ℂ) + (t : ℂ) * Complex.I)) / 2‖
  set Xb := ‖(1 + ((b : ℂ) + (t : ℂ) * Complex.I) * (((b : ℂ) + (t : ℂ) * Complex.I) - 1) *
        completedRiemannZeta₀ ((b : ℂ) + (t : ℂ) * Complex.I)) / 2‖
  have hXb : 0 ≤ Xb := norm_nonneg _
  rw [div_lt_div_iff₀ hFb hFa]
  nlinarith [mul_le_mul_of_nonneg_left hFab hXb]
