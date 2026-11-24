-- Prove2me | solution 1 for BroughanRH.speiser
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T02:00:33.530057+00:00
-- url     : https://prove2.me/submissions/86375ff1-885f-458c-991b-cb3363c2e4aa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Complex_hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant
import Theorems.Thm_TaoFivePrimes_zeta_ne_zero_strip_im_two_to_fourteen
import Theorems.Thm_XiHadamardPortPublished_concrete_xi_no_real_zeros
import Theorems.Thm_XiPairingPublished_concrete_upper_paired_product
import Theorems.Thm_Zeta23_StirlingVert_digamma_eq
import Theorems.Thm_Zeta23_StirlingVert_norm_eps_le
import Theorems.Thm_riemann_hypothesis
import Theorems.Thm_zeta_ne_zero_of_mem_strip_of_abs_im_le_two

section S1

open Complex

/-- Telescoping tail bound. -/
lemma nm_tsum_norm_le (f : ℕ → ℂ) {c K : ℝ} (hc : 1 < c) (hK : 0 ≤ K)
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

lemma nm_re_le_norm_shift (W : ℂ) (n : ℕ) (k : ℝ) (h : 0 ≤ (n:ℝ) + k + W.re) :
    (n:ℝ) + k + W.re ≤ ‖(n:ℂ) + k + W‖ := by
  have := Complex.re_le_norm ((n:ℂ) + k + W)
  simpa using this

/-- Two-sided Stirling bound for `Re ψ`. -/
lemma nm_re_digamma_bound {W : ℂ} (ha : 0 < W.re) (hy : 1/2 ≤ |W.im|) :
    |(Complex.digamma W).re - (Real.log ((1 + W.re) ^ 2 + W.im ^ 2) / 2 - W.re / (W.re ^ 2 + W.im ^ 2)
      - (1/2) * ((1 + W.re) / ((1 + W.re) ^ 2 + W.im ^ 2)))|
      ≤ (1/2) / (W.re * (W.re + 1)) + 1 / (3 * |W.im| * W.re) := by
  rw [Zeta23.StirlingVert.digamma_eq ha hy]
  set a := W.re with ha_def
  set y := |W.im| with hy_def
  have hypos : 0 < y := by linarith
  have hρ : ‖∑' n, Zeta23.StirlingVert.rho W n‖ ≤ (1 / (1 + a)) / ((1 + a) - 1) := by
    apply nm_tsum_norm_le _ (by linarith) (by positivity)
    intro n
    unfold Zeta23.StirlingVert.rho
    rw [norm_div, norm_one, norm_mul, norm_pow]
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    have h1 : (n:ℝ) + 1 + a ≤ ‖(n:ℂ) + 1 + W‖ := by
      have := nm_re_le_norm_shift W n 1 (by linarith); push_cast at this; exact this
    have h2 : (n:ℝ) + 2 + a ≤ ‖(n:ℂ) + 2 + W‖ := by
      have := nm_re_le_norm_shift W n 2 (by linarith); push_cast at this; exact this
    have hp1 : 0 < (n:ℝ) + 1 + a := by linarith
    have hq : ((n:ℝ) + 1 + a) ^ 2 ≤ ‖(n:ℂ) + 1 + W‖ ^ 2 := by
      exact pow_le_pow_left₀ hp1.le h1 2
    calc 1 / (‖(n:ℂ) + 1 + W‖ ^ 2 * ‖(n:ℂ) + 2 + W‖) ≤ 1 / (((n:ℝ) + 1 + a) ^ 2 * (1 + a)) := by
          apply one_div_le_one_div_of_le (mul_pos (pow_pos hp1 2) (by linarith))
          apply mul_le_mul hq (by linarith) (by linarith) (by positivity)
      _ = (1 / (1 + a)) / ((n:ℝ) + (1 + a)) ^ 2 := by
          rw [div_div]; ring_nf
  have hε : ‖∑' n : ℕ, Zeta23.StirlingVert.eps W ((n:ℝ) + 1)‖ ≤ (1 / (3 * y)) / ((1 + a) - 1) := by
    apply nm_tsum_norm_le _ (by linarith) (by have : 0 < 3 * y := by linarith
                                              positivity)
    intro n
    have he := Zeta23.StirlingVert.norm_eps_le ha hy (m := (n:ℝ) + 1) (by positivity)
    have hc : (((n:ℝ) + 1 : ℝ) : ℂ) + W = (n:ℂ) + 1 + W := by push_cast; ring
    rw [hc] at he
    rw [← hy_def] at he
    refine he.trans ?_
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    have h1 : (n:ℝ) + 1 + a ≤ ‖(n:ℂ) + 1 + W‖ := by
      have := nm_re_le_norm_shift W n 1 (by linarith); push_cast at this; exact this
    have hp1 : 0 < (n:ℝ) + 1 + a := by linarith
    have hq : ((n:ℝ) + 1 + a) ^ 2 ≤ ‖(n:ℂ) + 1 + W‖ ^ 2 := pow_le_pow_left₀ hp1.le h1 2
    have hp1' : 0 < (n:ℝ) + (1 + a) := by linarith
    rw [div_div, div_le_div_iff₀ (by nlinarith [pow_pos hp1 2]) (by nlinarith [pow_pos hp1' 2])]
    have : ((n:ℝ) + (1 + a)) ^ 2 = ((n:ℝ) + 1 + a) ^ 2 := by ring
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ 3 * y)]
  have hlog : (Complex.log (1 + W)).re = Real.log ((1 + a) ^ 2 + W.im ^ 2) / 2 := by
    rw [Complex.log_re, Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
    simp [ha_def]; ring_nf
  have hinv : (1 / W).re = a / (a ^ 2 + W.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]; ring
  have hinv2 : ((1 / 2 : ℂ) * (1 + W)⁻¹).re = (1/2) * ((1 + a) / ((1 + a) ^ 2 + W.im ^ 2)) := by
    rw [show ((1 / 2 : ℂ) * (1 + W)⁻¹).re = (1/2) * ((1 + W)⁻¹).re by simp [Complex.mul_re]]
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, zero_add]
    ring
  have hρre : |((1 / 2 : ℂ) * ∑' n, Zeta23.StirlingVert.rho W n).re| ≤ (1/2) * ‖∑' n, Zeta23.StirlingVert.rho W n‖ := by
    have : ((1 / 2 : ℂ) * ∑' n, Zeta23.StirlingVert.rho W n).re = (1/2) * (∑' n, Zeta23.StirlingVert.rho W n).re := by
      simp [Complex.mul_re]
    rw [this, abs_mul]
    have := Complex.abs_re_le_norm (∑' n, Zeta23.StirlingVert.rho W n)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    linarith
  have hεre := Complex.abs_re_le_norm (∑' n : ℕ, Zeta23.StirlingVert.eps W ((n:ℝ) + 1))
  simp only [Complex.add_re, Complex.sub_re]
  rw [hlog, hinv, hinv2]
  have e1 : (1 / (1 + a)) / ((1 + a) - 1) = 1 / (a * (a + 1)) := by
    rw [show (1 + a) - 1 = a by ring, div_div]; ring
  have e2 : (1 / (3 * y)) / ((1 + a) - 1) = 1 / (3 * y * a) := by
    rw [show (1 + a) - 1 = a by ring, div_div]
  rw [e1] at hρ; rw [e2] at hε
  have e3 : (1/2) / (a * (a + 1)) = (1/2) * (1 / (a * (a + 1))) := by ring
  rw [e3]
  rw [abs_le] at hρre hεre ⊢
  constructor <;> nlinarith [hρ, hε]

end S1

section S2

open Complex

lemma nm_digamma_shift (z : ℂ) (hz : 0 < z.re) (N : ℕ) :
    Complex.digamma z = Complex.digamma (z + N) - ∑ k ∈ Finset.range N, 1 / (z + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : ∀ m : ℕ, z + N ≠ -(m:ℂ) := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ m := m.cast_nonneg
      have : (0:ℝ) ≤ N := N.cast_nonneg
      linarith
    have := Complex.digamma_apply_add_one (z + N) hs
    rw [Finset.sum_range_succ]
    push_cast
    rw [show z + ((N:ℂ) + 1) = z + N + 1 by ring, this, ih]
    simp [one_div]

lemma nm_gauss (x y : ℝ) (hx : 0 < x) :
    HasSum (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (x + y * I)))
      (Complex.digamma (x + y * I) + (Real.eulerMascheroniConstant : ℂ)) :=
  Complex.hasSum_one_div_add_one_sub_one_div_add_eq_digamma_add_eulerMascheroniConstant _ (by simpa using hx)

lemma nm_term_re (x y : ℝ) (k : ℕ) (hx : 0 < x) :
    ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (x + y * I))).re
      = 1 / ((k:ℝ) + 1) - ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y ^ 2) := by
  have h1 : ((1 : ℂ) / ((k : ℂ) + 1)) = (((1 / ((k:ℝ) + 1) : ℝ)) : ℂ) := by push_cast; rfl
  rw [Complex.sub_re, h1, Complex.ofReal_re, one_div ((k:ℂ) + (x + y * I)), Complex.inv_re, Complex.normSq_apply]
  simp; ring

lemma nm_term_im (x y : ℝ) (k : ℕ) (hx : 0 < x) :
    ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (x + y * I))).im
      = y / (((k:ℝ) + x) ^ 2 + y ^ 2) := by
  have h1 : ((1 : ℂ) / ((k : ℂ) + 1)) = (((1 / ((k:ℝ) + 1) : ℝ)) : ℂ) := by push_cast; rfl
  rw [Complex.sub_im, h1, Complex.ofReal_im, one_div ((k:ℂ) + (x + y * I)), Complex.inv_im, Complex.normSq_apply]
  simp; ring

lemma nm_gauss_re (x y : ℝ) (hx : 0 < x) :
    HasSum (fun k : ℕ => 1 / ((k:ℝ) + 1) - ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y ^ 2))
      ((Complex.digamma (x + y * I)).re + Real.eulerMascheroniConstant) := by
  have h := (nm_gauss x y hx).mapL Complex.reCLM
  simp only [Complex.reCLM_apply, Complex.add_re, Complex.ofReal_re] at h
  convert h using 1
  funext k; exact (nm_term_re x y k hx).symm

lemma nm_gauss_im (x y : ℝ) (hx : 0 < x) :
    HasSum (fun k : ℕ => y / (((k:ℝ) + x) ^ 2 + y ^ 2)) ((Complex.digamma (x + y * I)).im) := by
  have h := (nm_gauss x y hx).mapL Complex.imCLM
  simp only [Complex.imCLM_apply, Complex.add_im, Complex.ofReal_im, add_zero] at h
  convert h using 1
  funext k; exact (nm_term_im x y k hx).symm

lemma nm_re_digamma_mono (x y1 y2 : ℝ) (hx : 0 < x) (h : y1 ^ 2 ≤ y2 ^ 2) :
    (Complex.digamma (x + y1 * I)).re ≤ (Complex.digamma (x + y2 * I)).re := by
  have := hasSum_le (fun k : ℕ => ?_) (nm_gauss_re x y1 hx) (nm_gauss_re x y2 hx)
  · linarith
  · have hk : 0 < (k:ℝ) + x := by have := (k.cast_nonneg : (0:ℝ) ≤ k); linarith
    have : ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y2 ^ 2) ≤ ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y1 ^ 2) :=
      div_le_div_of_nonneg_left hk.le (by positivity) (by linarith)
    linarith

lemma nm_im_digamma_anti (x1 x2 y : ℝ) (hx : 0 < x1) (h : x1 ≤ x2) (hy : 0 ≤ y) :
    (Complex.digamma (x2 + y * I)).im ≤ (Complex.digamma (x1 + y * I)).im := by
  refine hasSum_le (fun k : ℕ => ?_) (nm_gauss_im x2 y (by linarith)) (nm_gauss_im x1 y hx)
  have hk : 0 < (k:ℝ) + x1 := by have := (k.cast_nonneg : (0:ℝ) ≤ k); linarith
  apply div_le_div_of_nonneg_left hy (by positivity)
  nlinarith

lemma nm_im_digamma_lower (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (M : ℕ) (hM : y ^ 2 ≤ M + x) :
    ∑ k ∈ Finset.range M, y / (((k:ℝ) + x) ^ 2 + y ^ 2) + y / ((M:ℝ) + x)
      ≤ (Complex.digamma (x + y * I)).im := by
  have hS := nm_gauss_im x y hx
  set f : ℕ → ℝ := fun k => y / (((k:ℝ) + x) ^ 2 + y ^ 2) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by
    have hk : 0 < (k:ℝ) + x := by have := (k.cast_nonneg : (0:ℝ) ≤ k); linarith
    simp only [hf]; positivity
  -- tail telescoping lower bound
  have htel : ∀ n : ℕ, y / ((M:ℝ) + x) - y / ((M:ℝ) + n + x) ≤ ∑ k ∈ Finset.range n, f (k + M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have hc : 0 < (M:ℝ) + n + x := by
        have := (n.cast_nonneg : (0:ℝ) ≤ n); have := (M.cast_nonneg : (0:ℝ) ≤ M); linarith
      have key : y / ((M:ℝ) + n + x) - y / ((M:ℝ) + (n+1:ℕ) + x) ≤ f (n + M) := by
        simp only [hf]
        push_cast
        rw [div_sub_div _ _ hc.ne' (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
        have hn : (0:ℝ) ≤ n := n.cast_nonneg
        have : y ^ 2 ≤ (M:ℝ) + n + x := by linarith
        nlinarith [mul_nonneg hy (sub_nonneg.mpr this), sq_nonneg y]
      linarith
  have hsplit := (hS.summable.sum_add_tsum_nat_add M)
  rw [hS.tsum_eq] at hsplit
  have htail_s : Summable (fun k => f (k + M)) := (summable_nat_add_iff M).mpr hS.summable
  have htail : y / ((M:ℝ) + x) ≤ ∑' k, f (k + M) := by
    have hlim : Filter.Tendsto (fun n : ℕ => y / ((M:ℝ) + x) - y / ((M:ℝ) + n + x)) Filter.atTop
        (nhds (y / ((M:ℝ) + x) - 0)) := by
      apply tendsto_const_nhds.sub
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      apply Filter.tendsto_atTop_add_const_right
      apply Filter.tendsto_atTop_add_const_left
      exact tendsto_natCast_atTop_atTop
    rw [sub_zero] at hlim
    apply le_of_tendsto' hlim
    intro n
    exact (htel n).trans (htail_s.sum_le_tsum _ (fun k _ => hf0 _))
  rw [← hsplit]
  linarith

end S2

section S3

open Complex

lemma nm_re_shift (x y : ℝ) (hx : 0 < x) (N : ℕ) :
    (Complex.digamma ((x:ℂ) + y * I)).re = (Complex.digamma (((x + N : ℝ) : ℂ) + y * I)).re
      - ∑ k ∈ Finset.range N, ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y ^ 2) := by
  rw [nm_digamma_shift ((x:ℂ) + y * I) (by simpa using hx) N, Complex.sub_re, Complex.re_sum]
  congr 1
  · congr 2; push_cast; ring
  · apply Finset.sum_congr rfl
    intro k _
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp; ring

lemma nm_h_dec {c c0 y : ℝ} (hy : 0 < y) (h1 : y ≤ c0) (h2 : c0 ≤ c) :
    c / (c ^ 2 + y ^ 2) ≤ c0 / (c0 ^ 2 + y ^ 2) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr (show y ^ 2 ≤ c * c0 by nlinarith))]

lemma nm_h_inc {c c1 y : ℝ} (hc : 0 < c) (h1 : c ≤ c1) (h2 : c1 ≤ y) :
    c / (c ^ 2 + y ^ 2) ≤ c1 / (c1 ^ 2 + y ^ 2) := by
  have hc1 : 0 < c1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show c * c1 ≤ y ^ 2 by nlinarith))]

lemma nm_f_min {c ya yb y : ℝ} (hc : 0 < c) (hya : 0 < ya) (h1 : ya ≤ y) (h2 : y ≤ yb) :
    min (ya / (c ^ 2 + ya ^ 2)) (yb / (c ^ 2 + yb ^ 2)) ≤ y / (c ^ 2 + y ^ 2) := by
  by_cases hcy : y * ya ≤ c ^ 2
  · apply (min_le_left _ _).trans
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hcy)]
  · push Not at hcy
    apply (min_le_right _ _).trans
    have hyy : 0 < y := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ y * yb - c ^ 2 by nlinarith)]

lemma nm_log_pi_lt : Real.log Real.pi < 1.0986122888 + (3.141593 / 3 - 1) := by
  have h3 := Real.log_three_lt_d9
  have hp := Real.pi_lt_d6
  have e : Real.log Real.pi = Real.log 3 + Real.log (Real.pi / 3) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
  have := Real.log_le_sub_one_of_pos (show 0 < Real.pi / 3 by positivity)
  rw [e]; linarith

lemma nm_log_pi_gt : 1.0986122885 + (1 - 3 / 3.141592) < Real.log Real.pi := by
  have h3 := Real.log_three_gt_d9
  have hp := Real.pi_gt_d6
  have e : Real.log Real.pi = Real.log 3 + Real.log (Real.pi / 3) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
  have := Real.one_sub_inv_le_log_of_pos (show 0 < Real.pi / 3 by positivity)
  have h4 : 1 - 3 / 3.141592 < 1 - (Real.pi / 3)⁻¹ := by
    rw [inv_div]
    have : 3 / Real.pi < 3 / 3.141592 := div_lt_div_of_pos_left (by norm_num) (by norm_num) hp
    linarith
  rw [e]; linarith

lemma nm_log108 : Real.log 108 = 2 * Real.log 2 + 3 * Real.log 3 := by
  rw [show (108:ℝ) = 2 ^ 2 * 3 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]; push_cast; ring

lemma nm_log_ge (q : ℝ) (hq : 0 < q) : Real.log 108 + (1 - 108 / q) ≤ Real.log q := by
  have e : Real.log q = Real.log 108 + Real.log (q / 108) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have := Real.one_sub_inv_le_log_of_pos (show 0 < q / 108 by positivity)
  rw [inv_div] at this; linarith

lemma nm_log_le (q : ℝ) (hq : 0 < q) : Real.log q ≤ Real.log 108 + (q / 108 - 1) := by
  have e : Real.log q = Real.log 108 + Real.log (q / 108) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; field_simp
  have := Real.log_le_sub_one_of_pos (show 0 < q / 108 by positivity)
  linarith

/-- Test A: `Re E > 0` for `t ≥ 29/4`. -/
theorem nm_testA (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1/2) (ht : 29/4 ≤ t) :
    0 < (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) - Real.log Real.pi / 2
      + (1/2) * (Complex.digamma (((σ/2 + 1 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).re := by
  set x : ℝ := σ/2 + 1 with hxdef
  have hx1 : 1 ≤ x := by linarith
  have hx2 : x ≤ 5/4 := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 29/8 := ⟨_, rfl⟩
  have hmono := nm_re_digamma_mono x y (t/2) hx0 (by rw [hy]; nlinarith)
  have hsh := nm_re_shift x y hx0 8
  have hst := nm_re_digamma_bound (W := ((x + (8:ℕ) : ℝ) : ℂ) + (y:ℂ) * I)
    (by simp; linarith) (by simp; rw [hy, abs_of_pos (by norm_num)]; norm_num)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add,
    add_zero] at hst
  push_cast at hst hsh
  rw [abs_le] at hst
  have hlogq : Real.log (100 + y ^ 2) ≤ Real.log ((1 + (x + 8)) ^ 2 + y ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlq := nm_log_ge (100 + y ^ 2) (by positivity)
  have l108 := nm_log108
  have l2 := Real.log_two_gt_d9
  have l3 := Real.log_three_gt_d9
  have lpi := nm_log_pi_lt
  have hyabs : |y| = 29/8 := by rw [hy]; norm_num
  rw [hyabs] at hst
  -- the main terms
  have m1 : (x + 8) / ((x + 8) ^ 2 + y ^ 2) ≤ 576 / 6025 :=
    (nm_h_dec (c0 := 9) (by norm_num [hy]) (by norm_num [hy]) (by linarith)).trans (le_of_eq (by norm_num [hy]))
  have m2 : (1 + (x + 8)) / ((1 + (x + 8)) ^ 2 + y ^ 2) ≤ 640 / 7241 :=
    (nm_h_dec (c0 := 10) (by norm_num [hy]) (by norm_num [hy]) (by linarith)).trans (le_of_eq (by norm_num [hy]))
  have e1 : 1 / 2 / ((x + 8) * (x + 8 + 1)) ≤ 1 / 180 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e2 : 1 / (3 * (29 / 8) * (x + 8)) ≤ 8 / 783 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsum : ∑ k ∈ Finset.range 8, ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y ^ 2) ≤
      11742146645713936174704 / 12327117160612755099545 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, zero_add]
    have a0 : x / (x ^ 2 + y ^ 2) ≤ (5/4) / ((5/4) ^ 2 + y ^ 2) := nm_h_inc hx0 hx2 (by norm_num [hy])
    have a1 : (1 + x) / ((1 + x) ^ 2 + y ^ 2) ≤ (9/4) / ((9/4) ^ 2 + y ^ 2) :=
      nm_h_inc (by linarith) (by linarith) (by norm_num [hy])
    have a2 : (2 + x) / ((2 + x) ^ 2 + y ^ 2) ≤ (13/4) / ((13/4) ^ 2 + y ^ 2) :=
      nm_h_inc (by linarith) (by linarith) (by norm_num [hy])
    have a3 : (3 + x) / ((3 + x) ^ 2 + y ^ 2) ≤ 4 / (4 ^ 2 + y ^ 2) := nm_h_dec (by norm_num [hy]) (by norm_num [hy]) (by linarith)
    have a4 : (4 + x) / ((4 + x) ^ 2 + y ^ 2) ≤ 5 / (5 ^ 2 + y ^ 2) := nm_h_dec (by norm_num [hy]) (by norm_num [hy]) (by linarith)
    have a5 : (5 + x) / ((5 + x) ^ 2 + y ^ 2) ≤ 6 / (6 ^ 2 + y ^ 2) := nm_h_dec (by norm_num [hy]) (by norm_num [hy]) (by linarith)
    have a6 : (6 + x) / ((6 + x) ^ 2 + y ^ 2) ≤ 7 / (7 ^ 2 + y ^ 2) := nm_h_dec (by norm_num [hy]) (by norm_num [hy]) (by linarith)
    have a7 : (7 + x) / ((7 + x) ^ 2 + y ^ 2) ≤ 8 / (8 ^ 2 + y ^ 2) := nm_h_dec (by norm_num [hy]) (by norm_num [hy]) (by linarith)
    have : (5/4) / ((5/4) ^ 2 + y ^ 2) + (9/4) / ((9/4) ^ 2 + y ^ 2) + (13/4) / ((13/4) ^ 2 + y ^ 2)
      + 4 / (4 ^ 2 + y ^ 2) + 5 / (5 ^ 2 + y ^ 2) + 6 / (6 ^ 2 + y ^ 2) + 7 / (7 ^ 2 + y ^ 2)
      + 8 / (8 ^ 2 + y ^ 2) = 11742146645713936174704 / 12327117160612755099545 := by
      norm_num [hy]
    linarith
  have hrat : -(16/841) ≤ (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (σ - 1)]
  have hlq' : Real.log 108 + 329 / 7241 ≤ Real.log (100 + y ^ 2) := by
    have : (1:ℝ) - 108 / (100 + y ^ 2) = 329 / 7241 := by norm_num [hy]
    linarith
  have hfin := hst.1
  have hl : Real.log 108 > 2 * 0.6931471803 + 3 * 1.0986122885 := by rw [l108]; linarith
  have hsh2 := hsh
  have tA : Real.log ((1 + (x + 8)) ^ 2 + y ^ 2) / 2 - 576 / 6025 - (1/2) * (640 / 7241) - (1/180 + 8/783)
      ≤ (↑x + 8 + ↑y * I : ℂ).digamma.re := by linarith only [hfin, m1, m2, e1, e2]
  have tB : Real.log 108 + 329 / 7241 ≤ Real.log ((1 + (x + 8)) ^ 2 + y ^ 2) := by linarith only [hlogq, hlq']
  have hW : (Real.log 108 + 329 / 7241) / 2 - 576 / 6025 - (1/2) * (640 / 7241) - (1/180 + 8/783)
      ≤ (↑x + 8 + ↑y * I : ℂ).digamma.re := by linarith
  have hR : (Real.log 108 + 329 / 7241) / 2 - 576 / 6025 - (1/2) * (640 / 7241) - (1/180 + 8/783)
      - 11742146645713936174704 / 12327117160612755099545 ≤ (↑x + ↑y * I : ℂ).digamma.re := by linarith
  linarith

lemma nm_ratC (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1/2) (ht0 : 0 ≤ t) (ht : t ≤ 3) :
    (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) ≤ -(2/37) := by
  have hpos : 0 < (σ - 1) ^ 2 + t ^ 2 := by nlinarith
  rw [div_le_iff₀ hpos]
  have ht2 : t ^ 2 ≤ 9 := by nlinarith
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 2 * (1 - σ) - 1 by linarith) (show (0:ℝ) ≤ 18 - (1 - σ) by linarith)]

/-- Test C: `-Re E > (3/5) U` for `0 ≤ t ≤ 3`. -/
theorem nm_testC (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1/2) (ht0 : 0 ≤ t) (ht : t ≤ 3) :
    (3/5) * (3.141593 / 3 - 1) < -((σ - 1) / ((σ - 1) ^ 2 + t ^ 2) - Real.log Real.pi / 2
      + (1/2) * (Complex.digamma (((σ/2 + 1 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).re) := by
  set x : ℝ := σ/2 + 1 with hxdef
  have hx1 : 1 ≤ x := by linarith
  have hx2 : x ≤ 5/4 := by linarith
  have hx0 : 0 < x := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 3/2 := ⟨_, rfl⟩
  have hmono := nm_re_digamma_mono x (t/2) y hx0 (by rw [hy]; nlinarith)
  have hsh := nm_re_shift x y hx0 8
  have hst := nm_re_digamma_bound (W := ((x + (8:ℕ) : ℝ) : ℂ) + (y:ℂ) * I)
    (by simp; linarith) (by simp; rw [hy, abs_of_pos (by norm_num)]; norm_num)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add,
    add_zero] at hst
  push_cast at hst hsh
  rw [abs_le] at hst
  have hyabs : |y| = 3/2 := by rw [hy]; norm_num
  rw [hyabs] at hst
  have hlogq : Real.log ((1 + (x + 8)) ^ 2 + y ^ 2) ≤ Real.log ((41/4) ^ 2 + y ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hlq := nm_log_le ((41/4) ^ 2 + y ^ 2) (by positivity)
  have hlq' : Real.log ((41/4) ^ 2 + y ^ 2) ≤ Real.log 108 - 11 / 1728 := by
    have : ((41/4) ^ 2 + y ^ 2) / 108 - 1 = - (11 / 1728 : ℝ) := by rw [hy]; norm_num
    linarith
  have l108 := nm_log108
  have l2 := Real.log_two_lt_d9
  have l3 := Real.log_three_lt_d9
  have lpi := nm_log_pi_gt
  have m1 : 148 / 1405 ≤ (x + 8) / ((x + 8) ^ 2 + y ^ 2) :=
    (le_of_eq (by rw [hy]; norm_num)).trans (nm_h_dec (c := 37/4) (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith))
  have m2 : 164 / 1717 ≤ (1 + (x + 8)) / ((1 + (x + 8)) ^ 2 + y ^ 2) :=
    (le_of_eq (by rw [hy]; norm_num)).trans (nm_h_dec (c := 41/4) (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith))
  have e1 : 1 / 2 / ((x + 8) * (x + 8 + 1)) ≤ 1 / 180 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have e2 : 1 / (3 * (3 / 2) * (x + 8)) ≤ 2 / 81 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hsum : 3388294330384 / 2046982569125 ≤
      ∑ k ∈ Finset.range 8, ((k:ℝ) + x) / (((k:ℝ) + x) ^ 2 + y ^ 2) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_zero,
      Nat.cast_one, zero_add]
    have a0 : 1 / (1 ^ 2 + y ^ 2) ≤ x / (x ^ 2 + y ^ 2) := nm_h_inc (by norm_num) hx1 (by rw [hy]; linarith)
    have a1 : (9/4) / ((9/4) ^ 2 + y ^ 2) ≤ (1 + x) / ((1 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have a2 : (13/4) / ((13/4) ^ 2 + y ^ 2) ≤ (2 + x) / ((2 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have a3 : (17/4) / ((17/4) ^ 2 + y ^ 2) ≤ (3 + x) / ((3 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have a4 : (21/4) / ((21/4) ^ 2 + y ^ 2) ≤ (4 + x) / ((4 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have a5 : (25/4) / ((25/4) ^ 2 + y ^ 2) ≤ (5 + x) / ((5 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have a6 : (29/4) / ((29/4) ^ 2 + y ^ 2) ≤ (6 + x) / ((6 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have a7 : (33/4) / ((33/4) ^ 2 + y ^ 2) ≤ (7 + x) / ((7 + x) ^ 2 + y ^ 2) :=
      nm_h_dec (by rw [hy]; norm_num) (by rw [hy]; linarith) (by linarith)
    have : 1 / (1 ^ 2 + y ^ 2) + (9/4) / ((9/4) ^ 2 + y ^ 2) + (13/4) / ((13/4) ^ 2 + y ^ 2)
      + (17/4) / ((17/4) ^ 2 + y ^ 2) + (21/4) / ((21/4) ^ 2 + y ^ 2) + (25/4) / ((25/4) ^ 2 + y ^ 2)
      + (29/4) / ((29/4) ^ 2 + y ^ 2) + (33/4) / ((33/4) ^ 2 + y ^ 2)
        = 3388294330384 / 2046982569125 := by
      rw [hy]; norm_num
    linarith
  have hrat : (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) ≤ -(2/37) := nm_ratC σ t h0 h1 ht0 ht
  have hfin := hst.2
  have hl : Real.log 108 < 2 * 0.6931471808 + 3 * 1.0986122888 := by rw [l108]; linarith
  have tA : (↑x + 8 + ↑y * I : ℂ).digamma.re ≤ Real.log ((1 + (x + 8)) ^ 2 + y ^ 2) / 2 - 148 / 1405
      - (1/2) * (164 / 1717) + (1/180 + 2/81) := by linarith only [hfin, m1, m2, e1, e2]
  have tB : Real.log ((1 + (x + 8)) ^ 2 + y ^ 2) ≤ 2 * 0.6931471808 + 3 * 1.0986122888 - 11 / 1728 := by
    linarith only [hlogq, hlq', hl]
  have hR : (↑x + ↑y * I : ℂ).digamma.re ≤ (2 * 0.6931471808 + 3 * 1.0986122888 - 11 / 1728) / 2
      - 148 / 1405 - (1/2) * (164 / 1717) + (1/180 + 2/81) - 3388294330384 / 2046982569125 := by
    linarith only [tA, tB, hsh, hsum]
  linarith

lemma nm_corner (c ya yb y : ℝ) (hc : 0 < c) (hya : 0 < ya) (h1 : ya ≤ y) (h2 : y ≤ yb) :
    (if ya * yb ≤ c ^ 2 then ya / (c ^ 2 + ya ^ 2) else yb / (c ^ 2 + yb ^ 2)) ≤ y / (c ^ 2 + y ^ 2) := by
  have hy : 0 < y := by linarith
  split_ifs with h
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : y * ya ≤ c ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr this)]
  · push Not at h
    have hyb : 0 < yb := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : c ^ 2 ≤ y * yb := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr this)]

/-- Lower bound for `Im E` reduced to the critical line and to Gauss partial sums. -/
lemma nm_imE_lower (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1/2) (ht0 : 0 ≤ t) (ht : t ≤ 29/4) :
    -t / (1/4 + t ^ 2) + (1/2) * (∑ k ∈ Finset.range 14, (t/2) / (((k:ℝ) + 5/4) ^ 2 + (t/2) ^ 2)
      + (t/2) / ((14:ℕ) + 5/4))
      ≤ -t / ((σ - 1) ^ 2 + t ^ 2)
        + (1/2) * (Complex.digamma (((σ/2 + 1 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).im := by
  have hanti := nm_im_digamma_anti (σ/2 + 1) (5/4) (t/2) (by linarith) (by linarith) (by linarith)
  have hlow := nm_im_digamma_lower (5/4) (t/2) (by norm_num) (by linarith) 14 (by push_cast; nlinarith)
  have hrat : -t / (1/4 + t ^ 2) ≤ -t / ((σ - 1) ^ 2 + t ^ 2) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    apply div_le_div_of_nonneg_left ht0 (by nlinarith) (by nlinarith)
  push_cast at hlow hanti ⊢
  linarith

lemma nm_piece (ta tb : ℝ) (hta : 1/2 ≤ ta) (hab : ta ≤ tb) (htb : tb ≤ 29/4)
    (hnum : tb * (785/4) / (196 - tb ^ 2) * (3.141593 / 3 - 1) < -ta / (1/4 + ta ^ 2) + (1/2) *
      (∑ k ∈ Finset.range 14, (if (ta/2) * (tb/2) ≤ ((k:ℝ) + 5/4) ^ 2
          then (ta/2) / (((k:ℝ) + 5/4) ^ 2 + (ta/2) ^ 2) else (tb/2) / (((k:ℝ) + 5/4) ^ 2 + (tb/2) ^ 2))
        + (ta/2) / ((14:ℕ) + 5/4)))
    (t : ℝ) (h1 : ta ≤ t) (h2 : t ≤ tb) :
    t * (785/4) / (196 - t ^ 2) * (3.141593 / 3 - 1) < -t / (1/4 + t ^ 2) + (1/2) *
      (∑ k ∈ Finset.range 14, (t/2) / (((k:ℝ) + 5/4) ^ 2 + (t/2) ^ 2) + (t/2) / ((14:ℕ) + 5/4)) := by
  have hsum : ∑ k ∈ Finset.range 14, (if (ta/2) * (tb/2) ≤ ((k:ℝ) + 5/4) ^ 2
          then (ta/2) / (((k:ℝ) + 5/4) ^ 2 + (ta/2) ^ 2) else (tb/2) / (((k:ℝ) + 5/4) ^ 2 + (tb/2) ^ 2))
      ≤ ∑ k ∈ Finset.range 14, (t/2) / (((k:ℝ) + 5/4) ^ 2 + (t/2) ^ 2) := by
    apply Finset.sum_le_sum
    intro k _
    exact nm_corner _ _ _ _ (by positivity) (by linarith) (by linarith) (by linarith)
  have htail : (ta/2) / ((14:ℕ) + 5/4 : ℝ) ≤ (t/2) / ((14:ℕ) + 5/4 : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hrat : -ta / (1/4 + ta ^ 2) ≤ -t / (1/4 + t ^ 2) := by
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show (0:ℝ) ≤ t * ta - 1/4 by nlinarith)]
  have hk : t * (785/4) / (196 - t ^ 2) ≤ tb * (785/4) / (196 - tb ^ 2) := by
    have h3 : 0 < 196 - tb ^ 2 := by nlinarith
    have h4 : 196 - tb ^ 2 ≤ 196 - t ^ 2 := by nlinarith
    rw [div_le_div_iff₀ (by linarith) h3]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (show (0:ℝ) ≤ 196 + t * tb by nlinarith)]
  have hU : (0:ℝ) < 3.141593 / 3 - 1 := by norm_num
  have := mul_le_mul_of_nonneg_right hk hU.le
  linarith

/-- Test B: `Im E > k₂(t) U` for `3 ≤ t ≤ 29/4`. -/
theorem nm_testB (σ t : ℝ) (h0 : 0 ≤ σ) (h1 : σ ≤ 1/2) (ht0 : 3 ≤ t) (ht : t ≤ 29/4) :
    t * (785/4) / (196 - t ^ 2) * (3.141593 / 3 - 1) < -t / ((σ - 1) ^ 2 + t ^ 2)
        + (1/2) * (Complex.digamma (((σ/2 + 1 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).im := by
  refine lt_of_lt_of_le ?_ (nm_imE_lower σ t h0 h1 (by linarith) ht)
  rcases le_or_gt t (7/2) with h | h
  · exact nm_piece 3 (7/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t ht0 h
  rcases le_or_gt t 4 with h' | h'
  · exact nm_piece (7/2) 4 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h.le h'
  rcases le_or_gt t (9/2) with h | h
  · exact nm_piece 4 (9/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h'.le h
  rcases le_or_gt t 5 with h' | h'
  · exact nm_piece (9/2) 5 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h.le h'
  rcases le_or_gt t (11/2) with h | h
  · exact nm_piece 5 (11/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h'.le h
  rcases le_or_gt t 6 with h' | h'
  · exact nm_piece (11/2) 6 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h.le h'
  rcases le_or_gt t (13/2) with h | h
  · exact nm_piece 6 (13/2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h'.le h
  rcases le_or_gt t 7 with h' | h'
  · exact nm_piece (13/2) 7 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h.le h'
  · exact nm_piece 7 (29/4) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ]) t h'.le ht

end S3

section Z0

open Filter Topology

/-- `Λ(s) ≠ 0` for `Re s ≥ 1`, `s ≠ 1`. -/
lemma completed_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    completedRiemannZeta s ≠ 0 := by
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at hpos
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  rw [riemannZeta_def_of_ne_zero hs0] at hζ
  intro h
  rw [h, zero_div] at hζ
  exact hζ rfl

noncomputable def xiM (s : ℂ) : ℂ := (1 + s * (s-1) * completedRiemannZeta₀ s) / 2

/-- Under RH, zeros of `xiM` lie on the critical line. -/
lemma xiM_zero_re {s : ℂ} (hx' : xiM s = 0) : s.re = 1/2 := by
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

noncomputable def FP (z : ℂ) : ℂ :=
  ((z + 1/2) * ((z + 1/2) - 1) * completedRiemannZeta₀ (z + 1/2) + 1) / 2

lemma FP_eq (z : ℂ) : FP z = xiM (z + 1/2) := by
  unfold FP xiM; ring

lemma FP_ne_zero {w : ℂ} (hw : w.re ≠ 0) : FP w ≠ 0 := by
  rw [FP_eq]
  intro h
  have := xiM_zero_re h
  simp at this
  exact hw this

lemma FP_zero_ne : FP 0 ≠ 0 := by
  have := XiHadamardPortPublished.concrete_xi_no_real_zeros (1/2 : ℝ)
  rw [FP_eq, xiM]
  simpa using this

lemma xiM_two : xiM 2 = (Real.pi : ℂ) / 6 := by
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

lemma factor_lt {a wa wb : ℂ} (hre : a.re = 0) (hpos : 0 < a.im)
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

lemma zero_re_of_order {a : ℂ} (h : analyticOrderNatAt FP a ≠ 0) : a.re = 0 := by
  have h1 : analyticOrderAt FP a ≠ 0 := by
    intro h0; apply h; simp [analyticOrderNatAt, h0]
  have h2 := (analyticOrderAt_ne_zero.mp h1).2
  rw [FP_eq] at h2
  have := xiM_zero_re h2
  simpa using this


abbrev UU : Type := (z : {z : ℂ // 0 < z.im}) × Fin (analyticOrderNatAt FP z.val)

noncomputable def gg (p : UU) (w : ℂ) : ℂ := 1 + w ^ 2 / (-p.1.val ^ 2)

lemma key_UU : ∀ w : ℂ, Multipliable (fun p : UU => gg p w) ∧
    FP w / FP 0 = ∏' p : UU, gg p w :=
  XiPairingPublished.concrete_upper_paired_product

lemma UU_re (p : UU) : p.1.val.re = 0 := by
  have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
    intro h; have := p.2.isLt; omega
  exact zero_re_of_order hord

lemma UU_nonempty : Nonempty UU := by
  by_contra hU
  rw [not_nonempty_iff] at hU
  have h0 := FP_zero_ne
  have hc : ∀ w, FP w = FP 0 := by
    intro w
    have := (key_UU w).2
    rw [tprod_empty] at this
    field_simp at this
    exact this
  have e1 : FP (-1/2) = 1/2 := by unfold FP; ring_nf
  have e2 : FP (3/2) = (Real.pi : ℂ) / 6 := by
    rw [FP_eq]; norm_num; exact xiM_two
  have := (hc (3/2)).trans (hc (-1/2)).symm
  rw [e1, e2] at this
  have h3 : (Real.pi : ℂ) = 3 := by linear_combination 6 * this
  have : Real.pi = 3 := by exact_mod_cast h3
  linarith [Real.pi_gt_three]

/-- Cross-multiplied comparison isolating one factor. -/
lemma cross (p0 : UU) {wa wb : ℂ} (him : wa.im = wb.im) (hX : wa.re ^ 2 < wb.re ^ 2) :
    ‖gg p0 wb‖ * ‖FP wa‖ ≤ ‖gg p0 wa‖ * ‖FP wb‖ := by
  have h0 := FP_zero_ne
  have hP : ∀ w, FP w = FP 0 * ∏' p : UU, gg p w := by
    intro w; rw [← (key_UU w).2]; field_simp
  have hgle : ∀ p : UU, ‖gg p wa‖ ≤ ‖gg p wb‖ := fun p =>
    (factor_lt (UU_re p) p.1.2 him hX).le
  have hTa := (key_UU wa).1.hasProd.norm
  have hTb := (key_UU wb).1.hasProd.norm
  have hlim : ‖gg p0 wb‖ * ‖∏' p : UU, gg p wa‖ ≤ ‖gg p0 wa‖ * ‖∏' p : UU, gg p wb‖ := by
    apply le_of_tendsto_of_tendsto (hTa.const_mul _) (hTb.const_mul _)
    filter_upwards [Filter.eventually_ge_atTop {p0}] with S hS
    have hp0 : p0 ∈ S := Finset.singleton_subset_iff.mp hS
    rw [← Finset.mul_prod_erase S _ hp0, ← Finset.mul_prod_erase S (fun p => ‖gg p wb‖) hp0]
    have : ∏ x ∈ S.erase p0, ‖gg x wa‖ ≤ ∏ x ∈ S.erase p0, ‖gg x wb‖ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hgle i)
    have hn : 0 ≤ ‖gg p0 wb‖ * ‖gg p0 wa‖ := by positivity
    calc ‖gg p0 wb‖ * (‖gg p0 wa‖ * ∏ x ∈ S.erase p0, ‖gg x wa‖)
        = (‖gg p0 wb‖ * ‖gg p0 wa‖) * ∏ x ∈ S.erase p0, ‖gg x wa‖ := by ring
      _ ≤ (‖gg p0 wb‖ * ‖gg p0 wa‖) * ∏ x ∈ S.erase p0, ‖gg x wb‖ :=
          mul_le_mul_of_nonneg_left this hn
      _ = ‖gg p0 wa‖ * (‖gg p0 wb‖ * ∏ x ∈ S.erase p0, ‖gg x wb‖) := by ring
  rw [hP wa, hP wb, norm_mul, norm_mul]
  have := mul_le_mul_of_nonneg_left hlim (norm_nonneg (FP 0))
  linarith [this]

/-- Squared modulus of one factor. -/
lemma gg_sq (p : UU) (w : ℂ) :
    ‖gg p w‖ ^ 2 * (p.1.val.im ^ 2) ^ 2 =
      (p.1.val.im ^ 2 + w.re ^ 2 - w.im ^ 2) ^ 2 + (2 * w.re * w.im) ^ 2 := by
  have hre := UU_re p
  have hpos := p.1.2
  set a := p.1.val
  have ha : -a ^ 2 = ((a.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two, hre]
  have hc : (0:ℝ) < a.im ^ 2 := by positivity
  have hc' : ((a.im ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hrw : gg p w = (((a.im ^ 2 : ℝ) : ℂ) + w ^ 2) / ((a.im ^ 2 : ℝ) : ℂ) := by
    unfold gg; rw [ha]; field_simp
  rw [hrw, norm_div, div_pow, Complex.sq_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc, Complex.normSq_apply]
  field_simp
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, pow_two,
    Complex.mul_re, Complex.mul_im]
  ring

lemma logderiv_pos {s : ℂ} (hs : 1/2 < s.re) :
    0 < (deriv xiM s / xiM s).re := by
  have hdiff : Differentiable ℂ xiM := by
    intro z; unfold xiM; have := differentiable_completedZeta₀; fun_prop
  have hxs : xiM s ≠ 0 := by
    intro h; have := xiM_zero_re h; linarith
  obtain ⟨p0⟩ := UU_nonempty
  set γ := p0.1.val.im with hγ
  have hγpos : 0 < γ := p0.1.2
  set w0 : ℂ := s - 1/2 with hw0
  have hx0 : 0 < w0.re := by simp [hw0]; linarith
  -- the function along the horizontal direction
  let φ : ℝ → ℂ := fun h => xiM (s + h)
  let N : ℝ → ℝ := fun h => ‖φ h‖ ^ 2
  have hφ : HasDerivAt φ (deriv xiM s) 0 := by
    have h0 : HasDerivAt xiM (deriv xiM s) (s + ((0:ℝ):ℂ)) := by
      simpa using (hdiff s).hasDerivAt
    exact (h0.comp_const_add s ((0:ℝ):ℂ)).comp_ofReal
  have hN := hφ.norm_sq
  set d := 2 * inner ℝ (φ 0) (deriv xiM s) with hd
  have hφ0 : φ 0 = xiM s := by simp [φ]
  have hFP : ∀ h : ℝ, φ h = FP (w0 + h) := by
    intro h; simp only [φ, FP_eq, hw0]; ring_nf
  -- lower bound on the slope
  have hA0 : 0 < ‖gg p0 w0‖ := by
    rcases (norm_nonneg (gg p0 w0)).eq_or_lt with h | h
    · exfalso
      have hc := cross p0 (wa := w0) (wb := w0 + 1) (by simp) (by simp; nlinarith)
      rw [← h, zero_mul] at hc
      have hlt := factor_lt (UU_re p0) p0.1.2 (wa := w0) (wb := w0 + 1) (by simp) (by simp; nlinarith)
      have : 0 < ‖FP w0‖ := by
        have e := hFP 0
        simp only [Complex.ofReal_zero, add_zero] at e
        rw [← e, hφ0]; exact norm_pos_iff.mpr hxs
      have hg1 : 0 < ‖gg p0 (w0 + 1)‖ := by
        unfold gg at h ⊢; linarith
      nlinarith [mul_pos hg1 this]
    · exact h
  set A0 := ‖gg p0 w0‖
  set κ : ℝ := N 0 * (4 * w0.re / γ ^ 2) / A0 ^ 2 with hκ
  have hN0 : 0 < N 0 := by
    show 0 < ‖φ 0‖ ^ 2
    rw [hφ0]; exact pow_pos (norm_pos_iff.mpr hxs) 2
  have hκpos : 0 < κ := by
    rw [hκ]; have : 0 < 4 * w0.re / γ ^ 2 := by positivity
    positivity
  have hslope : ∀ h : ℝ, 0 < h → κ ≤ slope N 0 h := by
    intro h hh
    rw [slope_def_field, sub_zero]
    have hc := cross p0 (wa := w0) (wb := w0 + h) (by simp) (by simp; nlinarith)
    have hsq := gg_sq p0 w0
    have hsq' := gg_sq p0 (w0 + h)
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      add_zero] at hsq'
    rw [← hγ] at hsq hsq'
    have hNh : N h = ‖FP (w0 + h)‖ ^ 2 := by simp [N, hFP]
    have hN0' : N 0 = ‖FP w0‖ ^ 2 := by simp [N, hFP]
    -- squared cross inequality
    have hc2 : ‖gg p0 (w0 + h)‖ ^ 2 * N 0 ≤ A0 ^ 2 * N h := by
      rw [hNh, hN0']
      have := mul_le_mul hc hc (by positivity) (by positivity)
      nlinarith [this]
    -- growth of the factor
    have hgrow : A0 ^ 2 + 4 * w0.re * h / γ ^ 2 ≤ ‖gg p0 (w0 + h)‖ ^ 2 := by
      have hγ4 : 0 < (γ ^ 2) ^ 2 := by positivity
      have key : (A0 ^ 2 + 4 * w0.re * h / γ ^ 2) * (γ ^ 2) ^ 2 ≤
          ‖gg p0 (w0 + h)‖ ^ 2 * (γ ^ 2) ^ 2 := by
        rw [hsq']
        have : (A0 ^ 2 + 4 * w0.re * h / γ ^ 2) * (γ ^ 2) ^ 2 =
            A0 ^ 2 * (γ ^ 2) ^ 2 + 4 * w0.re * h * γ ^ 2 := by
          field_simp
        rw [this, hsq]
        nlinarith [mul_pos hx0 hh, sq_nonneg w0.im, sq_nonneg w0.re, mul_pos (mul_pos hx0 hh) hγpos,
          mul_nonneg (mul_nonneg hx0.le hh.le) (sq_nonneg w0.im), sq_nonneg h,
          mul_nonneg (sq_nonneg h) (sq_nonneg w0.im), mul_nonneg hh.le (sq_nonneg w0.im),
          mul_nonneg (mul_nonneg hx0.le hh.le) (sq_nonneg w0.re),
          mul_nonneg (sq_nonneg h) (sq_nonneg w0.re), mul_nonneg hh.le hx0.le, pow_pos hh 3,
          pow_pos hh 4, mul_nonneg (mul_nonneg hh.le hh.le) (mul_nonneg hx0.le hx0.le)]
      exact le_of_mul_le_mul_right key hγ4
    have hA0sq : 0 < A0 ^ 2 := by positivity
    rw [hκ, div_le_div_iff₀ hA0sq hh]
    have hN0nn := hN0.le
    have := mul_le_mul_of_nonneg_right hgrow hN0nn
    rw [show 4 * w0.re * h / γ ^ 2 = (4 * w0.re / γ ^ 2) * h by ring] at this
    linarith [this, hc2]
  -- pass to the limit
  have hlim : Tendsto (slope N 0) (𝓝[>] 0) (𝓝 d) := by
    have := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0:ℝ)) (by simp)).mp
      hN.hasDerivWithinAt
    exact this
  have hdk : κ ≤ d := ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun h hh => hslope h hh)
  have hdpos : 0 < d := lt_of_lt_of_le hκpos hdk
  rw [hd, hφ0, Complex.inner] at hdpos
  -- Re (ξ'/ξ) = Re (ξ' * conj ξ) / |ξ|^2
  have hns : 0 < Complex.normSq (xiM s) := Complex.normSq_pos.mpr hxs
  rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_pos (by linarith) (inv_pos.mpr hns)


end Z0

section Z1

open Filter Topology

lemma xiM_zeta_zero {s : ℂ} (hx' : xiM s = 0) (h0 : 0 < s.re) : riemannZeta s = 0 := by
  have hx : 1 + s * (s-1) * completedRiemannZeta₀ s = 0 := by
    unfold xiM at hx'; linear_combination 2 * hx'
  have hs0 : s ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hs1 : s ≠ 1 := by rintro h; rw [h] at hx; simp at hx
  have hΛ : completedRiemannZeta s = 0 := by
    rw [completedRiemannZeta_eq]
    have hss : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    linear_combination (-1 : ℂ) * hx
  rw [riemannZeta_def_of_ne_zero hs0, hΛ, zero_div]

lemma UU_FP_zero (p : UU) : FP p.1.val = 0 := by
  have hord : analyticOrderNatAt FP p.1.val ≠ 0 := by
    intro h; have := p.2.isLt; omega
  have h1 : analyticOrderAt FP p.1.val ≠ 0 := by
    intro h0; apply hord; simp [analyticOrderNatAt, h0]
  exact (analyticOrderAt_ne_zero.mp h1).2

lemma UU_im_gt (p : UU) : 14 < p.1.val.im := by
  have hre := UU_re p
  have hpos := p.1.2
  set a := p.1.val
  have hz : xiM (a + 1/2) = 0 := by rw [← FP_eq]; exact UU_FP_zero p
  have hζ := xiM_zeta_zero hz (by simp [hre])
  by_contra hle
  push Not at hle
  rcases le_or_gt a.im 2 with h | h
  · apply zeta_ne_zero_of_mem_strip_of_abs_im_le_two (a + 1/2) (by simp [hre]) (by simp [hre]; norm_num)
      (by simp; rw [abs_of_pos hpos]; exact h) hζ
  · exact TaoFivePrimes.zeta_ne_zero_strip_im_two_to_fourteen (a + 1/2) (by simp [hre])
      (by simp [hre]; norm_num) (by simp; linarith) (by simp; linarith) hζ

lemma UU_negsq (p : UU) : -p.1.val ^ 2 = ((p.1.val.im ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [pow_two, UU_re p]

lemma gg_eq (p : UU) (v : ℂ) : gg p v = 1 + v ^ 2 / ((p.1.val.im ^ 2 : ℝ) : ℂ) := by
  unfold gg; rw [UU_negsq]

lemma gg_real_norm (p : UU) (r : ℝ) : ‖gg p (r : ℂ)‖ = 1 + r ^ 2 / p.1.val.im ^ 2 := by
  rw [gg_eq]
  have : (1 : ℂ) + (r : ℂ) ^ 2 / ((p.1.val.im ^ 2 : ℝ) : ℂ) = ((1 + r ^ 2 / p.1.val.im ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

lemma one_add_sum_le_prod {ι : Type*} (S : Finset ι) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    1 + ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 + u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg (fun i _ => hu i)
    have h2 : 1 ≤ ∏ i ∈ S, (1 + u i) := by linarith
    nlinarith [hu a]

lemma xiM_one : xiM 1 = 1 / 2 := by unfold xiM; ring

/-- The zero-sum bound `∑ 2/(γ²+1/4) ≤ π/3 - 1`. -/
lemma U_bound (S : Finset UU) :
    ∑ p ∈ S, 2 / (p.1.val.im ^ 2 + 1/4) ≤ Real.pi / 3 - 1 := by
  classical
  set u : UU → ℝ := fun p => 2 / (p.1.val.im ^ 2 + 1/4) with hu
  have hu0 : ∀ p, 0 ≤ u p := fun p => by simp only [hu]; positivity
  have hfac : ∀ p : UU, ‖gg p ((3/2 : ℝ) : ℂ)‖ = ‖gg p ((1/2 : ℝ) : ℂ)‖ * (1 + u p) := by
    intro p
    rw [gg_real_norm, gg_real_norm]
    have hγ : 0 < p.1.val.im := p.1.2
    simp only [hu]
    field_simp
    ring
  have hT : ∀ v : ℂ, Tendsto (fun T : Finset UU => ∏ p ∈ T, ‖gg p v‖) atTop (𝓝 ‖∏' p : UU, gg p v‖) :=
    fun v => (key_UU v).1.hasProd.norm
  have hlim : ‖∏' p : UU, gg p ((1/2 : ℝ) : ℂ)‖ * ∏ p ∈ S, (1 + u p) ≤ ‖∏' p : UU, gg p ((3/2 : ℝ) : ℂ)‖ := by
    apply le_of_tendsto_of_tendsto ((hT _).mul_const _) (hT _)
    filter_upwards [Filter.eventually_ge_atTop S] with T hT
    rw [Finset.prod_congr rfl (fun p _ => hfac p), Finset.prod_mul_distrib]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    rw [← Finset.prod_sdiff hT]
    have h1 : 1 ≤ ∏ p ∈ T \ S, (1 + u p) := by
      have := one_add_sum_le_prod (T \ S) u hu0
      have : 0 ≤ ∑ p ∈ T \ S, u p := Finset.sum_nonneg (fun p _ => hu0 p)
      linarith
    have h2 : 0 ≤ ∏ p ∈ S, (1 + u p) := Finset.prod_nonneg (fun p _ => by linarith [hu0 p])
    nlinarith
  have h0 := FP_zero_ne
  have hP : ∀ v, ‖∏' p : UU, gg p v‖ = ‖FP v‖ / ‖FP 0‖ := by
    intro v; rw [← (key_UU v).2, norm_div]
  rw [hP, hP] at hlim
  have e1 : FP ((1/2 : ℝ) : ℂ) = 1/2 := by rw [FP_eq]; norm_num; exact xiM_one
  have e2 : FP ((3/2 : ℝ) : ℂ) = (Real.pi : ℂ) / 6 := by rw [FP_eq]; norm_num; exact xiM_two
  rw [e1, e2] at hlim
  have hn0 : 0 < ‖FP 0‖ := norm_pos_iff.mpr h0
  have n1 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
  have n2 : ‖(Real.pi : ℂ) / 6‖ = Real.pi / 6 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; norm_num
  rw [n1, n2, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn0] at hlim
  have := one_add_sum_le_prod S u hu0
  linarith

lemma factor_bound (γ : ℝ) (hγ : 14 < γ) (w c : ℂ) (k ε : ℝ) (hwre : |w.re| ≤ 1/2)
    (hwim : |w.im| ≤ 29/4) (hc : ‖c‖ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (H : (c * (2 * w / (w ^ 2 + ((γ ^ 2 : ℝ) : ℂ)))).re ≤ k * (2 / (γ ^ 2 + 1/4))) :
    ‖1 + (w + ε * c) ^ 2 / ((γ ^ 2 : ℝ) : ℂ)‖ ^ 2 ≤
      ‖1 + w ^ 2 / ((γ ^ 2 : ℝ) : ℂ)‖ ^ 2 * Real.exp ((2 * ε * k + 3 * ε ^ 2) * (2 / (γ ^ 2 + 1/4))) := by
  set G : ℂ := ((γ ^ 2 : ℝ) : ℂ) with hG
  have hγ2 : 196 < γ ^ 2 := by nlinarith
  have hG0 : G ≠ 0 := by rw [hG]; exact_mod_cast (by positivity : (γ ^ 2 : ℝ) ≠ 0)
  set D : ℂ := w ^ 2 + G with hD
  have hre2 : w.re ^ 2 ≤ 1/4 := by
    have := sq_abs w.re; nlinarith [abs_nonneg w.re]
  have him2 : w.im ^ 2 ≤ 841/16 := by
    have := sq_abs w.im; nlinarith [abs_nonneg w.im]
  have hDre : D.re = w.re ^ 2 - w.im ^ 2 + γ ^ 2 := by
    simp [hD, hG, pow_two]
  set d : ℝ := γ ^ 2 - 841/16 with hd
  have hd0 : 2295/16 ≤ d := by rw [hd]; linarith
  have hDn : d ≤ ‖D‖ := by
    have := Complex.re_le_norm D
    rw [hDre] at this; nlinarith
  have hDpos : 0 < ‖D‖ := by linarith
  have hD0 : D ≠ 0 := norm_pos_iff.mp hDpos
  set z : ℂ := ε * (c * (2 * w / D)) + ε ^ 2 * (c ^ 2 / D) with hz
  have hD1 : w ^ 2 + G ≠ 0 := hD0
  have hD2 : G + w ^ 2 ≠ 0 := by rw [add_comm]; exact hD0
  have hid : 1 + (w + ε * c) ^ 2 / G = (1 + w ^ 2 / G) * (1 + z) := by
    rw [hz, hD]; field_simp; ring
  rw [hid, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsq : ‖1 + z‖ ^ 2 = 1 + (2 * z.re + ‖z‖ ^ 2) := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]; simp; ring
  rw [hsq]
  refine le_trans ?_ (Real.add_one_le_exp _)
  suffices hmain : 2 * z.re + ‖z‖ ^ 2 ≤ (2 * ε * k + 3 * ε ^ 2) * (2 / (γ ^ 2 + 1/4)) by linarith
  -- bound on Re z
  have hc2 : ‖c ^ 2 / D‖ ≤ 1 / ‖D‖ := by
    rw [norm_div, norm_pow]
    apply div_le_div_of_nonneg_right _ hDpos.le
    nlinarith [norm_nonneg c]
  have hzre : z.re ≤ ε * (k * (2 / (γ ^ 2 + 1/4))) + ε ^ 2 * (1 / ‖D‖) := by
    have e : z.re = ε * (c * (2 * w / D)).re + ε ^ 2 * (c ^ 2 / D).re := by
      rw [hz]; simp [Complex.mul_re, pow_two]
    rw [e]
    have := Complex.re_le_norm (c ^ 2 / D)
    have h1 := mul_le_mul_of_nonneg_left H hε0
    have h2 := mul_le_mul_of_nonneg_left (this.trans hc2) (sq_nonneg ε)
    linarith
  -- bound on ‖z‖
  have hw : ‖w‖ ≤ 8 := by
    have : ‖w‖ ^ 2 ≤ 64 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith
    nlinarith [norm_nonneg w]
  have hzn : ‖z‖ ≤ ε * 17 / ‖D‖ := by
    have e : z = ε * (c * (2 * w + ε * c)) / D := by rw [hz]; field_simp
    rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
    apply div_le_div_of_nonneg_right _ hDpos.le
    apply mul_le_mul_of_nonneg_left _ hε0
    have h3 : ‖2 * w + ε * c‖ ≤ 17 := by
      calc ‖2 * w + ε * c‖ ≤ ‖2 * w‖ + ‖(ε:ℂ) * c‖ := norm_add_le _ _
        _ = 2 * ‖w‖ + ε * ‖c‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
          norm_num
        _ ≤ 17 := by nlinarith [norm_nonneg c]
    calc ‖c‖ * ‖2 * w + ε * c‖ ≤ 1 * 17 := mul_le_mul hc h3 (norm_nonneg _) (by norm_num)
      _ = 17 := by norm_num
  have hzn2 : ‖z‖ ^ 2 ≤ ε ^ 2 * (289 / ‖D‖ ^ 2) := by
    have := pow_le_pow_left₀ (norm_nonneg z) hzn 2
    rw [div_pow, mul_pow] at this
    have e : ε ^ 2 * 17 ^ 2 / ‖D‖ ^ 2 = ε ^ 2 * (289 / ‖D‖ ^ 2) := by ring
    linarith
  -- numerical comparison
  have hnum : 2 / ‖D‖ + 289 / ‖D‖ ^ 2 ≤ 3 * (2 / (γ ^ 2 + 1/4)) := by
    have hγd : γ ^ 2 + 1/4 = d + 845/16 := by rw [hd]; ring
    rw [hγd]
    have h1 : 2 / ‖D‖ ≤ 2 / d := div_le_div_of_nonneg_left (by norm_num) (by linarith) hDn
    have h2 : 289 / ‖D‖ ^ 2 ≤ 289 / d ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) hDn 2)
    have h3 : 2 / d + 289 / d ^ 2 ≤ 3 * (2 / (d + 845/16)) := by
      have hdp : 0 < d := by linarith
      rw [div_add_div _ _ hdp.ne' (by positivity), mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hdp hdp, mul_pos (mul_pos hdp hdp) hdp]
    linarith
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have := mul_le_mul_of_nonneg_left hnum hε2
  have e1 : 2 / ‖D‖ = 2 * (1 / ‖D‖) := by ring
  rw [e1] at this
  calc 2 * z.re + ‖z‖ ^ 2 ≤ 2 * (ε * (k * (2 / (γ ^ 2 + 1/4))) + ε ^ 2 * (1 / ‖D‖)) + ε ^ 2 * (289 / ‖D‖ ^ 2) := by
        linarith
    _ = 2 * ε * k * (2 / (γ ^ 2 + 1/4)) + ε ^ 2 * (2 * (1 / ‖D‖) + 289 / ‖D‖ ^ 2) := by ring
    _ ≤ 2 * ε * k * (2 / (γ ^ 2 + 1/4)) + ε ^ 2 * (3 * (2 / (γ ^ 2 + 1/4))) := by linarith
    _ = (2 * ε * k + 3 * ε ^ 2) * (2 / (γ ^ 2 + 1/4)) := by ring

lemma FP_differentiable : Differentiable ℂ FP := by
  intro z; unfold FP; have := differentiable_completedZeta₀; fun_prop

/-- Directional bound on the logarithmic derivative of `FP` from the Hadamard product. -/
lemma dirBound {w c : ℂ} {k : ℝ} (hw : w.re ≠ 0) (hwre : |w.re| ≤ 1/2) (hwim : |w.im| ≤ 29/4)
    (hc : ‖c‖ ≤ 1) (hk : 0 ≤ k)
    (H : ∀ γ : ℝ, 14 < γ → (c * (2 * w / (w ^ 2 + ((γ ^ 2 : ℝ) : ℂ)))).re ≤ k * (2 / (γ ^ 2 + 1/4))) :
    (c * (deriv FP w / FP w)).re ≤ k * (Real.pi / 3 - 1) := by
  set U : ℝ := Real.pi / 3 - 1 with hUdef
  have hU : 0 ≤ U := by rw [hUdef]; linarith [Real.pi_gt_three]
  have hFw : FP w ≠ 0 := FP_ne_zero hw
  have h0 := FP_zero_ne
  have hT : ∀ v : ℂ, Tendsto (fun T : Finset UU => ∏ p ∈ T, ‖gg p v‖) atTop (𝓝 ‖∏' p : UU, gg p v‖) :=
    fun v => (key_UU v).1.hasProd.norm
  have hP : ∀ v, ‖FP v‖ = ‖FP 0‖ * ‖∏' p : UU, gg p v‖ := by
    intro v; rw [← (key_UU v).2, norm_div]; field_simp
  -- Step 1: growth bound
  have hgrowth : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ‖FP (w + ε * c)‖ ^ 2 ≤ ‖FP w‖ ^ 2 * Real.exp ((2 * ε * k + 3 * ε ^ 2) * U) := by
    intro ε hε0 hε1
    have ha : 0 ≤ 2 * ε * k + 3 * ε ^ 2 := by positivity
    have hfin : ∀ T : Finset UU, (∏ p ∈ T, ‖gg p (w + ε * c)‖) ^ 2 ≤
        (∏ p ∈ T, ‖gg p w‖) ^ 2 * Real.exp ((2 * ε * k + 3 * ε ^ 2) * U) := by
      intro T
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      have hstep : ∏ p ∈ T, ‖gg p (w + ε * c)‖ ^ 2 ≤
          ∏ p ∈ T, (‖gg p w‖ ^ 2 * Real.exp ((2 * ε * k + 3 * ε ^ 2) * (2 / (p.1.val.im ^ 2 + 1/4)))) := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro p _
        rw [gg_eq, gg_eq]
        exact factor_bound _ (UU_im_gt p) w c k ε hwre hwim hc hε0 hε1 (H _ (UU_im_gt p))
      refine hstep.trans ?_
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => by positivity))
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (U_bound T) ha
    have hlim : ‖∏' p : UU, gg p (w + ε * c)‖ ^ 2 ≤
        ‖∏' p : UU, gg p w‖ ^ 2 * Real.exp ((2 * ε * k + 3 * ε ^ 2) * U) :=
      le_of_tendsto_of_tendsto' ((hT _).pow 2) (((hT _).pow 2).mul_const _) hfin
    rw [hP, hP w, mul_pow, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left hlim (by positivity)
  -- Step 2: derivative along the direction `c`
  let φ : ℝ → ℂ := fun ε => FP (w + ε * c)
  let N : ℝ → ℝ := fun ε => ‖φ ε‖ ^ 2
  have hφ : HasDerivAt φ (deriv FP w * c) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => w + (ε : ℂ) * c) c 0 := by
      have := ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const c).const_add w
      simpa using this
    have h2 : HasDerivAt FP (deriv FP w) (w + ((0:ℝ) : ℂ) * c) := by
      simpa using (FP_differentiable w).hasDerivAt
    exact h2.comp (0:ℝ) h1
  have hN := hφ.norm_sq
  have hφ0 : φ 0 = FP w := by simp [φ]
  set g : ℝ → ℝ := fun ε => Real.exp ((2 * ε * k + 3 * ε ^ 2) * U) with hg
  have hgd : HasDerivAt g (2 * k * U) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => (2 * ε * k + 3 * ε ^ 2) * U) (2 * k * U) 0 := by
      have := ((((hasDerivAt_id' (0:ℝ)).const_mul 2).mul_const k).fun_add
        ((hasDerivAt_pow 2 (0:ℝ)).const_mul 3)).mul_const U
      exact this.congr_deriv (by norm_num)
    have := h1.exp
    convert this using 1
    simp
  have hslopeN := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0:ℝ)) (by simp)).mp hN.hasDerivWithinAt
  have hslopeg := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0:ℝ)) (by simp)).mp hgd.hasDerivWithinAt
  have hineq : 2 * inner ℝ (φ 0) (deriv FP w * c) ≤ N 0 * (2 * k * U) := by
    apply le_of_tendsto_of_tendsto hslopeN (hslopeg.const_mul (N 0))
    have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      exact eventually_lt_nhds (by norm_num)
    filter_upwards [hev, self_mem_nhdsWithin] with ε hε1 hε0
    simp only [Set.mem_Ioi] at hε0
    rw [slope_def_field, slope_def_field, sub_zero]
    have hg0 : g 0 = 1 := by simp [hg]
    rw [hg0]
    have hb := hgrowth ε hε0.le hε1.le
    have hN0 : N 0 = ‖FP w‖ ^ 2 := by simp [N, hφ0]
    have hNe : N ε = ‖FP (w + ε * c)‖ ^ 2 := rfl
    show (‖FP (w + ε * c)‖ ^ 2 - ‖φ 0‖ ^ 2) / ε ≤ N 0 * ((g ε - 1) / ε)
    rw [hN0, hφ0, mul_div_assoc', div_le_div_iff_of_pos_right hε0]
    simp only [hg]
    nlinarith [hb]
  -- Step 3: conclude
  rw [hφ0, Complex.inner] at hineq
  have hN0 : N 0 = Complex.normSq (FP w) := by simp [N, hφ0, Complex.sq_norm]
  rw [hN0] at hineq
  have hns : 0 < Complex.normSq (FP w) := Complex.normSq_pos.mpr hFw
  have key : (c * (deriv FP w / FP w)).re = ((deriv FP w * c) * (starRingEnd ℂ) (FP w)).re / Complex.normSq (FP w) := by
    rw [div_eq_mul_inv, Complex.inv_def]
    have : c * (deriv FP w * ((starRingEnd ℂ) (FP w) * ((Complex.normSq (FP w))⁻¹ : ℝ))) =
        ((deriv FP w * c) * (starRingEnd ℂ) (FP w)) * (((Complex.normSq (FP w))⁻¹ : ℝ) : ℂ) := by ring
    rw [this, Complex.re_mul_ofReal, div_eq_mul_inv]
  rw [key, div_le_iff₀ hns]
  nlinarith [hineq]

end Z1

section Fin

open Filter Topology Complex

lemma H_re (x t γ : ℝ) (hx : |x| ≤ 1/2) (ht : t ^ 2 ≤ 9) (hγ : 14 < γ) :
    ((-1 : ℂ) * (2 * (x + t * I) / ((x + t * I) ^ 2 + ((γ ^ 2 : ℝ) : ℂ)))).re ≤ (3/5) * (2 / (γ ^ 2 + 1/4)) := by
  have hγ2 : 196 < γ ^ 2 := by nlinarith
  have hx2 : x ^ 2 ≤ 1/4 := by have := sq_abs x; nlinarith [abs_nonneg x]
  have hxl : -x ≤ 1/2 := by have := neg_abs_le x; linarith [abs_nonneg x]
  set P : ℝ := x ^ 2 - t ^ 2 + γ ^ 2 with hP
  set Q : ℝ := 2 * x * t with hQ
  have hPpos : γ ^ 2 - 9 ≤ P := by rw [hP]; nlinarith
  have hD : ((x:ℂ) + t * I) ^ 2 + ((γ ^ 2 : ℝ) : ℂ) = (P : ℂ) + (Q : ℂ) * I := by
    apply Complex.ext <;> simp [hP, hQ, pow_two] <;> ring
  rw [hD]
  have hN : 0 < P ^ 2 + Q ^ 2 := by nlinarith
  have hre : ((-1 : ℂ) * (2 * (x + t * I) / ((P : ℂ) + (Q : ℂ) * I))).re
      = -2 * (x * P + t * Q) / (P ^ 2 + Q ^ 2) := by
    simp [Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp
    ring
  rw [hre]
  have hxPQ : x * P + t * Q = x * (x ^ 2 + t ^ 2 + γ ^ 2) := by rw [hP, hQ]; ring
  rw [hxPQ]
  have hA : 0 ≤ x ^ 2 + t ^ 2 + γ ^ 2 := by positivity
  have h1 : -2 * (x * (x ^ 2 + t ^ 2 + γ ^ 2)) ≤ x ^ 2 + t ^ 2 + γ ^ 2 := by nlinarith
  have h2 : -2 * (x * (x ^ 2 + t ^ 2 + γ ^ 2)) / (P ^ 2 + Q ^ 2) ≤ (x ^ 2 + t ^ 2 + γ ^ 2) / P ^ 2 := by
    rcases le_or_gt (-2 * (x * (x ^ 2 + t ^ 2 + γ ^ 2))) 0 with h | h
    · exact (div_nonpos_of_nonpos_of_nonneg h hN.le).trans (by positivity)
    · calc -2 * (x * (x ^ 2 + t ^ 2 + γ ^ 2)) / (P ^ 2 + Q ^ 2)
          ≤ -2 * (x * (x ^ 2 + t ^ 2 + γ ^ 2)) / P ^ 2 :=
            div_le_div_of_nonneg_left h.le (by nlinarith) (by nlinarith [sq_nonneg Q])
        _ ≤ (x ^ 2 + t ^ 2 + γ ^ 2) / P ^ 2 := div_le_div_of_nonneg_right h1 (by positivity)
  refine h2.trans ?_
  rw [div_le_iff₀ (by nlinarith), mul_comm, ← mul_assoc, mul_div_assoc', le_div_iff₀ (by positivity)]
  have hP2 : (γ ^ 2 - 9) ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ (by linarith) hPpos 2
  nlinarith [mul_le_mul_of_nonneg_left hP2 (by norm_num : (0:ℝ) ≤ 6/5)]

lemma H_im (x t γ : ℝ) (hx : |x| ≤ 1/2) (ht0 : 0 ≤ t) (ht : t ≤ 29/4) (hγ : 14 < γ) :
    ((-I) * (2 * (x + t * I) / ((x + t * I) ^ 2 + ((γ ^ 2 : ℝ) : ℂ)))).re
      ≤ t * (785/4) / (196 - t ^ 2) * (2 / (γ ^ 2 + 1/4)) := by
  have hγ2 : 196 < γ ^ 2 := by nlinarith
  have hx2 : x ^ 2 ≤ 1/4 := by have := sq_abs x; nlinarith [abs_nonneg x]
  have ht2 : t ^ 2 ≤ 841/16 := by nlinarith
  set P : ℝ := x ^ 2 - t ^ 2 + γ ^ 2 with hP
  set Q : ℝ := 2 * x * t with hQ
  have hPpos : γ ^ 2 - t ^ 2 ≤ P := by rw [hP]; nlinarith
  have hD : ((x:ℂ) + t * I) ^ 2 + ((γ ^ 2 : ℝ) : ℂ) = (P : ℂ) + (Q : ℂ) * I := by
    apply Complex.ext <;> simp [hP, hQ, pow_two] <;> ring
  rw [hD]
  have hPp : 0 < P := by linarith
  have hN : 0 < P ^ 2 + Q ^ 2 := by positivity
  have hre : ((-I) * (2 * (x + t * I) / ((P : ℂ) + (Q : ℂ) * I))).re
      = 2 * (t * P - x * Q) / (P ^ 2 + Q ^ 2) := by
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    field_simp
  rw [hre]
  have hxPQ : t * P - x * Q = t * (γ ^ 2 - x ^ 2 - t ^ 2) := by rw [hP, hQ]; ring
  rw [hxPQ]
  have h0 : 0 ≤ t * (γ ^ 2 - x ^ 2 - t ^ 2) := mul_nonneg ht0 (by nlinarith)
  have h1 : t * (γ ^ 2 - x ^ 2 - t ^ 2) ≤ t * P := mul_le_mul_of_nonneg_left (by rw [hP]; nlinarith) ht0
  have h2 : 2 * (t * (γ ^ 2 - x ^ 2 - t ^ 2)) / (P ^ 2 + Q ^ 2) ≤ 2 * t / P := by
    rw [div_le_div_iff₀ hN hPp]
    nlinarith [sq_nonneg Q, mul_nonneg h0 (sq_nonneg Q)]
  refine h2.trans ?_
  have h196 : 0 < 196 - t ^ 2 := by nlinarith
  rw [div_le_iff₀ hPp]
  have : t * (785 / 4) / (196 - t ^ 2) * (2 / (γ ^ 2 + 1 / 4)) * P ≥
      t * (785 / 4) / (196 - t ^ 2) * (2 / (γ ^ 2 + 1 / 4)) * (γ ^ 2 - t ^ 2) :=
    mul_le_mul_of_nonneg_left hPpos (by positivity)
  refine le_trans ?_ this
  rw [div_mul_div_comm, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hγ2.le) (show (0:ℝ) ≤ t ^ 2 + 1/4 by positivity), ht0,
    mul_nonneg ht0 (mul_nonneg (sub_nonneg.mpr hγ2.le) (show (0:ℝ) ≤ t ^ 2 + 1/4 by positivity))]

noncomputable def mszF (s : ℂ) : ℂ := s * (s - 1) * Complex.Gammaℝ s

lemma nm_pole {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := m.cast_nonneg
  linarith

lemma nm_F_hasDerivAt {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt mszF (mszF s * (1 / s + 1 / (s - 1) + (-(Real.log Real.pi : ℂ) / 2
      + (1 / 2) * Complex.digamma (s / 2)))) s ∨ s = 1 := by
  by_cases h1' : s = 1
  · exact Or.inr h1'
  left
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΓ : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero (nm_pole hs)
  have hd1 : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hpi)
    simpa using this
  have hd2 : HasDerivAt (fun s : ℂ => Complex.Gamma (s / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2)) s := by
    exact (Complex.differentiableAt_Gamma (s / 2) (nm_pole hs)).hasDerivAt.comp s
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

lemma nm_F_ne {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) : mszF s ≠ 0 := by
  unfold mszF
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hG : Complex.Gammaℝ s ≠ 0 := by
    rw [Complex.Gammaℝ_def]
    apply mul_ne_zero
    · rw [Ne, Complex.cpow_eq_zero_iff]; push Not
      intro h; exfalso; exact Real.pi_ne_zero (by exact_mod_cast h)
    · exact Complex.Gamma_ne_zero (nm_pole hs)
  exact mul_ne_zero (mul_ne_zero h0 h1) hG

lemma nm_xi_eq {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) : xiM s = mszF s * riemannZeta s / 2 := by
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : 1 - s ≠ 0 := by intro h; apply h1'; linear_combination -h
  have hF := nm_F_ne hs h1
  have hG : Complex.Gammaℝ s ≠ 0 := by intro h; apply hF; rw [mszF, h, mul_zero]
  unfold xiM
  rw [riemannZeta_def_of_ne_zero h0, completedRiemannZeta_eq, mszF]
  field_simp
  ring

/-- At a zero of `ζ'` the logarithmic derivative of `ξ` is the gamma-factor term. -/
lemma nm_logderiv_eq {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) (hxi : xiM s ≠ 0)
    (hd : deriv riemannZeta s = 0) :
    deriv xiM s / xiM s = 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2 + 1) / 2 := by
  have hev : xiM =ᶠ[𝓝 s] fun z => mszF z * riemannZeta z / 2 := by
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
    filter_upwards [hopen.mem_nhds ⟨hs, h1⟩] with z hz
    exact nm_xi_eq hz.1 hz.2
  have hF := (nm_F_hasDerivAt hs).resolve_right h1
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta h1).hasDerivAt
  have hprod := (hF.mul hζ).div_const 2
  rw [hev.deriv_eq, show (fun z => mszF z * riemannZeta z / 2) = (fun x => (mszF * riemannZeta) x / 2) from rfl,
    hprod.deriv, hd, nm_xi_eq hs h1]
  have hFne := nm_F_ne hs h1
  have hζne : riemannZeta s ≠ 0 := by
    intro h; apply hxi; rw [nm_xi_eq hs h1, h]; ring
  have h0 : s ≠ 0 := by rintro rfl; simp at hs
  have hpsi : Complex.digamma (s / 2 + 1) = Complex.digamma (s / 2) + (s / 2)⁻¹ :=
    Complex.digamma_apply_add_one _ (nm_pole hs)
  rw [hpsi]
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

lemma xiM_one_sub (s : ℂ) : xiM (1 - s) = xiM s := by
  unfold xiM; rw [completedRiemannZeta₀_one_sub]; ring

lemma nm_re_Z_neg {s : ℂ} (hs : s.re < 1/2) : (deriv xiM s / xiM s).re < 0 := by
  have h := logderiv_pos (s := 1 - s) (by simp; linarith)
  have hdiff : Differentiable ℂ xiM := by
    intro z; unfold xiM; have := differentiable_completedZeta₀; fun_prop
  have hfun : xiM = fun z => xiM (1 - z) := by funext z; rw [xiM_one_sub]
  have hd : deriv xiM s = -deriv xiM (1 - s) := by
    have h2 : HasDerivAt (fun z => xiM (1 - z)) (deriv xiM (1 - s) * (-1)) s :=
      (hdiff (1 - s)).hasDerivAt.comp s ((hasDerivAt_id' s).const_sub 1)
    have e : deriv xiM s = deriv (fun z => xiM (1 - z)) s := congrArg (fun f => deriv f s) hfun
    rw [e, h2.deriv]; ring
  rw [hd, ← xiM_one_sub s, neg_div, Complex.neg_re]
  linarith

lemma nm_FP_logderiv (s : ℂ) : deriv FP (s - 1/2) / FP (s - 1/2) = deriv xiM s / xiM s := by
  have hdiff : Differentiable ℂ xiM := by
    intro z; unfold xiM; have := differentiable_completedZeta₀; fun_prop
  have hfun : FP = fun z => xiM (z + 1/2) := by funext z; exact FP_eq z
  have h2 : HasDerivAt (fun z => xiM (z + 1/2)) (deriv xiM s) (s - 1/2) := by
    have := (hdiff (s - 1/2 + 1/2)).hasDerivAt.comp_add_const (s - 1/2) (1/2)
    simpa using this
  rw [hfun, h2.deriv]
  simp

lemma speiser_upper (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (ht : 0 ≤ s.im) :
    deriv riemannZeta s ≠ 0 := by
  intro hd
  obtain ⟨σ, t, hsdecomp⟩ : ∃ σ t : ℝ, s = (σ : ℂ) + (t : ℂ) * I := ⟨s.re, s.im, (Complex.re_add_im s).symm⟩
  have hσ : s.re = σ := by rw [hsdecomp]; simp
  have ht_def : s.im = t := by rw [hsdecomp]; simp
  rw [hσ] at h0 h1
  rw [ht_def] at ht
  have hs1 : s ≠ 1 := by intro h; rw [h] at hσ; simp at hσ; linarith
  have hxi : xiM s ≠ 0 := by intro h; have := xiM_zero_re h; linarith
  have hZ := nm_logderiv_eq (by linarith) hs1 hxi hd
  set Z := deriv xiM s / xiM s with hZdef
  have harg : s / 2 + 1 = (((σ/2 + 1 : ℝ)) : ℂ) + ((t/2 : ℝ) : ℂ) * I := by
    rw [hsdecomp]; push_cast; ring
  have hden : 0 < (σ - 1) ^ 2 + t ^ 2 := by nlinarith
  have hinvre : (1 / (s - 1)).re = (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hsdecomp]; simp; ring
  have hinvim : (1 / (s - 1)).im = -t / ((σ - 1) ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_im, Complex.normSq_apply, hsdecomp]; simp; ring
  have hEre : Z.re = (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) - Real.log Real.pi / 2
      + (1/2) * (Complex.digamma (((σ/2 + 1 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).re := by
    rw [hZ, Complex.add_re, Complex.sub_re, hinvre, harg]
    simp [Complex.div_re]; ring
  have hEim : Z.im = -t / ((σ - 1) ^ 2 + t ^ 2)
      + (1/2) * (Complex.digamma (((σ/2 + 1 : ℝ) : ℂ) + ((t/2 : ℝ) : ℂ) * I)).im := by
    rw [hZ, Complex.add_im, Complex.sub_im, hinvim, harg]
    simp [Complex.div_im]; ring
  -- the zero-side data at `w = s - 1/2`
  set w := s - 1/2 with hw
  have hwZ : deriv FP w / FP w = Z := nm_FP_logderiv s
  have hwre : w.re = σ - 1/2 := by simp [hw, hσ]
  have hwim : w.im = t := by simp [hw, ht_def]
  have hwdecomp : w = ((σ - 1/2 : ℝ) : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [hwre, hwim]
  have hwre0 : w.re ≠ 0 := by rw [hwre]; intro h; linarith
  have hwre1 : |w.re| ≤ 1/2 := by rw [hwre, abs_le]; constructor <;> linarith
  have hpi := Real.pi_lt_d6
  rcases le_or_gt (29/4) t with hA | hA
  · have := nm_testA σ t (by linarith) h1.le hA
    have := nm_re_Z_neg (s := s) (by rw [hσ]; exact h1)
    rw [← hZdef] at this
    linarith
  rcases le_or_gt 3 t with hB | hB
  · have hT := nm_testB σ t (by linarith) h1.le hB hA.le
    have hk : 0 ≤ t * (785/4) / (196 - t ^ 2) := by
      apply div_nonneg (by positivity); nlinarith
    have hD := dirBound (c := -I) (k := t * (785/4) / (196 - t ^ 2)) hwre0 hwre1
      (by rw [hwim, abs_le]; constructor <;> linarith) (by simp) hk
      (fun γ hγ => by
        rw [hwdecomp]
        exact H_im (σ - 1/2) t γ (by rw [abs_le]; constructor <;> linarith) ht hA.le hγ)
    rw [hwZ] at hD
    have hre : ((-I) * Z).re = Z.im := by simp
    rw [hre] at hD
    have hU : t * (785/4) / (196 - t ^ 2) * (Real.pi / 3 - 1) ≤
        t * (785/4) / (196 - t ^ 2) * (3.141593 / 3 - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hk
    linarith
  · have hT := nm_testC σ t (by linarith) h1.le ht hB.le
    have hD := dirBound (c := -1) (k := 3/5) hwre0 hwre1
      (by rw [hwim, abs_le]; constructor <;> linarith) (by simp) (by norm_num)
      (fun γ hγ => by
        rw [hwdecomp]
        exact H_re (σ - 1/2) t γ (by rw [abs_le]; constructor <;> linarith) (by nlinarith) hγ)
    rw [hwZ] at hD
    have hre : ((-1 : ℂ) * Z).re = -Z.re := by simp
    rw [hre] at hD
    linarith

theorem solution :
    ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 → deriv riemannZeta s ≠ 0 := by
  intro s h0 h1
  rcases le_or_gt 0 s.im with ht | ht
  · exact speiser_upper s h0 h1 ht
  · intro hd
    have hconj : deriv riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (deriv riemannZeta s) := by
      have hf : (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) = riemannZeta := by
        funext z; simp [riemannZeta_conj]
      have := congrFun (deriv_conj_conj (f := riemannZeta)) ((starRingEnd ℂ) s)
      rw [hf] at this
      simpa using this
    apply speiser_upper ((starRingEnd ℂ) s) (by simpa using h0) (by simpa using h1)
      (by simp; linarith)
    rw [hconj, hd, map_zero]

end Fin
