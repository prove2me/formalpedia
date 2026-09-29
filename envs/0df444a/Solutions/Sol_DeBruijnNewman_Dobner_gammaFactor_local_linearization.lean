-- Prove2me | solution 1 for DeBruijnNewman.Dobner.gammaFactor_local_linearization
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-25T00:47:23.518678+00:00
-- url     : https://prove2.me/submissions/08d58db1-1517-42a4-b3a9-fdc75dc999f1

import Definitions.Def_DeBruijnNewman_Dobner_Saddle
import Theorems.Thm_Zeta23_StirlingVert_digamma_stirling

/-!
Dobner's local logarithmic expansion, using the proved derivative form of
Stirling's formula. The recurrence for digamma extends that estimate from
the right half-plane to the upper sector needed by the growing window.
-/

open Complex Filter Set
open scoped Topology
open DeBruijnNewman.Dobner

private lemma upper_ne_zero (w : ℂ) (hw : 0 < w.im) : w ≠ 0 := by
  intro h
  simp [h] at hw

private lemma upper_not_neg_nat (w : ℂ) (hw : 0 < w.im) :
    ∀ m : ℕ, w ≠ -(m : ℂ) := by
  intro m h
  simp [h] at hw

/-- The principal logarithms have no branch jump in the upper half-plane. -/
private lemma log_div_upper (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    Complex.log (z / w) = Complex.log z - Complex.log w := by
  have hzarg := Complex.arg_nonneg_iff.mpr hz.le
  have hwarg := Complex.arg_nonneg_iff.mpr hw.le
  have hzpi := Complex.arg_lt_pi_iff.mpr (Or.inr hz.ne')
  have hwpi := Complex.arg_lt_pi_iff.mpr (Or.inr hw.ne')
  have he : Complex.exp (Complex.log z - Complex.log w) = z / w := by
    rw [Complex.exp_sub, Complex.exp_log (upper_ne_zero z hz),
      Complex.exp_log (upper_ne_zero w hw)]
  rw [← he, Complex.log_exp]
  · simp only [Complex.sub_im, Complex.log_im]
    linarith
  · simp only [Complex.sub_im, Complex.log_im]
    linarith

private lemma log_shift_upper (w : ℂ) (hw : 0 < w.im) :
    Complex.log (w + 1) - Complex.log w = Complex.log (1 + w⁻¹) := by
  rw [← log_div_upper (w + 1) w (by simpa using hw) hw]
  congr 1
  field_simp [upper_ne_zero w hw]

private lemma log_remainder_half (h : ℂ) (hh : ‖h‖ ≤ 1 / 2) :
    ‖Complex.log (1 + h) - h‖ ≤ ‖h‖ ^ 2 := by
  have hlt : ‖h‖ < 1 := by linarith
  have hi : (1 - ‖h‖)⁻¹ ≤ 2 := by
    apply (inv_le_comm₀ (by linarith : 0 < 1 - ‖h‖) (by norm_num)).mpr
    norm_num
    linarith
  calc
    _ ≤ ‖h‖ ^ 2 * (1 - ‖h‖)⁻¹ / 2 :=
      Complex.norm_log_one_add_sub_self_le hlt
    _ ≤ ‖h‖ ^ 2 * 2 / 2 := by gcongr
    _ = _ := by ring

private lemma norm_inv_le_height (w : ℂ) (hw : 0 < w.im) :
    ‖w⁻¹‖ ≤ 1 / w.im := by
  rw [norm_inv, one_div]
  exact inv_anti₀ hw (Complex.im_le_norm w)

private lemma digamma_step (w : ℂ) (hw : 2 ≤ w.im) :
    ‖Complex.digamma w - Complex.log w‖ ≤
      ‖Complex.digamma (w + 1) - Complex.log (w + 1)‖ + 1 / w.im ^ 2 := by
  have hwp : 0 < w.im := by linarith
  have hinv := norm_inv_le_height w hwp
  have hhalf : ‖w⁻¹‖ ≤ 1 / 2 := hinv.trans (by gcongr)
  have hrem : ‖Complex.log (1 + w⁻¹) - w⁻¹‖ ≤ 1 / w.im ^ 2 := by
    calc
      _ ≤ ‖w⁻¹‖ ^ 2 := log_remainder_half _ hhalf
      _ ≤ (1 / w.im) ^ 2 := by gcongr
      _ = _ := by ring
  have he :
      Complex.digamma w - Complex.log w =
        (Complex.digamma (w + 1) - Complex.log (w + 1)) +
          (Complex.log (1 + w⁻¹) - w⁻¹) := by
    rw [Complex.digamma_apply_add_one w (upper_not_neg_nat w hwp),
      ← log_shift_upper w hwp]
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hrem)

private lemma digamma_shift (w : ℂ) (hw : 2 ≤ w.im) (m : ℕ) :
    ‖Complex.digamma w - Complex.log w‖ ≤
      ‖Complex.digamma (w + m) - Complex.log (w + m)‖ + m / w.im ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep := digamma_step (w + m) (by simpa using hw)
    simp only [Complex.add_im, Complex.natCast_im, add_zero] at hstep
    calc
      _ ≤ ‖Complex.digamma (w + m) - Complex.log (w + m)‖ + m / w.im ^ 2 := ih
      _ ≤ (‖Complex.digamma (w + m + 1) - Complex.log (w + m + 1)‖ +
          1 / w.im ^ 2) + m / w.im ^ 2 := by gcongr
      _ = _ := by push_cast; simp only [← add_assoc]; ring

/-- Stirling's logarithmic-derivative estimate extended to a fixed upper sector. -/
private lemma digamma_sub_log_upper (w : ℂ) (hw : 2 ≤ w.im)
    (hcone : |w.re| ≤ w.im) :
    ‖Complex.digamma w - Complex.log w‖ ≤ 6 / w.im := by
  let m : ℕ := ⌊|w.re|⌋₊ + 1
  have hmlo : |w.re| < (m : ℝ) := by
    simpa [m] using Nat.lt_floor_add_one |w.re|
  have hmhi : (m : ℝ) ≤ w.im + 1 := by
    have hf := Nat.floor_le (abs_nonneg w.re)
    dsimp [m]
    push_cast
    linarith
  have hwr : 0 < (w + m).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [neg_abs_le w.re]
  have hwp : 0 < w.im := by linarith
  have hst := Zeta23.StirlingVert.digamma_stirling (w := w + m) hwr
    (by simpa [abs_of_pos hwp] using (show (1 / 2 : ℝ) ≤ w.im by linarith))
  simp only [Complex.add_im, Complex.natCast_im, add_zero] at hst
  have hcorr : ‖(1 / 2 : ℂ) / (w + m)‖ ≤ (1 / 2 : ℝ) / w.im := by
    rw [norm_div]
    norm_num
    gcongr
    simpa using Complex.im_le_norm (w + m)
  calc
    _ ≤ ‖Complex.digamma (w + m) - Complex.log (w + m)‖ + m / w.im ^ 2 :=
      digamma_shift w hw m
    _ ≤ (3 / w.im ^ 2 + (1 / 2 : ℝ) / w.im) + m / w.im ^ 2 := by
      gcongr
      calc
        _ = ‖(Complex.digamma (w + m) - Complex.log (w + m) +
            (1 / 2 : ℂ) / (w + m)) - (1 / 2 : ℂ) / (w + m)‖ := by congr 1; ring
        _ ≤ ‖Complex.digamma (w + m) - Complex.log (w + m) +
            (1 / 2 : ℂ) / (w + m)‖ + ‖(1 / 2 : ℂ) / (w + m)‖ := norm_sub_le _ _
        _ ≤ _ := add_le_add hst hcorr
    _ ≤ 6 / w.im := by
      calc
        _ = (3 + w.im / 2 + m) / w.im ^ 2 := by field_simp
        _ ≤ (6 * w.im) / w.im ^ 2 := by gcongr; linarith
        _ = _ := by field_simp

private noncomputable def mainSlope (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.log (s / ((2 * Real.pi : ℝ) : ℂ))

private noncomputable def gammaSlope (w : ℂ) : ℂ :=
  w⁻¹ + (w - 1)⁻¹ - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (w / 2) / 2

private lemma mainSlope_eq (s : ℂ) (hs : 0 < s.im) :
    mainSlope s = (Complex.log (s / 2) - (Real.log Real.pi : ℂ)) / 2 := by
  have hs2 : s / 2 ≠ 0 := div_ne_zero (upper_ne_zero s hs) (by norm_num)
  have he : s / ((2 * Real.pi : ℝ) : ℂ) = (s / 2) * ((Real.pi⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [mainSlope, he,
    Complex.log_mul_ofReal _ (inv_pos.mpr Real.pi_pos) _ hs2, Real.log_inv]
  push_cast
  ring

private lemma gammaFactor_ne_zero_upper (w : ℂ) (hw : 0 < w.im) :
    gammaFactor w ≠ 0 := by
  have hw0 := upper_ne_zero w hw
  have hw1 := upper_ne_zero (w - 1) (by simpa using hw)
  have hg := Complex.Gamma_ne_zero (upper_not_neg_nat (w / 2) (by simp; linarith))
  exact mul_ne_zero
    (mul_ne_zero (div_ne_zero (mul_ne_zero hw0 hw1) (by norm_num))
      (Complex.exp_ne_zero _)) hg

private lemma gamma_hasDerivAt (w : ℂ) (hw : 0 < w.im) :
    HasDerivAt gammaFactor (gammaSlope w * gammaFactor w) w := by
  have hw0 := upper_ne_zero w hw
  have hw1 := upper_ne_zero (w - 1) (by simpa using hw)
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) w :=
    (hasDerivAt_id w).div_const 2
  have hgn := upper_not_neg_nat (w / 2) (by simp; linarith)
  have hg : HasDerivAt Complex.Gamma
      (Complex.digamma (w / 2) * Complex.Gamma (w / 2)) (w / 2) := by
    convert! (Complex.differentiableAt_Gamma (w / 2) hgn).hasDerivAt using 1
    simp [Complex.digamma, logDeriv_apply, Complex.Gamma_ne_zero hgn]
  have hpoly := ((hasDerivAt_id w).mul ((hasDerivAt_id w).sub_const 1)).div_const 2
  have hexp := (hhalf.neg.mul_const (Real.log Real.pi : ℂ)).cexp
  have hprod := (hpoly.mul hexp).mul (hg.comp w hhalf)
  convert! hprod using 1
  dsimp [gammaSlope, gammaFactor]
  field_simp
  ring

/-- The polynomial factors contribute two reciprocal terms to the slope. -/
private lemma gamma_slope_error (w : ℂ) (hw : 4 ≤ w.im)
    (hcone : |w.re| ≤ w.im) :
    ‖gammaSlope w - mainSlope w‖ ≤ 8 / w.im := by
  have hwp : 0 < w.im := by linarith
  have hpsi := digamma_sub_log_upper (w / 2)
    (by simp; linarith)
    (by simpa [abs_div] using
      (div_le_div_of_nonneg_right hcone (by norm_num : (0 : ℝ) ≤ 2)))
  have hw0 := norm_inv_le_height w hwp
  have hw1 := norm_inv_le_height (w - 1) (by simpa using hwp)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at hw1
  have he : gammaSlope w - mainSlope w =
      w⁻¹ + (w - 1)⁻¹ + (Complex.digamma (w / 2) - Complex.log (w / 2)) / 2 := by
    rw [mainSlope_eq w hwp, gammaSlope]
    ring
  rw [he]
  calc
    _ ≤ (‖w⁻¹‖ + ‖(w - 1)⁻¹‖) +
        ‖(Complex.digamma (w / 2) - Complex.log (w / 2)) / 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (1 / w.im + 1 / w.im) + (6 / (w.im / 2)) / 2 := by
      gcongr
      norm_num only [norm_div, Complex.norm_ofNat]
      simpa using (div_le_div_of_nonneg_right hpsi (by norm_num : (0 : ℝ) ≤ 2))
    _ = _ := by ring

private lemma mainSlope_difference (s w : ℂ) (hs : 0 < s.im) (hw : 0 < w.im)
    (hnear : ‖w - s‖ / ‖s‖ ≤ 1 / 2) :
    ‖mainSlope w - mainSlope s‖ ≤ (3 / 4 : ℝ) * (‖w - s‖ / ‖s‖) := by
  have hs0 := upper_ne_zero s hs
  have hlogs : Complex.log (w / 2) - Complex.log (s / 2) =
      Complex.log (1 + (w - s) / s) := by
    rw [← log_div_upper (w / 2) (s / 2) (by simp; linarith) (by simp; linarith)]
    congr 1
    field_simp
    ring
  have he : mainSlope w - mainSlope s = Complex.log (1 + (w - s) / s) / 2 := by
    rw [mainSlope_eq w hw, mainSlope_eq s hs, ← hlogs]
    ring
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := (w - s) / s) (by simpa only [norm_div] using hnear)
  rw [he, norm_div]
  norm_num only [Complex.norm_ofNat]
  simp only [norm_div] at hlog
  linarith

/-- At sufficiently large heights the prescribed window occupies at most a
quarter of the height. -/
private lemma window_small :
    ∃ Y : ℝ, 8 ≤ Y ∧ ∀ y : ℝ, Y ≤ y → 2 * mellinWindow y ≤ y / 4 := by
  have hthird : Tendsto (fun y : ℝ => y ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp ((tendsto_atTop.mp hthird) 8)
  refine ⟨max 8 Y₀, le_max_left _ _, ?_⟩
  intro y hy
  have hyp : 0 < y := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hy)
  have hroot := hY₀ y ((le_max_right _ _).trans hy)
  have hprod : mellinWindow y * y ^ (1 / 3 : ℝ) = y := by
    rw [mellinWindow, ← Real.rpow_add hyp]
    norm_num
  have h := mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hyp.le (2 / 3 : ℝ))
  change mellinWindow y * 8 ≤ mellinWindow y * y ^ (1 / 3 : ℝ) at h
  rw [hprod] at h
  linarith

private lemma slope_on_disk (s w : ℂ) (hs : 8 ≤ s.im)
    (hstrip : |s.re| ≤ s.im / 4) (hnear : ‖w - s‖ ≤ s.im / 4) :
    0 < w.im ∧
      ‖gammaSlope w - mainSlope s‖ ≤ (16 + (3 / 4 : ℝ) * ‖w - s‖) / s.im := by
  have hsp : 0 < s.im := by linarith
  have hsim := Complex.im_le_norm s
  have hsn : 0 < ‖s‖ := hsp.trans_le hsim
  have him : s.im - ‖w - s‖ ≤ w.im := by
    have h := Complex.im_le_norm (s - w)
    rw [Complex.sub_im, norm_sub_rev] at h
    linarith
  have hw4 : 4 ≤ w.im := by linarith
  have hwp : 0 < w.im := by linarith
  have hre : |w.re| ≤ ‖w - s‖ + |s.re| := by
    calc
      _ = |(w - s).re + s.re| := by simp
      _ ≤ |(w - s).re| + |s.re| := abs_add_le _ _
      _ ≤ _ := add_le_add (Complex.abs_re_le_norm _) le_rfl
  have hcone : |w.re| ≤ w.im := by linarith
  have hsmall : ‖w - s‖ / ‖s‖ ≤ 1 / 2 := by
    apply (div_le_iff₀ hsn).mpr
    linarith
  refine ⟨hwp, ?_⟩
  calc
    _ ≤ ‖gammaSlope w - mainSlope w‖ + ‖mainSlope w - mainSlope s‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 8 / w.im + (3 / 4 : ℝ) * (‖w - s‖ / ‖s‖) :=
      add_le_add (gamma_slope_error w hw4 hcone) (mainSlope_difference s w hsp hwp hsmall)
    _ ≤ 16 / s.im + (3 / 4 : ℝ) * (‖w - s‖ / s.im) := by
      apply add_le_add
      · apply (div_le_div_iff₀ hwp hsp).mpr
        linarith
      · gcongr
    _ = _ := by ring

/-- An elementary consequence of Grönwall, used to exponentiate the
logarithmic-derivative estimate without choosing a logarithm of Gamma. -/
private lemma exponential_ode_bound (f f' : ℝ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' u) u)
    (hf0 : f 0 = 1)
    (hbound : ∀ u ∈ Icc (0 : ℝ) 1, ‖f' u‖ ≤ K * ‖f u‖) :
    ‖f 1 - 1‖ ≤ K * Real.exp K := by
  have hc : ContinuousOn (fun u => f u - 1) (Icc (0 : ℝ) 1) := by
    intro u hu
    exact ((hderiv u hu).sub_const 1).continuousAt.continuousWithinAt
  have hd : ∀ u ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (fun u => f u - 1) (f' u) (Ici u) u := by
    intro u hu
    exact ((hderiv u ⟨hu.1, hu.2.le⟩).sub_const 1).hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) 1, ‖f' u‖ ≤ K * ‖f u - 1‖ + K := by
    intro u hu
    have hnorm : ‖f u‖ ≤ ‖f u - 1‖ + 1 := by
      simpa using norm_sub_le (f u - 1) (-1 : ℂ)
    calc
      _ ≤ K * ‖f u‖ := hbound u ⟨hu.1, hu.2.le⟩
      _ ≤ K * (‖f u - 1‖ + 1) := mul_le_mul_of_nonneg_left hnorm hK
      _ = _ := by ring
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (δ := 0) (ε := K) (by simp [hf0]) hb 1 (by simp)
  have he : gronwallBound 0 K K (1 - 0) = Real.exp K - 1 := by
    by_cases hzero : K = 0 <;> simp [gronwallBound, hzero]
  rw [he] at h
  apply h.trans
  have hexp : (1 - K) * Real.exp K ≤ 1 := by
    calc
      _ = (-K + 1) * Real.exp K := by ring
      _ ≤ Real.exp (-K) * Real.exp K :=
        mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-K)) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  nlinarith

private noncomputable def normalizedPath (s z : ℂ) (u : ℝ) : ℂ :=
  gammaFactor (s + (u : ℂ) * (z - s)) / gammaFactor s *
    Complex.exp (-mainSlope s * ((u : ℂ) * (z - s)))

private lemma normalizedPath_derivative (s z : ℂ) (u : ℝ)
    (hw : 0 < (s + (u : ℂ) * (z - s)).im) :
    HasDerivAt (normalizedPath s z)
      ((z - s) * (gammaSlope (s + (u : ℂ) * (z - s)) - mainSlope s) *
        normalizedPath s z u) u := by
  have haff : HasDerivAt (fun v : ℂ => s + v * (z - s)) (z - s) (u : ℂ) := by
    simpa using ((hasDerivAt_id (u : ℂ)).mul_const (z - s)).const_add s
  have hg := (gamma_hasDerivAt _ hw).comp (u : ℂ) haff
  have hexp := (((hasDerivAt_id (u : ℂ)).mul_const (z - s)).const_mul
    (-mainSlope s)).cexp
  have hprod := (hg.div_const (gammaFactor s)).mul hexp
  convert! hprod.comp_ofReal using 1
  dsimp [normalizedPath]
  ring

private lemma linearization_on_disk (s z : ℂ) (hs : 8 ≤ s.im)
    (hstrip : |s.re| ≤ s.im / 4) (hnear : ‖z - s‖ ≤ s.im / 4) :
    ‖gammaLinearError s z‖ ≤
      (17 * Real.exp 4) / s.im * (1 + ‖z - s‖) ^ 3 *
        Real.exp (‖z - s‖ ^ 2 / s.im) := by
  let R : ℝ := ‖z - s‖
  let K : ℝ := R * (16 + (3 / 4 : ℝ) * R) / s.im
  have hsp : 0 < s.im := by linarith
  have hR : 0 ≤ R := norm_nonneg _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdist (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖s + (u : ℂ) * (z - s) - s‖ ≤ R := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hu.1]
    exact mul_le_of_le_one_left hR hu.2
  have hpoint (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      0 < (s + (u : ℂ) * (z - s)).im ∧
        ‖gammaSlope (s + (u : ℂ) * (z - s)) - mainSlope s‖ ≤
          (16 + (3 / 4 : ℝ) * R) / s.im := by
    obtain ⟨hi, hb⟩ := slope_on_disk s (s + (u : ℂ) * (z - s)) hs hstrip
      ((hdist u hu).trans hnear)
    refine ⟨hi, hb.trans ?_⟩
    gcongr
    exact hdist u hu
  have hderiv (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :=
    normalizedPath_derivative s z u (hpoint u hu).1
  have hf0 : normalizedPath s z 0 = 1 := by
    simp [normalizedPath, gammaFactor_ne_zero_upper s hsp]
  have hbound (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      ‖(z - s) * (gammaSlope (s + (u : ℂ) * (z - s)) - mainSlope s) *
        normalizedPath s z u‖ ≤ K * ‖normalizedPath s z u‖ := by
    rw [norm_mul, norm_mul]
    calc
      _ ≤ R * ((16 + (3 / 4 : ℝ) * R) / s.im) * ‖normalizedPath s z u‖ := by
        gcongr
        exact (hpoint u hu).2
      _ = _ := by dsimp [K]; ring
  have hode := exponential_ode_bound (normalizedPath s z)
    (fun u => (z - s) * (gammaSlope (s + (u : ℂ) * (z - s)) - mainSlope s) *
      normalizedPath s z u) K hK hderiv hf0 hbound
  have hend : normalizedPath s z 1 - 1 = gammaLinearError s z := by
    have hsz : s + (z - s) = z := by ring
    simp only [normalizedPath, Complex.ofReal_one, one_mul, hsz, neg_mul, Complex.exp_neg,
      gammaLinearError, mainSlope, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hend] at hode
  have hpoly : K ≤ 17 / s.im * (1 + R) ^ 3 := by
    have hnum : R * (16 + (3 / 4 : ℝ) * R) ≤ 17 * (1 + R) ^ 3 := by
      nlinarith [pow_nonneg hR 3]
    calc
      K ≤ (17 * (1 + R) ^ 3) / s.im := div_le_div_of_nonneg_right hnum hsp.le
      _ = _ := by ring
  have hlin : 16 * R / s.im ≤ 4 := by
    apply (div_le_iff₀ hsp).mpr
    change R ≤ s.im / 4 at hnear
    linarith
  have hquad : (3 / 4 : ℝ) * R ^ 2 / s.im ≤ R ^ 2 / s.im := by
    apply div_le_div_of_nonneg_right _ hsp.le
    nlinarith [sq_nonneg R]
  have hexponent : K ≤ 4 + R ^ 2 / s.im := by
    calc
      K = 16 * R / s.im + (3 / 4 : ℝ) * R ^ 2 / s.im := by dsimp [K]; ring
      _ ≤ _ := add_le_add hlin hquad
  calc
    _ ≤ K * Real.exp K := hode
    _ ≤ (17 / s.im * (1 + R) ^ 3) * Real.exp (4 + R ^ 2 / s.im) :=
      mul_le_mul hpoly (Real.exp_le_exp.mpr hexponent) (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [Real.exp_add]; dsimp [R]; ring

theorem solution (a b : ℝ) (_hab : a < b) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧
      ∀ s z : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
        1 ≤ z.im → ‖z - s‖ ≤ 2 * DeBruijnNewman.Dobner.mellinWindow s.im →
          ‖DeBruijnNewman.Dobner.gammaLinearError s z‖ ≤
            C / s.im * (1 + ‖z - s‖) ^ 3 *
              Real.exp (‖z - s‖ ^ 2 / s.im) := by
  obtain ⟨Y₀, hY₀, hwindow⟩ := window_small
  refine ⟨17 * Real.exp 4, max Y₀ (4 * (|a| + |b|)), by positivity,
    (by linarith : (1 : ℝ) ≤ Y₀).trans (le_max_left _ _), ?_⟩
  intro s z ha hb hy _hz hnear
  have hy₀ : Y₀ ≤ s.im := (le_max_left _ _).trans hy
  have hs8 : 8 ≤ s.im := hY₀.trans hy₀
  have hstrip : |s.re| ≤ s.im / 4 := by
    have hstrip' : |s.re| ≤ |a| + |b| := by
      apply abs_le.mpr
      constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
    have hheight : 4 * (|a| + |b|) ≤ s.im := (le_max_right _ _).trans hy
    linarith
  exact linearization_on_disk s z hs8 hstrip (hnear.trans (hwindow s.im hy₀))
