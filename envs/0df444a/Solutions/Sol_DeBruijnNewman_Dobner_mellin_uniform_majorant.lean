-- Prove2me | solution 1 for DeBruijnNewman.Dobner.mellin_uniform_majorant
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-25T01:10:19.90193+00:00
-- url     : https://prove2.me/submissions/f5121bbe-4a68-4712-95f7-e9060f510002

import Theorems.Thm_DeBruijnNewman_Dobner_gammaFactor_local_linearization

/- Dobner's two contour estimates, with a fixed-time cutoff log(N)^2 <= K*y.
All constants in this proof are independent of the coefficient index. -/

open MeasureTheory Set Filter DeBruijnNewman.Dobner
open scoped Topology

private theorem gamma_norm_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  apply norm_integral_le_of_norm_le (Real.GammaIntegral_convergent hz)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

private theorem gamma_norm_le_shift (z : ℂ) (hz : 1 ≤ |z.im|) (m : ℕ) :
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + m)‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hn : 1 ≤ ‖z + (m : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (z + (m : ℂ))
      simp only [Complex.add_im, Complex.natCast_im, add_zero] at h
      exact hz.trans h
    have hne : z + (m : ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ ≤ ‖Complex.Gamma (z + m)‖ := ih
      _ ≤ ‖z + (m : ℂ)‖ * ‖Complex.Gamma (z + m)‖ := by
        nlinarith [norm_nonneg (Complex.Gamma (z + m))]
      _ = _ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne,
          norm_mul]

/-- Recurrence moves the strip into the right half-plane, where Euler's
integral and compactness give a uniform bound. -/
private theorem gamma_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → 1 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ C := by
  obtain ⟨m, hm⟩ := exists_nat_gt (-a)
  have ha : 0 < a + (m : ℝ) := by linarith
  have hc : ContinuousOn (fun x : ℝ => Complex.Gamma (x : ℂ))
      (Icc (a + m) (b + m)) := by
    intro x hx
    have hxpos : 0 < x := ha.trans_le hx.1
    apply ContinuousAt.continuousWithinAt
    apply (Complex.differentiableAt_Gamma (x : ℂ) ?_).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
    intro k hk
    have h := congrArg Complex.re hk
    norm_num at h
    linarith [Nat.cast_nonneg (α := ℝ) k]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hza hzb hz
  have hzpos : 0 < (z + (m : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  calc
    ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + m)‖ := gamma_norm_le_shift z hz m
    _ ≤ Real.Gamma (z.re + m) := by
      simpa using gamma_norm_le_real (z + m) hzpos
    _ ≤ ‖Complex.Gamma ((z.re + (m : ℝ) : ℝ) : ℂ)‖ := by
      rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ C := hC _ ⟨by linarith, by linarith⟩
    _ ≤ max C 1 := le_max_left _ _

private theorem gamma_nonzero_of_im_ne (z : ℂ) (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  apply hz
  simpa using congrArg Complex.im hm

private theorem sin_norm_bound (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  calc
    _ ≤ (‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖) / 2 :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by
      simp [Complex.norm_exp, Complex.mul_re]
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by
      gcongr
      · exact le_abs_self _
      · exact neg_le_abs _
    _ = _ := by ring

private theorem zeta_polynomial_bound (t : ℝ) (ht : t < 0) (a : ℝ)
    (s : ℂ) (ha : a ≤ s.re) (n : ℕ) :
    ‖zetaTerm t s n‖ * (1 + |t| / 2 * Real.log ((n : ℝ) + 1)) ^ 3 ≤
      Real.exp (2 * (|a| + 3 * |t| / 2) ^ 2 / |t|) *
        Real.exp (t / 8 * Real.log ((n : ℝ) + 1) ^ 2) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  let L := Real.log ((n : ℝ) + 1)
  let d := |t| / 2 * L
  let M := |a| + 3 * |t| / 2
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hzn : ‖zetaTerm t s n‖ ≤ Real.exp (t / 4 * L ^ 2 - a * L) := by
    unfold zetaTerm
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    change t / 4 * L ^ 2 - s.re * L ≤ _
    nlinarith only [mul_le_mul_of_nonneg_right ha hL]
  have hpoly : (1 + d) ^ 3 ≤ Real.exp (3 * d) := by
    have hh : (1 + d) ^ 3 ≤ (Real.exp d) ^ 3 := by
      gcongr
      linarith only [Real.add_one_le_exp d]
    simpa only [show (3 : ℝ) * d = (3 : ℕ) * d by norm_num,
      Real.exp_nat_mul] using hh
  have hyoung : M * L ≤ |t| / 8 * L ^ 2 + 2 * M ^ 2 / |t| := by
    apply sub_nonneg.mp
    have heq : |t| / 8 * L ^ 2 + 2 * M ^ 2 / |t| - M * L =
        (|t| * L - 4 * M) ^ 2 / (8 * |t|) := by
      field_simp
      ring
    rw [heq]
    positivity
  have he : t / 4 * L ^ 2 - a * L + 3 * d ≤
      2 * M ^ 2 / |t| + t / 8 * L ^ 2 := by
    have hlin := mul_le_mul_of_nonneg_right (neg_le_abs a) hL
    dsimp [d, M] at *
    rw [abs_of_neg ht] at hyoung ⊢
    nlinarith only [hyoung, hlin]
  calc
    _ ≤ Real.exp (t / 4 * L ^ 2 - a * L) * Real.exp (3 * d) :=
      mul_le_mul hzn hpoly (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (t / 4 * L ^ 2 - a * L + 3 * d) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * M ^ 2 / |t| + t / 8 * L ^ 2) := Real.exp_le_exp.mpr he
    _ = _ := Real.exp_add _ _

private theorem gamma_inv_reflection (z : ℂ) (hz : z.im ≠ 0) :
    (Complex.Gamma z)⁻¹ =
      Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z) / (Real.pi : ℂ) := by
  have hg := gamma_nonzero_of_im_ne z hz
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have h := congrArg Complex.im hk
    norm_num [Complex.mul_im] at h
    exact hz h
  have hr := (eq_div_iff hs).mp (Complex.Gamma_mul_Gamma_one_sub z)
  apply (eq_div_iff hp).mpr
  field_simp [hg]
  linear_combination -hr

private theorem gamma_inv_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ s.im →
      ‖(Complex.Gamma (s / 2))⁻¹‖ ≤ C * Real.exp (Real.pi * s.im) := by
  obtain ⟨M, hM, hbound⟩ := gamma_strip_bound (1 - b / 2) (1 - a / 2)
  refine ⟨M / Real.pi, div_pos hM Real.pi_pos, ?_⟩
  intro s ha hb hy
  have hsi : 0 < (s / 2).im := by norm_num; linarith
  have hg : ‖Complex.Gamma (1 - s / 2)‖ ≤ M := by
    apply hbound <;> norm_num
    · linarith
    · linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ s.im / 2)]
      linarith
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * (s / 2))‖ ≤
      Real.exp (Real.pi * s.im) := by
    apply (sin_norm_bound _).trans
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_im]
    rw [abs_of_nonneg (by linarith : 0 ≤ s.im / 2)]
    rw [abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [gamma_inv_reflection (s / 2) hsi.ne', norm_div, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ (M * Real.exp (Real.pi * s.im)) / Real.pi := by
      gcongr
    _ = _ := by ring

private theorem gamma_factor_inv_identity (s : ℂ) :
    (gammaFactor s)⁻¹ = 2 * s⁻¹ * (s - 1)⁻¹ *
      Complex.exp ((s / 2) * (Real.log Real.pi : ℂ)) *
        (Complex.Gamma (s / 2))⁻¹ := by
  unfold gammaFactor
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← Complex.exp_neg, neg_mul, neg_neg]
  ring

private theorem gamma_factor_inv_bound (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ s.im →
      ‖(gammaFactor s)⁻¹‖ ≤ C * Real.exp (Real.pi * s.im) := by
  obtain ⟨M, hM, hbound⟩ := gamma_inv_strip_bound a b
  refine ⟨2 * Real.exp (b / 2 * Real.log Real.pi) * M, by positivity, ?_⟩
  intro s ha hb hy
  have h0 : ‖s⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    apply inv_le_one_of_one_le₀
    exact (show 1 ≤ s.im by linarith).trans (Complex.im_le_norm s)
  have h1 : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    apply inv_le_one_of_one_le₀
    have h := Complex.im_le_norm (s - 1)
    norm_num at h
    linarith
  have hlog : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have he : ‖Complex.exp ((s / 2) * (Real.log Real.pi : ℂ))‖ ≤
      Real.exp (b / 2 * Real.log Real.pi) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_re]
    nlinarith
  rw [gamma_factor_inv_identity]
  simp only [norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * 1 * 1 * Real.exp (b / 2 * Real.log Real.pi) *
        (M * Real.exp (Real.pi * s.im)) := by
      gcongr
      exact hbound s ha hb hy
    _ = _ := by ring

private theorem gamma_normalizing_exp_inv_bound (t : ℝ) (ht : t < 0) (s : ℂ) :
    ‖(Complex.exp ((s - J t s) ^ 2 / ((|t| : ℝ) : ℂ)))⁻¹‖ ≤
      Real.exp (|t| * Real.pi ^ 2 / 16) := by
  let L := Complex.log (s / ((2 * Real.pi : ℝ) : ℂ))
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  have hT0 : ((|t| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  have hq : (s - J t s) ^ 2 / ((|t| : ℝ) : ℂ) =
      ((|t| / 16 : ℝ) : ℂ) * L ^ 2 := by
    dsimp [J, L]
    push_cast
    field_simp
    ring
  rw [← Complex.exp_neg, Complex.norm_exp, hq]
  apply Real.exp_le_exp.mpr
  have hre :
      (-(((|t| / 16 : ℝ) : ℂ) * L ^ 2)).re =
        |t| / 16 * (L.im ^ 2 - L.re ^ 2) := by
    norm_num [Complex.mul_re, sq]
    ring
  rw [hre]
  have hi : L.im ^ 2 ≤ Real.pi ^ 2 := by
    have h := Complex.abs_arg_le_pi (s / ((2 * Real.pi : ℝ) : ℂ))
    have hsq := sq_le_sq₀ (abs_nonneg _) Real.pi_pos.le |>.mpr h
    simpa only [sq_abs, L, Complex.log_im] using hsq
  nlinarith [mul_nonneg (abs_nonneg t) (sq_nonneg L.re),
    mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hi)]

/-- A deliberately coarse reciprocal bound, sufficient because the
contour remainder decays like exp(-c * y^(4/3)). -/
private theorem gammaT_inv_bound (t : ℝ) (ht : t < 0) (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ s.im →
      ‖(gammaT t s)⁻¹‖ ≤ C * Real.exp (Real.pi * s.im) := by
  obtain ⟨M, hM, hbound⟩ := gamma_factor_inv_bound a b
  refine ⟨M * Real.exp (|t| * Real.pi ^ 2 / 16), by positivity, ?_⟩
  intro s ha hb hy
  unfold gammaT
  rw [mul_inv_rev, norm_mul]
  calc
    _ ≤ Real.exp (|t| * Real.pi ^ 2 / 16) *
        (M * Real.exp (Real.pi * s.im)) := by
      gcongr
      · exact gamma_normalizing_exp_inv_bound t ht s
      · exact hbound s ha hb hy
    _ = _ := by ring

private theorem gamma_factor_strip_bound (a b : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      (2 ≤ |z.im| ∨ z.re = 2) →
        ‖gammaFactor z‖ ≤ C * (1 + |z.im|) ^ 2 := by
  obtain ⟨M, hM, hbound⟩ := gamma_strip_bound (a / 2) (b / 2)
  let B := |a| + |b|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let E := Real.exp (-(a / 2) * Real.log Real.pi)
  have hE : 0 < E := Real.exp_pos _
  refine ⟨(B + 1) ^ 2 * E * max M 1, by positivity, ?_⟩
  intro z ha hb hz
  have hg : ‖Complex.Gamma (z / 2)‖ ≤ max M 1 := by
    rcases hz with hz | hz
    · apply (hbound (z / 2) ?_ ?_ ?_).trans (le_max_left _ _)
      · norm_num; linarith
      · norm_num; linarith
      · norm_num [abs_div]
        linarith
    · apply le_trans (gamma_norm_le_real (z / 2) (by norm_num [hz]))
      simp [hz]
  have hx : |z.re| ≤ B := by
    apply abs_le.mpr
    constructor <;>
      dsimp [B] <;> linarith [le_abs_self b, neg_abs_le a, abs_nonneg a, abs_nonneg b]
  have hn : ‖z‖ ≤ B + |z.im| := by
    linarith [Complex.norm_le_abs_re_add_abs_im z]
  have hn1 : ‖z - 1‖ ≤ B + |z.im| + 1 := by
    have h := norm_sub_le z (1 : ℂ)
    norm_num at h
    linarith
  have hp0 : 0 ≤ (B + 1) * (1 + |z.im|) := by positivity
  have hnp : ‖z‖ ≤ (B + 1) * (1 + |z.im|) := by
    nlinarith [mul_nonneg hB (abs_nonneg z.im)]
  have hn1p : ‖z - 1‖ ≤ (B + 1) * (1 + |z.im|) := by
    nlinarith [mul_nonneg hB (abs_nonneg z.im)]
  have hp : ‖z‖ * ‖z - 1‖ / 2 ≤ ((B + 1) * (1 + |z.im|)) ^ 2 := by
    have h := mul_le_mul hnp hn1p (norm_nonneg _) hp0
    nlinarith [sq_nonneg ((B + 1) * (1 + |z.im|))]
  have he : ‖Complex.exp (-(z / 2) * (Real.log Real.pi : ℂ))‖ ≤ E := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    norm_num [Complex.mul_re]
    have hlog : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by linarith [Real.pi_gt_three])
    nlinarith
  unfold gammaFactor
  simp only [norm_mul, norm_div, Complex.norm_ofNat]
  calc
    _ ≤ ((B + 1) * (1 + |z.im|)) ^ 2 * E * max M 1 := by gcongr
    _ = _ := by ring

private theorem abs_le_strip (a b x : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    |x| ≤ |a| + |b| := by
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self b, neg_abs_le a, abs_nonneg a, abs_nonneg b]

private theorem shear_bounds (t a b c d : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, ∀ x : ℝ,
      a ≤ s.re → s.re ≤ b → c ≤ x → x ≤ d →
      1 ≤ s.im → 2 * Real.pi ≤ s.im →
        |(J t s).re - x| ≤ D * Real.sqrt s.im ∧
        |(J t s).im - s.im| ≤ |t| * Real.pi / 4 := by
  let B := |a| + |b|
  let X := |c| + |d|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  let D := B + X + |t| / 2 * Real.sqrt (B + 1) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro s x ha hb hc hd hy hpi
  have hsa : |s.re| ≤ B := abs_le_strip a b s.re ha hb
  have hxa : |x| ≤ X := abs_le_strip c d x hc hd
  have hs0 : 0 ≤ s.im := by linarith
  have hsqrt : 1 ≤ Real.sqrt s.im := by simpa using Real.sqrt_le_sqrt hy
  let R := ‖s / ((2 * Real.pi : ℝ) : ℂ)‖
  have hR : R = ‖s‖ / (2 * Real.pi) := by
    dsimp [R]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hR1 : 1 ≤ R := by
    rw [hR, le_div_iff₀ (by positivity)]
    simpa using hpi.trans (Complex.im_le_norm s)
  have hRu : R ≤ (B + 1) * s.im := by
    calc
      R ≤ ‖s‖ := by
        rw [hR]
        exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
      _ ≤ B + s.im := by
        have h := Complex.norm_le_abs_re_add_abs_im s
        rw [abs_of_nonneg hs0] at h
        linarith
      _ ≤ (B + 1) * s.im := by nlinarith
  have hlog : Real.log R ≤ 2 * Real.sqrt R := by
    have h := Real.log_le_rpow_div (zero_le_one.trans hR1) (by norm_num : 0 < (1 / 2 : ℝ))
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hroot : Real.sqrt R ≤ Real.sqrt (B + 1) * Real.sqrt s.im := by
    simpa only [Real.sqrt_mul (by positivity : 0 ≤ B + 1)] using Real.sqrt_le_sqrt hRu
  have hterm : |t| / 4 * Real.log R ≤
      |t| / 2 * Real.sqrt (B + 1) * Real.sqrt s.im := by
    calc
      _ ≤ |t| / 4 * (2 * (Real.sqrt (B + 1) * Real.sqrt s.im)) := by
        gcongr
        linarith
      _ = _ := by ring
  have hterm0 : 0 ≤ |t| / 4 * Real.log R := by
    exact mul_nonneg (by positivity) (Real.log_nonneg hR1)
  have hre : (J t s).re = s.re + |t| / 4 * Real.log R := by
    simp only [J, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.log_re, R]
  have him : (J t s).im - s.im =
      |t| / 4 * Complex.arg (s / ((2 * Real.pi : ℝ) : ℂ)) := by
    simp only [J, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.log_im]
    ring
  constructor
  · rw [hre]
    have hds : B + X + |t| / 2 * Real.sqrt (B + 1) * Real.sqrt s.im ≤
        D * Real.sqrt s.im := by
      dsimp [D]
      nlinarith [mul_nonneg (add_nonneg hB hX) (sub_nonneg.mpr hsqrt)]
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hsa).1, (abs_le.mp hsa).2,
      (abs_le.mp hxa).1, (abs_le.mp hxa).2]
  · rw [him, abs_mul, abs_of_nonneg (by positivity : 0 ≤ |t| / 4)]
    have h := mul_le_mul_of_nonneg_left
      (Complex.abs_arg_le_pi (s / ((2 * Real.pi : ℝ) : ℂ)))
      (show 0 ≤ |t| / 4 by positivity)
    linarith

private noncomputable def linePoint (x v : ℝ) : ℂ := (x : ℂ) + (v : ℂ) * Complex.I

private noncomputable def integrand (t : ℝ) (s : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  gammaFactor z * Complex.exp
    ((J t s - z) ^ 2 / ((|t| : ℝ) : ℂ) - z * (Real.log ((n : ℝ) + 1) : ℂ))

private theorem integrand_norm (t : ℝ) (s : ℂ) (n : ℕ) (x v : ℝ) :
    ‖integrand t s n (linePoint x v)‖ =
      ‖gammaFactor (linePoint x v)‖ *
        Real.exp ((((J t s).re - x) ^ 2 - ((J t s).im - v) ^ 2) / |t| -
          x * Real.log ((n : ℝ) + 1)) := by
  rw [integrand, norm_mul, Complex.norm_exp]
  congr 2
  norm_num [linePoint, Complex.sub_re, Complex.div_ofReal_re, sq,
    Complex.mul_re, Complex.mul_im]

private theorem polynomial_exp_bound (T y v : ℝ) (hT : 0 < T) (hy : 0 ≤ y) :
    (1 + |v|) ^ 2 ≤
      (2 + 16 * T) * Real.exp (2 * y + (v - y) ^ 2 / (8 * T)) := by
  let u := v - y
  have hv : |v| ≤ y + |u| := by
    have h := abs_add_le (v - y) y
    rw [sub_add_cancel, abs_of_nonneg hy] at h
    linarith
  have hfirst : (1 + |v|) ^ 2 ≤ ((1 + y) * (1 + |u|)) ^ 2 := by
    gcongr 1
    nlinarith [mul_nonneg hy (abs_nonneg u)]
  have hyexp : (1 + y) ^ 2 ≤ Real.exp (2 * y) := by
    have he := Real.add_one_le_exp y
    rw [show 2 * y = y + y by ring, Real.exp_add]
    nlinarith [Real.exp_pos y]
  have he1 : 1 ≤ Real.exp (u ^ 2 / (8 * T)) := Real.one_le_exp (by positivity)
  have heu : u ^ 2 ≤ 8 * T * Real.exp (u ^ 2 / (8 * T)) := by
    have h : u ^ 2 / (8 * T) ≤ Real.exp (u ^ 2 / (8 * T)) := by
      linarith [Real.add_one_le_exp (u ^ 2 / (8 * T))]
    have h' := (div_le_iff₀ (show 0 < 8 * T by positivity)).mp h
    nlinarith
  have huexp : (1 + |u|) ^ 2 ≤ (2 + 16 * T) * Real.exp (u ^ 2 / (8 * T)) := by
    have hp : (1 + |u|) ^ 2 ≤ 2 + 2 * u ^ 2 := by
      nlinarith [sq_nonneg (|u| - 1), sq_abs u]
    nlinarith
  calc
    _ ≤ (1 + y) ^ 2 * (1 + |u|) ^ 2 := by simpa only [mul_pow] using hfirst
    _ ≤ Real.exp (2 * y) * ((2 + 16 * T) * Real.exp (u ^ 2 / (8 * T))) := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring

private theorem integrand_gaussian_bound (t : ℝ) (ht : t < 0) (s : ℂ) (n : ℕ)
    (c x v C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D) (hy : 0 ≤ s.im) (hx : c ≤ x)
    (hg : ‖gammaFactor (linePoint x v)‖ ≤ C * (1 + |v|) ^ 2)
    (hre : |(J t s).re - x| ≤ D * Real.sqrt s.im)
    (him : |(J t s).im - s.im| ≤ |t| * Real.pi / 4) :
    ‖integrand t s n (linePoint x v)‖ ≤
      (C * (2 + 16 * |t|) *
        Real.exp ((|t| * Real.pi / 4) ^ 2 / |t| - c * Real.log ((n : ℝ) + 1))) *
      Real.exp ((D ^ 2 / |t| + 2) * s.im - 3 * (v - s.im) ^ 2 / (8 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hre2 : ((J t s).re - x) ^ 2 ≤ D ^ 2 * s.im := by
    have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hD (Real.sqrt_nonneg _))).mpr hre
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hy] using h
  have him2 : ((J t s).im - s.im) ^ 2 ≤ (|t| * Real.pi / 4) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr him
    simpa only [sq_abs, mellinWindow] using! h
  have hq : ((J t s).re - x) ^ 2 - ((J t s).im - v) ^ 2 ≤
      D ^ 2 * s.im + (|t| * Real.pi / 4) ^ 2 - (v - s.im) ^ 2 / 2 := by
    nlinarith [sq_nonneg ((v - s.im) - 2 * ((J t s).im - s.im))]
  have he :
      (((J t s).re - x) ^ 2 - ((J t s).im - v) ^ 2) / |t| -
          x * Real.log ((n : ℝ) + 1) ≤
        (D ^ 2 * s.im + (|t| * Real.pi / 4) ^ 2 - (v - s.im) ^ 2 / 2) / |t| -
          c * Real.log ((n : ℝ) + 1) := by
    gcongr
  rw [integrand_norm]
  calc
    _ ≤ (C * ((2 + 16 * |t|) *
        Real.exp (2 * s.im + (v - s.im) ^ 2 / (8 * |t|)))) *
        Real.exp ((D ^ 2 * s.im + (|t| * Real.pi / 4) ^ 2 -
          (v - s.im) ^ 2 / 2) / |t| - c * Real.log ((n : ℝ) + 1)) := by
      apply mul_le_mul _ (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by positivity)
      exact hg.trans (mul_le_mul_of_nonneg_left (polynomial_exp_bound |t| s.im v hT hy) hC)
    _ = _ := by
      simp only [mul_assoc]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 3
      ring

private theorem window_sq (y : ℝ) (hy : 0 ≤ y) :
    mellinWindow y ^ 2 = y ^ (4 / 3 : ℝ) := by
  rw [mellinWindow, ← Real.rpow_two, ← Real.rpow_mul hy]
  norm_num

private theorem height_domination (K : ℝ) :
    ∃ Y : ℝ, 4 ≤ Y ∧ ∀ y : ℝ, Y ≤ y →
      mellinWindow y ≤ y - 2 ∧ K * y ≤ y ^ (4 / 3 : ℝ) := by
  have hthird : Tendsto (fun y : ℝ => y ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp ((tendsto_atTop.mp hthird) (max 2 K))
  refine ⟨max 4 Y₀, le_max_left _ _, ?_⟩
  intro y hy
  have hy4 : 4 ≤ y := (le_max_left _ _).trans hy
  have hyp : 0 < y := by linarith
  have hroot := hY₀ y ((le_max_right _ _).trans hy)
  have hprod : mellinWindow y * y ^ (1 / 3 : ℝ) = y := by
    rw [mellinWindow, ← Real.rpow_add hyp]
    norm_num
  have hr : 0 ≤ mellinWindow y := Real.rpow_nonneg hyp.le _
  have htwo : 2 ≤ y ^ (1 / 3 : ℝ) := (le_max_left _ _).trans hroot
  have hK : K ≤ y ^ (1 / 3 : ℝ) := (le_max_right _ _).trans hroot
  constructor
  · have h := mul_le_mul_of_nonneg_left htwo hr
    rw [hprod] at h
    linarith
  · calc
      K * y ≤ y ^ (1 / 3 : ℝ) * y := mul_le_mul_of_nonneg_right hK hyp.le
      _ = y ^ (4 / 3 : ℝ) := by
        rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.rpow_add hyp, Real.rpow_one]

private theorem integrand_differentiableAt (t : ℝ) (s : ℂ) (n : ℕ) (z : ℂ)
    (hz : 0 < z.im ∨ z.re = 2) :
    DifferentiableAt ℂ (integrand t s n) z := by
  have hno : ∀ k : ℕ, z / 2 ≠ -k := by
    intro k hk
    rcases hz with hz | hz
    · have h := congrArg Complex.im hk
      norm_num at h
      linarith
    · have h := congrArg Complex.re hk
      norm_num [hz] at h
      linarith [Nat.cast_nonneg (α := ℝ) k]
  have hG : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hno).comp z (by fun_prop)
  unfold integrand gammaFactor
  fun_prop

private theorem integrand_continuous_on_line (t : ℝ) (s : ℂ) (n : ℕ) :
    Continuous (fun v : ℝ => integrand t s n (linePoint 2 v)) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  apply (integrand_differentiableAt t s n (linePoint 2 v)
    (Or.inr (by simp [linePoint]))).continuousAt.comp
  unfold linePoint
  fun_prop

private theorem rectangle_bound (t : ℝ) (s : ℂ) (n : ℕ) (x₁ x₂ l u : ℝ)
    (hl : 0 < l) (hlu : l ≤ u) :
    ‖(∫ v in l..u, integrand t s n (linePoint x₁ v)) -
        ∫ v in l..u, integrand t s n (linePoint x₂ v)‖ ≤
      ‖∫ x in x₁..x₂, integrand t s n (linePoint x l)‖ +
        ‖∫ x in x₁..x₂, integrand t s n (linePoint x u)‖ := by
  have hD : DifferentiableOn ℂ (integrand t s n)
      (uIcc (linePoint x₁ l).re (linePoint x₂ u).re ×ℂ
        uIcc (linePoint x₁ l).im (linePoint x₂ u).im) := by
    intro z hz
    have him : z.im ∈ Icc l u := by
      simpa [linePoint, uIcc_of_le hlu] using hz.2
    exact (integrand_differentiableAt t s n z (Or.inl (hl.trans_le him.1))).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand t s n) (linePoint x₁ l) (linePoint x₂ u) hD
  simp only [linePoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add,
    smul_eq_mul] at h
  have he :
      Complex.I * ((∫ v in l..u, integrand t s n (linePoint x₁ v)) -
        ∫ v in l..u, integrand t s n (linePoint x₂ v)) =
      (∫ x in x₁..x₂, integrand t s n (linePoint x l)) -
        ∫ x in x₁..x₂, integrand t s n (linePoint x u) := by
    dsimp [linePoint]
    linear_combination -h
  calc
    _ = ‖Complex.I * ((∫ v in l..u, integrand t s n (linePoint x₁ v)) -
        ∫ v in l..u, integrand t s n (linePoint x₂ v))‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ = _ := by rw [he]
    _ ≤ _ := norm_sub_le _ _

private theorem shifted_gaussian_integrable (T y : ℝ) (hT : 0 < T) :
    Integrable (fun v : ℝ => Real.exp (-((v - y) ^ 2) / T)) := by
  have h : Integrable (fun v : ℝ => Real.exp (-v ^ 2 / T)) := by
    simpa only [div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using
      integrable_exp_neg_mul_sq (inv_pos.mpr hT)
  exact h.comp_sub_right y

private theorem shifted_gaussian_integral (T y : ℝ) :
    ∫ v : ℝ, Real.exp (-((v - y) ^ 2) / T) = Real.sqrt (Real.pi * T) := by
  rw [integral_sub_right_eq_self (fun v : ℝ => Real.exp (-v ^ 2 / T)) y]
  simpa only [div_eq_mul_inv, neg_mul, mul_neg, mul_comm, inv_inv] using
    integral_gaussian T⁻¹

private theorem outside_interval (y r v : ℝ) (hv : v ∈ (Icc (y - r) (y + r))ᶜ) :
    r ≤ |v - y| := by
  have h : v < y - r ∨ y + r < v := by
    simpa only [mem_compl_iff, mem_Icc, not_and_or, not_le] using hv
  rcases h with h | h <;> linarith [le_abs_self (v - y), neg_abs_le (v - y)]

private theorem integrable_of_gaussian_tail (f : ℝ → ℂ) (hf : Continuous f)
    (T C y r : ℝ) (hT : 0 < T)
    (hbound : ∀ v : ℝ, r ≤ |v - y| →
      ‖f v‖ ≤ C * Real.exp (-((v - y) ^ 2) / (4 * T))) :
    Integrable f := by
  have hi₁ : IntegrableOn f (Icc (y - r) (y + r)) := hf.continuousOn.integrableOn_Icc
  have hi₂ : IntegrableOn f (Icc (y - r) (y + r))ᶜ := by
    apply (((shifted_gaussian_integrable (4 * T) y (by positivity)).const_mul C).integrableOn).mono'
      hf.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
    exact hbound v (outside_interval y r v hv)
  simpa only [union_compl_self, integrableOn_univ] using hi₁.union hi₂

private theorem gaussian_tail_integral_bound (f : ℝ → ℂ) (hf : Integrable f)
    (T C y r : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hr : 0 ≤ r)
    (hbound : ∀ v : ℝ, r ≤ |v - y| →
      ‖f v‖ ≤ C * Real.exp (-((v - y) ^ 2) / (4 * T))) :
    ‖(∫ v : ℝ, f v) - ∫ v in Icc (y - r) (y + r), f v‖ ≤
      C * Real.sqrt (Real.pi * (8 * T)) * Real.exp (-r ^ 2 / (8 * T)) := by
  have hi := (shifted_gaussian_integrable (8 * T) y (by positivity)).const_mul
    (C * Real.exp (-r ^ 2 / (8 * T)))
  have hb : ∀ v ∈ (Icc (y - r) (y + r))ᶜ,
      ‖f v‖ ≤ (C * Real.exp (-r ^ 2 / (8 * T))) *
        Real.exp (-((v - y) ^ 2) / (8 * T)) := by
    intro v hv
    have hv' := outside_interval y r v hv
    have hsq : r ^ 2 ≤ (v - y) ^ 2 := by
      simpa only [sq_abs] using! (sq_le_sq₀ hr (abs_nonneg _)).mpr hv'
    have he : -((v - y) ^ 2) / (4 * T) ≤
        -r ^ 2 / (8 * T) + -((v - y) ^ 2) / (8 * T) := by
      have h := div_le_div_of_nonneg_right hsq (show 0 ≤ 8 * T by positivity)
      ring_nf at h ⊢
      linarith
    calc
      ‖f v‖ ≤ C * Real.exp (-((v - y) ^ 2) / (4 * T)) := hbound v hv'
      _ ≤ C * Real.exp (-r ^ 2 / (8 * T) + -((v - y) ^ 2) / (8 * T)) := by gcongr
      _ = _ := by rw [Real.exp_add]; ring
  rw [← setIntegral_compl measurableSet_Icc hf]
  calc
    _ ≤ ∫ v in (Icc (y - r) (y + r))ᶜ,
        (C * Real.exp (-r ^ 2 / (8 * T))) *
          Real.exp (-((v - y) ^ 2) / (8 * T)) := by
      apply norm_integral_le_of_norm_le hi.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with v hv
      exact hb v hv
    _ ≤ ∫ v : ℝ, (C * Real.exp (-r ^ 2 / (8 * T))) *
        Real.exp (-((v - y) ^ 2) / (8 * T)) :=
      setIntegral_le_integral hi (ae_of_all _ fun _ => by positivity)
    _ = _ := by
      rw [integral_const_mul, shifted_gaussian_integral]
      ring

private theorem central_segment_identity (t : ℝ) (s : ℂ) (n : ℕ) (hy : 0 ≤ s.im) :
    centralMellinTerm t s n =
      (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
        ∫ v in (s.im - mellinWindow s.im)..(s.im + mellinWindow s.im),
          integrand t s n
            (linePoint (s.re + |t| / 2 * Real.log ((n : ℝ) + 1)) v) := by
  have hr : 0 ≤ mellinWindow s.im := Real.rpow_nonneg hy _
  have hp (u : ℝ) :
      mellinSaddlePoint t s n u =
        linePoint (s.re + |t| / 2 * Real.log ((n : ℝ) + 1)) (u + s.im) := by
    apply Complex.ext <;> simp [linePoint, mellinSaddlePoint]
    ring
  have hi :
      (∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
        integrand t s n (mellinSaddlePoint t s n u)) =
      ∫ v in (s.im - mellinWindow s.im)..(s.im + mellinWindow s.im),
        integrand t s n
          (linePoint (s.re + |t| / 2 * Real.log ((n : ℝ) + 1)) v) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -mellinWindow s.im ≤ mellinWindow s.im by linarith)]
    simp_rw [hp]
    rw [intervalIntegral.integral_comp_add_right
      (fun v : ℝ => integrand t s n
        (linePoint (s.re + |t| / 2 * Real.log ((n : ℝ) + 1)) v)) s.im]
    congr 1 <;> ring
  change (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
    (∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
      integrand t s n (mellinSaddlePoint t s n u)) = _
  rw [hi]

private theorem gammaFactor_nonzero (s : ℂ) (hs : 0 < s.im) :
    gammaFactor s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have he : s = 1 := sub_eq_zero.mp h
    simp [he] at hs
  have hG : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hk
    have h := congrArg Complex.im hk
    norm_num at h
    linarith
  unfold gammaFactor
  exact mul_ne_zero (mul_ne_zero
    (div_ne_zero (mul_ne_zero hs0 hs1) (by norm_num)) (Complex.exp_ne_zero _)) hG

private theorem gammaT_nonzero (t : ℝ) (s : ℂ) (hs : 0 < s.im) :
    gammaT t s ≠ 0 := by
  exact mul_ne_zero (gammaFactor_nonzero s hs) (Complex.exp_ne_zero _)

private theorem gammaFactor_continuousAt (s : ℂ) (hs : 0 < s.im) :
    ContinuousAt gammaFactor s := by
  have hG : ContinuousAt (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    apply (Complex.differentiableAt_Gamma (s / 2) ?_).continuousAt.comp
      (f := fun z : ℂ => z / 2) (by fun_prop)
    intro k hk
    have h := congrArg Complex.im hk
    norm_num at h
    linarith
  unfold gammaFactor
  fun_prop

private noncomputable def gaussian (T u : ℝ) : ℝ := Real.exp (-u ^ 2 / T)

private theorem gaussian_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (gaussian T) := by
  unfold gaussian
  simpa only [div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using
    integrable_exp_neg_mul_sq (inv_pos.mpr hT)

private theorem gaussian_integral (T : ℝ) :
    ∫ u : ℝ, gaussian T u = Real.sqrt (Real.pi * T) := by
  simpa only [gaussian, div_eq_mul_inv, neg_mul, mul_neg, mul_comm, inv_inv] using
    integral_gaussian T⁻¹

private theorem saddle_displacement (t : ℝ) (s : ℂ) (n : ℕ) (u : ℝ) :
    mellinSaddlePoint t s n u - s =
      ((|t| / 2 * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) + (u : ℂ) * Complex.I := by
  unfold mellinSaddlePoint
  ring

private theorem saddle_gaussian_identity (t : ℝ) (ht : t < 0)
    (s : ℂ) (hs : 0 < s.im) (n : ℕ) (u : ℝ) :
    (gammaFactor (mellinSaddlePoint t s n u) *
      Complex.exp ((J t s - mellinSaddlePoint t s n u) ^ 2 / ((|t| : ℝ) : ℂ) -
        mellinSaddlePoint t s n u * (Real.log ((n : ℝ) + 1) : ℂ))) / gammaT t s =
      zetaTerm t s n * (gaussian |t| u : ℂ) *
        (1 + gammaLinearError s (mellinSaddlePoint t s n u)) := by
  let z := mellinSaddlePoint t s n u
  let L := (1 / 2 : ℂ) * Complex.log (s / ((2 * Real.pi : ℝ) : ℂ))
  have hgs := gammaFactor_nonzero s hs
  have hg : gammaFactor z =
      (gammaFactor s * Complex.exp (L * (z - s))) * (1 + gammaLinearError s z) := by
    have he : 1 + gammaLinearError s z =
        gammaFactor z / (gammaFactor s * Complex.exp (L * (z - s))) := by
      unfold gammaLinearError L
      ring
    rw [he, mul_div_cancel₀ _ (mul_ne_zero hgs (Complex.exp_ne_zero _))]
  have hp : L * (z - s) + ((J t s - z) ^ 2 / ((|t| : ℝ) : ℂ) -
      z * (Real.log ((n : ℝ) + 1) : ℂ)) =
      (s - J t s) ^ 2 / ((|t| : ℝ) : ℂ) +
        (((t / 4 * Real.log ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) -
          s * (Real.log ((n : ℝ) + 1) : ℂ)) +
        ((-u ^ 2 / |t| : ℝ) : ℂ) := by
    dsimp [L, z, J, mellinSaddlePoint]
    rw [abs_of_neg ht]
    push_cast
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  apply (div_eq_iff (gammaT_nonzero t s hs)).mpr
  change gammaFactor z * _ = _
  rw [hg]
  calc
    _ = gammaFactor s *
        Complex.exp (L * (z - s) +
          ((J t s - z) ^ 2 / ((|t| : ℝ) : ℂ) -
            z * (Real.log ((n : ℝ) + 1) : ℂ))) *
        (1 + gammaLinearError s z) := by
      rw [Complex.exp_add]
      ring
    _ = _ := by
      rw [hp, Complex.exp_add, Complex.exp_add]
      simp only [gammaT, zetaTerm, gaussian, Complex.ofReal_exp]
      ring

/-- A subquadratic growth bound, obtained from monotonicity and n! ≤ n^n. -/
private theorem real_gamma_subquadratic (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      Real.Gamma (x / 2 + 2) ≤ C * Real.exp (ε * x ^ 2) := by
  let δ : ℝ := ε / 32
  let M : ℝ := |Real.log δ|
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hM : 0 ≤ M := abs_nonneg _
  refine ⟨Real.exp (8 * M ^ 2 / ε), Real.exp_pos _, ?_⟩
  intro x hx
  let m : ℕ := ⌈x / 2 + 2⌉₊
  have hmlo : x / 2 + 2 ≤ (m : ℝ) := Nat.le_ceil _
  have hmhi : (m : ℝ) ≤ 4 * x := by
    have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ x / 2 + 2)
    change (m : ℝ) < x / 2 + 2 + 1 at h
    linarith
  have hmp : 0 < (m : ℝ) := by linarith
  have hlog : Real.log (m : ℝ) ≤ δ * m + M := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hδ hmp)
    rw [Real.log_mul hδ.ne' hmp.ne'] at h
    have hneg := neg_le_abs (Real.log δ)
    dsimp [M]
    linarith
  have hquadratic : 4 * M * x ≤ ε / 2 * x ^ 2 + 8 * M ^ 2 / ε := by
    refine le_of_mul_le_mul_right (a := ε) ?_ hε
    field_simp
    nlinarith [sq_nonneg (ε * x - 4 * M)]
  have hexp : (m : ℝ) * Real.log m ≤ 8 * M ^ 2 / ε + ε * x ^ 2 := by
    calc
      _ ≤ δ * (m : ℝ) ^ 2 + M * m := by nlinarith
      _ ≤ δ * (4 * x) ^ 2 + M * (4 * x) := by gcongr
      _ = ε / 2 * x ^ 2 + 4 * M * x := by dsimp [δ]; ring
      _ ≤ _ := by linarith
  calc
    _ ≤ Real.Gamma ((m : ℝ) + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp; linarith) (by simp; linarith)
        (by linarith)
    _ = (m.factorial : ℝ) := Real.Gamma_nat_eq_factorial m
    _ ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
    _ = Real.exp ((m : ℝ) * Real.log m) := by rw [Real.exp_nat_mul, Real.exp_log hmp]
    _ ≤ Real.exp (8 * M ^ 2 / ε + ε * x ^ 2) := Real.exp_le_exp.mpr hexp
    _ = _ := Real.exp_add _ _

/-- Two Gamma recurrences absorb the quadratic polynomial factor uniformly
in the imaginary part. -/
private theorem gamma_factor_le_real (z : ℂ) (hz : 1 ≤ z.re) :
    ‖gammaFactor z‖ ≤ 2 * Real.Gamma (z.re / 2 + 2) := by
  have hz0 : z / 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hz1 : z / 2 + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have hz2 : z + 2 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith
  have he : gammaFactor z =
      2 * ((z - 1) / (z + 2)) *
        Complex.exp (-(z / 2) * (Real.log Real.pi : ℂ)) * Complex.Gamma (z / 2 + 2) := by
    rw [show z / 2 + 2 = (z / 2 + 1) + 1 by ring,
      Complex.Gamma_add_one _ hz1, Complex.Gamma_add_one _ hz0, gammaFactor]
    field_simp
  have hr : ‖(z - 1) / (z + 2)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hz2)]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [Complex.sq_norm, Complex.normSq_apply]
    norm_num
    nlinarith
  have hp : ‖Complex.exp (-(z / 2) * (Real.log Real.pi : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    norm_num [Complex.mul_re]
    have hlog := Real.log_nonneg (show 1 ≤ Real.pi by linarith [Real.pi_gt_three])
    nlinarith
  have hg : ‖Complex.Gamma (z / 2 + 2)‖ ≤ Real.Gamma (z.re / 2 + 2) := by
    simpa using gamma_norm_le_real (z / 2 + 2) (by norm_num; linarith)
  rw [he, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
  calc
    _ ≤ 2 * 1 * 1 * Real.Gamma (z.re / 2 + 2) := by gcongr
    _ = _ := by ring

private theorem gamma_factor_right_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re →
      ‖gammaFactor z‖ ≤ C * Real.exp (ε * z.re ^ 2) := by
  obtain ⟨C, hC, hb⟩ := real_gamma_subquadratic ε hε
  refine ⟨2 * C, by positivity, ?_⟩
  intro z hz
  calc
    _ ≤ 2 * Real.Gamma (z.re / 2 + 2) := gamma_factor_le_real z hz
    _ ≤ 2 * (C * Real.exp (ε * z.re ^ 2)) :=
      mul_le_mul_of_nonneg_left (hb z.re hz) (by norm_num)
    _ = _ := by ring

/-- A global bound for the horizontal pieces, with only a fixed lower
bound on the real part. -/
private theorem gamma_factor_lower_re_bound (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → (2 ≤ |z.im| ∨ 1 ≤ z.re) →
      ‖gammaFactor z‖ ≤ C * (1 + |z.im|) ^ 2 * Real.exp (z.re ^ 2) := by
  obtain ⟨A, hA, hright⟩ := gamma_factor_right_growth 1 (by norm_num)
  obtain ⟨B, hB, hstrip⟩ := gamma_factor_strip_bound a 1
  refine ⟨A + B, by positivity, ?_⟩
  intro z hz hzi
  have hp : 1 ≤ (1 + |z.im|) ^ 2 := by nlinarith [abs_nonneg z.im]
  have he : 1 ≤ Real.exp (z.re ^ 2) := Real.one_le_exp (sq_nonneg _)
  by_cases hx : 1 ≤ z.re
  · have hg := hright z hx
    simp only [one_mul] at hg
    apply hg.trans
    gcongr
    nlinarith
  · have hg := hstrip z hz (by linarith) (Or.inl (hzi.resolve_right hx))
    apply hg.trans
    calc
      _ ≤ (A + B) * (1 + |z.im|) ^ 2 := by gcongr; linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) he

private theorem integrand_right_differentiableAt (t : ℝ) (s : ℂ) (n : ℕ)
    (z : ℂ) (hz : 1 ≤ z.re) :
    DifferentiableAt ℂ (integrand t s n) z := by
  have hno : ∀ m : ℕ, z / 2 ≠ -(m : ℂ) := by
    intro m hm
    have h := congrArg Complex.re hm
    norm_num at h
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hG : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hno).comp z (by fun_prop)
  unfold integrand gammaFactor
  fun_prop

private theorem rectangle_right_bound (t : ℝ) (s : ℂ) (n : ℕ) (x₁ x₂ l u : ℝ)
    (hx₁ : 1 ≤ x₁) (hx₂ : 1 ≤ x₂) :
    ‖(∫ v in l..u, integrand t s n (linePoint x₁ v)) -
        ∫ v in l..u, integrand t s n (linePoint x₂ v)‖ ≤
      ‖∫ x in x₁..x₂, integrand t s n (linePoint x l)‖ +
        ‖∫ x in x₁..x₂, integrand t s n (linePoint x u)‖ := by
  have hD : DifferentiableOn ℂ (integrand t s n)
      (uIcc (linePoint x₁ l).re (linePoint x₂ u).re ×ℂ
        uIcc (linePoint x₁ l).im (linePoint x₂ u).im) := by
    intro z hz
    have hre : min x₁ x₂ ≤ z.re := by simpa [linePoint] using hz.1.1
    exact (integrand_right_differentiableAt t s n z
      ((le_min hx₁ hx₂).trans hre)).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (integrand t s n) (linePoint x₁ l) (linePoint x₂ u) hD
  simp only [linePoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero, zero_add, smul_eq_mul] at h
  have he :
      Complex.I * ((∫ v in l..u, integrand t s n (linePoint x₁ v)) -
        ∫ v in l..u, integrand t s n (linePoint x₂ v)) =
      (∫ x in x₁..x₂, integrand t s n (linePoint x l)) -
        ∫ x in x₁..x₂, integrand t s n (linePoint x u) := by
    dsimp [linePoint]
    linear_combination -h
  calc
    _ = ‖Complex.I * ((∫ v in l..u, integrand t s n (linePoint x₁ v)) -
        ∫ v in l..u, integrand t s n (linePoint x₂ v))‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ = _ := by rw [he]
    _ ≤ _ := norm_sub_le _ _

private theorem right_strip_gaussian_bound (t : ℝ) (ht : t < 0) (s : ℂ)
    (n : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∃ A : ℝ, 0 < A ∧ ∀ r v : ℝ, r ∈ uIcc 2 x →
      ‖integrand t s n (linePoint r v)‖ ≤
        A * Real.exp (-((v - (J t s).im) ^ 2) / |t|) := by
  obtain ⟨C, hC, hgrowth⟩ := gamma_factor_right_growth 1 (by norm_num)
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  let D : ℝ := 2 + |x|
  let A : ℝ := C * Real.exp (D ^ 2 + (|(J t s).re| + D) ^ 2 / |t|)
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro r v hr
  have hr1 : 1 ≤ r := (le_min (by norm_num) hx).trans hr.1
  have hrD : |r| ≤ D := by
    rw [abs_of_nonneg (by linarith)]
    exact hr.2.trans (max_le (by dsimp [D]; linarith [abs_nonneg x])
      (by dsimp [D]; linarith [le_abs_self x]))
  have hJr : |(J t s).re - r| ≤ |(J t s).re| + D := by
    have h := abs_add_le (J t s).re (-r)
    rw [abs_neg, ← sub_eq_add_neg] at h
    linarith
  have hJr2 : ((J t s).re - r) ^ 2 ≤ (|(J t s).re| + D) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by dsimp [D]; positivity)).mpr hJr
  have hr2 : r ^ 2 ≤ D ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by dsimp [D]; positivity)).mpr hrD
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hg : ‖gammaFactor (linePoint r v)‖ ≤ C * Real.exp (D ^ 2) := by
    apply (hgrowth (linePoint r v) (by simpa [linePoint] using hr1)).trans
    simp only [linePoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      one_mul]
    gcongr
  have hphase :
      (((J t s).re - r) ^ 2 - ((J t s).im - v) ^ 2) / |t| -
          r * Real.log ((n : ℝ) + 1) ≤
        (|(J t s).re| + D) ^ 2 / |t| - (v - (J t s).im) ^ 2 / |t| := by
    have h := div_le_div_of_nonneg_right hJr2 hT.le
    have hn := mul_nonneg (show 0 ≤ r by linarith) hlog
    rw [sub_div, show ((J t s).im - v) ^ 2 = (v - (J t s).im) ^ 2 by ring]
    linarith
  rw [integrand_norm]
  calc
    _ ≤ (C * Real.exp (D ^ 2)) *
        Real.exp ((|(J t s).re| + D) ^ 2 / |t| - (v - (J t s).im) ^ 2 / |t|) :=
      mul_le_mul hg (Real.exp_le_exp.mpr hphase) (Real.exp_nonneg _) (by positivity)
    _ = _ := by
      dsimp [A]
      rw [show -((v - (J t s).im) ^ 2) / |t| =
        -((v - (J t s).im) ^ 2 / |t|) by ring, Real.exp_neg, Real.exp_sub, Real.exp_add]
      ring

private theorem gaussian_tendsto_zero (T : ℝ) (hT : 0 < T) :
    Tendsto (fun R : ℝ => Real.exp (-R ^ 2 / T)) atTop (𝓝 0) := by
  have hp : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hq : Tendsto (fun R : ℝ => R ^ 2 / T) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (tendsto_const_mul_atTop_of_pos (inv_pos.mpr hT)).mpr hp
  simpa only [Function.comp_def, neg_div] using!
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq)

private theorem vertical_integrals_eq (t : ℝ) (ht : t < 0) (s : ℂ) (n : ℕ)
    (x : ℝ) (hx : 1 ≤ x) :
    (∫ v : ℝ, integrand t s n (linePoint 2 v)) =
      ∫ v : ℝ, integrand t s n (linePoint x v) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨A, hA, hb⟩ := right_strip_gaussian_bound t ht s n x hx
  let y := (J t s).im
  have hi (r : ℝ) (hr : r ∈ uIcc 2 x) :
      Integrable (fun v : ℝ => integrand t s n (linePoint r v)) := by
    have hr1 : 1 ≤ r := (le_min (by norm_num) hx).trans hr.1
    have hc : Continuous (fun v : ℝ => integrand t s n (linePoint r v)) := by
      apply continuous_iff_continuousAt.mpr
      intro v
      apply (integrand_right_differentiableAt t s n _ (by simpa [linePoint] using hr1)).continuousAt.comp
      unfold linePoint
      fun_prop
    apply ((shifted_gaussian_integrable |t| y hT).const_mul A).mono' hc.aestronglyMeasurable
    filter_upwards with v
    exact hb r v hr
  have hl : Tendsto (fun R : ℝ => y - R) atTop atBot := by
    refine tendsto_atBot.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (y - b)] with R hR
    linarith
  have hu : Tendsto (fun R : ℝ => y + R) atTop atTop := by
    refine tendsto_atTop.mpr fun b => ?_
    filter_upwards [eventually_ge_atTop (b - y)] with R hR
    linarith
  have hlim := (intervalIntegral_tendsto_integral (hi 2 (by simp)) hl hu).sub
    (intervalIntegral_tendsto_integral (hi x (by simp)) hl hu)
  have hbound (R : ℝ) :
      ‖(∫ v in (y - R)..(y + R), integrand t s n (linePoint 2 v)) -
          ∫ v in (y - R)..(y + R), integrand t s n (linePoint x v)‖ ≤
        (2 * A * |x - 2|) * Real.exp (-R ^ 2 / |t|) := by
    have hlow : ‖∫ r in (2 : ℝ)..x, integrand t s n (linePoint r (y - R))‖ ≤
        (A * Real.exp (-R ^ 2 / |t|)) * |x - 2| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      convert! hb r (y - R) (uIoc_subset_uIcc hr) using 1
      dsimp [y]
      congr 2
      ring
    have hupp : ‖∫ r in (2 : ℝ)..x, integrand t s n (linePoint r (y + R))‖ ≤
        (A * Real.exp (-R ^ 2 / |t|)) * |x - 2| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      convert! hb r (y + R) (uIoc_subset_uIcc hr) using 1
      dsimp [y]
      congr 2
      ring
    apply (rectangle_right_bound t s n 2 x (y - R) (y + R) (by norm_num) hx).trans
    nlinarith
  have hzero := squeeze_zero (fun R : ℝ => norm_nonneg
      ((∫ v in (y - R)..(y + R), integrand t s n (linePoint 2 v)) -
        ∫ v in (y - R)..(y + R), integrand t s n (linePoint x v)))
    hbound (by simpa only [mul_zero] using!
      (gaussian_tendsto_zero |t| hT).const_mul (2 * A * |x - 2|))
  exact sub_eq_zero.mp (norm_eq_zero.mp (tendsto_nhds_unique hlim.norm hzero))

private theorem mellin_shift_right (t : ℝ) (ht : t < 0) (s : ℂ) (n : ℕ)
    (x : ℝ) (hx : 1 ≤ x) :
    mellinTerm t s n = (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
      ∫ v : ℝ, integrand t s n (linePoint x v) := by
  change (1 / (Real.sqrt (Real.pi * |t|) : ℂ)) *
    (∫ v : ℝ, integrand t s n (linePoint 2 v)) = _
  rw [vertical_integrals_eq t ht s n x hx]

private theorem mellin_right_bound (t : ℝ) (ht : t < 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ∀ n : ℕ,
      1 ≤ (J t s).re + |t| / 2 * Real.log ((n : ℝ) + 1) →
      ‖mellinTerm t s n‖ ≤ C * Real.exp
        (ε * ((J t s).re + |t| / 2 * Real.log ((n : ℝ) + 1)) ^ 2 -
          |t| / 4 * Real.log ((n : ℝ) + 1) ^ 2 -
          (J t s).re * Real.log ((n : ℝ) + 1)) := by
  obtain ⟨C, hC, hgrowth⟩ := gamma_factor_right_growth ε hε
  refine ⟨C, hC, ?_⟩
  intro s n hx
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  let L := Real.log ((n : ℝ) + 1)
  let X := (J t s).re + |t| / 2 * L
  let E := ε * X ^ 2 - |t| / 4 * L ^ 2 - (J t s).re * L
  let p := Real.sqrt (Real.pi * |t|)
  have hp : 0 < p := Real.sqrt_pos.mpr (by positivity)
  have hb (v : ℝ) : ‖integrand t s n (linePoint X v)‖ ≤
      (C * Real.exp E) * Real.exp (-((v - (J t s).im) ^ 2) / |t|) := by
    have hg := hgrowth (linePoint X v) (by simpa [linePoint, X, L] using hx)
    simp only [linePoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      at hg
    rw [integrand_norm]
    calc
      _ ≤ (C * Real.exp (ε * X ^ 2)) *
          Real.exp ((((J t s).re - X) ^ 2 - ((J t s).im - v) ^ 2) / |t| - X * L) :=
        mul_le_mul_of_nonneg_right hg (Real.exp_nonneg _)
      _ = _ := by
        simp only [mul_assoc]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        dsimp [E, X]
        field_simp
        ring
  have hnorm : ‖∫ v : ℝ, integrand t s n (linePoint X v)‖ ≤
      (C * Real.exp E) * p := by
    calc
      _ ≤ ∫ v : ℝ, (C * Real.exp E) *
          Real.exp (-((v - (J t s).im) ^ 2) / |t|) :=
        norm_integral_le_of_norm_le
          ((shifted_gaussian_integrable |t| _ hT).const_mul _) (ae_of_all _ hb)
      _ = _ := by rw [integral_const_mul, shifted_gaussian_integral]
  rw [mellin_shift_right t ht s n X hx, norm_mul, norm_div, norm_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  change (1 / p) * _ ≤ C * Real.exp E
  calc
    _ ≤ (1 / p) * ((C * Real.exp E) * p) := by gcongr
    _ = _ := by field_simp

set_option maxHeartbeats 800000 in
/-- For large indices the full rightward shift gives more decay than is
needed to pay for the reciprocal normalization. -/
private theorem large_index_bound (t : ℝ) (ht : t < 0) (a b : ℝ) :
    ∃ K C Y : ℝ, 0 < K ∧ 0 < C ∧ 1 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im → ∀ n : ℕ,
        K * s.im < Real.log ((n : ℝ) + 1) ^ 2 →
        ‖normalizedMellinTerm t s n‖ ≤
          C * Real.exp (t / 40 * Real.log ((n : ℝ) + 1) ^ 2) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨D, hD, hJ⟩ := shear_bounds t a b 0 0
  obtain ⟨M, hM, hright⟩ := mellin_right_bound t ht (1 / (100 * |t|)) (by positivity)
  obtain ⟨G, hG, hginv⟩ := gammaT_inv_bound t ht a b
  let K : ℝ := 1 + 100 * D ^ 2 / |t| ^ 2 + 20 * Real.pi / |t|
  have hK1 : 1 ≤ K := by
    dsimp [K]
    linarith [div_nonneg (show 0 ≤ 100 * D ^ 2 by positivity) (sq_nonneg |t|),
      div_nonneg (show 0 ≤ 20 * Real.pi by positivity) hT.le]
  have hKD : 100 * D ^ 2 ≤ |t| ^ 2 * K := by
    have h : 100 * D ^ 2 / |t| ^ 2 ≤ K := by
      dsimp [K]
      linarith [div_nonneg (show 0 ≤ 20 * Real.pi by positivity) hT.le]
    have hh := (div_le_iff₀ (sq_pos_of_pos hT)).mp h
    nlinarith
  have hKP : 20 * Real.pi ≤ |t| * K := by
    have h : 20 * Real.pi / |t| ≤ K := by
      dsimp [K]
      linarith [div_nonneg (show 0 ≤ 100 * D ^ 2 by positivity) (sq_nonneg |t|)]
    have hh := (div_le_iff₀ hT).mp h
    linarith
  refine ⟨K, M * G, max (2 * Real.pi) (max 2 (100 / |t| ^ 2)),
    lt_of_lt_of_le zero_lt_one hK1, mul_pos hM hG,
    (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi).trans (le_max_left _ _), ?_⟩
  intro s ha hb hy n hlarge
  let L := Real.log ((n : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hyπ : 2 * Real.pi ≤ s.im := (le_max_left _ _).trans hy
  have hy2 : 2 ≤ s.im := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hyp : 0 < s.im := by linarith
  have hysq : 100 ≤ s.im * |t| ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hT)).mp
      ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hcut : s.im ≤ L ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hK1 hyp.le
    dsimp [L]
    linarith
  have hsize : 10 ≤ |t| * L := by
    have h := mul_le_mul_of_nonneg_right hcut (sq_nonneg |t|)
    nlinarith [mul_nonneg hT.le hL]
  have hJs := hJ s 0 ha hb (by norm_num) (by norm_num) (by linarith) hyπ
  simp only [sub_zero] at hJs
  have hJsq : (J t s).re ^ 2 ≤ D ^ 2 * s.im := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hJs.1
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hyp.le] using h
  have hJsmall : |(J t s).re| ≤ |t| / 10 * L := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs]
    have h₁ := mul_le_mul_of_nonneg_right hKD hyp.le
    have h₂ := mul_le_mul_of_nonneg_left hlarge.le (sq_nonneg |t|)
    change |t| ^ 2 * (K * s.im) ≤ |t| ^ 2 * L ^ 2 at h₂
    nlinarith only [hJsq, h₁, h₂]
  let X := (J t s).re + |t| / 2 * L
  have hX : 1 ≤ X := by
    dsimp [X]
    linarith [(abs_le.mp hJsmall).1]
  have hXu : X ≤ |t| * L := by
    dsimp [X]
    linarith [(abs_le.mp hJsmall).2]
  have hXsq : X ^ 2 ≤ (|t| * L) ^ 2 :=
    (sq_le_sq₀ (by linarith) (by positivity)).mpr hXu
  have hquadratic : 1 / (100 * |t|) * X ^ 2 ≤ |t| / 100 * L ^ 2 := by
    have h := div_le_div_of_nonneg_right hXsq (show 0 ≤ 100 * |t| by positivity)
    convert! h using 1 <;> field_simp
  have hlinear : -(J t s).re * L ≤ |t| / 10 * L ^ 2 := by
    have h := mul_le_mul_of_nonneg_right (abs_le.mp hJsmall).1 hL
    nlinarith
  have hmain : ‖mellinTerm t s n‖ ≤ M * Real.exp (-|t| / 10 * L ^ 2) := by
    apply (hright s n hX).trans
    apply mul_le_mul_of_nonneg_left _ hM.le
    apply Real.exp_le_exp.mpr
    change 1 / (100 * |t|) * X ^ 2 - |t| / 4 * L ^ 2 - (J t s).re * L ≤ _
    nlinarith [mul_nonneg hT.le (sq_nonneg L)]
  have hnormexp : Real.pi * s.im ≤ |t| / 20 * L ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hKP hyp.le
    have h₂ := mul_le_mul_of_nonneg_left hlarge.le hT.le
    change |t| * (K * s.im) ≤ |t| * L ^ 2 at h₂
    nlinarith
  rw [normalizedMellinTerm, div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (M * Real.exp (-|t| / 10 * L ^ 2)) *
        (G * Real.exp (Real.pi * s.im)) :=
      mul_le_mul hmain (hginv s ha hb hy2) (norm_nonneg _) (by positivity)
    _ = (M * G) * Real.exp (-|t| / 10 * L ^ 2 + Real.pi * s.im) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_pos hM hG).le
      apply Real.exp_le_exp.mpr
      change -|t| / 10 * L ^ 2 + Real.pi * s.im ≤ t / 40 * L ^ 2
      rw [abs_of_neg ht] at hnormexp ⊢
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ht.le (sq_nonneg L)]

/-- Uniform control away from the saddle when the contour width is of
order sqrt(y) and log(n+1)^2 is at most K*y. -/
private theorem uniform_off_saddle_bound (t : ℝ) (ht : t < 0)
    (a b c K D : ℝ) (hK : 0 < K) (hD : 0 < D) :
    ∃ C Y : ℝ, 0 < C ∧ 4 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
      ∀ n : ℕ, Real.log ((n : ℝ) + 1) ^ 2 ≤ K * s.im →
      ∀ x v : ℝ, c ≤ x → |x| ≤ D * Real.sqrt s.im →
        (2 ≤ |v| ∨ x = 2) → mellinWindow s.im ≤ |v - s.im| →
        ‖integrand t s n (linePoint x v)‖ ≤
          C * Real.exp (-((v - s.im) ^ 2) / (4 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨M, hM, hgrowth⟩ := gamma_factor_lower_re_bound c
  obtain ⟨D₀, hD₀, hshear⟩ := shear_bounds t a b 0 0
  let Q := Real.sqrt K
  let E := D₀ + D
  let B := D ^ 2 + E ^ 2 / |t| + 2 + |c| * Q
  let C := M * (2 + 16 * |t|) * Real.exp ((|t| * Real.pi / 4) ^ 2 / |t|)
  obtain ⟨Y₀, hY₀, hheight⟩ := height_domination (8 * |t| * B)
  refine ⟨C, max Y₀ (2 * Real.pi), (by dsimp [C]; positivity),
    hY₀.trans (le_max_left _ _), ?_⟩
  intro s ha hb hy n hn x v hx hxa hv hfar
  have hy₀ : Y₀ ≤ s.im := (le_max_left _ _).trans hy
  have hyπ : 2 * Real.pi ≤ s.im := (le_max_right _ _).trans hy
  have hy4 : 4 ≤ s.im := hY₀.trans hy₀
  have hy1 : 1 ≤ s.im := by linarith
  have hy0 : 0 ≤ s.im := by linarith
  have hsqrt1 : 1 ≤ Real.sqrt s.im := by simpa using Real.sqrt_le_sqrt hy1
  have hsqrty : Real.sqrt s.im ≤ s.im := by
    nlinarith only [Real.sq_sqrt hy0,
      mul_nonneg (Real.sqrt_nonneg s.im) (sub_nonneg.mpr hsqrt1)]
  let L := Real.log ((n : ℝ) + 1)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hLbound : L ≤ Q * Real.sqrt s.im := by
    apply (sq_le_sq₀ hL (by dsimp [Q]; positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hy0, Q, L] using hn
  have hj := hshear s 0 ha hb (by norm_num) (by norm_num) hy1 hyπ
  simp only [sub_zero] at hj
  have hre : |(J t s).re - x| ≤ E * Real.sqrt s.im := by
    have hh := abs_add_le (J t s).re (-x)
    rw [abs_neg] at hh
    change |(J t s).re - x| ≤ |(J t s).re| + |x| at hh
    dsimp [E]
    nlinarith only [hh, hj.1, hxa]
  have hxsq : x ^ 2 ≤ D ^ 2 * s.im := by
    have hh := (sq_le_sq₀ (abs_nonneg x) (by positivity)).mpr hxa
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hy0] using hh
  have hg₀ := hgrowth (linePoint x v) (by simpa [linePoint] using hx)
    (by
      simp only [linePoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
        zero_add, Complex.add_re, Complex.mul_re, sub_zero]
      rcases hv with hv | rfl
      · exact Or.inl hv
      · exact Or.inr (by norm_num))
  simp only [linePoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_add] at hg₀
  have hg : ‖gammaFactor (linePoint x v)‖ ≤
      (M * Real.exp (D ^ 2 * s.im)) * (1 + |v|) ^ 2 := by
    calc
      _ ≤ M * (1 + |v|) ^ 2 * Real.exp (x ^ 2) := hg₀
      _ ≤ M * (1 + |v|) ^ 2 * Real.exp (D ^ 2 * s.im) := by gcongr
      _ = _ := by ring
  have hbnd := integrand_gaussian_bound t ht s n c x v
    (M * Real.exp (D ^ 2 * s.im)) E (by positivity)
    (by dsimp [E]; positivity) hy0 hx hg hre hj.2
  have hlin : -c * L ≤ |c| * Q * s.im := by
    calc
      -c * L ≤ |c| * L := mul_le_mul_of_nonneg_right (neg_le_abs c) hL
      _ ≤ |c| * (Q * Real.sqrt s.im) := by gcongr
      _ ≤ |c| * (Q * s.im) := by dsimp [Q]; gcongr
      _ = _ := by ring
  have hfar2 : s.im ^ (4 / 3 : ℝ) ≤ (v - s.im) ^ 2 := by
    have hh := (sq_le_sq₀ (show 0 ≤ mellinWindow s.im from Real.rpow_nonneg hy0 _)
      (abs_nonneg _)).mpr hfar
    simpa only [window_sq _ hy0, sq_abs] using hh
  have hBy : B * s.im ≤ (v - s.im) ^ 2 / (8 * |t|) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * |t|)).mpr
    have hh := (hheight s.im hy₀).2.trans hfar2
    nlinarith only [hh]
  calc
    _ ≤ _ := hbnd
    _ = C * Real.exp (D ^ 2 * s.im - c * L +
        (E ^ 2 / |t| + 2) * s.im - 3 * (v - s.im) ^ 2 / (8 * |t|)) := by
      dsimp [C, L]
      simp only [Real.exp_add, Real.exp_sub]
      ring
    _ ≤ C * Real.exp (B * s.im - 3 * (v - s.im) ^ 2 / (8 * |t|)) := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      apply Real.exp_le_exp.mpr
      dsimp [B]
      nlinarith only [hlin]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
      apply Real.exp_le_exp.mpr
      have heq : 3 * (v - s.im) ^ 2 / (8 * |t|) =
          (v - s.im) ^ 2 / (8 * |t|) + (v - s.im) ^ 2 / (4 * |t|) := by ring
      rw [heq]
      simp only [neg_div]
      linarith only [hBy]

private theorem uniform_unnormalized_remainder (t : ℝ) (ht : t < 0)
    (a b K : ℝ) (hK : 0 < K) :
    ∃ C Y : ℝ, 0 < C ∧ 4 ≤ Y ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → Y ≤ s.im → ∀ n : ℕ,
        Real.log ((n : ℝ) + 1) ^ 2 ≤ K * s.im →
        ‖mellinTerm t s n - centralMellinTerm t s n‖ ≤
          C * Real.exp (s.im - s.im ^ (4 / 3 : ℝ) / (8 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  let B := |a| + |b|
  let D := 2 + B + |t| / 2 * Real.sqrt K
  let c := min 2 a
  let W := D + 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD2 : 2 ≤ D := by
    dsimp [D]
    linarith [mul_nonneg (show 0 ≤ |t| / 2 by positivity) (Real.sqrt_nonneg K)]
  have hD : 0 < D := by linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨C, Y₁, hC, hY₁, hoff⟩ := uniform_off_saddle_bound t ht a b c K D hK hD
  obtain ⟨Y₂, hY₂, hgeom⟩ := height_domination 0
  let p := Real.sqrt (Real.pi * |t|)
  have hp : 0 < p := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hT)
  let A := (C * Real.sqrt (Real.pi * (8 * |t|)) + 2 * C * W) / p
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, max Y₁ Y₂, hA, hY₁.trans (le_max_left _ _), ?_⟩
  intro s ha hb hy n hn
  let y := s.im
  let r := mellinWindow y
  let L := Real.log ((n : ℝ) + 1)
  let δ := |t| / 2 * L
  let X := s.re + δ
  let f : ℝ → ℂ := fun v => integrand t s n (linePoint 2 v)
  let g : ℝ → ℂ := fun v => integrand t s n (linePoint X v)
  have hy₁ : Y₁ ≤ y := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ y := (le_max_right _ _).trans hy
  have hy4 : 4 ≤ y := hY₁.trans hy₁
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hr : 0 ≤ r := Real.rpow_nonneg hy0 _
  have hrgeom : r ≤ y - 2 := (hgeom y hy₂).1
  have hlu : y - r ≤ y + r := by linarith
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hsqrt1 : 1 ≤ Real.sqrt y := by simpa using Real.sqrt_le_sqrt hy1
  have hLbound : L ≤ Real.sqrt K * Real.sqrt y := by
    apply (sq_le_sq₀ hL (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt hK.le, Real.sq_sqrt hy0, L, y] using hn
  have htwo : 2 ≤ D * Real.sqrt y := by nlinarith only [hD2, hsqrt1]
  have hXc : c ≤ X :=
    (min_le_right _ _).trans (by dsimp [X]; linarith)
  have hXabs : |X| ≤ D * Real.sqrt y := by
    have hsabs : |s.re| ≤ B := abs_le_strip a b s.re ha hb
    have hsum := abs_add_le s.re δ
    rw [abs_of_nonneg hδ] at hsum
    have hδb : δ ≤ |t| / 2 * (Real.sqrt K * Real.sqrt y) :=
      mul_le_mul_of_nonneg_left hLbound (by positivity)
    have hBb := mul_le_mul_of_nonneg_left hsqrt1 hB
    dsimp [X, D]
    nlinarith only [hsum, hsabs, hδb, hBb, Real.sqrt_nonneg y]
  have hwidth : |X - 2| ≤ W * Real.exp y := by
    have hh := abs_add_le X (-2 : ℝ)
    norm_num at hh
    change |X - 2| ≤ |X| + 2 at hh
    have hroot : Real.sqrt y ≤ y := by
      nlinarith only [Real.sq_sqrt hy0,
        mul_nonneg (Real.sqrt_nonneg y) (sub_nonneg.mpr hsqrt1)]
    have hexp : Real.sqrt y ≤ Real.exp y := by
      linarith only [hroot, Real.add_one_le_exp y]
    calc
      _ ≤ W * Real.sqrt y := by
        dsimp [W]
        nlinarith only [hh, hXabs, hsqrt1]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp hW
  have htail (v : ℝ) (hv : r ≤ |v - y|) :
      ‖f v‖ ≤ C * Real.exp (-((v - y) ^ 2) / (4 * |t|)) :=
    hoff s ha hb hy₁ n hn 2 v (min_le_left _ _) (by simpa using htwo) (Or.inr rfl) hv
  have hfi : Integrable f :=
    integrable_of_gaussian_tail f (integrand_continuous_on_line t s n)
      |t| C y r hT htail
  have hvert :
      ‖(∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), f v‖ ≤
        C * Real.sqrt (Real.pi * (8 * |t|)) * Real.exp (-r ^ 2 / (8 * |t|)) := by
    have h := gaussian_tail_integral_bound f hfi |t| C y r hT hC.le hr htail
    rwa [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlu] at h
  have hhor (v : ℝ) (hv : 2 ≤ v) (hvr : |v - y| = r) :
      ‖∫ x in 2..X, integrand t s n (linePoint x v)‖ ≤
        C * W * Real.exp (y - r ^ 2 / (4 * |t|)) := by
    have hbnd (x : ℝ) (hx : x ∈ uIoc 2 X) :
        ‖integrand t s n (linePoint x v)‖ ≤ C * Real.exp (-r ^ 2 / (4 * |t|)) := by
      have hx' : x ∈ uIcc 2 X := uIoc_subset_uIcc hx
      have hxc : c ≤ x := (le_min (min_le_left _ _) hXc).trans hx'.1
      have hxabs : |x| ≤ D * Real.sqrt y := by
        apply abs_le.mpr
        exact ⟨(le_min (by linarith only [htwo]) (abs_le.mp hXabs).1).trans hx'.1,
          hx'.2.trans (max_le htwo (abs_le.mp hXabs).2)⟩
      have h := hoff s ha hb hy₁ n hn x v hxc hxabs
        (Or.inl (hv.trans (le_abs_self v))) hvr.ge
      have hsq : (v - s.im) ^ 2 = r ^ 2 := by
        change (v - y) ^ 2 = r ^ 2
        rw [← sq_abs (v - y), hvr]
      simpa only [hsq] using h
    calc
      _ ≤ (C * Real.exp (-r ^ 2 / (4 * |t|))) * |X - 2| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      _ ≤ (C * Real.exp (-r ^ 2 / (4 * |t|))) * (W * Real.exp y) := by gcongr
      _ = _ := by
        rw [show y - r ^ 2 / (4 * |t|) = -r ^ 2 / (4 * |t|) + y by ring,
          Real.exp_add]
        ring
  have hbot := hhor (y - r) (by linarith)
    (by rw [show y - r - y = -r by ring, abs_neg, abs_of_nonneg hr])
  have htop := hhor (y + r) (by linarith)
    (by rw [show y + r - y = r by ring, abs_of_nonneg hr])
  have hrect :
      ‖(∫ v in (y - r)..(y + r), f v) - ∫ v in (y - r)..(y + r), g v‖ ≤
        2 * C * W * Real.exp (y - r ^ 2 / (4 * |t|)) := by
    have h := (rectangle_bound t s n 2 X (y - r) (y + r) (by linarith) hlu).trans
      (add_le_add hbot htop)
    dsimp [f, g]
    linarith
  have he : Real.exp (y - r ^ 2 / (4 * |t|)) ≤
      Real.exp (y - r ^ 2 / (8 * |t|)) := by
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ r ^ 2 / (8 * |t|) := by positivity
    have heq : r ^ 2 / (4 * |t|) = 2 * (r ^ 2 / (8 * |t|)) := by ring
    rw [heq]
    linarith only [h0]
  have he₀ : Real.exp (-r ^ 2 / (8 * |t|)) ≤
      Real.exp (y - r ^ 2 / (8 * |t|)) := by
    apply Real.exp_le_exp.mpr
    simp only [neg_div]
    linarith only [hy0]
  have hfull :
      ‖(∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), g v‖ ≤
        (C * Real.sqrt (Real.pi * (8 * |t|)) + 2 * C * W) *
          Real.exp (y - r ^ 2 / (8 * |t|)) := by
    calc
      _ = ‖((∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), f v) +
          ((∫ v in (y - r)..(y + r), f v) - ∫ v in (y - r)..(y + r), g v)‖ := by
        congr 1
        ring
      _ ≤ ‖(∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), f v‖ +
          ‖(∫ v in (y - r)..(y + r), f v) - ∫ v in (y - r)..(y + r), g v‖ :=
        norm_add_le _ _
      _ ≤ C * Real.sqrt (Real.pi * (8 * |t|)) * Real.exp (-r ^ 2 / (8 * |t|)) +
          2 * C * W * Real.exp (y - r ^ 2 / (4 * |t|)) := add_le_add hvert hrect
      _ ≤ C * Real.sqrt (Real.pi * (8 * |t|)) * Real.exp (y - r ^ 2 / (8 * |t|)) +
          2 * C * W * Real.exp (y - r ^ 2 / (8 * |t|)) := by gcongr
      _ = _ := by ring
  rw [central_segment_identity t s n hy0]
  change ‖(1 / (p : ℂ)) * (∫ v : ℝ, f v) -
    (1 / (p : ℂ)) * (∫ v in (y - r)..(y + r), g v)‖ ≤ _
  rw [← mul_sub, norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_of_nonneg hp.le]
  calc
    _ ≤ (1 / p) * ((C * Real.sqrt (Real.pi * (8 * |t|)) + 2 * C * W) *
        Real.exp (y - r ^ 2 / (8 * |t|))) := mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = _ := by
      have hrsq : r ^ 2 = s.im ^ (4 / 3 : ℝ) := window_sq _ hy0
      rw [hrsq]
      dsimp [A]
      ring

private theorem uniform_contour_remainder (t : ℝ) (ht : t < 0)
    (a b K : ℝ) (hK : 0 < K) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → Y ≤ s.im → ∀ n : ℕ,
        Real.log ((n : ℝ) + 1) ^ 2 ≤ K * s.im →
        ‖(mellinTerm t s n - centralMellinTerm t s n) / gammaT t s‖ ≤
          C * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (40 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨A, Y₁, hA, hY₁, hrem⟩ := uniform_unnormalized_remainder t ht a b K hK
  obtain ⟨D, hD, hnorm⟩ := gammaT_inv_bound t ht a b
  obtain ⟨Y₂, hY₂, hheight⟩ := height_domination (10 * |t| * (Real.pi + 1))
  refine ⟨A * D, max Y₁ Y₂, mul_pos hA hD,
    (show (1 : ℝ) ≤ 4 by norm_num).trans (hY₁.trans (le_max_left _ _)), ?_⟩
  intro s ha hb hy n hn
  have hy₁ : Y₁ ≤ s.im := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ s.im := (le_max_right _ _).trans hy
  have hy4 : 4 ≤ s.im := hY₁.trans hy₁
  have hq : (Real.pi + 1) * s.im ≤ s.im ^ (4 / 3 : ℝ) / (10 * |t|) := by
    apply (le_div_iff₀ (show 0 < 10 * |t| by positivity)).mpr
    calc
      ((Real.pi + 1) * s.im) * (10 * |t|) =
          (10 * |t| * (Real.pi + 1)) * s.im := by ring
      _ ≤ s.im ^ (4 / 3 : ℝ) := (hheight s.im hy₂).2
  have he : s.im - s.im ^ (4 / 3 : ℝ) / (8 * |t|) + Real.pi * s.im ≤
      -(s.im ^ (4 / 3 : ℝ)) / (40 * |t|) := by
    calc
      _ ≤ -(s.im ^ (4 / 3 : ℝ)) / (8 * |t|) +
          s.im ^ (4 / 3 : ℝ) / (10 * |t|) := by
        simp only [neg_div]
        nlinarith only [hq]
      _ = _ := by ring
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (A * Real.exp (s.im - s.im ^ (4 / 3 : ℝ) / (8 * |t|))) *
        (D * Real.exp (Real.pi * s.im)) := by
      apply mul_le_mul (hrem s ha hb hy₁ n hn) (hnorm s ha hb (by linarith))
        (norm_nonneg _) (by positivity)
    _ = (A * D) * Real.exp
        (s.im - s.im ^ (4 / 3 : ℝ) / (8 * |t|) + Real.pi * s.im) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (mul_pos hA hD).le

private noncomputable def gaussianPolynomial (T u : ℝ) : ℝ :=
  (1 + |u|) ^ 3 * gaussian (2 * T) u

private theorem gaussianPolynomial_nonneg (T u : ℝ) :
    0 ≤ gaussianPolynomial T u := by
  unfold gaussianPolynomial gaussian
  positivity

private theorem gaussianPolynomial_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (gaussianPolynomial T) := by
  have h0 := gaussian_integrable (2 * T) (by positivity)
  have h3 : Integrable (fun u : ℝ => |u| ^ 3 * gaussian (2 * T) u) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq
      (inv_pos.mpr (show 0 < 2 * T by positivity)) (s := 3) (by norm_num)).norm
    simpa only [gaussian, Real.rpow_natCast, Real.rpow_ofNat, norm_mul, Real.norm_eq_abs,
      abs_pow, Real.abs_exp, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using h
  apply ((h0.add h3).const_mul 4).mono' (by unfold gaussianPolynomial gaussian; fun_prop)
  filter_upwards with u
  rw [Real.norm_of_nonneg (gaussianPolynomial_nonneg T u)]
  have hb : (1 + |u|) ^ 3 ≤ 4 * (1 + |u| ^ 3) := by
    convert! add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (abs_nonneg u) 3 using 1
    norm_num
  calc
    _ ≤ (4 * (1 + |u| ^ 3)) * gaussian (2 * T) u :=
      mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
    _ = _ := by simp only [Pi.add_apply]; ring

private theorem uniform_weighted_error (T C d Q y u : ℝ) (hT : 0 < T)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hy : 1 ≤ y) (hyT : 2 * T ≤ y)
    (hdQ : d ^ 2 / y ≤ Q) (e : ℂ)
    (he : ‖e‖ ≤ C / y * (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 *
      Real.exp (‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y)) :
    ‖(gaussian T u : ℂ) * e‖ ≤
      (C * Real.exp Q) * (1 + d) ^ 3 * gaussianPolynomial T u := by
  have hyp : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hw : ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ≤ d + |u| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
      mul_one, abs_of_nonneg hd] using norm_add_le (d : ℂ) ((u : ℂ) * Complex.I)
  have hw2 : ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 = d ^ 2 + u ^ 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hexp : -u ^ 2 / T + ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y ≤
      Q - u ^ 2 / (2 * T) := by
    rw [hw2, add_div]
    have hu := div_le_div_of_nonneg_left (sq_nonneg u) (show 0 < 2 * T by positivity) hyT
    have hsplit : -u ^ 2 / T = -2 * (u ^ 2 / (2 * T)) := by field_simp
    rw [hsplit]
    linarith only [hdQ, hu]
  have hpoly : (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 ≤
      ((1 + d) * (1 + |u|)) ^ 3 := by
    gcongr 1
    nlinarith only [hw, mul_nonneg hd (abs_nonneg u)]
  rw [norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (show 0 ≤ gaussian T u from Real.exp_nonneg _)]
  calc
    _ ≤ gaussian T u * (C / y *
        (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 *
        Real.exp (‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y)) :=
      mul_le_mul_of_nonneg_left he (Real.exp_nonneg _)
    _ = C / y * (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 *
        Real.exp (-u ^ 2 / T + ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y) := by
      rw [Real.exp_add]
      unfold gaussian
      ring
    _ ≤ C * ((1 + d) * (1 + |u|)) ^ 3 * Real.exp (Q - u ^ 2 / (2 * T)) := by
      apply mul_le_mul _ (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)
      exact mul_le_mul (div_le_self hC hy) hpoly (by positivity) hC
    _ = _ := by
      rw [show Q - u ^ 2 / (2 * T) = Q + (-u ^ 2 / (2 * T)) by ring, Real.exp_add]
      unfold gaussianPolynomial gaussian
      ring

private theorem uniform_weighted_factor (T C d Q y u : ℝ) (hT : 0 < T)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hy : 1 ≤ y) (hyT : 2 * T ≤ y)
    (hdQ : d ^ 2 / y ≤ Q) (e : ℂ)
    (he : ‖e‖ ≤ C / y * (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 *
      Real.exp (‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y)) :
    ‖(gaussian T u : ℂ) * (1 + e)‖ ≤
      (1 + C * Real.exp Q) * (1 + d) ^ 3 * gaussianPolynomial T u := by
  have hg : gaussian T u ≤ gaussian (2 * T) u := by
    unfold gaussian
    apply Real.exp_le_exp.mpr
    have hh : -u ^ 2 / T = -2 * (u ^ 2 / (2 * T)) := by field_simp
    rw [hh]
    simp only [neg_div]
    linarith only [show 0 ≤ u ^ 2 / (2 * T) by positivity]
  have hp₁ : (1 : ℝ) ≤ (1 + d) ^ 3 := by
    calc
      (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ _ := by gcongr; linarith only [hd]
  have hp₂ : (1 : ℝ) ≤ (1 + |u|) ^ 3 := by
    calc
      (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ _ := by gcongr; linarith only [abs_nonneg u]
  have hbase : gaussian T u ≤ (1 + d) ^ 3 * gaussianPolynomial T u := by
    calc
      _ ≤ gaussian (2 * T) u := hg
      _ = 1 * (1 * gaussian (2 * T) u) := by ring
      _ ≤ _ := by
        unfold gaussianPolynomial
        gcongr <;> (unfold gaussian; positivity)
  calc
    _ = ‖(gaussian T u : ℂ) + (gaussian T u : ℂ) * e‖ := by congr 1; ring
    _ ≤ ‖(gaussian T u : ℂ)‖ + ‖(gaussian T u : ℂ) * e‖ := norm_add_le _ _
    _ = gaussian T u + ‖(gaussian T u : ℂ) * e‖ := by
      rw [Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ gaussian T u from Real.exp_nonneg _)]
    _ ≤ (1 + d) ^ 3 * gaussianPolynomial T u +
        (C * Real.exp Q) * (1 + d) ^ 3 * gaussianPolynomial T u :=
      add_le_add hbase (uniform_weighted_error T C d Q y u hT hC hd hy hyT hdQ e he)
    _ = _ := by ring

private theorem uniform_central_bound (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) (K : ℝ) (_hK : 0 < K) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → Y ≤ s.im → ∀ n : ℕ,
        Real.log ((n : ℝ) + 1) ^ 2 ≤ K * s.im →
        ‖centralMellinTerm t s n / gammaT t s‖ ≤
          C * Real.exp (t / 8 * Real.log ((n : ℝ) + 1) ^ 2) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨C, Y₁, hC, hY₁, hlin⟩ := gammaFactor_local_linearization a b hab
  let Q := (|t| / 2) ^ 2 * K
  obtain ⟨Y₂, hY₂, hgeom⟩ := height_domination Q
  let p := Real.sqrt (Real.pi * |t|)
  have hp : 0 < p := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hT)
  let A := ∫ u : ℝ, gaussianPolynomial |t| u
  have hA : 0 ≤ A := integral_nonneg (gaussianPolynomial_nonneg |t|)
  have hAi := gaussianPolynomial_integrable |t| hT
  let H := 1 + C * Real.exp Q
  have hH : 0 < H := by dsimp [H]; positivity
  let W := H / p * (1 + A)
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨W * Real.exp (2 * (|a| + 3 * |t| / 2) ^ 2 / |t|),
    max Y₁ (max Y₂ (2 * |t|)), mul_pos hW (Real.exp_pos _),
    hY₁.trans (le_max_left _ _), ?_⟩
  intro s ha hb hy n hn
  have hy₁ : Y₁ ≤ s.im := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ s.im := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hyT : 2 * |t| ≤ s.im := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hy1 : 1 ≤ s.im := hY₁.trans hy₁
  have hyp : 0 < s.im := lt_of_lt_of_le zero_lt_one hy1
  let L := Real.log ((n : ℝ) + 1)
  let d := |t| / 2 * L
  let r := mellinWindow s.im
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hr : 0 ≤ r := Real.rpow_nonneg hyp.le _
  have hrd : r ≤ s.im - 2 := (hgeom s.im hy₂).1
  have hd2 : d ^ 2 ≤ Q * s.im := by
    calc
      _ = (|t| / 2) ^ 2 * L ^ 2 := by dsimp [d]; ring
      _ ≤ (|t| / 2) ^ 2 * (K * s.im) :=
        mul_le_mul_of_nonneg_left hn (sq_nonneg _)
      _ = _ := by dsimp [Q]; ring
  have hdr : d ≤ r := by
    apply (sq_le_sq₀ hd hr).mp
    calc
      d ^ 2 ≤ Q * s.im := hd2
      _ ≤ s.im ^ (4 / 3 : ℝ) := (hgeom s.im hy₂).2
      _ = r ^ 2 := (window_sq s.im hyp.le).symm
  have hdQ : d ^ 2 / s.im ≤ Q := (div_le_iff₀ hyp).mpr hd2
  have hpoint (u : ℝ) (hu : u ∈ Icc (-r) r) :
      ‖integrand t s n (mellinSaddlePoint t s n u) / gammaT t s‖ ≤
        (‖zetaTerm t s n‖ * H * (1 + d) ^ 3) * gaussianPolynomial |t| u := by
    have hzi : 1 ≤ (mellinSaddlePoint t s n u).im := by
      simp only [mellinSaddlePoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
      linarith only [hrd, hu.1]
    have hz : ‖mellinSaddlePoint t s n u - s‖ ≤ 2 * r := by
      rw [saddle_displacement]
      calc
        _ ≤ d + |u| := by
          simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            mul_one, abs_of_nonneg hd] using norm_add_le (d : ℂ) ((u : ℂ) * Complex.I)
        _ ≤ r + r := add_le_add hdr (abs_le.mpr hu)
        _ = _ := by ring
    have he := hlin s (mellinSaddlePoint t s n u) ha hb hy₁ hzi hz
    rw [saddle_displacement] at he
    have hw := uniform_weighted_factor |t| C d Q s.im u hT hC.le hd hy1 hyT hdQ _ he
    change ‖(gammaFactor _ * _) / gammaT t s‖ ≤ _
    rw [saddle_gaussian_identity t ht s hyp n u, mul_assoc, norm_mul]
    calc
      _ ≤ ‖zetaTerm t s n‖ *
          (H * (1 + d) ^ 3 * gaussianPolynomial |t| u) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = _ := by ring
  have hI :
      ‖∫ u in Icc (-r) r,
        integrand t s n (mellinSaddlePoint t s n u) / gammaT t s‖ ≤
        (‖zetaTerm t s n‖ * H * (1 + d) ^ 3) * A := by
    calc
      _ ≤ ∫ u in Icc (-r) r,
          (‖zetaTerm t s n‖ * H * (1 + d) ^ 3) * gaussianPolynomial |t| u := by
        apply norm_integral_le_of_norm_le (hAi.const_mul _).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact hpoint u hu
      _ ≤ ∫ u : ℝ, (‖zetaTerm t s n‖ * H * (1 + d) ^ 3) *
          gaussianPolynomial |t| u := by
        apply setIntegral_le_integral (hAi.const_mul _)
        exact ae_of_all _ fun u => mul_nonneg (by positivity)
          (gaussianPolynomial_nonneg |t| u)
      _ = _ := integral_const_mul _ _
  have hcentral : ‖centralMellinTerm t s n / gammaT t s‖ ≤
      W * (‖zetaTerm t s n‖ * (1 + d) ^ 3) := by
    unfold centralMellinTerm
    rw [mul_div_assoc, ← integral_div, norm_mul, norm_div, norm_one,
      Complex.norm_real, Real.norm_of_nonneg hp.le]
    change (1 / p) * ‖∫ u in Icc (-r) r,
      integrand t s n (mellinSaddlePoint t s n u) / gammaT t s‖ ≤ _
    calc
      _ ≤ (1 / p) * ((‖zetaTerm t s n‖ * H * (1 + d) ^ 3) * A) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
      _ ≤ (1 / p) * ((‖zetaTerm t s n‖ * H * (1 + d) ^ 3) * (1 + A)) := by
        gcongr
        linarith
      _ = _ := by dsimp [W]; ring
  calc
    _ ≤ W * (‖zetaTerm t s n‖ * (1 + d) ^ 3) := hcentral
    _ ≤ W * (Real.exp (2 * (|a| + 3 * |t| / 2) ^ 2 / |t|) *
        Real.exp (t / 8 * L ^ 2)) :=
      mul_le_mul_of_nonneg_left (zeta_polynomial_bound t ht a s ha n) hW.le
    _ = _ := by ring

/-- Dobner's two contour estimates, with a fixed-time cutoff
log(n+1)^2 = K * Im(s), give a summable Gaussian majorant. -/
theorem solution (t : ℝ) (ht : t < 0) (a b : ℝ) (hab : a < b) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im → ∀ n : ℕ,
        ‖DeBruijnNewman.Dobner.normalizedMellinTerm t s n‖ ≤
          C * Real.exp (t / 40 * Real.log ((n : ℝ) + 1) ^ 2) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨K, B, YB, hK, hB, hYB, hlarge⟩ := large_index_bound t ht a b
  obtain ⟨C, YC, hC, hYC, hcentral⟩ := uniform_central_bound t ht a b hab K hK
  obtain ⟨D, YD, hD, hYD, hremainder⟩ := uniform_contour_remainder t ht a b K hK
  obtain ⟨YG, hYG, hgeometry⟩ := height_domination (|t| ^ 2 * K)
  refine ⟨B + C + D, max YB (max YC (max YD YG)), (by positivity),
    hYB.trans (le_max_left _ _), ?_⟩
  intro s ha hb hy n
  have hyB : YB ≤ s.im := (le_max_left _ _).trans hy
  have hyC : YC ≤ s.im := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hyD : YD ≤ s.im :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hyG : YG ≤ s.im :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  let L := Real.log ((n : ℝ) + 1)
  by_cases hn : L ^ 2 ≤ K * s.im
  · have hcentral' := hcentral s ha hb hyC n hn
    have hremainder' := hremainder s ha hb hyD n hn
    have hpow : |t| ^ 2 * L ^ 2 ≤ s.im ^ (4 / 3 : ℝ) := by
      calc
        _ ≤ |t| ^ 2 * (K * s.im) := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
        _ = (|t| ^ 2 * K) * s.im := by ring
        _ ≤ _ := (hgeometry s.im hyG).2
    have hq : |t| / 40 * L ^ 2 ≤ s.im ^ (4 / 3 : ℝ) / (40 * |t|) := by
      apply (le_div_iff₀ (by positivity : 0 < 40 * |t|)).mpr
      nlinarith only [hpow]
    have heR : Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (40 * |t|)) ≤
        Real.exp (t / 40 * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div]
      rw [abs_of_neg ht] at hq ⊢
      linarith only [hq]
    have heC : Real.exp (t / 8 * L ^ 2) ≤ Real.exp (t / 40 * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg ht.le (sq_nonneg L)]
    calc
      _ = ‖centralMellinTerm t s n / gammaT t s +
          (mellinTerm t s n - centralMellinTerm t s n) / gammaT t s‖ := by
        unfold normalizedMellinTerm
        congr 1
        ring
      _ ≤ ‖centralMellinTerm t s n / gammaT t s‖ +
          ‖(mellinTerm t s n - centralMellinTerm t s n) / gammaT t s‖ := norm_add_le _ _
      _ ≤ C * Real.exp (t / 8 * L ^ 2) +
          D * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (40 * |t|)) :=
        add_le_add hcentral' hremainder'
      _ ≤ C * Real.exp (t / 40 * L ^ 2) + D * Real.exp (t / 40 * L ^ 2) := by gcongr
      _ = (C + D) * Real.exp (t / 40 * L ^ 2) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        linarith only [hB]
  · apply (hlarge s ha hb hyB n (lt_of_not_ge hn)).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    linarith only [hC, hD]
