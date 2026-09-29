-- Prove2me | solution 1 for DeBruijnNewman.Dobner.mellin_contour_remainder
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-25T00:29:47.02844+00:00
-- url     : https://prove2.me/submissions/1d45ea60-2fed-4488-bc2a-aa216140c033

import Definitions.Def_DeBruijnNewman_Dobner_Saddle

/- Dobner's finite contour shift for a fixed coefficient and strip.
The coarse gamma estimates below follow from Euler's integral, recurrence,
and reflection. The discarded contour pieces have Gaussian decay, which
also absorbs the exponential cost of division by gammaT. -/

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

/-- The pointwise estimate used on both horizontal segments and both
tails on Re(z)=2. It is uniform on the fixed real-part intervals. -/
private theorem off_saddle_bound (t : ℝ) (ht : t < 0) (a b c d : ℝ) (n : ℕ) :
    ∃ C Y : ℝ, 0 < C ∧ 4 ≤ Y ∧ ∀ s : ℂ, ∀ x v : ℝ,
      a ≤ s.re → s.re ≤ b → c ≤ x → x ≤ d → Y ≤ s.im →
      (2 ≤ |v| ∨ x = 2) → mellinWindow s.im ≤ |v - s.im| →
        ‖integrand t s n (linePoint x v)‖ ≤
          C * Real.exp (-((v - s.im) ^ 2) / (4 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨M, hM, hgamma⟩ := gamma_factor_strip_bound c d
  obtain ⟨D, hD, hJ⟩ := shear_bounds t a b c d
  let K := D ^ 2 / |t| + 2
  obtain ⟨Y₀, hY₀, hheight⟩ := height_domination (8 * |t| * K)
  let C := M * (2 + 16 * |t|) *
    Real.exp ((|t| * Real.pi / 4) ^ 2 / |t| - c * Real.log ((n : ℝ) + 1))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, max Y₀ (2 * Real.pi), hC, hY₀.trans (le_max_left _ _), ?_⟩
  intro s x v ha hb hc hd hy hv hu
  have hy₀ : Y₀ ≤ s.im := (le_max_left _ _).trans hy
  have hy4 : 4 ≤ s.im := hY₀.trans hy₀
  have hy0 : 0 ≤ s.im := by linarith
  have hJ' := hJ s x ha hb hc hd (by linarith) ((le_max_right _ _).trans hy)
  have hg : ‖gammaFactor (linePoint x v)‖ ≤ M * (1 + |v|) ^ 2 := by
    simpa [linePoint] using hgamma (linePoint x v)
      (by simpa [linePoint] using hc) (by simpa [linePoint] using hd)
      (by simpa [linePoint] using hv)
  have hmain := integrand_gaussian_bound t ht s n c x v M D hM.le hD.le hy0 hc hg
    hJ'.1 hJ'.2
  have hpow : s.im ^ (4 / 3 : ℝ) ≤ (v - s.im) ^ 2 := by
    rw [← window_sq _ hy0]
    have h := (sq_le_sq₀ (Real.rpow_nonneg hy0 (2 / 3 : ℝ)) (abs_nonneg _)).mpr hu
    simpa only [sq_abs, mellinWindow] using! h
  have hKy : K * s.im ≤ (v - s.im) ^ 2 / (8 * |t|) := by
    apply (le_div_iff₀ (show 0 < 8 * |t| by positivity)).mpr
    have h := (hheight s.im hy₀).2.trans hpow
    nlinarith
  apply hmain.trans
  change C * Real.exp _ ≤ C * Real.exp _
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  change K * s.im - 3 * (v - s.im) ^ 2 / (8 * |t|) ≤ _
  have heq : 3 * (v - s.im) ^ 2 / (8 * |t|) =
      (v - s.im) ^ 2 / (8 * |t|) + (v - s.im) ^ 2 / (4 * |t|) := by ring
  rw [heq]
  simp only [neg_div]
  linarith

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

private theorem unnormalized_remainder_bound (t : ℝ) (ht : t < 0)
    (a b : ℝ) (n : ℕ) :
    ∃ C Y : ℝ, 0 < C ∧ 4 ≤ Y ∧ ∀ s : ℂ,
      a ≤ s.re → s.re ≤ b → Y ≤ s.im →
        ‖mellinTerm t s n - centralMellinTerm t s n‖ ≤
          C * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (8 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  let δ := |t| / 2 * Real.log ((n : ℝ) + 1)
  let c := min 2 (a + δ)
  let d := max 2 (b + δ)
  let W := |a + δ| + |b + δ| + 2
  have hW : 0 ≤ W := by dsimp [W]; positivity
  obtain ⟨C, Y₁, hC, hY₁, hoff⟩ := off_saddle_bound t ht a b c d n
  obtain ⟨Y₂, hY₂, hgeom⟩ := height_domination 0
  let p := Real.sqrt (Real.pi * |t|)
  have hp : 0 < p := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hT)
  let A := (C * Real.sqrt (Real.pi * (8 * |t|)) + 2 * C * W) / p
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, max Y₁ Y₂, hA, hY₁.trans (le_max_left _ _), ?_⟩
  intro s ha hb hy
  let y := s.im
  let r := mellinWindow y
  let X := s.re + δ
  let f : ℝ → ℂ := fun v => integrand t s n (linePoint 2 v)
  let g : ℝ → ℂ := fun v => integrand t s n (linePoint X v)
  have hy₁ : Y₁ ≤ y := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ y := (le_max_right _ _).trans hy
  have hy4 : 4 ≤ y := hY₁.trans hy₁
  have hy0 : 0 ≤ y := by linarith
  have hr : 0 ≤ r := Real.rpow_nonneg hy0 _
  have hrgeom : r ≤ y - 2 := (hgeom y hy₂).1
  have hlu : y - r ≤ y + r := by linarith
  have hXc : c ≤ X := (min_le_right _ _).trans (by dsimp [X]; linarith)
  have hXd : X ≤ d := (show X ≤ b + δ by dsimp [X]; linarith).trans (le_max_right _ _)
  have hwidth : |X - 2| ≤ W := by
    have hx := abs_le_strip (a + δ) (b + δ) X
      (by dsimp [X]; linarith) (by dsimp [X]; linarith)
    apply abs_le.mpr
    dsimp [W]
    constructor <;> linarith [(abs_le.mp hx).1, (abs_le.mp hx).2]
  have htail (v : ℝ) (hv : r ≤ |v - y|) :
      ‖f v‖ ≤ C * Real.exp (-((v - y) ^ 2) / (4 * |t|)) :=
    hoff s 2 v ha hb (min_le_left _ _) (le_max_left _ _) hy₁ (Or.inr rfl) hv
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
        C * W * Real.exp (-r ^ 2 / (4 * |t|)) := by
    have hbnd (x : ℝ) (hx : x ∈ uIoc 2 X) :
        ‖integrand t s n (linePoint x v)‖ ≤ C * Real.exp (-r ^ 2 / (4 * |t|)) := by
      have hx' : x ∈ uIcc 2 X := uIoc_subset_uIcc hx
      have hxc : c ≤ x := (le_min (min_le_left _ _) hXc).trans hx'.1
      have hxd : x ≤ d := hx'.2.trans (max_le (le_max_left _ _) hXd)
      have h := hoff s x v ha hb hxc hxd hy₁
        (Or.inl (hv.trans (le_abs_self v))) hvr.ge
      have hsq : (v - s.im) ^ 2 = r ^ 2 := by
        change (v - y) ^ 2 = r ^ 2
        rw [← sq_abs (v - y), hvr]
      simpa only [hsq] using h
    calc
      _ ≤ (C * Real.exp (-r ^ 2 / (4 * |t|))) * |X - 2| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbnd
      _ ≤ (C * Real.exp (-r ^ 2 / (4 * |t|))) * W := by gcongr
      _ = _ := by ring
  have hbot := hhor (y - r) (by linarith)
    (by rw [show y - r - y = -r by ring, abs_neg, abs_of_nonneg hr])
  have htop := hhor (y + r) (by linarith)
    (by rw [show y + r - y = r by ring, abs_of_nonneg hr])
  have hrect :
      ‖(∫ v in (y - r)..(y + r), f v) - ∫ v in (y - r)..(y + r), g v‖ ≤
        2 * C * W * Real.exp (-r ^ 2 / (4 * |t|)) := by
    have h := (rectangle_bound t s n 2 X (y - r) (y + r) (by linarith) hlu).trans
      (add_le_add hbot htop)
    dsimp [f, g]
    linarith
  have he : Real.exp (-r ^ 2 / (4 * |t|)) ≤ Real.exp (-r ^ 2 / (8 * |t|)) := by
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ r ^ 2 / (8 * |t|) := by positivity
    have heq : -r ^ 2 / (4 * |t|) = -2 * (r ^ 2 / (8 * |t|)) := by ring
    rw [heq]
    simp only [neg_div]
    linarith
  have hfull :
      ‖(∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), g v‖ ≤
        (C * Real.sqrt (Real.pi * (8 * |t|)) + 2 * C * W) *
          Real.exp (-r ^ 2 / (8 * |t|)) := by
    calc
      _ = ‖((∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), f v) +
          ((∫ v in (y - r)..(y + r), f v) - ∫ v in (y - r)..(y + r), g v)‖ := by
        congr 1
        ring
      _ ≤ ‖(∫ v : ℝ, f v) - ∫ v in (y - r)..(y + r), f v‖ +
          ‖(∫ v in (y - r)..(y + r), f v) - ∫ v in (y - r)..(y + r), g v‖ :=
        norm_add_le _ _
      _ ≤ C * Real.sqrt (Real.pi * (8 * |t|)) * Real.exp (-r ^ 2 / (8 * |t|)) +
          2 * C * W * Real.exp (-r ^ 2 / (4 * |t|)) := add_le_add hvert hrect
      _ ≤ C * Real.sqrt (Real.pi * (8 * |t|)) * Real.exp (-r ^ 2 / (8 * |t|)) +
          2 * C * W * Real.exp (-r ^ 2 / (8 * |t|)) := by gcongr
      _ = _ := by ring
  rw [central_segment_identity t s n hy0]
  change ‖(1 / (p : ℂ)) * (∫ v : ℝ, f v) -
    (1 / (p : ℂ)) * (∫ v in (y - r)..(y + r), g v)‖ ≤ _
  rw [← mul_sub, norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_of_nonneg hp.le]
  calc
    _ ≤ (1 / p) * ((C * Real.sqrt (Real.pi * (8 * |t|)) + 2 * C * W) *
        Real.exp (-r ^ 2 / (8 * |t|))) := mul_le_mul_of_nonneg_left hfull (by positivity)
    _ = _ := by
      have hrsq : r ^ 2 = s.im ^ (4 / 3 : ℝ) := window_sq _ hy0
      rw [hrsq]
      dsimp [A]
      ring

theorem solution (t : ℝ) (ht : t < 0) (a b : ℝ) (_hab : a < b) (n : ℕ) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
        ‖(DeBruijnNewman.Dobner.mellinTerm t s n -
            DeBruijnNewman.Dobner.centralMellinTerm t s n) /
              DeBruijnNewman.Dobner.gammaT t s‖ ≤
          C * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (40 * |t|)) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨A, Y₁, hA, hY₁, hrem⟩ := unnormalized_remainder_bound t ht a b n
  obtain ⟨D, hD, hnorm⟩ := gammaT_inv_bound t ht a b
  obtain ⟨Y₂, hY₂, hheight⟩ := height_domination (10 * |t| * Real.pi)
  refine ⟨A * D, max Y₁ Y₂, mul_pos hA hD,
    (show (1 : ℝ) ≤ 4 by norm_num).trans (hY₁.trans (le_max_left _ _)), ?_⟩
  intro s ha hb hy
  have hy₁ : Y₁ ≤ s.im := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ s.im := (le_max_right _ _).trans hy
  have hy4 : 4 ≤ s.im := hY₁.trans hy₁
  have hq : Real.pi * s.im ≤ s.im ^ (4 / 3 : ℝ) / (10 * |t|) := by
    apply (le_div_iff₀ (show 0 < 10 * |t| by positivity)).mpr
    calc
      (Real.pi * s.im) * (10 * |t|) = (10 * |t| * Real.pi) * s.im := by ring
      _ ≤ s.im ^ (4 / 3 : ℝ) := (hheight s.im hy₂).2
  have he : -(s.im ^ (4 / 3 : ℝ)) / (8 * |t|) + Real.pi * s.im ≤
      -(s.im ^ (4 / 3 : ℝ)) / (40 * |t|) := by
    calc
      _ ≤ -(s.im ^ (4 / 3 : ℝ)) / (8 * |t|) +
          s.im ^ (4 / 3 : ℝ) / (10 * |t|) := by gcongr
      _ = _ := by ring
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (A * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (8 * |t|))) *
        (D * Real.exp (Real.pi * s.im)) := by
      apply mul_le_mul (hrem s ha hb hy₁) (hnorm s ha hb (by linarith))
        (norm_nonneg _) (by positivity)
    _ = (A * D) * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (8 * |t|) + Real.pi * s.im) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (mul_pos hA hD).le
