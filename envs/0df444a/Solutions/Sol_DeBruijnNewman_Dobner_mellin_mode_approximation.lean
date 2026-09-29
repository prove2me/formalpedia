-- Prove2me | solution 1 for DeBruijnNewman.Dobner.mellin_mode_approximation
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-25T00:04:38.351358+00:00
-- url     : https://prove2.me/submissions/1ba498cb-9e4c-4d86-983b-ff252e7839c0

import Theorems.Thm_DeBruijnNewman_Dobner_gammaFactor_local_linearization
import Theorems.Thm_DeBruijnNewman_Dobner_mellin_contour_remainder

/- A fixed-coefficient version of Dobner's steepest-descent argument.
The two imported estimates are the remaining analytic inputs. Gaussian
normalization, the integrated error bound, and uniform convergence are
proved below. -/

open MeasureTheory Set Filter DeBruijnNewman.Dobner
open scoped Topology

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

private noncomputable def gaussianMass (T y : ℝ) : ℂ :=
  (1 / (Real.sqrt (Real.pi * T) : ℂ)) *
    ∫ u in Icc (-mellinWindow y) (mellinWindow y), (gaussian T u : ℂ)

private theorem window_tendsto :
    Tendsto mellinWindow atTop atTop :=
  tendsto_rpow_atTop (by norm_num : 0 < (2 / 3 : ℝ))

private theorem gaussian_mass_tendsto (T : ℝ) (hT : 0 < T) :
    Tendsto (gaussianMass T) atTop (𝓝 1) := by
  let F : ℝ → ℝ → ℂ := fun y =>
    (Icc (-mellinWindow y) (mellinWindow y)).indicator (fun u => (gaussian T u : ℂ))
  have hm : ∀ᶠ y : ℝ in atTop, AEStronglyMeasurable (F y) := by
    filter_upwards with y
    exact ((show Measurable (fun u : ℝ => (gaussian T u : ℂ)) by
      unfold gaussian; fun_prop).indicator measurableSet_Icc).aestronglyMeasurable
  have hb : ∀ᶠ y : ℝ in atTop, ∀ᵐ u : ℝ, ‖F y u‖ ≤ gaussian T u := by
    filter_upwards with y
    filter_upwards with u
    dsimp [F]
    by_cases hu : u ∈ Icc (-mellinWindow y) (mellinWindow y)
    · simp only [indicator_of_mem hu, Complex.norm_real,
        Real.norm_of_nonneg (show 0 ≤ gaussian T u from Real.exp_nonneg _), le_refl]
    · simp only [indicator_of_notMem hu, norm_zero]
      exact Real.exp_nonneg _
  have hl : ∀ᵐ u : ℝ, Tendsto (fun y => F y u) atTop (𝓝 (gaussian T u : ℂ)) := by
    filter_upwards with u
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_atTop.mp window_tendsto) |u|] with y hy
    have hu : u ∈ Icc (-mellinWindow y) (mellinWindow y) := by
      constructor <;> linarith [le_abs_self u, neg_abs_le u]
    simp [F, hu]
  have h := tendsto_integral_filter_of_dominated_convergence (gaussian T)
    hm hb (gaussian_integrable T hT) hl
  simp only [F, integral_indicator measurableSet_Icc, integral_complex_ofReal,
    gaussian_integral] at h
  have hp : (Real.sqrt (Real.pi * T) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  unfold gaussianMass
  simpa only [integral_complex_ofReal, one_div, inv_mul_cancel₀ hp] using
    h.const_mul (1 / (Real.sqrt (Real.pi * T) : ℂ))

private theorem window_geometry (d : ℝ) :
    ∃ Y : ℝ, 2 ≤ Y ∧ ∀ y : ℝ, Y ≤ y →
      |d| ≤ mellinWindow y ∧ mellinWindow y ≤ y - 1 := by
  obtain ⟨Y₁, h₁⟩ := eventually_atTop.mp ((tendsto_atTop.mp window_tendsto) |d|)
  have hthird : Tendsto (fun y : ℝ => y ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  obtain ⟨Y₂, h₂⟩ := eventually_atTop.mp ((tendsto_atTop.mp hthird) 2)
  refine ⟨max 2 (max Y₁ Y₂), le_max_left _ _, ?_⟩
  intro y hy
  have hy2 : 2 ≤ y := (le_max_left _ _).trans hy
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy2
  refine ⟨h₁ y ((le_max_left _ _).trans ((le_max_right _ _).trans hy)), ?_⟩
  have hprod : mellinWindow y * y ^ (1 / 3 : ℝ) = y := by
    rw [mellinWindow, ← Real.rpow_add hypos]
    norm_num
  have hroot := h₂ y ((le_max_right _ _).trans ((le_max_right _ _).trans hy))
  have hr : 0 ≤ mellinWindow y := Real.rpow_nonneg hypos.le _
  have hbound := mul_le_mul_of_nonneg_left hroot hr
  rw [hprod] at hbound
  linarith

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

private noncomputable def errorMajorant (T C d u : ℝ) : ℝ :=
  C * Real.exp (d ^ 2) * (1 + |d| + |u|) ^ 3 * gaussian (2 * T) u

private theorem error_majorant_nonneg (T C d u : ℝ) (hC : 0 ≤ C) :
    0 ≤ errorMajorant T C d u := by
  unfold errorMajorant gaussian
  positivity

private theorem error_majorant_integrable (T C d : ℝ) (hT : 0 < T) (hC : 0 ≤ C) :
    Integrable (errorMajorant T C d) := by
  have h0 := gaussian_integrable (2 * T) (by positivity)
  have h3 : Integrable (fun u : ℝ => |u| ^ 3 * gaussian (2 * T) u) := by
    have h := (integrable_rpow_mul_exp_neg_mul_sq
      (inv_pos.mpr (show 0 < 2 * T by positivity)) (s := 3) (by norm_num)).norm
    simpa only [gaussian, Real.rpow_natCast, Real.rpow_ofNat, norm_mul, Real.norm_eq_abs, abs_pow,
      Real.abs_exp, div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using h
  have hi := ((h0.const_mul ((1 + |d|) ^ 3)).add h3).const_mul
    (4 * (C * Real.exp (d ^ 2)))
  apply hi.mono' (by unfold errorMajorant gaussian; fun_prop)
  filter_upwards with u
  rw [Real.norm_of_nonneg (error_majorant_nonneg T C d u hC)]
  have hb : (1 + |d| + |u|) ^ 3 ≤ 4 * ((1 + |d|) ^ 3 + |u| ^ 3) := by
    convert! add_pow_le (show 0 ≤ 1 + |d| by positivity) (abs_nonneg u) 3 using 1
    norm_num
  calc
    _ ≤ C * Real.exp (d ^ 2) * (4 * ((1 + |d|) ^ 3 + |u| ^ 3)) *
        gaussian (2 * T) u := by
      unfold errorMajorant
      gcongr
      exact Real.exp_nonneg _
    _ = _ := by simp only [Pi.add_apply]; ring

private theorem weighted_error_bound (T C d y u : ℝ) (hT : 0 < T)
    (hC : 0 ≤ C) (hy : 1 ≤ y) (hyT : 2 * T ≤ y) (e : ℂ)
    (he : ‖e‖ ≤ C / y * (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 *
      Real.exp (‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y)) :
    ‖(gaussian T u : ℂ) * e‖ ≤ errorMajorant T C d u / y := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hw : ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ≤ |d| + |u| := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one] using
      norm_add_le (d : ℂ) ((u : ℂ) * Complex.I)
  have hw2 : ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 = d ^ 2 + u ^ 2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hexp : -u ^ 2 / T + ‖(d : ℂ) + (u : ℂ) * Complex.I‖ ^ 2 / y ≤
      d ^ 2 - u ^ 2 / (2 * T) := by
    rw [hw2, add_div]
    have hd := div_le_self (sq_nonneg d) hy
    have hu := div_le_div_of_nonneg_left (sq_nonneg u) (show 0 < 2 * T by positivity) hyT
    have hsplit : -u ^ 2 / T = -2 * (u ^ 2 / (2 * T)) := by field_simp
    rw [hsplit]
    linarith
  have hexpeq : Real.exp (d ^ 2 - u ^ 2 / (2 * T)) =
      Real.exp (d ^ 2) * gaussian (2 * T) u := by
    rw [gaussian, ← Real.exp_add]
    congr 1
    ring
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
    _ ≤ C / y * (1 + |d| + |u|) ^ 3 * Real.exp (d ^ 2 - u ^ 2 / (2 * T)) := by
      have hpoly : (1 + ‖(d : ℂ) + (u : ℂ) * Complex.I‖) ^ 3 ≤
          (1 + |d| + |u|) ^ 3 := by
        gcongr 1
        linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (div_nonneg hC hypos.le))
        (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) (by positivity)
    _ = errorMajorant T C d u / y := by
      rw [hexpeq]
      unfold errorMajorant
      ring

private theorem saddle_height (t : ℝ) (s : ℂ) (n : ℕ) (u : ℝ)
    (hr : mellinWindow s.im ≤ s.im - 1)
    (hu : u ∈ Icc (-mellinWindow s.im) (mellinWindow s.im)) :
    1 ≤ (mellinSaddlePoint t s n u).im := by
  simp only [mellinSaddlePoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero]
  linarith [hu.1]

private theorem saddle_error_integrable (t : ℝ) (s : ℂ) (n : ℕ) (hs : 0 < s.im)
    (hr : mellinWindow s.im ≤ s.im - 1) :
    IntegrableOn (fun u : ℝ =>
      (gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u))
      (Icc (-mellinWindow s.im) (mellinWindow s.im)) := by
  apply ContinuousOn.integrableOn_Icc
  intro u hu
  have hz : 0 < (mellinSaddlePoint t s n u).im :=
    lt_of_lt_of_le zero_lt_one (saddle_height t s n u hr hu)
  have hzc : ContinuousAt (mellinSaddlePoint t s n) u := by
    unfold mellinSaddlePoint
    fun_prop
  have hgc := (gammaFactor_continuousAt _ hz).comp hzc
  have hec : ContinuousAt (fun v : ℝ =>
      gammaLinearError s (mellinSaddlePoint t s n v)) u := by
    unfold gammaLinearError
    apply ContinuousAt.sub _ continuousAt_const
    apply hgc.div (by fun_prop)
    exact mul_ne_zero (gammaFactor_nonzero s hs) (Complex.exp_ne_zero _)
  exact ((show ContinuousAt (fun v : ℝ => (gaussian |t| v : ℂ)) u by
    unfold gaussian; fun_prop).mul hec).continuousWithinAt

private theorem central_gaussian_identity (t : ℝ) (ht : t < 0) (s : ℂ)
    (hs : 0 < s.im) (n : ℕ) (hr : mellinWindow s.im ≤ s.im - 1) :
    centralMellinTerm t s n / gammaT t s =
      zetaTerm t s n * gaussianMass |t| s.im +
        (zetaTerm t s n / (Real.sqrt (Real.pi * |t|) : ℂ)) *
          ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
            (gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u) := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  have hiG : IntegrableOn (fun u : ℝ => (gaussian |t| u : ℂ))
      (Icc (-mellinWindow s.im) (mellinWindow s.im)) :=
    ((gaussian_integrable |t| hT).ofReal).integrableOn
  have hiE := saddle_error_integrable t s n hs hr
  have hint :
      (∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
        (gammaFactor (mellinSaddlePoint t s n u) *
          Complex.exp ((J t s - mellinSaddlePoint t s n u) ^ 2 / ((|t| : ℝ) : ℂ) -
            mellinSaddlePoint t s n u * (Real.log ((n : ℝ) + 1) : ℂ))) / gammaT t s) =
        zetaTerm t s n *
          (∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im), (gaussian |t| u : ℂ)) +
        zetaTerm t s n *
          ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
            (gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u) := by
    calc
      _ = ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
          (zetaTerm t s n * (gaussian |t| u : ℂ) +
            zetaTerm t s n *
              ((gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u))) := by
        apply integral_congr_ae
        filter_upwards with u
        rw [saddle_gaussian_identity t ht s hs n u]
        ring
      _ = _ := by
        rw [integral_add (hiG.const_mul _) (hiE.const_mul _),
          integral_const_mul, integral_const_mul]
  unfold centralMellinTerm gaussianMass
  rw [mul_div_assoc, ← integral_div, hint]
  ring

private noncomputable def termWeight (t a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (t / 4 * Real.log ((n : ℝ) + 1) ^ 2 - a * Real.log ((n : ℝ) + 1))

private theorem term_norm_bound (t a : ℝ) (n : ℕ) (s : ℂ) (ha : a ≤ s.re) :
    ‖zetaTerm t s n‖ ≤ termWeight t a n := by
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  unfold zetaTerm termWeight
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  nlinarith

/-- The local gamma estimate gives an integrable polynomial-Gaussian error,
uniformly in the strip. The constant may depend on the fixed coefficient. -/
private theorem central_error_bound (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) (n : ℕ) :
    ∃ K Y : ℝ, 0 ≤ K ∧ 1 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
        ‖centralMellinTerm t s n / gammaT t s - zetaTerm t s n‖ ≤
          termWeight t a n * ‖gaussianMass |t| s.im - 1‖ + K / s.im := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨C, Y₁, hC, hY₁, hlin⟩ := gammaFactor_local_linearization a b hab
  let d := |t| / 2 * Real.log ((n : ℝ) + 1)
  obtain ⟨Y₂, hY₂, hgeom⟩ := window_geometry d
  let p := Real.sqrt (Real.pi * |t|)
  have hp : 0 < p := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hT)
  let A := ∫ u : ℝ, errorMajorant |t| C d u
  have hA : 0 ≤ A := integral_nonneg fun u =>
    error_majorant_nonneg |t| C d u hC.le
  have hW : 0 ≤ termWeight t a n := Real.exp_nonneg _
  have hM := error_majorant_integrable |t| C d hT hC.le
  refine ⟨termWeight t a n / p * A, max Y₁ (max Y₂ (2 * |t|)),
    mul_nonneg (div_nonneg hW hp.le) hA, hY₁.trans (le_max_left _ _), ?_⟩
  intro s ha hb hy
  have hy₁ : Y₁ ≤ s.im := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ s.im := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hyT : 2 * |t| ≤ s.im := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hy1 : 1 ≤ s.im := hY₁.trans hy₁
  have hs : 0 < s.im := lt_of_lt_of_le zero_lt_one hy1
  obtain ⟨hd, hr⟩ := hgeom s.im hy₂
  have hpoint : ∀ u ∈ Icc (-mellinWindow s.im) (mellinWindow s.im),
      ‖(gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u)‖ ≤
        errorMajorant |t| C d u / s.im := by
    intro u hu
    have hz : ‖mellinSaddlePoint t s n u - s‖ ≤ 2 * mellinWindow s.im := by
      rw [saddle_displacement]
      calc
        _ ≤ |d| + |u| := by
          simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
            mul_one] using norm_add_le (d : ℂ) ((u : ℂ) * Complex.I)
        _ ≤ mellinWindow s.im + mellinWindow s.im :=
          add_le_add hd (abs_le.mpr hu)
        _ = _ := by ring
    have he := hlin s (mellinSaddlePoint t s n u) ha hb hy₁
      (saddle_height t s n u hr hu) hz
    rw [saddle_displacement] at he
    exact weighted_error_bound |t| C d s.im u hT hC.le hy1 hyT _ he
  have hI :
      ‖∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
        (gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u)‖ ≤
        A / s.im := by
    calc
      _ ≤ ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
          errorMajorant |t| C d u / s.im := by
        apply norm_integral_le_of_norm_le (hM.div_const s.im).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
        exact hpoint u hu
      _ ≤ ∫ u : ℝ, errorMajorant |t| C d u / s.im :=
        setIntegral_le_integral (hM.div_const s.im)
          (ae_of_all _ fun u => div_nonneg (error_majorant_nonneg |t| C d u hC.le) hs.le)
      _ = A / s.im := integral_div _ _
  have hz := term_norm_bound t a n s ha
  calc
    _ = ‖zetaTerm t s n * (gaussianMass |t| s.im - 1) +
        (zetaTerm t s n / (p : ℂ)) *
          ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
            (gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u)‖ := by
      rw [central_gaussian_identity t ht s hs n hr]
      congr 1
      ring
    _ ≤ ‖zetaTerm t s n * (gaussianMass |t| s.im - 1)‖ +
        ‖(zetaTerm t s n / (p : ℂ)) *
          ∫ u in Icc (-mellinWindow s.im) (mellinWindow s.im),
            (gaussian |t| u : ℂ) * gammaLinearError s (mellinSaddlePoint t s n u)‖ :=
      norm_add_le _ _
    _ ≤ termWeight t a n * ‖gaussianMass |t| s.im - 1‖ +
        (termWeight t a n / p) * (A / s.im) := by
      rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le]
      exact add_le_add (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
        (mul_le_mul (div_le_div_of_nonneg_right hz hp.le) hI
          (norm_nonneg _) (div_nonneg hW hp.le))
    _ = _ := by ring

private theorem contour_bound_tendsto (T C : ℝ) (hT : 0 < T) :
    Tendsto (fun y : ℝ => C * Real.exp (-(y ^ (4 / 3 : ℝ)) / (40 * T)))
      atTop (𝓝 0) := by
  have hp : Tendsto (fun y : ℝ => y ^ (4 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hd : Tendsto (fun y : ℝ => y ^ (4 / 3 : ℝ) / (40 * T)) atTop atTop := by
    simpa only [div_eq_mul_inv] using
      hp.atTop_mul_const (inv_pos.mpr (show 0 < 40 * T by positivity))
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hd)
  simpa only [Function.comp_def, neg_div, mul_zero] using he.const_mul C

theorem solution (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
      ‖DeBruijnNewman.Dobner.normalizedMellinTerm t s n -
        DeBruijnNewman.Dobner.zetaTerm t s n‖ < ε := by
  have hT : 0 < |t| := abs_pos.mpr ht.ne
  obtain ⟨K, Y₁, hK, hY₁, hcentral⟩ := central_error_bound t ht a b hab n
  obtain ⟨C, Y₂, hC, hY₂, htail⟩ := mellin_contour_remainder t ht a b hab n
  have hg : Tendsto (fun y : ℝ =>
      termWeight t a n * ‖gaussianMass |t| y - 1‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (((gaussian_mass_tendsto |t| hT).sub_const (1 : ℂ)).norm).const_mul
        (termWeight t a n)
  have hk : Tendsto (fun y : ℝ => K / y) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul K
  have hbound : Tendsto (fun y : ℝ =>
      termWeight t a n * ‖gaussianMass |t| y - 1‖ + K / y +
        C * Real.exp (-(y ^ (4 / 3 : ℝ)) / (40 * |t|))) atTop (𝓝 0) := by
    simpa only [zero_add] using (hg.add hk).add (contour_bound_tendsto |t| C hT)
  obtain ⟨Y₃, hsmall⟩ := eventually_atTop.mp (hbound.eventually (gt_mem_nhds hε))
  refine ⟨max Y₁ (max Y₂ Y₃), ?_⟩
  intro s ha hb hy
  have hy₁ : Y₁ ≤ s.im := (le_max_left _ _).trans hy
  have hy₂ : Y₂ ≤ s.im := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hy₃ : Y₃ ≤ s.im := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hc := hcentral s ha hb hy₁
  have ht' := htail s ha hb hy₂
  calc
    _ = ‖(centralMellinTerm t s n / gammaT t s - zetaTerm t s n) +
        (mellinTerm t s n - centralMellinTerm t s n) / gammaT t s‖ := by
      unfold normalizedMellinTerm
      congr 1
      ring
    _ ≤ ‖centralMellinTerm t s n / gammaT t s - zetaTerm t s n‖ +
        ‖(mellinTerm t s n - centralMellinTerm t s n) / gammaT t s‖ :=
      norm_add_le _ _
    _ ≤ termWeight t a n * ‖gaussianMass |t| s.im - 1‖ + K / s.im +
        C * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (40 * |t|)) :=
      add_le_add hc ht'
    _ < ε := hsmall s.im hy₃
