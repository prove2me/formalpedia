-- Prove2me | solution 1 for BerryEsseenFeller.berry_esseen
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T19:25:25.336566+00:00
-- url     : https://prove2.me/submissions/c6cd76d6-9e39-4d0e-aea6-62524a783a91

import Mathlib

set_option autoImplicit false

section CharBoundLib


open MeasureTheory ProbabilityTheory Complex
open scoped Real

namespace BerryEsseenFeller

lemma hasDerivAt_cexp_mul_I (y : ℝ) :
    HasDerivAt (fun y : ℝ => cexp (y * I)) (I * cexp (y * I)) y := by
  have h : HasDerivAt (fun z : ℂ => cexp (z * I)) (cexp ((y : ℂ) * I) * (1 * I)) (y : ℂ) :=
    ((hasDerivAt_id (y : ℂ)).mul_const I).cexp
  refine h.comp_ofReal.congr_deriv ?_
  ring

lemma norm_cexp_sub_one_sub_le_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    ‖cexp (x * I) - 1 - x * I‖ ≤ x ^ 2 / 2 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => cexp (y * I) - 1 - y * I)
      (I * (cexp (y * I) - 1)) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) (1 * I) y := by
      have := ((hasDerivAt_id (y : ℂ)).mul_const I).comp_ofReal
      simpa using this
    refine (((hasDerivAt_cexp_mul_I y).sub_const 1).sub h2).congr_deriv ?_
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun y : ℝ => cexp (y * I) - 1 - y * I) (f' := fun y : ℝ => I * (cexp (y * I) - 1))
    (a := 0) (b := x) (B := fun y => y ^ 2 / 2) (B' := fun y => y)
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => (hd y).hasDerivWithinAt)
    (by simp) (fun y => by simpa using ((hasDerivAt_pow 2 y).div_const 2))
    (fun y hy => by
      rw [norm_mul, Complex.norm_I, one_mul]
      have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := y)
      rw [mul_comm] at this
      simpa [Real.norm_eq_abs, abs_of_nonneg hy.1] using this)
  exact key ⟨hx, le_rfl⟩

lemma norm_cexp_sub_one_sub_le (x : ℝ) :
    ‖cexp (x * I) - 1 - x * I‖ ≤ x ^ 2 / 2 := by
  rcases le_total 0 x with hx | hx
  · exact norm_cexp_sub_one_sub_le_of_nonneg x hx
  · have h := norm_cexp_sub_one_sub_le_of_nonneg (-x) (by linarith)
    have hz : (((-x : ℝ)) : ℂ) * I = (starRingEnd ℂ) ((x : ℂ) * I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]; ring
    have hc : cexp ((-x : ℝ) * I) - 1 - (-x : ℝ) * I =
        (starRingEnd ℂ) (cexp (x * I) - 1 - x * I) := by
      rw [hz, Complex.exp_conj, map_sub, map_sub, map_one]
    rw [hc, Complex.norm_conj] at h
    simpa using h

lemma norm_cexp_sub_taylor_two_le_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    ‖cexp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2‖ ≤ x ^ 3 / 6 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => cexp (y * I) - 1 - y * I + (y : ℂ) ^ 2 / 2)
      (I * (cexp (y * I) - 1 - y * I)) y := by
    intro y
    have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) (1 * I) y := by
      have := ((hasDerivAt_id (y : ℂ)).mul_const I).comp_ofReal
      simpa using this
    have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 / 2) (2 * (y : ℂ) / 2) y := by
      have := (((hasDerivAt_id (y : ℂ)).pow 2).div_const 2).comp_ofReal
      simpa using this
    refine ((((hasDerivAt_cexp_mul_I y).sub_const 1).sub h2).add h3).congr_deriv ?_
    have hI : I * ((y : ℂ) * I) = -(y : ℂ) := by rw [mul_left_comm, Complex.I_mul_I]; ring
    linear_combination hI
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun y : ℝ => cexp (y * I) - 1 - y * I + (y : ℂ) ^ 2 / 2)
    (f' := fun y : ℝ => I * (cexp (y * I) - 1 - y * I))
    (a := 0) (b := x) (B := fun y => y ^ 3 / 6) (B' := fun y => y ^ 2 / 2)
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => (hd y).hasDerivWithinAt)
    (by simp) (fun y => by
      exact ((hasDerivAt_pow 3 y).div_const 6).congr_deriv
        (by rw [show (3 : ℕ) - 1 = 2 from rfl]; push_cast; ring))
    (fun y hy => by
      rw [norm_mul, Complex.norm_I, one_mul]
      exact norm_cexp_sub_one_sub_le y)
  exact key ⟨hx, le_rfl⟩

/-- `‖e^{ix} - 1 - ix + x²/2‖ ≤ |x|³/6` for every real `x`. -/
lemma norm_cexp_sub_taylor_two_le (x : ℝ) :
    ‖cexp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2‖ ≤ |x| ^ 3 / 6 := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact norm_cexp_sub_taylor_two_le_of_nonneg x hx
  · have h := norm_cexp_sub_taylor_two_le_of_nonneg (-x) (by linarith)
    have hc : cexp ((-x : ℝ) * I) - 1 - (-x : ℝ) * I + (((-x : ℝ)) : ℂ) ^ 2 / 2 =
        (starRingEnd ℂ) (cexp (x * I) - 1 - x * I + (x : ℂ) ^ 2 / 2) := by
      have hz : (((-x : ℝ)) : ℂ) * I = (starRingEnd ℂ) ((x : ℂ) * I) := by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]; ring
      have hq : (((-x : ℝ)) : ℂ) ^ 2 / 2 = (starRingEnd ℂ) ((x : ℂ) ^ 2 / 2) := by
        rw [map_div₀, map_pow, Complex.conj_ofReal, map_ofNat, Complex.ofReal_neg]; ring
      rw [hz, hq, Complex.exp_conj, map_add, map_sub, map_sub, map_one]
    rw [hc, Complex.norm_conj] at h
    rw [abs_of_nonpos hx]
    simpa using h

/-- `‖aⁿ - bⁿ‖ ≤ n ‖a - b‖ cⁿ⁻¹` when `‖a‖, ‖b‖ ≤ c`. -/
lemma norm_pow_sub_pow_le' (a b : ℂ) (c : ℝ) (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ n * ‖a - b‖ * c ^ (n - 1) := by
  have hc : 0 ≤ c := (norm_nonneg a).trans ha
  induction n with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by ring
    rw [e]
    calc ‖a * (a ^ k - b ^ k) + (a - b) * b ^ k‖
        ≤ ‖a‖ * ‖a ^ k - b ^ k‖ + ‖a - b‖ * ‖b‖ ^ k := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow]
      _ ≤ c * (k * ‖a - b‖ * c ^ (k - 1)) + ‖a - b‖ * c ^ k := by
          gcongr
      _ = ((k + 1 : ℕ) : ℝ) * ‖a - b‖ * c ^ (k + 1 - 1) := by
          rcases k with _ | k
          · simp
          · simp only [Nat.add_sub_cancel]
            push_cast
            rw [pow_succ]
            ring

/-- (B1) Second-order Taylor bound for a characteristic function with a third moment. -/
theorem norm_charFun_sub_taylor_two_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h3 : Integrable (fun x => |x| ^ 3) μ) (s : ℝ) :
    ‖charFun μ s - (1 + (s : ℂ) * I * (∫ x, x ∂μ) - (s : ℂ) ^ 2 / 2 * (∫ x, x ^ 2 ∂μ))‖ ≤
      |s| ^ 3 / 6 * ∫ x, |x| ^ 3 ∂μ := by
  have hb1 : ∀ x : ℝ, |x| ≤ 1 + |x| ^ 3 := by
    intro x
    rcases le_total (|x|) 1 with h | h
    · nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
    · have e : |x| ^ 3 = |x| * (|x| * |x|) := by ring
      nlinarith [abs_nonneg x, mul_le_mul h h zero_le_one (abs_nonneg x)]
  have hb2 : ∀ x : ℝ, x ^ 2 ≤ 1 + |x| ^ 3 := by
    intro x
    have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    rw [this]
    rcases le_total (|x|) 1 with h | h
    · nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
    · have e : |x| ^ 3 = |x| * (|x| * |x|) := by ring
      nlinarith [abs_nonneg x, mul_le_mul h h zero_le_one (abs_nonneg x)]
  have hbig : Integrable (fun x : ℝ => 1 + |x| ^ 3) μ := (integrable_const 1).add h3
  have hi1 : Integrable (fun x : ℝ => x) μ := by
    refine hbig.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using hb1 x
  have hi2 : Integrable (fun x : ℝ => x ^ 2) μ := by
    refine hbig.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using hb2 x
  have hi1c : Integrable (fun x : ℝ => (s : ℂ) * I * (x : ℂ)) μ :=
    (hi1.ofReal (𝕜 := ℂ)).const_mul _
  have hi2c : Integrable (fun x : ℝ => (s : ℂ) ^ 2 / 2 * ((x ^ 2 : ℝ) : ℂ)) μ :=
    (hi2.ofReal (𝕜 := ℂ)).const_mul _
  have hexp : Integrable (fun x : ℝ => cexp (s * x * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    have : (s : ℂ) * x * I = ((s * x : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hrepr : charFun μ s - (1 + (s : ℂ) * I * (∫ x, x ∂μ) - (s : ℂ) ^ 2 / 2 * (∫ x, x ^ 2 ∂μ)) =
      ∫ x, (cexp (((s * x : ℝ)) * I) - 1 - ((s * x : ℝ) : ℂ) * I +
        (((s * x : ℝ)) : ℂ) ^ 2 / 2) ∂μ := by
    have hpoly : Integrable (fun x : ℝ => (1 : ℂ) + (s : ℂ) * I * (x : ℂ) -
        (s : ℂ) ^ 2 / 2 * ((x ^ 2 : ℝ) : ℂ)) μ := ((integrable_const _).add hi1c).sub hi2c
    have hP : ∫ x, ((1 : ℂ) + (s : ℂ) * I * (x : ℂ) - (s : ℂ) ^ 2 / 2 * ((x ^ 2 : ℝ) : ℂ)) ∂μ =
        1 + (s : ℂ) * I * (∫ x, x ∂μ) - (s : ℂ) ^ 2 / 2 * (∫ x, x ^ 2 ∂μ) := by
      rw [integral_sub (f := fun x : ℝ => (1 : ℂ) + (s : ℂ) * I * (x : ℂ))
          (g := fun x : ℝ => (s : ℂ) ^ 2 / 2 * ((x ^ 2 : ℝ) : ℂ))
          (by exact (integrable_const _).add hi1c) hi2c,
        integral_add (f := fun _ : ℝ => (1 : ℂ)) (g := fun x : ℝ => (s : ℂ) * I * (x : ℂ))
          (integrable_const _) hi1c,
        integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
      simp
    rw [charFun_apply_real, ← hP, ← integral_sub hexp hpoly]
    congr 1
    ext x
    push_cast
    ring
  rw [hrepr]
  calc ‖∫ x, (cexp (((s * x : ℝ)) * I) - 1 - ((s * x : ℝ) : ℂ) * I +
        (((s * x : ℝ)) : ℂ) ^ 2 / 2) ∂μ‖
      ≤ ∫ x, |s * x| ^ 3 / 6 ∂μ :=
        norm_integral_le_of_norm_le ((h3.const_mul (|s| ^ 3 / 6)).congr
          (Filter.Eventually.of_forall fun x => by simp only [abs_mul, mul_pow]; ring))
          (Filter.Eventually.of_forall fun x => norm_cexp_sub_taylor_two_le (s * x))
    _ = |s| ^ 3 / 6 * ∫ x, |x| ^ 3 ∂μ := by
        rw [← integral_const_mul]
        congr 1
        ext x
        rw [abs_mul, mul_pow]
        ring


/-- `0 ≤ e^{-x} - 1 + x ≤ x²/2` for `x ≥ 0`. -/
lemma exp_neg_sub_one_add_le (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) - 1 + x ≤ x ^ 2 / 2 := by
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y) - 1 + y) (1 - Real.exp (-y)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-y) * (-1)) y :=
      (hasDerivAt_neg y).exp
    refine ((h1.sub_const 1).add (hasDerivAt_id y)).congr_deriv ?_
    simp; ring
  have hB : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ 2 / 2) y y := by
    intro y
    exact ((hasDerivAt_pow 2 y).div_const 2).congr_deriv (by push_cast; ring)
  have key := image_le_of_deriv_right_le_deriv_boundary
    (f := fun y : ℝ => Real.exp (-y) - 1 + y) (f' := fun y => 1 - Real.exp (-y))
    (a := 0) (b := x) (B := fun y => y ^ 2 / 2) (B' := fun y => y)
    (fun y _ => (hd y).continuousAt.continuousWithinAt) (fun y _ => (hd y).hasDerivWithinAt)
    (by simp) (fun y _ => (hB y).continuousAt.continuousWithinAt)
    (fun y _ => (hB y).hasDerivWithinAt)
    (fun y _ => by linarith [Real.add_one_le_exp (-y)])
  exact key ⟨hx, le_rfl⟩

set_option maxHeartbeats 1000000 in
/-- (B) Feller XVI.5 Lemma 1 with explicit constants: for a centred, unit-variance `Y` with
`β = E|Y|³`, `T = 4√n/(3β)`, `n ≥ 10` and `|t| ≤ T`. -/
theorem charFun_pow_sub_gaussian_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) P)
    (h0 : ∫ ω, Y ω ∂P = 0) (h1 : ∫ ω, Y ω ^ 2 ∂P = 1) (n : ℕ) (hn : 10 ≤ n) (t : ℝ)
    (ht : |t| ≤ 4 * √(n : ℝ) / (3 * ∫ ω, |Y ω| ^ 3 ∂P)) :
    ‖(charFun (P.map Y) ((√(n : ℝ))⁻¹ * t)) ^ n - cexp (-(t : ℂ) ^ 2 / 2)‖ ≤
      (2 * |t| ^ 3 / (9 * (4 * √(n : ℝ) / (3 * ∫ ω, |Y ω| ^ 3 ∂P))) + t ^ 4 / (8 * n)) *
        Real.exp (-t ^ 2 / 4) := by
  set β := ∫ ω, |Y ω| ^ 3 ∂P with hβ
  have : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY
  have hm3 : Integrable (fun x : ℝ => |x| ^ 3) (P.map Y) := by
    rw [integrable_map_measure (by fun_prop) hY]; exact h3
  have e0 : ∫ x, x ∂(P.map Y) = 0 := by rw [integral_map hY (by fun_prop)]; exact h0
  have e2 : ∫ x, x ^ 2 ∂(P.map Y) = 1 := by rw [integral_map hY (by fun_prop)]; exact h1
  have e3 : ∫ x, |x| ^ 3 ∂(P.map Y) = β := by rw [integral_map hY (by fun_prop)]
  -- Lyapunov: β ≥ 1
  have hβ1 : 1 ≤ β := by
    have hpt : ∀ ω, Y ω ^ 2 ≤ 2 / 3 * |Y ω| ^ 3 + 1 / 3 := by
      intro ω
      have ha := abs_nonneg (Y ω)
      rw [← sq_abs (Y ω)]
      nlinarith [mul_nonneg (sq_nonneg (|Y ω| - 1)) (by linarith : (0 : ℝ) ≤ 2 * |Y ω| + 1)]
    have hI : Integrable (fun ω => 2 / 3 * |Y ω| ^ 3 + 1 / 3) P :=
      (h3.const_mul (2 / 3)).add (integrable_const (1 / 3 : ℝ))
    have hi2 : Integrable (fun ω => Y ω ^ 2) P :=
      hI.mono' (hY.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
    have hmono := integral_mono hi2 hI hpt
    have hval : ∫ ω, (2 / 3 * |Y ω| ^ 3 + 1 / 3) ∂P = 2 / 3 * β + 1 / 3 := by
      rw [integral_add (h3.const_mul _) (integrable_const _), integral_const_mul]
      simp [hβ]
    rw [h1, hval] at hmono
    linarith
  have hβ0 : 0 < β := by linarith
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hn0
  have hr2 : r ^ 2 = n := Real.sq_sqrt hn0.le
  set u := r⁻¹ * t with hudef
  have hu2 : u ^ 2 = t ^ 2 / n := by
    rw [hudef, mul_pow, inv_pow, hr2]; ring
  have hu3 : |u| ^ 3 = |t| ^ 3 / (n * r) := by
    rw [hudef, abs_mul, abs_inv, abs_of_pos hr, mul_pow, inv_pow,
      show r ^ 3 = r ^ 2 * r by ring, hr2]
    field_simp
  have hbt : β * |t| ≤ 4 * r / 3 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 3 * β)).1 ht
    linarith
  have ht2 : t ^ 2 ≤ 16 * (n : ℝ) / 9 := by
    have h1' : |t| ≤ 4 * r / 3 := by nlinarith [abs_nonneg t]
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [this]
    calc |t| ^ 2 ≤ (4 * r / 3) ^ 2 := by gcongr
      _ = 16 * (n : ℝ) / 9 := by rw [div_pow, mul_pow, hr2]; ring
  -- Taylor bound
  have hB1 := norm_charFun_sub_taylor_two_le (P.map Y) hm3 u
  rw [e0, e2, e3] at hB1
  set ψ := charFun (P.map Y) u with hψ
  set q : ℝ := 1 - t ^ 2 / (2 * n) with hq
  have hq_eq : (1 + (u : ℂ) * I * ((0 : ℝ) : ℂ) - (u : ℂ) ^ 2 / 2 * ((1 : ℝ) : ℂ)) = (q : ℂ) := by
    have : q = 1 - u ^ 2 / 2 := by rw [hq, hu2]; ring
    rw [this]; push_cast <;> ring
  rw [hq_eq] at hB1
  have key1 : |u| ^ 3 / 6 * β ≤ 2 * t ^ 2 / (9 * n) := by
    have e : |u| ^ 3 / 6 * β = (β * |t|) * (t ^ 2 / (6 * n * r)) := by
      rw [hu3, ← sq_abs t]; field_simp <;> ring
    rw [e]
    calc (β * |t|) * (t ^ 2 / (6 * n * r)) ≤ (4 * r / 3) * (t ^ 2 / (6 * n * r)) :=
          mul_le_mul_of_nonneg_right hbt (by positivity)
      _ = 2 * t ^ 2 / (9 * n) := by field_simp; ring
  have hq0 : 0 ≤ q := by
    rw [hq]
    have : t ^ 2 / (2 * n) ≤ 8 / 9 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  set c := Real.exp (-(5 * t ^ 2 / (18 * n))) with hc
  have hψc : ‖ψ‖ ≤ c := by
    have h1' : ‖ψ‖ ≤ q + 2 * t ^ 2 / (9 * n) := by
      calc ‖ψ‖ = ‖(q : ℂ) + (ψ - q)‖ := by ring_nf
        _ ≤ ‖(q : ℂ)‖ + ‖ψ - q‖ := norm_add_le _ _
        _ ≤ q + 2 * t ^ 2 / (9 * n) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
          linarith
    have h2' : q + 2 * t ^ 2 / (9 * n) = -(5 * t ^ 2 / (18 * n)) + 1 := by
      rw [hq]; field_simp; ring
    rw [h2'] at h1'
    exact h1'.trans (Real.add_one_le_exp _)
  set b : ℂ := cexp ((-(t ^ 2 / (2 * n)) : ℝ)) with hb
  have hbnorm : ‖b‖ ≤ c := by
    rw [hb, Complex.norm_exp_ofReal, hc]
    apply Real.exp_le_exp.2
    have : 5 * t ^ 2 / (18 * n) ≤ t ^ 2 / (2 * n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg t]
    linarith
  have hbn : b ^ n = cexp (-(t : ℂ) ^ 2 / 2) := by
    rw [hb, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    field_simp
  have hψb : ‖ψ - b‖ ≤ |u| ^ 3 / 6 * β + (t ^ 2 / (2 * n)) ^ 2 / 2 := by
    have hx0 : 0 ≤ t ^ 2 / (2 * n) := by positivity
    have hexp := exp_neg_sub_one_add_le (t ^ 2 / (2 * n)) hx0
    have hexp' := Real.add_one_le_exp (-(t ^ 2 / (2 * n)))
    have hqb : ‖(q : ℂ) - b‖ ≤ (t ^ 2 / (2 * n)) ^ 2 / 2 := by
      rw [hb, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_le]
      constructor <;> rw [hq] <;> linarith
    calc ‖ψ - b‖ = ‖(ψ - q) + ((q : ℂ) - b)‖ := by ring_nf
      _ ≤ ‖ψ - q‖ + ‖(q : ℂ) - b‖ := norm_add_le _ _
      _ ≤ |u| ^ 3 / 6 * β + (t ^ 2 / (2 * n)) ^ 2 / 2 := add_le_add hB1 hqb
  have hpow := norm_pow_sub_pow_le' ψ b c hψc hbnorm n
  rw [hbn] at hpow
  have hcpow : c ^ (n - 1) ≤ Real.exp (-t ^ 2 / 4) := by
    rw [hc, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hcast : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hcast]
    have e : ((n : ℝ) - 1) * (-(5 * t ^ 2 / (18 * n))) =
        -t ^ 2 / 4 - t ^ 2 * (2 * n - 20) / (72 * n) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ t ^ 2 * (2 * n - 20) / (72 * n) := by
      apply div_nonneg _ (by positivity)
      exact mul_nonneg (sq_nonneg t) (by linarith)
    linarith
  have hfin : (n : ℝ) * (|u| ^ 3 / 6 * β + (t ^ 2 / (2 * n)) ^ 2 / 2) =
      2 * |t| ^ 3 / (9 * (4 * r / (3 * β))) + t ^ 4 / (8 * n) := by
    rw [hu3]; field_simp; ring
  calc ‖ψ ^ n - cexp (-(t : ℂ) ^ 2 / 2)‖ ≤ n * ‖ψ - b‖ * c ^ (n - 1) := hpow
    _ ≤ n * (|u| ^ 3 / 6 * β + (t ^ 2 / (2 * n)) ^ 2 / 2) * Real.exp (-t ^ 2 / 4) := by
        gcongr
    _ = (2 * |t| ^ 3 / (9 * (4 * r / (3 * β))) + t ^ 4 / (8 * n)) * Real.exp (-t ^ 2 / 4) := by
        rw [hfin]

end BerryEsseenFeller

open MeasureTheory ProbabilityTheory Complex

namespace BerryEsseenFeller

/-- (A) Esseen's smoothing inequality, as a proposition (proved separately). -/
def EsseenSmoothingStmt : Prop :=
  ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    Integrable id μ → Integrable id ν →
    ∀ {m T : ℝ}, 0 < T → (∀ x y, x ≤ y → cdf ν y - cdf ν x ≤ m * (y - x)) →
    MeasureTheory.IntegrableOn (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) (Set.Icc (-T) T) →
    ∀ x : ℝ, |cdf μ x - cdf ν x| ≤
      (1 / π) * (∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t|) + 24 * m / (π * T)

/-- (C1) The standard normal distribution function is `2/5`-Lipschitz. -/
lemma cdf_gaussianReal_lipschitz (x y : ℝ) (hxy : x ≤ y) :
    cdf (gaussianReal 0 1) y - cdf (gaussianReal 0 1) x ≤ 2 / 5 * (y - x) := by
  have hpdf : ∀ z, gaussianPDFReal 0 1 z ≤ 2 / 5 := by
    intro z
    rw [gaussianPDFReal]
    have h1 : Real.exp (-(z - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := sq_nonneg (z - 0)
      push_cast
      linarith
    have h2 : (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ ≤ 2 / 5 := by
      push_cast
      rw [inv_le_comm₀ (by positivity) (by norm_num), show ((2 : ℝ) / 5)⁻¹ = 5 / 2 by norm_num,
        Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_d2]
    calc (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ * Real.exp (-(z - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)))
        ≤ (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ * 1 := by gcongr
      _ ≤ 2 / 5 := by linarith
  have hmeas := (cdf (gaussianReal 0 1)).measure_Ioc x y
  rw [measure_cdf, gaussianReal_apply 0 one_ne_zero] at hmeas
  have hle : ∫⁻ z in Set.Ioc x y, gaussianPDF 0 1 z ≤ ENNReal.ofReal (2 / 5 * (y - x)) := by
    calc ∫⁻ z in Set.Ioc x y, gaussianPDF 0 1 z ≤ ∫⁻ z in Set.Ioc x y, ENNReal.ofReal (2 / 5) :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hpdf z)
      _ = ENNReal.ofReal (2 / 5) * volume (Set.Ioc x y) := setLIntegral_const _ _
      _ = ENNReal.ofReal (2 / 5 * (y - x)) := by
          rw [Real.volume_Ioc, ← ENNReal.ofReal_mul (by norm_num)]
  rw [hmeas] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).1 hle

/-- Lyapunov for the third moment: `E Y² = 1` forces `E|Y|³ ≥ 1`. -/
lemma one_le_abs_moment_three {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P)
    (h3 : Integrable (fun ω => |Y ω| ^ 3) P) (h1 : ∫ ω, Y ω ^ 2 ∂P = 1) :
    1 ≤ ∫ ω, |Y ω| ^ 3 ∂P := by
  have hpt : ∀ ω, Y ω ^ 2 ≤ 2 / 3 * |Y ω| ^ 3 + 1 / 3 := by
    intro ω
    have ha := abs_nonneg (Y ω)
    rw [← sq_abs (Y ω)]
    nlinarith [mul_nonneg (sq_nonneg (|Y ω| - 1)) (by linarith : (0 : ℝ) ≤ 2 * |Y ω| + 1)]
  have hI : Integrable (fun ω => 2 / 3 * |Y ω| ^ 3 + 1 / 3) P :=
    (h3.const_mul (2 / 3)).add (integrable_const (1 / 3 : ℝ))
  have hi2 : Integrable (fun ω => Y ω ^ 2) P :=
    hI.mono' (hY.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω)
  have hmono := integral_mono hi2 hI hpt
  have hval : ∫ ω, (2 / 3 * |Y ω| ^ 3 + 1 / 3) ∂P = 2 / 3 * (∫ ω, |Y ω| ^ 3 ∂P) + 1 / 3 := by
    rw [integral_add (h3.const_mul _) (integrable_const _), integral_const_mul]
    simp
  rw [h1, hval] at hmono
  linarith

/-- `∫ |t|³ e^{-t²/4} = 16`. -/
lemma integral_abs_pow_three_mul_exp :
    ∫ t : ℝ, |t| ^ 3 * Real.exp (-t ^ 2 / 4) = 16 := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ (3 : ℝ) * Real.exp (-(1 / 4) * y ^ (2 : ℝ)))
  have hG := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 3) (b := 1 / 4) (by norm_num)
    (by norm_num) (by norm_num)
  rw [hG] at h
  have e1 : (fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 4)) =
      fun t : ℝ => |t| ^ (3 : ℝ) * Real.exp (-(1 / 4) * |t| ^ (2 : ℝ)) := by
    ext t
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_two, sq_abs]
    ring_nf
  rw [e1, h]
  have g2 : Real.Gamma ((3 + 1) / 2) = 1 := by
    rw [show ((3 : ℝ) + 1) / 2 = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]; simp
  rw [g2, show -((3 : ℝ) + 1) / 2 = -2 by norm_num, Real.rpow_neg (by norm_num), Real.rpow_two]
  norm_num

/-- `∫ t² e^{-t²/4} = 4√π`. -/
lemma integral_sq_mul_exp :
    ∫ t : ℝ, t ^ 2 * Real.exp (-t ^ 2 / 4) = 4 * √π := by
  have h := integral_comp_abs (f := fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-(1 / 4) * y ^ (2 : ℝ)))
  have hG := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2) (b := 1 / 4) (by norm_num)
    (by norm_num) (by norm_num)
  rw [hG] at h
  have e1 : (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 4)) =
      fun t : ℝ => |t| ^ (2 : ℝ) * Real.exp (-(1 / 4) * |t| ^ (2 : ℝ)) := by
    ext t
    rw [Real.rpow_two, sq_abs]
    ring_nf
  rw [e1, h]
  have g2 : Real.Gamma ((2 + 1) / 2) = √π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have r8 : (1 / 4 : ℝ) ^ (-((2 : ℝ) + 1) / 2) = 8 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num,
      ← Real.rpow_mul (by norm_num), show (2 : ℝ) * (-((2 : ℝ) + 1) / 2) = ((-3 : ℤ) : ℝ) by
        norm_num, Real.rpow_intCast]
    norm_num
  rw [g2, r8]
  ring

set_option maxHeartbeats 1000000 in
/-- Assembly: Berry–Esseen with constant 3 from the smoothing inequality (A). -/
theorem berry_esseen_of_smoothing (hA : EsseenSmoothingStmt) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {σ ρ : ℝ} (hσ : 0 < σ) (h3 : Integrable (fun ω => |X 0 ω| ^ 3) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = σ ^ 2)
    (hρ : ∫ ω, |X 0 ω| ^ 3 ∂P = ρ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |cdf (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) / (σ * √(n : ℝ)))) x
        - cdf (gaussianReal 0 1) x| ≤ 3 * ρ / (σ ^ 3 * √(n : ℝ)) := by
  set Y : ℕ → Ω → ℝ := fun i ω => X i ω / σ with hYdef
  have hYind : iIndepFun Y P := hindep.comp (fun _ x => x / σ) (fun _ => measurable_id.div_const σ)
  have hYid : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    (hident i).comp (measurable_id.div_const σ)
  have hX0 : AEMeasurable (X 0) P := (hident 0).aemeasurable_fst
  have hY0 : AEMeasurable (Y 0) P := hX0.div_const σ
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hmapeq : (fun ω => (∑ i ∈ Finset.range n, X i ω) / (σ * √(n : ℝ))) =
      fun ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, Y k ω := by
    funext ω
    simp only [hYdef]
    rw [← Finset.sum_div]
    field_simp
  rw [hmapeq]
  set β := ∫ ω, |Y 0 ω| ^ 3 ∂P with hβdef
  have hY3 : Integrable (fun ω => |Y 0 ω| ^ 3) P :=
    (h3.div_const (σ ^ 3)).congr (Filter.Eventually.of_forall fun ω => by
      simp [hYdef, abs_div, div_pow, abs_of_pos hσ])
  have hYm : ∫ ω, Y 0 ω ∂P = 0 := by
    simp only [hYdef]; rw [integral_div, hmean, zero_div]
  have hYv : ∫ ω, Y 0 ω ^ 2 ∂P = 1 := by
    simp only [hYdef, div_pow]; rw [integral_div, hvar]; field_simp
  have hβ : β = ρ / σ ^ 3 := by
    simp only [hβdef, hYdef, abs_div, abs_of_pos hσ, div_pow]; rw [integral_div, hρ]
  have hβ1 : 1 ≤ β := one_le_abs_moment_three P (Y 0) hY0 hY3 hYv
  have hRHS : 3 * ρ / (σ ^ 3 * √(n : ℝ)) = 3 * β / √(n : ℝ) := by
    rw [hβ]; field_simp
  rw [hRHS]
  have hSmeas : AEMeasurable (fun ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, Y k ω) P := by
    apply AEMeasurable.const_mul
    exact Finset.aemeasurable_fun_sum _ (fun k _ => (hYid k).aemeasurable_fst)
  set μn := P.map (fun ω => (√(n : ℝ))⁻¹ * ∑ k ∈ Finset.range n, Y k ω) with hμn
  have : IsProbabilityMeasure μn := Measure.isProbabilityMeasure_map hSmeas
  rcases lt_or_ge n 10 with hsmall | hbig
  · have hle1 : |cdf μn x - cdf (gaussianReal 0 1) x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [cdf_nonneg μn x, cdf_le_one μn x, cdf_nonneg (gaussianReal 0 1) x,
        cdf_le_one (gaussianReal 0 1) x]
    have hs3 : √(n : ℝ) ≤ 3 := by
      rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : n ≤ 9))
    have h1 : 1 ≤ 3 * β / √(n : ℝ) := by
      rw [le_div_iff₀ hsq]; nlinarith
    linarith
  · set s := √(n : ℝ) with hsdef
    set T := 4 * s / (3 * β) with hTdef
    have hT : 0 < T := by positivity
    have hn' : (n : ℝ) = s ^ 2 := (Real.sq_sqrt (by linarith)).symm
    have hφ : ∀ t, charFun μn t = (charFun (P.map (Y 0)) (s⁻¹ * t)) ^ n := fun t =>
      charFun_inv_sqrt_mul_sum hYind hYid
    have hγ : ∀ t : ℝ, charFun (gaussianReal 0 1) t = cexp (-(t : ℂ) ^ 2 / 2) := by
      intro t; rw [charFun_gaussianReal]; congr 1; push_cast; ring
    set g : ℝ → ℝ := fun t => 2 / (9 * T) * (t ^ 2 * Real.exp (-t ^ 2 / 4)) +
      1 / (8 * n) * (|t| ^ 3 * Real.exp (-t ^ 2 / 4)) with hgdef
    have hbound : ∀ t ∈ Set.Icc (-T) T,
        ‖charFun μn t - charFun (gaussianReal 0 1) t‖ / |t| ≤ g t := by
      intro t ht
      have hta : |t| ≤ T := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
      have hB := charFun_pow_sub_gaussian_le P (Y 0) hY0 hY3 hYm hYv n hbig t hta
      rw [← hβdef, ← hsdef, ← hTdef] at hB
      rw [hφ, hγ]
      rcases eq_or_ne t 0 with h0 | h0
      · subst h0; simp [hgdef]
      · have hta0 : 0 < |t| := abs_pos.2 h0
        rw [div_le_iff₀ hta0]
        refine hB.trans (le_of_eq ?_)
        have h4 : t ^ 4 = |t| ^ 4 := by
          rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ← sq_abs t]; ring
        have h2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
        simp only [hgdef]
        rw [h4, h2]
        field_simp <;> ring
    have hgcont : Continuous g := by
      simp only [hgdef]; fun_prop
    have hint : IntegrableOn (fun t : ℝ => ‖charFun μn t - charFun (gaussianReal 0 1) t‖ / |t|)
        (Set.Icc (-T) T) := by
      refine Integrable.mono' (g := g) (hgcont.integrableOn_Icc) ?_ ?_
      · exact (((continuous_charFun.sub continuous_charFun).norm).measurable.div
          continuous_abs.measurable).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hbound t ht
    have hY0int : Integrable (Y 0) P := by
      refine ((integrable_const (1 : ℝ)).add hY3).mono' hY0.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      show |Y 0 ω| ≤ 1 + |Y 0 ω| ^ 3
      rcases le_total (|Y 0 ω|) 1 with h | h
      · nlinarith [abs_nonneg (Y 0 ω), pow_nonneg (abs_nonneg (Y 0 ω)) 3]
      · nlinarith [abs_nonneg (Y 0 ω), mul_le_mul h h zero_le_one (abs_nonneg (Y 0 ω))]
    have hμint : Integrable id μn := by
      rw [hμn, integrable_map_measure aestronglyMeasurable_id hSmeas]
      apply Integrable.const_mul
      exact integrable_finset_sum _ (fun k _ => (hYid k).integrable_iff.2 hY0int)
    have hνint : Integrable id (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 1).integrable (by simp)
    have hA' := hA μn (gaussianReal 0 1) hμint hνint (m := 2 / 5) hT
      (fun a b hab => cdf_gaussianReal_lipschitz a b hab) hint x
    have h2int : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-t ^ 2 / 4)) := by
      have := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 2) (by norm_num)
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [Real.rpow_two]
      ring_nf
    have h3int : Integrable (fun t : ℝ => |t| ^ 3 * Real.exp (-t ^ 2 / 4)) := by
      have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num) (s := 3)
        (by norm_num)).norm
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      simp only [Real.norm_eq_abs]
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, abs_mul, abs_pow,
        abs_of_pos (Real.exp_pos _)]
      ring_nf
    have hgint : Integrable g := by
      simp only [hgdef]
      exact (h2int.const_mul _).add (h3int.const_mul _)
    have hI : ∫ t in (-T)..T, ‖charFun μn t - charFun (gaussianReal 0 1) t‖ / |t| ≤
        2 / (9 * T) * (4 * √π) + 1 / (8 * n) * 16 := by
      have hint' : IntegrableOn (fun t : ℝ => ‖charFun μn t - charFun (gaussianReal 0 1) t‖ / |t|)
          (Set.uIcc (-T) T) := by
        rw [Set.uIcc_of_le (by linarith)]; exact hint
      calc ∫ t in (-T)..T, ‖charFun μn t - charFun (gaussianReal 0 1) t‖ / |t|
          ≤ ∫ t in (-T)..T, g t :=
            intervalIntegral.integral_mono_on (by linarith) hint'.intervalIntegrable
              (hgcont.intervalIntegrable _ _) hbound
        _ ≤ ∫ t, g t := by
            rw [intervalIntegral.integral_of_le (by linarith)]
            exact setIntegral_le_integral hgint (Filter.Eventually.of_forall fun t => by
              simp only [hgdef]; positivity)
        _ = 2 / (9 * T) * (4 * √π) + 1 / (8 * n) * 16 := by
            simp only [hgdef]
            rw [integral_add (h2int.const_mul _) (h3int.const_mul _), integral_const_mul,
              integral_const_mul, integral_sq_mul_exp, integral_abs_pow_three_mul_exp]
    have hs10 : (3.16 : ℝ) ≤ s := by
      rw [hsdef, Real.le_sqrt (by norm_num) (by positivity)]
      have : (10 : ℝ) ≤ n := by exact_mod_cast hbig
      nlinarith
    have hsqpi : √π ≤ 1.8 := by
      rw [show (1.8 : ℝ) = √(1.8 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
    have hβs : 3.16 ≤ β * s := by nlinarith
    have h8 : 8 / (3 * β * s) ≤ 0.85 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have key : 8 * √π / 9 + 8 / (3 * β * s) + 48 / 5 ≤ 4 * π := by
      nlinarith [Real.pi_gt_d2]
    have eL : (1 / π) * (2 / (9 * T) * (4 * √π) + 1 / (8 * n) * 16) + 24 * (2 / 5) / (π * T) =
        (8 * √π / 9 + 8 / (3 * β * s) + 48 / 5) / (π * T) := by
      rw [hn', hTdef]; field_simp; ring
    have eR : 3 * β / s = 4 * π / (π * T) := by
      rw [hTdef]; field_simp <;> ring
    calc |cdf μn x - cdf (gaussianReal 0 1) x|
        ≤ (1 / π) * (∫ t in (-T)..T, ‖charFun μn t - charFun (gaussianReal 0 1) t‖ / |t|) +
            24 * (2 / 5) / (π * T) := hA'
      _ ≤ (1 / π) * (2 / (9 * T) * (4 * √π) + 1 / (8 * n) * 16) + 24 * (2 / 5) / (π * T) := by
          gcongr
      _ = (8 * √π / 9 + 8 / (3 * β * s) + 48 / 5) / (π * T) := eL
      _ ≤ 4 * π / (π * T) := by gcongr
      _ = 3 * β / s := eR.symm

end BerryEsseenFeller

end CharBoundLib

section SmoothingLib


open MeasureTheory ProbabilityTheory Filter Topology FourierTransform Complex
open scoped Real

namespace BerryEsseenFeller

/-- Fejér density `v_T(y) = (T/2π) sinc(Ty/2)^2`. -/
noncomputable def fej (T y : ℝ) : ℝ := T / (2 * π) * Real.sinc (T * y / 2) ^ 2

lemma fej_nonneg {T : ℝ} (hT : 0 < T) (y : ℝ) : 0 ≤ fej T y := by
  unfold fej; positivity

lemma fej_neg (T y : ℝ) : fej T (-y) = fej T y := by
  unfold fej; rw [show T * -y / 2 = -(T * y / 2) by ring, Real.sinc_neg]

lemma continuous_fej (T : ℝ) : Continuous (fej T) := by
  unfold fej
  exact continuous_const.mul ((Real.continuous_sinc.comp (by fun_prop)).pow 2)

lemma fej_le_const {T : ℝ} (hT : 0 < T) (y : ℝ) : fej T y ≤ T / (2 * π) := by
  unfold fej
  have h1 : Real.sinc (T * y / 2) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    have := Real.abs_sinc_le_one (T * y / 2)
    have h0 := abs_nonneg (Real.sinc (T * y / 2))
    nlinarith
  have h2 : 0 ≤ T / (2 * π) := by positivity
  calc T / (2 * π) * Real.sinc (T * y / 2) ^ 2 ≤ T / (2 * π) * 1 := by gcongr
    _ = T / (2 * π) := by ring

lemma fej_eq {T : ℝ} (hT : 0 < T) {y : ℝ} (hy : y ≠ 0) :
    fej T y = (1 - Real.cos (T * y)) / (π * T * y ^ 2) := by
  unfold fej
  have hu : T * y / 2 ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hu]
  have hc : Real.cos (T * y) = 1 - 2 * Real.sin (T * y / 2) ^ 2 := by
    rw [show T * y = 2 * (T * y / 2) by ring, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (T * y / 2)
    rw [show 2 * (T * y / 2) / 2 = T * y / 2 by ring]
    linarith
  rw [hc]
  have hT0 : T ≠ 0 := hT.ne'
  have hp : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

lemma fej_le_inv_sq {T : ℝ} (hT : 0 < T) {y : ℝ} (hy : y ≠ 0) :
    fej T y ≤ 2 / (π * T) * (y ^ 2)⁻¹ := by
  rw [fej_eq hT hy]
  have h1 : 1 - Real.cos (T * y) ≤ 2 := by linarith [Real.neg_one_le_cos (T * y)]
  have hpos : 0 < π * T * y ^ 2 := by positivity
  rw [show 2 / (π * T) * (y ^ 2)⁻¹ = 2 / (π * T * y ^ 2) by field_simp]
  exact div_le_div_of_nonneg_right h1 hpos.le

lemma fej_le_dom {T : ℝ} (hT : 0 < T) (y : ℝ) :
    fej T y ≤ (T / π + 4 / (π * T)) * (1 + y ^ 2)⁻¹ := by
  have hA : 0 < T / π := by positivity
  have hB : 0 < 4 / (π * T) := by positivity
  have h1 : 0 < 1 + y ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h1]
  rcases le_or_gt (y ^ 2) 1 with hy | hy
  · have h := fej_le_const hT y
    have hfe := fej_nonneg hT y
    have : T / (2 * π) * 2 = T / π := by ring
    nlinarith
  · have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
    have h := fej_le_inv_sq hT hy0
    have hfe := fej_nonneg hT y
    have hy2 : 0 < y ^ 2 := by positivity
    have : 2 / (π * T) * (y ^ 2)⁻¹ * (2 * y ^ 2) = 4 / (π * T) := by field_simp; ring
    nlinarith

lemma integrable_fej {T : ℝ} (hT : 0 < T) : Integrable (fej T) := by
  refine (integrable_inv_one_add_sq.const_mul (T / π + 4 / (π * T))).mono'
    (continuous_fej T).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fej_nonneg hT y)]
  exact fej_le_dom hT y

lemma integral_Ioi_inv_sq {c h : ℝ} (hc : 0 < c) (hh : 0 < h) :
    IntegrableOn (fun y : ℝ => c * (y ^ 2)⁻¹) (Set.Ioi h) ∧
      ∫ y in Set.Ioi h, c * (y ^ 2)⁻¹ = c / h := by
  have hderiv : ∀ x ∈ Set.Ici h, HasDerivAt (fun y : ℝ => -c * y⁻¹) (c * (x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := (lt_of_lt_of_le hh hx).ne'
    exact ((hasDerivAt_inv hx0).const_mul (-c)).congr_deriv (by ring)
  have hpos : ∀ x ∈ Set.Ioi h, 0 ≤ c * (x ^ 2)⁻¹ := fun x _ => by positivity
  have hlim : Tendsto (fun y : ℝ => -c * y⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (-c)
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim]
  field_simp
  ring

lemma fej_tail_le {T h : ℝ} (hT : 0 < T) (hh : 0 < h) :
    ∫ y in (Set.Icc (-h) h)ᶜ, fej T y ≤ 4 / (π * T * h) := by
  have hcompl : (Set.Icc (-h) h)ᶜ = Set.Iio (-h) ∪ Set.Ioi h := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
      not_and_or, not_le]
  have hdisj : Disjoint (Set.Iio (-h)) (Set.Ioi h) :=
    Set.disjoint_left.2 fun y h1 h2 => by
      simp only [Set.mem_Iio, Set.mem_Ioi] at h1 h2; linarith
  have hI := integrable_fej hT
  rw [hcompl, setIntegral_union hdisj measurableSet_Ioi hI.integrableOn hI.integrableOn]
  have hneg : ∫ y in Set.Iio (-h), fej T y = ∫ y in Set.Ioi h, fej T y := by
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi]
    simp_rw [fej_neg]
  rw [hneg]
  have hc : 0 < 2 / (π * T) := by positivity
  obtain ⟨hint, hval⟩ := integral_Ioi_inv_sq hc hh
  have hle : ∫ y in Set.Ioi h, fej T y ≤ ∫ y in Set.Ioi h, 2 / (π * T) * (y ^ 2)⁻¹ :=
    setIntegral_mono_on hI.integrableOn hint measurableSet_Ioi
      (fun y hy => fej_le_inv_sq hT (ne_of_gt (lt_trans hh hy)))
  rw [hval] at hle
  have : 2 / (π * T) / h + 2 / (π * T) / h = 4 / (π * T * h) := by field_simp; ring
  linarith

/-- The odd moment of the Fejér density on a symmetric interval vanishes. -/
lemma integral_Icc_mul_fej_odd (T h : ℝ) :
    ∫ y in Set.Icc (-h) h, y * fej T y = 0 := by
  rcases le_or_gt 0 h with hh | hh
  · have hle : -h ≤ h := by linarith
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    have h1 := intervalIntegral.integral_comp_neg (a := -h) (b := h) (fun y => y * fej T y)
    simp only [neg_neg, fej_neg, neg_mul, intervalIntegral.integral_neg] at h1
    linarith
  · rw [Set.Icc_eq_empty (by linarith)]
    simp

/-- Feller XVI.3 Lemma 1, core estimate: a function that is at least `a/2 + b y` on `[-h, h]` and
at least `-η` everywhere has Fejér average at least `a/2 - (a/2 + η) * tail`. -/
lemma lower_bound_smooth {T : ℝ} (hT : 0 < T) (hint1 : ∫ y, fej T y = 1) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume) {η a b h : ℝ} (hη : ∀ y, |f y| ≤ η)
    (hlow : ∀ y ∈ Set.Icc (-h) h, a / 2 + b * y ≤ f y) :
    a / 2 - (a / 2 + η) * (∫ y in (Set.Icc (-h) h)ᶜ, fej T y) ≤ ∫ y, f y * fej T y := by
  have hI := integrable_fej hT
  have hfI : Integrable (fun y => f y * fej T y) :=
    hI.bdd_mul hf (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hη y)
  have hms : MeasurableSet (Set.Icc (-h) h) := measurableSet_Icc
  rw [← integral_add_compl hms hfI]
  have hcont : Continuous fun y => (a / 2 + b * y) * fej T y := by
    have := continuous_fej T; fun_prop
  have hIcc : IntegrableOn (fun y => (a / 2 + b * y) * fej T y) (Set.Icc (-h) h) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have h1 : ∫ y in Set.Icc (-h) h, (a / 2 + b * y) * fej T y ≤
      ∫ y in Set.Icc (-h) h, f y * fej T y :=
    setIntegral_mono_on hIcc hfI.integrableOn hms
      (fun y hy => mul_le_mul_of_nonneg_right (hlow y hy) (fej_nonneg hT y))
  have h2 : ∫ y in (Set.Icc (-h) h)ᶜ, (-η) * fej T y ≤
      ∫ y in (Set.Icc (-h) h)ᶜ, f y * fej T y :=
    setIntegral_mono_on (hI.const_mul (-η)).integrableOn hfI.integrableOn hms.compl
      (fun y _ => mul_le_mul_of_nonneg_right (by linarith [neg_abs_le (f y), hη y])
        (fej_nonneg hT y))
  have hsplit : ∫ y in Set.Icc (-h) h, (a / 2 + b * y) * fej T y =
      a / 2 * (∫ y in Set.Icc (-h) h, fej T y) + b * ∫ y in Set.Icc (-h) h, y * fej T y := by
    have he : (fun y => (a / 2 + b * y) * fej T y) =
        fun y => a / 2 * fej T y + b * (y * fej T y) := by ext y; ring
    have hc2 : Continuous fun y => b * (y * fej T y) := by have := continuous_fej T; fun_prop
    rw [he, integral_add (hI.const_mul _).integrableOn
      (hc2.continuousOn.integrableOn_compact isCompact_Icc), integral_const_mul,
      integral_const_mul]
  rw [hsplit, integral_Icc_mul_fej_odd] at h1
  rw [integral_const_mul] at h2
  have htot := integral_add_compl hms hI
  rw [hint1] at htot
  have hq : ∫ y in Set.Icc (-h) h, fej T y = 1 - ∫ y in (Set.Icc (-h) h)ᶜ, fej T y := by
    linarith
  rw [hq] at h1
  linarith

/-- (A2) Fourier representation of the Fejér density. -/
lemma fej_eq_integral {T : ℝ} (hT : 0 < T) (y : ℝ) :
    fej T y = (1 / π) * ∫ z in (0 : ℝ)..T, (1 - z / T) * Real.cos (z * y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [mul_zero, Real.cos_zero, mul_one]
    have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 T := intervalIntegrable_const
    have h2 : IntervalIntegrable (fun z : ℝ => z / T) volume 0 T :=
      (continuous_id.div_const T).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const,
      intervalIntegral.integral_div, integral_id]
    unfold fej
    simp only [mul_zero, zero_div, Real.sinc_zero, one_pow, mul_one, smul_eq_mul, sub_zero]
    field_simp
    ring
  · have hT0 : T ≠ 0 := hT.ne'
    have hderiv : ∀ z ∈ Set.uIcc (0 : ℝ) T, HasDerivAt
        (fun z => (1 - z / T) * Real.sin (z * y) / y - Real.cos (z * y) / (T * y ^ 2))
        ((1 - z / T) * Real.cos (z * y)) z := by
      intro z _
      have h1 : HasDerivAt (fun z : ℝ => z * y) y z := by
        simpa using (hasDerivAt_id z).mul_const y
      have hs := (Real.hasDerivAt_sin (z * y)).comp z h1
      have hc := (Real.hasDerivAt_cos (z * y)).comp z h1
      have hl : HasDerivAt (fun z : ℝ => 1 - z / T) (-(1 / T)) z := by
        simpa using ((hasDerivAt_id z).div_const T).const_sub 1
      refine (((hl.mul hs).div_const y).sub (hc.div_const (T * y ^ 2))).congr_deriv ?_
      simp only [Function.comp_apply]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun z : ℝ => (1 - z / T) * Real.cos (z * y)).intervalIntegrable _ _),
      fej_eq hT hy]
    simp only [div_self hT0, sub_self, zero_mul, zero_div, zero_sub, Real.sin_zero, mul_zero,
      Real.cos_zero, zero_mul]
    field_simp
    ring

/-- Triangle function `(1 - |z|/T)_+`, the characteristic function of the Fejér law. -/
noncomputable def tri (T z : ℝ) : ℝ := max 0 (1 - |z| / T)

lemma continuous_tri (T : ℝ) : Continuous (tri T) := by
  unfold tri; fun_prop

lemma tri_neg (T z : ℝ) : tri T (-z) = tri T z := by
  unfold tri; rw [abs_neg]

lemma tri_eq_zero {T z : ℝ} (hT : 0 < T) (hz : T ≤ |z|) : tri T z = 0 := by
  unfold tri
  have : 1 - |z| / T ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hT]; linarith
  exact max_eq_left this

lemma tri_eq_of_mem {T z : ℝ} (hT : 0 < T) (hz : z ∈ Set.Icc 0 T) : tri T z = 1 - z / T := by
  unfold tri
  rw [abs_of_nonneg hz.1]
  apply max_eq_right
  rw [sub_nonneg, div_le_one hT]; exact hz.2

lemma exp_add_exp_neg (x : ℝ) :
    cexp (((-x : ℝ) : ℂ) * I) + cexp ((x : ℂ) * I) = ((2 * Real.cos x : ℝ) : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

lemma fourier_tri {T : ℝ} (hT : 0 < T) (w : ℝ) :
    𝓕 (fun z => (tri T z : ℂ)) w = ((2 * π * fej T (2 * π * w) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set g : ℝ → ℂ := fun v => cexp (↑(-2 * π * v * w) * I) • (tri T v : ℂ) with hg
  have hgc : Continuous g := by
    rw [hg]
    have := continuous_tri T
    fun_prop
  have hsupp : ∫ v, g v = ∫ v in (-T)..T, g v := by
    rw [intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro z hz
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hz
    have : T ≤ |z| := by
      rcases hz with hz | hz
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [hg, tri_eq_zero hT this]
  rw [hsupp, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hgc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)]
  have hneg : ∫ v in (-T)..0, g v = ∫ v in (0 : ℝ)..T, g (-v) := by
    rw [intervalIntegral.integral_comp_neg]; simp
  have hi1 : IntervalIntegrable (fun v => g (-v)) volume 0 T :=
    (hgc.comp continuous_neg).intervalIntegrable _ _
  rw [hneg, ← intervalIntegral.integral_add hi1 (hgc.intervalIntegrable _ _)]
  have hpt : ∀ z ∈ Set.uIcc (0 : ℝ) T, g (-z) + g z =
      (((2 * ((1 - z / T) * Real.cos (z * (2 * π * w))) : ℝ)) : ℂ) := by
    intro z hz
    rw [Set.uIcc_of_le hT.le] at hz
    simp only [hg, smul_eq_mul, tri_neg]
    rw [tri_eq_of_mem hT hz, show (-2 * π * -z * w : ℝ) = -(-(z * (2 * π * w))) by ring,
      show (-2 * π * z * w : ℝ) = -(z * (2 * π * w)) by ring, ← add_mul,
      exp_add_exp_neg, Real.cos_neg]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_const_mul, fej_eq_integral hT]
  congr 1
  rw [← mul_assoc, show 2 * π * (1 / π) = (2 : ℝ) by field_simp]

lemma integral_fej {T : ℝ} (hT : 0 < T) : ∫ y, fej T y = 1 := by
  set ω : ℝ → ℂ := fun z => (tri T z : ℂ) with hω
  have hωc : Continuous ω := by rw [hω]; have := continuous_tri T; fun_prop
  have hsupp : HasCompactSupport ω := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun z hz => ?_
    simp only [Set.mem_Icc, not_and_or, not_le] at hz
    have : T ≤ |z| := by
      rcases hz with hz | hz
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [hω, tri_eq_zero hT this]
  have hωi : Integrable ω := hωc.integrable_of_hasCompactSupport hsupp
  have hF : 𝓕 ω = fun w => ((2 * π * fej T (2 * π * w) : ℝ) : ℂ) := by
    ext w; exact fourier_tri hT w
  have hFi : Integrable (𝓕 ω) := by
    rw [hF]
    have h1 : Integrable fun w : ℝ => fej T (2 * π * w) :=
      (integrable_fej hT).comp_mul_left' (by positivity)
    exact (h1.const_mul (2 * π)).ofReal
  have hinv := hωi.fourierInv_fourier_eq hFi hωc.continuousAt (v := 0)
  rw [Real.fourierInv_eq', hF] at hinv
  simp only [inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul] at hinv
  rw [integral_complex_ofReal] at hinv
  have h0 : ω 0 = 1 := by simp [hω, tri]
  rw [h0] at hinv
  have hreal : ∫ w, 2 * π * fej T (2 * π * w) = 1 := by exact_mod_cast hinv
  rw [integral_const_mul, Measure.integral_comp_mul_left] at hreal
  have hp : 0 < 2 * π := by positivity
  rw [abs_of_pos (inv_pos.2 hp), smul_eq_mul] at hreal
  field_simp at hreal
  linarith

lemma tri_nonneg (T z : ℝ) : 0 ≤ tri T z := le_max_left _ _

lemma tri_le_one {T : ℝ} (hT : 0 < T) (z : ℝ) : tri T z ≤ 1 := by
  unfold tri
  apply max_le zero_le_one
  have : 0 ≤ |z| / T := by positivity
  linarith

/-- `S_T(w) = (1/π) ∫_0^T tri(z) w sinc(zw) dz`, so that `∫_{-∞}^w fej = 1/2 + S_T(w)`. -/
noncomputable def Sfn (T w : ℝ) : ℝ :=
  (1 / π) * ∫ z in (0 : ℝ)..T, tri T z * (w * Real.sinc (z * w))

lemma integral_cos_mul (z w : ℝ) :
    ∫ y in (0 : ℝ)..w, Real.cos (z * y) = w * Real.sinc (z * w) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [intervalIntegral.integral_comp_mul_left Real.cos hz, integral_cos]
    simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul]
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hz hw)]
      field_simp

lemma integral_zero_to_fej {T : ℝ} (hT : 0 < T) (w : ℝ) :
    ∫ y in (0 : ℝ)..w, fej T y = Sfn T w := by
  have h1 : ∀ y, fej T y = (1 / π) * ∫ z in (0 : ℝ)..T, tri T z * Real.cos (z * y) := by
    intro y
    rw [fej_eq_integral hT]
    congr 1
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [Set.uIcc_of_le hT.le] at hz
    simp only [tri_eq_of_mem hT hz]
  simp_rw [h1]
  have hc : Continuous (Function.uncurry fun (y z : ℝ) => tri T z * Real.cos (z * y)) := by
    have := continuous_tri T
    exact (this.comp continuous_snd).mul
      (Real.continuous_cos.comp (continuous_snd.mul continuous_fst))
  rw [intervalIntegral.integral_const_mul, intervalIntegral_intervalIntegral_swap
    ((hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc))]
  unfold Sfn
  congr 1
  refine intervalIntegral.integral_congr fun z _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_cos_mul]

lemma integral_Iic_fej {T : ℝ} (hT : 0 < T) (w : ℝ) :
    ∫ y in Set.Iic w, fej T y = 1 / 2 + Sfn T w := by
  have hI := integrable_fej hT
  have h0 : ∫ y in Set.Iic 0, fej T y = 1 / 2 := by
    have htot := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hI
    rw [Set.compl_Iic, integral_fej hT] at htot
    have hs := integral_comp_neg_Iic 0 (fej T)
    rw [neg_zero] at hs
    simp_rw [fej_neg] at hs
    linarith
  have h2 := intervalIntegral.integral_Iic_sub_Iic hI.integrableOn hI.integrableOn
    (a := 0) (b := w)
  rw [integral_zero_to_fej hT] at h2
  linarith

lemma Fc_nonneg {T : ℝ} (hT : 0 < T) (w : ℝ) : 0 ≤ ∫ y in Set.Iic w, fej T y :=
  setIntegral_nonneg measurableSet_Iic fun y _ => fej_nonneg hT y

lemma Fc_le_one {T : ℝ} (hT : 0 < T) (w : ℝ) : ∫ y in Set.Iic w, fej T y ≤ 1 := by
  rw [← integral_fej hT]
  exact setIntegral_le_integral (integrable_fej hT) (Eventually.of_forall (fej_nonneg hT))

lemma Fc_mono {T : ℝ} (hT : 0 < T) : Monotone fun w => ∫ y in Set.Iic w, fej T y := by
  intro a b hab
  exact setIntegral_mono_set (integrable_fej hT).integrableOn
    (Eventually.of_forall (fej_nonneg hT)) (Eventually.of_forall (Set.Iic_subset_Iic.2 hab))

lemma integrable_Fc_comp {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    Integrable (fun s => ∫ y in Set.Iic (x - s), fej T y) μ := by
  have hm : Measurable fun s : ℝ => ∫ y in Set.Iic (x - s), fej T y :=
    (Fc_mono hT).measurable.comp (measurable_const.sub measurable_id)
  refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Fc_nonneg hT _)]
  exact Fc_le_one hT _

lemma integral_cdf_mul_fej {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) : ∫ y, cdf μ (x - y) * fej T y = ∫ s, (∫ y in Set.Iic (x - s), fej T y) ∂μ := by
  set F : ℝ → ℝ → ℝ := fun y s => if s + y ≤ x then fej T y else 0 with hF
  have h1 : ∀ y, ∫ s, F y s ∂μ = cdf μ (x - y) * fej T y := by
    intro y
    have : F y = Set.indicator (Set.Iic (x - y)) (fun _ => fej T y) := by
      ext s; simp [hF, Set.indicator_apply, le_sub_iff_add_le]
    rw [this, integral_indicator_const _ measurableSet_Iic, cdf_eq_real, smul_eq_mul]
  have h2 : ∀ s, ∫ y, F y s = ∫ y in Set.Iic (x - s), fej T y := by
    intro s
    have : (fun y => F y s) = Set.indicator (Set.Iic (x - s)) (fej T) := by
      ext y; simp [hF, Set.indicator_apply, le_sub_iff_add_le, add_comm]
    rw [this, integral_indicator measurableSet_Iic]
  have hmeas : Measurable (Function.uncurry F) := by
    refine Measurable.ite ?_ ((continuous_fej T).measurable.comp measurable_fst) measurable_const
    exact measurableSet_le (measurable_snd.add measurable_fst) measurable_const
  have hint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod μ) := by
    refine ((integrable_fej hT).comp_fst μ).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hF]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (fej_nonneg hT _)]
    · simp [fej_nonneg hT]
  simp_rw [← h1, ← h2]
  exact integral_integral_swap hint

lemma integral_Sfn_comp_eq {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) : ∫ s, Sfn T (x - s) ∂μ = ∫ s, (∫ y in Set.Iic (x - s), fej T y) ∂μ - 1 / 2 := by
  have : (fun s => Sfn T (x - s)) = fun s => (∫ y in Set.Iic (x - s), fej T y) - 1 / 2 := by
    ext s; rw [integral_Iic_fej hT]; ring
  rw [this, integral_sub (integrable_Fc_comp hT μ x) (integrable_const _)]
  simp

/-- The Fejér-smoothed difference of distribution functions is the difference of `S_T` averages. -/
lemma smoothed_eq {T : ℝ} (hT : 0 < T) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (x : ℝ) :
    ∫ y, (cdf μ (x - y) - cdf ν (x - y)) * fej T y =
      ∫ s, Sfn T (x - s) ∂μ - ∫ s, Sfn T (x - s) ∂ν := by
  have hI := integrable_fej hT
  have hb : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      Integrable (fun y => cdf ρ (x - y) * fej T y) := by
    intro ρ _
    refine hI.bdd_mul (c := 1)
      (((cdf ρ).mono.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (cdf_nonneg _ _)]
    exact cdf_le_one _ _
  simp_rw [sub_mul]
  rw [integral_sub (hb μ) (hb ν), integral_cdf_mul_fej hT, integral_cdf_mul_fej hT,
    integral_Sfn_comp_eq hT, integral_Sfn_comp_eq hT]
  ring

lemma integrable_kernel {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (x : ℝ) :
    Integrable (Function.uncurry fun (z s : ℝ) => tri T z * ((x - s) * Real.sinc (z * (x - s))))
      ((volume.restrict (Set.uIoc (0 : ℝ) T)).prod μ) := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) T)) := by
    rw [Set.uIoc_of_le hT.le]; infer_instance
  have hg : Integrable (fun s : ℝ => |x| + |s|) μ :=
    (integrable_const _).add (by simpa using hμ.abs)
  have hc : Continuous (Function.uncurry fun (z s : ℝ) =>
      tri T z * ((x - s) * Real.sinc (z * (x - s)))) := by
    have := continuous_tri T
    exact (this.comp continuous_fst).mul ((continuous_const.sub continuous_snd).mul
      (Real.continuous_sinc.comp (continuous_fst.mul (continuous_const.sub continuous_snd))))
  refine (hg.comp_snd _).mono' hc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
  have h1 := Real.abs_sinc_le_one (p.1 * (x - p.2))
  have h2 : |tri T p.1| ≤ 1 := by
    rw [abs_of_nonneg (tri_nonneg _ _)]; exact tri_le_one hT _
  have h3 : |x - p.2| ≤ |x| + |p.2| := abs_sub _ _
  have h4 := abs_nonneg (x - p.2)
  have h5 := abs_nonneg (Real.sinc (p.1 * (x - p.2)))
  have h6 := abs_nonneg (tri T p.1)
  calc |tri T p.1| * (|x - p.2| * |Real.sinc (p.1 * (x - p.2))|)
      ≤ 1 * (|x - p.2| * 1) := by gcongr
    _ ≤ |x| + |p.2| := by linarith

lemma integral_Sfn {T : ℝ} (hT : 0 < T) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (x : ℝ) :
    ∫ s, Sfn T (x - s) ∂μ =
      (1 / π) * ∫ z in (0 : ℝ)..T, tri T z * ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ := by
  unfold Sfn
  rw [integral_const_mul, ← intervalIntegral_integral_swap (integrable_kernel hT μ hμ x)]
  congr 1
  refine intervalIntegral.integral_congr fun z _ => ?_
  rw [integral_const_mul]

lemma sinc_moment_eq (x z s : ℝ) (hz : z ≠ 0) :
    (x - s) * Real.sinc (z * (x - s)) = Real.sin (z * (x - s)) / z := by
  rcases eq_or_ne (x - s) 0 with h | h
  · rw [h]; simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hz h)]
    field_simp

lemma integral_sin_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (x z : ℝ) :
    ∫ s, Real.sin (z * (x - s)) ∂μ = (cexp ((z * x : ℝ) * I) * charFun μ (-z)).im := by
  have hint : Integrable (fun s : ℝ => cexp (((z * (x - s) : ℝ) : ℂ) * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Eventually.of_forall fun s => ?_)
    rw [Complex.norm_exp_ofReal_mul_I]
  have h1 : (fun s : ℝ => Real.sin (z * (x - s))) =
      fun s => RCLike.im (cexp (((z * (x - s) : ℝ) : ℂ) * I)) := by
    ext s; change _ = Complex.im _; rw [Complex.exp_ofReal_mul_I_im]
  have h2 : (fun s : ℝ => cexp (((z * (x - s) : ℝ) : ℂ) * I)) =
      fun s : ℝ => cexp (((z * x : ℝ) : ℂ) * I) * cexp (((-z : ℝ) : ℂ) * (s : ℂ) * I) := by
    ext s
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, integral_im hint, h2, integral_const_mul, charFun_apply_real]
  rfl

lemma sinc_moment_diff (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (x z : ℝ) (hz : z ≠ 0) :
    |∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ - ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ν| ≤
      ‖charFun μ z - charFun ν z‖ / |z| := by
  simp_rw [sinc_moment_eq x z _ hz]
  rw [integral_div, integral_div, integral_sin_eq, integral_sin_eq, ← sub_div, abs_div]
  gcongr
  rw [← Complex.sub_im, ← mul_sub]
  refine (Complex.abs_im_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, charFun_neg, charFun_neg, ← map_sub,
    Complex.norm_conj]

set_option maxHeartbeats 1000000 in
lemma smoothed_bound {T : ℝ} (hT : 0 < T) (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable id μ) (hν : Integrable id ν)
    (hint : IntegrableOn (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) (Set.Icc (-T) T))
    (x : ℝ) :
    |∫ y, (cdf μ (x - y) - cdf ν (x - y)) * fej T y| ≤
      (1 / (2 * π)) * ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| := by
  set g : ℝ → ℝ := fun t => ‖charFun μ t - charFun ν t‖ / |t| with hg
  have hJ : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ], Integrable id ρ →
      IntervalIntegrable (fun z => tri T z * ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ρ)
        volume 0 T := by
    intro ρ _ hρ
    have := (integrable_kernel hT ρ hρ x).integral_prod_left
    rw [intervalIntegrable_iff]
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry]
    rw [integral_const_mul]
  rw [smoothed_eq hT, integral_Sfn hT μ hμ, integral_Sfn hT ν hν, ← mul_sub,
    ← intervalIntegral.integral_sub (hJ μ hμ) (hJ ν hν)]
  have hgi : IntervalIntegrable g volume 0 T :=
    (hint.mono_set (by
      rw [Set.uIcc_of_le hT.le]; exact Set.Icc_subset_Icc (by linarith) le_rfl)).intervalIntegrable
  have hgi' : IntervalIntegrable g volume (-T) 0 :=
    (hint.mono_set (by
      rw [Set.uIcc_of_le (by linarith)]; exact Set.Icc_subset_Icc le_rfl hT.le)).intervalIntegrable
  have hbound : ‖∫ z in (0 : ℝ)..T, (tri T z * ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ -
      tri T z * ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ν)‖ ≤ ∫ z in (0 : ℝ)..T, g z := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT.le
      (Eventually.of_forall fun z hz => ?_) hgi
    have hz0 : z ≠ 0 := (ne_of_gt hz.1)
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (tri_nonneg _ _)]
    have h1 := sinc_moment_diff μ ν x z hz0
    have h2 := tri_le_one hT z
    have h3 := abs_nonneg (∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ -
      ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ν)
    have h4 := tri_nonneg T z
    calc tri T z * |∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ -
          ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ν|
        ≤ 1 * |∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ -
          ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ν| := by gcongr
      _ ≤ g z := by rw [one_mul]; exact h1
  have heven : ∫ t in (-T)..T, g t = 2 * ∫ z in (0 : ℝ)..T, g z := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hgi' hgi]
    have : ∫ t in (-T)..0, g t = ∫ z in (0 : ℝ)..T, g z := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := T) g
      rw [neg_zero] at h
      rw [← h]
      refine intervalIntegral.integral_congr fun z _ => ?_
      simp only [hg, abs_neg, charFun_neg, ← map_sub, Complex.norm_conj]
    rw [this]; ring
  rw [heven, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  rw [Real.norm_eq_abs] at hbound
  have hp : 0 < π := Real.pi_pos
  calc 1 / π * |∫ z in (0 : ℝ)..T, (tri T z * ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂μ -
        tri T z * ∫ s, (x - s) * Real.sinc (z * (x - s)) ∂ν)|
      ≤ 1 / π * ∫ z in (0 : ℝ)..T, g z := by gcongr
    _ = 1 / (2 * π) * (2 * ∫ z in (0 : ℝ)..T, g z) := by field_simp

lemma lip_pos {ν : Measure ℝ} [IsProbabilityMeasure ν] {m : ℝ}
    (hlip : ∀ x y, x ≤ y → cdf ν y - cdf ν x ≤ m * (y - x)) : 0 < m := by
  by_contra hm
  rw [not_lt] at hm
  have h1 : (1 : ℝ) ≤ cdf ν 0 := by
    refine le_of_tendsto (tendsto_cdf_atTop ν) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    have := hlip 0 y hy
    nlinarith
  have h2 : cdf ν 0 ≤ 0 := by
    refine ge_of_tendsto (tendsto_cdf_atBot ν) ?_
    filter_upwards [eventually_le_atBot (0 : ℝ)] with y hy
    have := hlip y 0 hy
    nlinarith
  linarith

/-- Final algebra of Feller's Lemma 1. -/
lemma lemma1_algebra {K c η a p : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hlt : K + 3 * c < η)
    (ha : a = (η + K + 3 * c) / 2) (hp : a * p ≤ c) (hη : 0 ≤ a / 2 + η)
    (hmain : a / 2 - (a / 2 + η) * p ≤ K / 2) : False := by
  set δ := (η - K - 3 * c) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hηe : η = K + 3 * c + 2 * δ := by rw [hδ]; ring
  have hae : a = K + 3 * c + δ := by rw [ha, hηe]; ring
  have hapos : 0 < a := by rw [hae]; linarith
  have h1 : a * (a / 2 - (a / 2 + η) * p) ≤ a * (K / 2) :=
    mul_le_mul_of_nonneg_left hmain hapos.le
  have h2 : (a / 2 + η) * (a * p) ≤ (a / 2 + η) * c := mul_le_mul_of_nonneg_left hp hη
  have h3 : a * a / 2 - (a / 2 + η) * c ≤ a * K / 2 := by nlinarith
  rw [hae, hηe] at h3
  nlinarith [mul_pos hδ0 (by linarith : 0 < c + K + δ)]

set_option maxHeartbeats 1000000 in
/-- **Esseen's smoothing inequality** (Feller XVI.3 Lemma 2). -/
theorem esseen_smoothing : ∀ (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
    Integrable id μ → Integrable id ν →
    ∀ {m T : ℝ}, 0 < T → (∀ x y, x ≤ y → cdf ν y - cdf ν x ≤ m * (y - x)) →
    MeasureTheory.IntegrableOn (fun t : ℝ => ‖charFun μ t - charFun ν t‖ / |t|) (Set.Icc (-T) T) →
    ∀ x : ℝ, |cdf μ x - cdf ν x| ≤
      (1 / π) * (∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t|) + 24 * m / (π * T) := by
  intro μ ν _ _ hμ hν m T hT hlip hint x
  have hm := lip_pos hlip
  set K := (1 / π) * ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have : 0 ≤ ∫ t in (-T)..T, ‖charFun μ t - charFun ν t‖ / |t| :=
      intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
    positivity
  have hsm : ∀ t, |∫ y, (cdf μ (t - y) - cdf ν (t - y)) * fej T y| ≤ K / 2 := by
    intro t
    refine (smoothed_bound hT μ ν hμ hν hint t).trans (le_of_eq ?_)
    rw [hKdef]; field_simp
  set Δ : ℝ → ℝ := fun u => cdf μ u - cdf ν u with hΔ
  have hΔ1 : ∀ u, |Δ u| ≤ 1 := by
    intro u
    rw [hΔ, abs_le]
    constructor <;> linarith [cdf_nonneg μ u, cdf_le_one μ u, cdf_nonneg ν u, cdf_le_one ν u]
  have hbdd : BddAbove (Set.range fun u => |Δ u|) := ⟨1, by rintro _ ⟨u, rfl⟩; exact hΔ1 u⟩
  set η := sSup (Set.range fun u => |Δ u|) with hηdef
  have hle : ∀ u, |Δ u| ≤ η := fun u => le_csSup hbdd ⟨u, rfl⟩
  set c := 8 * m / (π * T) with hc
  have hc0 : 0 < c := by positivity
  have hmeasΔ : ∀ t : ℝ, Measurable fun y : ℝ => Δ (t - y) := by
    intro t
    exact ((cdf μ).mono.measurable.comp (measurable_const.sub measurable_id)).sub
      ((cdf ν).mono.measurable.comp (measurable_const.sub measurable_id))
  have hmain : η ≤ K + 3 * c := by
    by_contra hcon
    rw [not_le] at hcon
    set a := (η + K + 3 * c) / 2 with ha
    have hη0 : 0 ≤ η := le_trans (abs_nonneg _) (hle 0)
    have hapos : 0 < a := by rw [ha]; linarith
    have halt : a < η := by rw [ha]; linarith
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) halt
    simp only at hu
    set h := a / (2 * m) with hh
    have hh0 : 0 < h := by positivity
    have hmh : m * h = a / 2 := by rw [hh]; field_simp
    have htail := fej_tail_le hT hh0
    have hp : a * (∫ y in (Set.Icc (-h) h)ᶜ, fej T y) ≤ c := by
      have : 4 / (π * T * h) = c / a := by rw [hh, hc]; field_simp; ring
      rw [this] at htail
      have := mul_le_mul_of_nonneg_left htail hapos.le
      rwa [mul_div_cancel₀ _ hapos.ne'] at this
    have hηa : 0 ≤ a / 2 + η := by linarith
    rcases le_or_gt 0 (Δ u) with hpos | hneg
    · -- positive excursion: look at `t = u + h`
      rw [abs_of_nonneg hpos] at hu
      have hlow : ∀ y ∈ Set.Icc (-h) h, a / 2 + m * y ≤ Δ (u + h - y) := by
        intro y hy
        have hs : 0 ≤ h - y := by linarith [hy.2]
        have h1 : cdf μ u ≤ cdf μ (u + h - y) := (cdf μ).mono (by linarith)
        have h2 := hlip u (u + h - y) (by linarith)
        simp only [hΔ]
        nlinarith
      have hlb := lower_bound_smooth hT (integral_fej hT) (hmeasΔ (u + h)).aestronglyMeasurable
        (fun y => hle _) hlow
      have hup := (le_abs_self _).trans (hsm (u + h))
      exact lemma1_algebra hK0 hc0 hcon ha hp hηa (hlb.trans hup)
    · -- negative excursion: look at `t = u - h`
      rw [abs_of_neg hneg] at hu
      have hlow : ∀ y ∈ Set.Icc (-h) h, a / 2 + (-m) * y ≤ -Δ (u - h - y) := by
        intro y hy
        have hs : 0 ≤ h + y := by linarith [hy.1]
        have h1 : cdf μ (u - h - y) ≤ cdf μ u := (cdf μ).mono (by linarith)
        have h2 := hlip (u - h - y) u (by linarith)
        simp only [hΔ]
        nlinarith
      have hlb := lower_bound_smooth hT (integral_fej hT) (f := fun y => -Δ (u - h - y))
        ((hmeasΔ (u - h)).neg.aestronglyMeasurable)
        (fun y => by show |-Δ (u - h - y)| ≤ η; rw [abs_neg]; exact hle _) hlow
      have heq : ∫ y, -Δ (u - h - y) * fej T y =
          -∫ y, (cdf μ (u - h - y) - cdf ν (u - h - y)) * fej T y := by
        rw [← integral_neg]; simp only [hΔ, neg_mul]
      rw [heq] at hlb
      have hup := (neg_le_abs _).trans (hsm (u - h))
      exact lemma1_algebra hK0 hc0 hcon ha hp hηa (hlb.trans hup)
  have h3c : 3 * c = 24 * m / (π * T) := by rw [hc]; ring
  calc |cdf μ x - cdf ν x| = |Δ x| := rfl
    _ ≤ η := hle x
    _ ≤ K + 3 * c := hmain
    _ = _ := by rw [h3c]

end BerryEsseenFeller

end SmoothingLib

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {σ ρ : ℝ} (hσ : 0 < σ) (h3 : Integrable (fun ω => |X 0 ω| ^ 3) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = σ ^ 2)
    (hρ : ∫ ω, |X 0 ω| ^ 3 ∂P = ρ) (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |cdf (P.map (fun ω => (∑ i ∈ Finset.range n, X i ω) / (σ * √(n : ℝ)))) x
        - cdf (gaussianReal 0 1) x| ≤ 3 * ρ / (σ ^ 3 * √(n : ℝ)) := by
  exact BerryEsseenFeller.berry_esseen_of_smoothing BerryEsseenFeller.esseen_smoothing hindep
    hident hσ h3 hmean hvar hρ n hn x
