-- Prove2me | solution 1 for CouplingHMC.Exact.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T21:31:03.446207+00:00
-- url     : https://prove2.me/submissions/966e7bef-8665-40a3-b31d-e0b7657c48e8

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory CouplingHMC.Exact
open scoped InnerProductSpace ENNReal

namespace HMCF

lemma g_cont (a R1 : ℝ) : Continuous (fun s : ℝ => Real.exp (-(a * min s R1))) :=
  Real.continuous_exp.comp ((continuous_const.mul (continuous_id.min continuous_const)).neg)

lemma g_anti {a R1 : ℝ} (ha : 0 < a) {s t : ℝ} (hst : s ≤ t) :
    Real.exp (-(a * min t R1)) ≤ Real.exp (-(a * min s R1)) := by
  apply Real.exp_le_exp.2
  have : min s R1 ≤ min t R1 := min_le_min_right R1 hst
  nlinarith

lemma g_pos (a R1 s : ℝ) : 0 < Real.exp (-(a * min s R1)) := Real.exp_pos _

lemma fC_sub (a R1 r s : ℝ) :
    fConc a R1 s - fConc a R1 r = ∫ t in r..s, Real.exp (-(a * min t R1)) := by
  unfold fConc
  exact intervalIntegral.integral_interval_sub_left ((g_cont a R1).intervalIntegrable _ _)
    ((g_cont a R1).intervalIntegrable _ _)

/-- concavity: `f(s) - f(r) ≤ f'(r) (s - r)`. -/
lemma fC_concave {a R1 : ℝ} (ha : 0 < a) (r s : ℝ) :
    fConc a R1 s - fConc a R1 r ≤ Real.exp (-(a * min r R1)) * (s - r) := by
  rw [fC_sub]
  rcases le_total r s with h | h
  · have := intervalIntegral.integral_mono_on h ((g_cont a R1).intervalIntegrable r s)
      (continuous_const.intervalIntegrable (μ := volume) r s)
      (fun t ht => g_anti (R1 := R1) ha ht.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · rw [intervalIntegral.integral_symm]
    have := intervalIntegral.integral_mono_on h
      (continuous_const.intervalIntegrable (μ := volume) s r)
      ((g_cont a R1).intervalIntegrable s r)
      (fun t ht => g_anti (R1 := R1) ha ht.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith

lemma fC_lower {a R1 : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r) :
    r * Real.exp (-(a * min r R1)) ≤ fConc a R1 r := by
  unfold fConc
  have := intervalIntegral.integral_mono_on hr
    (continuous_const.intervalIntegrable (μ := volume) 0 r)
    ((g_cont a R1).intervalIntegrable 0 r)
    (fun t ht => g_anti (R1 := R1) ha ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma fC_nonneg {a R1 : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ fConc a R1 r :=
  le_trans (mul_nonneg hr (g_pos a R1 r).le) (fC_lower ha hr)

lemma fC_le_self {a R1 : ℝ} (ha : 0 < a) (hR : 0 ≤ R1) {r : ℝ} (hr : 0 ≤ r) :
    fConc a R1 r ≤ r := by
  unfold fConc
  have := intervalIntegral.integral_mono_on hr
    ((g_cont a R1).intervalIntegrable 0 r)
    (continuous_const.intervalIntegrable (μ := volume) 0 r)
    (fun t ht => (by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ min t R1 := le_min ht.1 hR
      nlinarith : Real.exp (-(a * min t R1)) ≤ 1))
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

lemma fC_explicit {a R1 : ℝ} (ha : 0 < a) (hR : 0 ≤ R1) {r : ℝ} (hr : r ≤ R1) :
    fConc a R1 r = (1 - Real.exp (-(a * r))) / a := by
  unfold fConc
  have h1 : ∫ s in (0:ℝ)..r, Real.exp (-(a * min s R1)) = ∫ s in (0:ℝ)..r, Real.exp (-(a * s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have : s ≤ R1 := le_trans hs.2 (max_le hR hr)
    simp only [min_eq_left this]
  rw [h1]
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) r,
      HasDerivAt (fun s : ℝ => -Real.exp (-(a * s)) / a) (Real.exp (-(a * x))) x := by
    intro x _
    have h0 : HasDerivAt (fun s : ℝ => a * s) a x := by
      simpa using (hasDerivAt_id x).const_mul a
    have h := ((h0.fun_neg).exp.fun_neg).div_const a
    have ha' := ha.ne'
    exact h.congr_deriv (by field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).intervalIntegrable _ _)]
  simp only [mul_zero, neg_zero, Real.exp_zero]
  ring

lemma fC_tail {a R1 : ℝ} {r : ℝ} (h : R1 ≤ r) :
    fConc a R1 r = fConc a R1 R1 + (r - R1) * Real.exp (-(a * R1)) := by
  have h1 := fC_sub a R1 R1 r
  have h2 : ∫ t in R1..r, Real.exp (-(a * min t R1)) = ∫ t in R1..r, Real.exp (-(a * R1)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have : R1 ≤ t := by
      have := ht.1
      rwa [min_eq_left h] at this
    simp only [min_eq_right this]
  rw [h2, intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith

/-- convexity bound: for `0 ≤ r ≤ r0 ≤ R1`, `f(r) · (a r0) ≤ r f'(r) e^{a r0}`. -/
lemma fC_upper {a R1 : ℝ} (ha : 0 < a) (hR : 0 ≤ R1) {r r0 : ℝ} (hr0 : 0 < r0) (hr0R : r0 ≤ R1)
    (hr : 0 ≤ r) (hrr0 : r ≤ r0) :
    fConc a R1 r * (a * r0) ≤ r * Real.exp (-(a * min r R1)) * Real.exp (a * r0) := by
  have hrR : r ≤ R1 := le_trans hrr0 hr0R
  rw [fC_explicit ha hR hrR, min_eq_left hrR]
  set θ := r / r0 with hθ
  have hθ0 : 0 ≤ θ := div_nonneg hr hr0.le
  have hθ1 : θ ≤ 1 := (div_le_one hr0).2 hrr0
  have hconv := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (a * r0)) (sub_nonneg.2 hθ1) hθ0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hs : θ * (a * r0) = a * r := by rw [hθ]; field_simp
  rw [hs] at hconv
  have he : Real.exp (-(a * r)) * Real.exp (a * r) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(a * r))
  have hA := Real.exp_pos (a * r0)
  -- (1 - e^{-s}) / a * (a r0) = (1 - e^{-s}) r0
  have key : (1 - Real.exp (-(a * r))) * r0 ≤ r * Real.exp (-(a * r)) * Real.exp (a * r0) := by
    -- e^{s} - 1 ≤ θ (e^A - 1) ≤ θ e^A, multiply by e^{-s} r0
    have h3 : (Real.exp (a * r) - 1) * r0 ≤ r * Real.exp (a * r0) := by
      have : (Real.exp (a * r) - 1) ≤ θ * Real.exp (a * r0) := by nlinarith
      have h4 : θ * Real.exp (a * r0) * r0 = r * Real.exp (a * r0) := by
        rw [hθ]; field_simp
      nlinarith
    have h5 : (1 - Real.exp (-(a * r))) * r0 =
        Real.exp (-(a * r)) * ((Real.exp (a * r) - 1) * r0) := by
      nlinarith
    rw [h5]
    have := mul_le_mul_of_nonneg_left h3 hpos.le
    linarith
  have : (1 - Real.exp (-(a * r))) / a * (a * r0) = (1 - Real.exp (-(a * r))) * r0 := by
    field_simp
  rw [this]
  exact key

lemma fC_upper_global {a R1 : ℝ} (ha : 0 < a) (hR1 : 0 < R1) {r : ℝ} (hr : 0 ≤ r) :
    fConc a R1 r * (a * R1) ≤ r * Real.exp (-(a * min r R1)) * Real.exp (a * R1) := by
  rcases le_total r R1 with h | h
  · exact fC_upper ha hR1.le hR1 le_rfl hr h
  · have hb := fC_upper ha hR1.le (r := R1) (r0 := R1) hR1 le_rfl hR1.le le_rfl
    rw [min_self] at hb
    have he : Real.exp (-(a * R1)) * Real.exp (a * R1) = 1 := by
      rw [← Real.exp_add]; simp
    rw [mul_assoc, he, mul_one] at hb
    rw [fC_tail h, min_eq_right h, mul_assoc, he, mul_one]
    have hA : a * R1 * Real.exp (-(a * R1)) ≤ 1 := by
      have := Real.add_one_le_exp (a * R1)
      have hp := Real.exp_pos (-(a * R1))
      nlinarith
    nlinarith

/-- the step bound used for rejected moves: for `0 ≤ r ≤ R1`, `f(s) - f(r) ≤ a⁻¹ f'(r) + f'(R1) (s - R1)_+`. -/
lemma fC_step {a R1 : ℝ} (ha : 0 < a) (hR : 0 ≤ R1) {r : ℝ} (hrR : r ≤ R1) (s : ℝ) :
    fConc a R1 s - fConc a R1 r ≤
      a⁻¹ * Real.exp (-(a * min r R1)) + Real.exp (-(a * R1)) * max (s - R1) 0 := by
  have hb : ∀ s', s' ≤ R1 → fConc a R1 s' - fConc a R1 r ≤ a⁻¹ * Real.exp (-(a * min r R1)) := by
    intro s' hs'
    rcases le_total s' r with h | h
    · have := fC_concave (R1 := R1) ha r s'
      have : Real.exp (-(a * min r R1)) * (s' - r) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (g_pos a R1 r).le (by linarith)
      have : 0 ≤ a⁻¹ * Real.exp (-(a * min r R1)) := mul_nonneg (inv_nonneg.2 ha.le) (g_pos a R1 r).le
      linarith
    · rw [fC_explicit ha hR hs', fC_explicit ha hR hrR, min_eq_left hrR]
      have := Real.exp_pos (-(a * s'))
      have : (1 - Real.exp (-(a * s'))) / a - (1 - Real.exp (-(a * r))) / a =
          a⁻¹ * Real.exp (-(a * r)) - a⁻¹ * Real.exp (-(a * s')) := by
        field_simp; ring
      rw [this]
      have : 0 ≤ a⁻¹ * Real.exp (-(a * s')) := mul_nonneg (inv_nonneg.2 ha.le) (Real.exp_pos _).le
      linarith
  have hm : 0 ≤ Real.exp (-(a * R1)) * max (s - R1) 0 :=
    mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
  rcases le_total s R1 with h | h
  · have := hb s h; linarith
  · rw [fC_tail h, max_eq_left (by linarith : (0:ℝ) ≤ s - R1)]
    have := hb R1 le_rfl
    nlinarith

lemma exp_five_halves_lt : Real.exp (5 / 2) < 12.5 := by
  have h5 : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  have h2 : (2.7182818286 : ℝ) ^ 5 < 12.5 ^ 2 := by norm_num
  by_contra h
  push Not at h
  have := pow_le_pow_left₀ (by norm_num) h 2
  linarith

lemma aR1_eq {T ℛ : ℝ} (hT : 0 < T) : aC T * R1C T ℛ = 5 / 2 * (1 + ℛ / T) := by
  unfold aC R1C; field_simp; ring

/-- Case (i) arithmetic: a deterministic contraction `R'² ≤ (1 - KT²/2) r²` gives
`f(R') ≤ (1 - c) f(r)`. -/
lemma caseI_pt {K T ℛ r R' : ℝ} (hT : 0 < T) (hR0 : 0 ≤ ℛ) (hK : 0 < K) (hKT : K * T ^ 2 ≤ 1)
    (hr : 0 ≤ r) (hR'0 : 0 ≤ R') (hR' : R' ^ 2 ≤ (1 - K * T ^ 2 / 2) * r ^ 2) :
    fConc (aC T) (R1C T ℛ) R' ≤ (1 - rateC K T ℛ) * fConc (aC T) (R1C T ℛ) r := by
  have ha : 0 < aC T := inv_pos.2 hT
  have hR1 : 0 < R1C T ℛ := by unfold R1C; positivity
  have hKT0 : 0 ≤ K * T ^ 2 := by positivity
  -- R' ≤ (1 - KT²/4) r
  have hρ : R' ≤ (1 - K * T ^ 2 / 4) * r := by
    by_contra h
    push Not at h
    have h0 : 0 ≤ (1 - K * T ^ 2 / 4) * r := mul_nonneg (by linarith) hr
    have := pow_lt_pow_left₀ h h0 two_ne_zero
    have e : ((1 - K * T ^ 2 / 4) * r) ^ 2 = (1 - K * T ^ 2 / 2) * r ^ 2 + (K * T ^ 2 / 4 * r) ^ 2 := by
      ring
    have := sq_nonneg (K * T ^ 2 / 4 * r)
    linarith
  set G := Real.exp (-(aC T * min r (R1C T ℛ))) with hG
  have hGpos : 0 < G := Real.exp_pos _
  have hcc := fC_concave (R1 := R1C T ℛ) ha r R'
  have hstep : fConc (aC T) (R1C T ℛ) R' ≤ fConc (aC T) (R1C T ℛ) r - K * T ^ 2 / 4 * r * G := by
    have : G * (R' - r) ≤ G * (-(K * T ^ 2 / 4 * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hGpos.le
    linarith
  set X := fConc (aC T) (R1C T ℛ) r with hX
  have hX0 : 0 ≤ X := fC_nonneg ha hr
  have hup := fC_upper_global (R1 := R1C T ℛ) ha hR1 hr
  rw [← hX, ← hG] at hup
  set A := aC T * R1C T ℛ with hA
  have hA' : A = 5 / 2 * (1 + ℛ / T) := aR1_eq hT
  have hApos : 0 < A := by rw [hA']; positivity
  set p1 := Real.exp (-(ℛ / (2 * T))) with hp1
  set p2 := Real.exp (-(2 * ℛ / T)) with hp2
  have hp1p : 0 < p1 := Real.exp_pos _
  have hp2p : 0 < p2 := Real.exp_pos _
  have hexp : p1 * p2 * Real.exp A = Real.exp (5 / 2) := by
    rw [hp1, hp2, ← Real.exp_add, ← Real.exp_add, hA']
    congr 1; field_simp; ring
  have hu : 0 ≤ ℛ / T := div_nonneg hR0 hT.le
  -- c ≤ Q
  set Q := 1 / 10 * (1 / 2 * K * T ^ 2 * (1 + ℛ / T) * p1) * p2 with hQ
  have hcQ : rateC K T ℛ ≤ Q := by
    unfold rateC
    rw [← hp1, ← hp2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
      hp2p.le
  have hQ0 : 0 ≤ Q := by positivity
  have hQX : Q * X ≤ K * T ^ 2 / 4 * r * G := by
    have s1 : Q * (X * A) ≤ Q * (r * G * Real.exp A) := mul_le_mul_of_nonneg_left hup hQ0
    have s2 : Q * (r * G * Real.exp A) = 1 / 20 * K * T ^ 2 * (1 + ℛ / T) * r * G *
        (p1 * p2 * Real.exp A) := by rw [hQ]; ring
    rw [hexp] at s2
    have hc0 : 0 ≤ 1 / 20 * K * T ^ 2 * (1 + ℛ / T) * r * G := by positivity
    have s3 := mul_le_mul_of_nonneg_left exp_five_halves_lt.le hc0
    have key : (Q * X) * A ≤ (K * T ^ 2 / 4 * r * G) * A := by
      have e : (K * T ^ 2 / 4 * r * G) * A = 1 / 20 * K * T ^ 2 * (1 + ℛ / T) * r * G * 12.5 := by
        rw [hA']; ring
      linarith
    exact le_of_mul_le_mul_right key hApos
  have hcX : rateC K T ℛ * X ≤ Q * X := mul_le_mul_of_nonneg_right hcQ hX0
  linarith


lemma grad_lip {d : ℕ} {U : E d → ℝ} {L : ℝ} (hU : ContDiff ℝ 4 U)
    (hL : ∀ x, ‖iteratedFDeriv ℝ 2 U x‖ ≤ L) (x y : E d) :
    ‖gradient U x - gradient U y‖ ≤ L * ‖x - y‖ := by
  have hd : ContDiff ℝ 3 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hdiff : Differentiable ℝ (fderiv ℝ U) := hd.differentiable (by norm_num)
  have hb : ∀ z ∈ (Set.univ : Set (E d)), ‖fderiv ℝ (fderiv ℝ U) z‖ ≤ L := by
    intro z _
    have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := U) (n := 1) (x := z)
    rw [norm_iteratedFDeriv_one] at h1
    rw [h1]; exact hL z
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) hb
    (Set.mem_univ y) (Set.mem_univ x)
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  exact this


lemma seg_norm_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (z0 w0 : V) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) : ‖z0 + s • w0‖ ≤ max ‖z0‖ ‖z0 + t • w0‖ := by
  rcases eq_or_lt_of_le (hs0.trans hst) with ht | ht
  · have : s = 0 := by linarith
    subst this; simp
  · set lam := s / t with hlam
    have hl0 : 0 ≤ lam := div_nonneg hs0 ht.le
    have hl1 : lam ≤ 1 := (div_le_one ht).2 hst
    have hmul : lam * t = s := div_mul_cancel₀ s ht.ne'
    have heq : (1 - lam) • z0 + lam • (z0 + t • w0) = z0 + s • w0 := by
      rw [smul_add, smul_smul, hmul, sub_smul, one_smul]; abel
    rw [← heq]
    calc ‖(1 - lam) • z0 + lam • (z0 + t • w0)‖
        ≤ ‖(1 - lam) • z0‖ + ‖lam • (z0 + t • w0)‖ := norm_add_le _ _
      _ = (1 - lam) * ‖z0‖ + lam * ‖z0 + t • w0‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hl0]
      _ ≤ (1 - lam) * max ‖z0‖ ‖z0 + t • w0‖ + lam * max ‖z0‖ ‖z0 + t • w0‖ := by
          have h1 : 0 ≤ 1 - lam := by linarith
          exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) hl0)
      _ = max ‖z0‖ ‖z0 + t • w0‖ := by ring

/-- Sup-bootstrap behind Lemma 3.2 (h = 0): for `z' = w`, `w' = F`, `‖F‖ ≤ L ‖z‖`. -/
lemma bootstrap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : ℝ} (hL : 0 ≤ L) (z w F : ℝ → V)
    (hz : ∀ s, HasDerivAt z (w s) s) (hw : ∀ s, HasDerivAt w (F s) s)
    (hF : ∀ s, ‖F s‖ ≤ L * ‖z s‖) {t : ℝ} (ht : 0 ≤ t) :
    ∃ M, 0 ≤ M ∧ (∀ s ∈ Set.Icc 0 t, ‖z s‖ ≤ M) ∧
      M * (1 - L * t ^ 2 / 2) ≤ max ‖z 0‖ ‖z 0 + t • w 0‖ ∧
      (∀ s ∈ Set.Icc 0 t, ‖w s - w 0‖ ≤ L * M * s) ∧
      (∀ s ∈ Set.Icc 0 t, ‖z s - z 0 - s • w 0‖ ≤ L * M * s ^ 2 / 2) := by
  have hzc : Continuous z := continuous_iff_continuousAt.2 fun s => (hz s).continuousAt
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun s => (hw s).continuousAt
  obtain ⟨s0, hs0, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) t)).exists_isMaxOn
    (Set.nonempty_Icc.2 ht) (continuous_norm.comp hzc).continuousOn
  have hzM : ∀ s ∈ Set.Icc 0 t, ‖z s‖ ≤ ‖z s0‖ := fun s hs => hmax hs
  have hM0 : 0 ≤ ‖z s0‖ := norm_nonneg _
  have hLM : 0 ≤ L * ‖z s0‖ := mul_nonneg hL hM0
  have hw1 : ∀ s ∈ Set.Icc 0 t, ‖w s - w 0‖ ≤ L * ‖z s0‖ * s := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := fun s => w s - w 0)
      (f' := F) (a := 0) (b := t) (B := fun s => L * ‖z s0‖ * s) (B' := fun _ => L * ‖z s0‖)
      ((hwc.sub continuous_const).continuousOn)
      (fun s _ => ((hw s).sub_const (w 0)).hasDerivWithinAt) (by simp) ?_ ?_
    · intro s
      exact ((hasDerivAt_id' s).const_mul (L * ‖z s0‖)).congr_deriv (by ring)
    · intro s hs
      exact (hF s).trans (mul_le_mul_of_nonneg_left (hzM s (Set.Ico_subset_Icc_self hs)) hL)
  have hz1 : ∀ s ∈ Set.Icc 0 t, ‖z s - z 0 - s • w 0‖ ≤ L * ‖z s0‖ * s ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s => z s - z 0 - s • w 0)
      (f' := fun s => w s - w 0) (a := 0) (b := t) (B := fun s => L * ‖z s0‖ * s ^ 2 / 2)
      (B' := fun s => L * ‖z s0‖ * s)
      (((hzc.sub continuous_const).sub (continuous_id.smul continuous_const)).continuousOn)
      (fun s _ => ((((hz s).sub_const (z 0)).sub ((hasDerivAt_id' s).smul_const (w 0))).congr_deriv
        (by simp)).hasDerivWithinAt) (by simp) ?_ ?_
    · intro s
      exact (((hasDerivAt_pow 2 s).const_mul (L * ‖z s0‖)).div_const 2).congr_deriv
        (by norm_num; ring)
    · intro s hs
      exact hw1 s (Set.Ico_subset_Icc_self hs)
  refine ⟨‖z s0‖, hM0, hzM, ?_, hw1, hz1⟩
  have hsplit : z s0 = (z 0 + s0 • w 0) + (z s0 - z 0 - s0 • w 0) := by abel
  have h1 : ‖z s0‖ ≤ ‖z 0 + s0 • w 0‖ + ‖z s0 - z 0 - s0 • w 0‖ := by
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  have h2 := seg_norm_le (z 0) (w 0) hs0.1 hs0.2
  have h3 := hz1 s0 hs0
  have h4 : s0 ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs0.1 hs0.2 2
  have h5 : L * ‖z s0‖ * s0 ^ 2 ≤ L * ‖z s0‖ * t ^ 2 := mul_le_mul_of_nonneg_left h4 hLM
  nlinarith

/-- Lemma 3.2 for the exact flow (h = 0), bootstrap form. -/
lemma flow_boot {d : ℕ} {U : E d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hU : ContDiff ℝ 4 U)
    (hLb : ∀ x, ‖iteratedFDeriv ℝ 2 U x‖ ≤ L) {q p : ℝ → E d → E d → E d}
    (hflow : IsExactFlow U q p) (x y u v : E d) {t : ℝ} (ht : 0 ≤ t) :
    ∃ M, 0 ≤ M ∧ (∀ s ∈ Set.Icc 0 t, ‖q s x u - q s y v‖ ≤ M) ∧
      M * (1 - L * t ^ 2 / 2) ≤ max ‖x - y‖ ‖x - y + t • (u - v)‖ ∧
      (∀ s ∈ Set.Icc 0 t, ‖(p s x u - p s y v) - (u - v)‖ ≤ L * M * s) ∧
      (∀ s ∈ Set.Icc 0 t, ‖(q s x u - q s y v) - (x - y) - s • (u - v)‖ ≤ L * M * s ^ 2 / 2) := by
  obtain ⟨hq0x, hp0x, hdx⟩ := hflow x u
  obtain ⟨hq0y, hp0y, hdy⟩ := hflow y v
  have := bootstrap hL (fun s => q s x u - q s y v) (fun s => p s x u - p s y v)
    (fun s => -gradient U (q s x u) - -gradient U (q s y v))
    (fun s => (hdx s).1.sub (hdy s).1) (fun s => (hdx s).2.sub (hdy s).2)
    (fun s => by
      rw [neg_sub_neg, norm_sub_rev]
      exact grad_lip hU hLb _ _) ht
  simp only [hq0x, hq0y, hp0x, hp0y] at this
  exact this

/-- Lemma 3.4 for the exact flow (h = 0): synchronous contraction for `|x - y| ≥ 2ℛ`. -/
lemma sync_contract {d : ℕ} {U : E d → ℝ} {L M N ℛ K : ℝ} (hU : Assumption21 U L M N ℛ K)
    {q p : ℝ → E d → E d → E d} (hflow : IsExactFlow U q p) {T : ℝ} (hT : 0 < T)
    (hLT : L * T ^ 2 ≤ 1 / 4) (hLK : L ^ 2 * T ^ 2 ≤ K) (x y v : E d) (hr : 2 * ℛ ≤ ‖x - y‖) :
    ‖q T x v - q T y v‖ ^ 2 ≤ (1 - K * T ^ 2 / 2) * ‖x - y‖ ^ 2 := by
  obtain ⟨⟨hC, _⟩, _, ⟨hLb, _, _⟩, hR0, hK, hA3⟩ := hU
  have hL : 0 ≤ L := (norm_nonneg _).trans (hLb 0)
  have hr0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  obtain ⟨Mb, hM0, -, hMmax, hwb, hzb⟩ := flow_boot hL hC hLb hflow x y v v hT.le
  simp only [sub_self, smul_zero, add_zero, max_self, sub_zero] at hMmax hwb hzb
  obtain ⟨hq0x, hp0x, hdx⟩ := hflow x v
  obtain ⟨hq0y, hp0y, hdy⟩ := hflow y v
  -- abbreviations
  set r := ‖x - y‖ with hr_def
  set z : ℝ → E d := fun s => q s x v - q s y v with hz_def
  set w : ℝ → E d := fun s => p s x v - p s y v with hw_def
  set F : ℝ → E d := fun s => -gradient U (q s x v) - -gradient U (q s y v) with hF_def
  have hz : ∀ s, HasDerivAt z (w s) s := fun s => (hdx s).1.sub (hdy s).1
  have hw : ∀ s, HasDerivAt w (F s) s := fun s => (hdx s).2.sub (hdy s).2
  have hM8 : 7 * Mb ≤ 8 * r := by
    have := mul_le_mul_of_nonneg_left (show (7:ℝ) / 8 ≤ 1 - L * T ^ 2 / 2 by linarith) hM0
    linarith
  set C : ℝ := 8 / 7 * K * L * r ^ 2 + 64 / 49 * L ^ 2 * r ^ 2 with hC_def
  -- pointwise bound on the second derivative
  have hbd : ∀ s ∈ Set.Icc 0 T, ⟪z s, F s⟫_ℝ + ⟪w s, w s⟫_ℝ ≤ -K * r ^ 2 + C * s ^ 2 := by
    intro s hs
    have hs2 : s ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hs.1 hs.2 2
    have hLM : 0 ≤ L * Mb := mul_nonneg hL hM0
    have hc1 : L * Mb * s ^ 2 ≤ Mb / 4 := by
      have := mul_le_mul_of_nonneg_left hs2 hLM
      have h2 : L * Mb * T ^ 2 = Mb * (L * T ^ 2) := by ring
      have h3 := mul_le_mul_of_nonneg_left hLT hM0
      linarith
    have hcs : 0 ≤ L * Mb * s ^ 2 := mul_nonneg hLM (sq_nonneg s)
    have hzd : ‖z s - (x - y)‖ ≤ L * Mb * s ^ 2 / 2 := hzb s hs
    have hzlow : r - L * Mb * s ^ 2 / 2 ≤ ‖z s‖ := by
      have := norm_sub_norm_le (x - y) (z s)
      have h2 : ‖x - y - z s‖ = ‖z s - (x - y)‖ := norm_sub_rev _ _
      linarith
    have hzR : ℛ ≤ ‖z s‖ := by linarith
    have hA : K * ‖z s‖ ^ 2 ≤ ⟪z s, gradient U (q s x v) - gradient U (q s y v)⟫_ℝ :=
      hA3 (q s x v) (q s y v) hzR
    have hFz : ⟪z s, F s⟫_ℝ = -⟪z s, gradient U (q s x v) - gradient U (q s y v)⟫_ℝ := by
      rw [← inner_neg_right]
      congr 1
      simp only [hF_def]; abel
    have hzsq : r ^ 2 - r * (L * Mb * s ^ 2) ≤ ‖z s‖ ^ 2 := by
      have h0 : 0 ≤ r - L * Mb * s ^ 2 / 2 := by linarith
      have := pow_le_pow_left₀ h0 hzlow 2
      have e : (r - L * Mb * s ^ 2 / 2) ^ 2 = r ^ 2 - r * (L * Mb * s ^ 2) + (L * Mb * s ^ 2 / 2) ^ 2 := by
        ring
      have := sq_nonneg (L * Mb * s ^ 2 / 2)
      linarith
    have hrM : r * (L * Mb * s ^ 2) ≤ 8 / 7 * L * r ^ 2 * s ^ 2 := by
      have h1 : 0 ≤ L * s ^ 2 * r := by positivity
      have := mul_le_mul_of_nonneg_left (show Mb ≤ 8 / 7 * r by linarith) h1
      linarith
    have hwn : ‖w s‖ ≤ L * Mb * s := hwb s hs
    have hww : ⟪w s, w s⟫_ℝ ≤ 64 / 49 * L ^ 2 * r ^ 2 * s ^ 2 := by
      rw [real_inner_self_eq_norm_sq]
      have h1 : L * Mb * s ≤ 8 / 7 * L * r * s := by
        have h2 : 0 ≤ L * s := mul_nonneg hL hs.1
        have := mul_le_mul_of_nonneg_left (show Mb ≤ 8 / 7 * r by linarith) h2
        linarith
      have h3 := pow_le_pow_left₀ (norm_nonneg _) (hwn.trans h1) 2
      linarith
    have hK1 : K * (r ^ 2 - r * (L * Mb * s ^ 2)) ≤ K * ‖z s‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hzsq hK.le
    have hK2 : K * (r * (L * Mb * s ^ 2)) ≤ K * (8 / 7 * L * r ^ 2 * s ^ 2) :=
      mul_le_mul_of_nonneg_left hrM hK.le
    rw [hFz, hC_def]
    linarith
  -- first integration: b(s) = ⟪z s, w s⟫
  have hb : ∀ s ∈ Set.Icc 0 T, ⟪z s, w s⟫_ℝ ≤ -K * r ^ 2 * s + C * s ^ 3 / 3 := by
    have hder : ∀ s, HasDerivAt (fun s => ⟪z s, w s⟫_ℝ) (⟪z s, F s⟫_ℝ + ⟪w s, w s⟫_ℝ) s :=
      fun s => HasDerivAt.inner (𝕜 := ℝ) (hz s) (hw s)
    refine image_le_of_deriv_right_le_deriv_boundary
      (f := fun s => ⟪z s, w s⟫_ℝ) (f' := fun s => ⟪z s, F s⟫_ℝ + ⟪w s, w s⟫_ℝ)
      (B := fun s => -K * r ^ 2 * s + C * s ^ 3 / 3) (B' := fun s => -K * r ^ 2 + C * s ^ 2)
      (fun s _ => (hder s).continuousAt.continuousWithinAt)
      (fun s _ => (hder s).hasDerivWithinAt) ?_ (by fun_prop) ?_ ?_
    · simp [hz_def, hw_def, hp0x, hp0y]
    · intro s _
      exact (((hasDerivAt_id' s).const_mul (-K * r ^ 2)).add
        (((hasDerivAt_pow 3 s).const_mul C).div_const 3)).hasDerivWithinAt.congr_deriv
        (by norm_num; ring)
    · intro s hs
      exact hbd s (Set.Ico_subset_Icc_self hs)
  -- second integration: a(s) = ⟪z s, z s⟫
  have ha : ∀ s ∈ Set.Icc 0 T, ⟪z s, z s⟫_ℝ ≤ r ^ 2 - K * r ^ 2 * s ^ 2 + C * s ^ 4 / 6 := by
    have hder : ∀ s, HasDerivAt (fun s => ⟪z s, z s⟫_ℝ) (⟪z s, w s⟫_ℝ + ⟪w s, z s⟫_ℝ) s :=
      fun s => HasDerivAt.inner (𝕜 := ℝ) (hz s) (hz s)
    refine image_le_of_deriv_right_le_deriv_boundary
      (f := fun s => ⟪z s, z s⟫_ℝ) (f' := fun s => ⟪z s, w s⟫_ℝ + ⟪w s, z s⟫_ℝ)
      (B := fun s => r ^ 2 - K * r ^ 2 * s ^ 2 + C * s ^ 4 / 6)
      (B' := fun s => -2 * K * r ^ 2 * s + 2 * C * s ^ 3 / 3)
      (fun s _ => (hder s).continuousAt.continuousWithinAt)
      (fun s _ => (hder s).hasDerivWithinAt) ?_ (by fun_prop) ?_ ?_
    · simp [hz_def, hq0x, hq0y, real_inner_self_eq_norm_sq, hr_def]
    · intro s _
      exact (((hasDerivAt_const s (r ^ 2)).sub ((hasDerivAt_pow 2 s).const_mul (K * r ^ 2))).add
        (((hasDerivAt_pow 4 s).const_mul C).div_const 6)).hasDerivWithinAt.congr_deriv
        (by norm_num; ring)
    · intro s hs
      have := hb s (Set.Ico_subset_Icc_self hs)
      rw [real_inner_comm (z s) (w s)]
      linarith
  have hT2 := ha T ⟨hT.le, le_rfl⟩
  rw [real_inner_self_eq_norm_sq] at hT2
  have hP : 0 ≤ K * r ^ 2 * T ^ 2 := by positivity
  have h1 : K * L * r ^ 2 * T ^ 4 ≤ K * r ^ 2 * T ^ 2 / 4 := by
    have := mul_le_mul_of_nonneg_left hLT hP
    linarith
  have h2 : L ^ 2 * r ^ 2 * T ^ 4 ≤ K * r ^ 2 * T ^ 2 := by
    have h0 : 0 ≤ r ^ 2 * T ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hLK h0
    linarith
  have hfin : C * T ^ 4 / 6 ≤ 13 / 49 * (K * r ^ 2 * T ^ 2) := by
    rw [hC_def]; linarith
  show ‖z T‖ ^ 2 ≤ _
  linarith

section Gauss
open Real

/-- `⟪e, ξ⟫ ∼ N(0,1)` for `ξ ∼ N(0, I_d)` and a unit vector `e`. -/
lemma map_inner_stdGaussian {d : ℕ} (e : E d) (he : ‖e‖ = 1) :
    (stdGaussian (E d)).map (fun ξ => ⟪e, ξ⟫_ℝ) = gaussianReal 0 1 := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (E d)) (innerSL ℝ e)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm, he] at h
  have hf : (⇑(innerSL ℝ e) : E d → ℝ) = fun ξ => ⟪e, ξ⟫_ℝ := by
    funext ξ; simp [innerSL_apply_apply]
  rw [hf] at h
  rw [h]; simp

lemma lintegral_sq_gaussianReal :
    ∫⁻ s, ENNReal.ofReal (s ^ 2) ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  simp only [id] at hv
  rw [integral_id_gaussianReal] at hv
  have hint : Integrable (fun s : ℝ => s ^ 2) (gaussianReal 0 1) := by
    have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
    simpa using this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun s => sq_nonneg s)]
  simp only [sub_zero, NNReal.coe_one] at hv
  rw [hv]; simp

/-- the standard normal density -/
noncomputable def phi0 (v : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-v ^ 2 / 2)

lemma pdf_eq (v : ℝ) : gaussianPDFReal 0 1 v = phi0 v := by
  simp [gaussianPDFReal, phi0]

lemma phi0_pos (v : ℝ) : 0 < phi0 v := by unfold phi0; positivity

lemma phi0_cont : Continuous phi0 := by unfold phi0; fun_prop

lemma phi0_deriv (v : ℝ) : HasDerivAt phi0 (-(v * phi0 v)) v := by
  have := ((((hasDerivAt_pow 2 v).fun_neg).div_const 2).exp).const_mul (√(2 * π))⁻¹
  unfold phi0
  exact this.congr_deriv (by norm_num; ring)

lemma half_moment : ∫ v in Set.Ioi (0:ℝ), v * phi0 v = (√(2 * π))⁻¹ := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)
  have e1 : (fun x : ℝ => x ^ (1:ℝ) * rexp (-(1 / 2) * x ^ (2:ℝ))) = fun x => x * rexp (-x ^ 2 / 2) := by
    funext x; rw [Real.rpow_one, Real.rpow_two]; ring_nf
  rw [e1] at h
  have e2 : (fun v : ℝ => v * phi0 v) = fun v => (√(2 * π))⁻¹ * (v * rexp (-v ^ 2 / 2)) := by
    funext v; unfold phi0; ring
  rw [e2, integral_const_mul, h]
  norm_num [Real.Gamma_one]

lemma lintegral_pos_part_phi0 :
    ∫⁻ v, ENNReal.ofReal (max v 0 * phi0 v) = ENNReal.ofReal ((√(2 * π))⁻¹) := by
  have hint : IntegrableOn (fun v => v * phi0 v) (Set.Ioi 0) := by
    have := (integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (√(2 * π))⁻¹
    refine (this.congr (Filter.Eventually.of_forall fun v => ?_)).integrableOn
    simp only [phi0]; ring_nf
  have h1 : (fun v => ENNReal.ofReal (max v 0 * phi0 v)) =
      (Set.Ioi (0:ℝ)).indicator (fun v => ENNReal.ofReal (v * phi0 v)) := by
    funext v
    by_cases hv : 0 < v
    · simp [Set.indicator, hv, max_eq_left hv.le]
    · push Not at hv
      simp [Set.indicator, not_lt.2 hv, max_eq_right hv]
  rw [h1, lintegral_indicator measurableSet_Ioi, ← half_moment]
  rw [ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact mul_nonneg (le_of_lt hv) (phi0_pos v).le

lemma pt_bound {δ : ℝ} (hδ : 0 ≤ δ) (s : ℝ) :
    ENNReal.ofReal (phi0 s - phi0 (s + δ)) ≤
      ∫⁻ v, ({p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ p.1 + δ}.indicator
        (fun p => ENNReal.ofReal (max p.2 0 * phi0 p.2))) (s, v) := by
  have hc1 : Continuous fun v : ℝ => v * phi0 v := continuous_id.mul phi0_cont
  have hc2 : Continuous fun v : ℝ => max v 0 * phi0 v :=
    (continuous_id.max continuous_const).mul phi0_cont
  have hftc : ∫ v in s..(s + δ), -(v * phi0 v) = phi0 (s + δ) - phi0 s :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => phi0_deriv v)
      (hc1.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at hftc
  have hle : ∫ v in s..(s + δ), v * phi0 v ≤ ∫ v in s..(s + δ), max v 0 * phi0 v :=
    intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)
      (fun v _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (phi0_pos v).le)
  have heq : phi0 s - phi0 (s + δ) = ∫ v in s..(s + δ), v * phi0 v := by linarith
  have hind : ∀ v, ({p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ p.1 + δ}.indicator
        (fun p => ENNReal.ofReal (max p.2 0 * phi0 p.2))) (s, v) =
      (Set.Ioc s (s + δ)).indicator (fun v => ENNReal.ofReal (max v 0 * phi0 v)) v := by
    intro v
    simp only [Set.indicator, Set.mem_setOf_eq, Set.mem_Ioc]
  simp_rw [hind]
  rw [heq, lintegral_indicator measurableSet_Ioc]
  calc ENNReal.ofReal (∫ v in s..(s + δ), v * phi0 v)
      ≤ ENNReal.ofReal (∫ v in s..(s + δ), max v 0 * phi0 v) := ENNReal.ofReal_le_ofReal hle
    _ = ∫⁻ v in Set.Ioc s (s + δ), ENNReal.ofReal (max v 0 * phi0 v) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        exact ofReal_integral_eq_lintegral_ofReal
          ((hc2.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self)
          (Filter.Eventually.of_forall fun v => mul_nonneg (le_max_right _ _) (phi0_pos v).le)

/-- Total-variation bound: `P(reject) ≤ δ/√(2π)` for the maximal coupling of `N(0,1)` and
`N(-δ,1)`. -/
lemma tv_bound {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫⁻ s, ENNReal.ofReal (1 - gaussianPDFReal 0 1 (s + δ) / gaussianPDFReal 0 1 s)
      ∂(gaussianReal 0 1) ≤ ENNReal.ofReal (δ * (√(2 * π))⁻¹) := by
  simp_rw [pdf_eq]
  have hmeas : Measurable fun s => ENNReal.ofReal (1 - phi0 (s + δ) / phi0 s) :=
    ((continuous_const.sub ((phi0_cont.comp (continuous_add_right δ)).div phi0_cont
      (fun s => (phi0_pos s).ne'))).measurable).ennreal_ofReal
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) hmeas]
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < p.2 ∧ p.2 ≤ p.1 + δ} with hS_def
  have hF : Measurable fun v : ℝ => ENNReal.ofReal (max v 0 * phi0 v) :=
    (((continuous_id.max continuous_const).mul phi0_cont).measurable).ennreal_ofReal
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const δ))
  calc ∫⁻ s, (gaussianPDF 0 1 * fun s => ENNReal.ofReal (1 - phi0 (s + δ) / phi0 s)) s
      ≤ ∫⁻ s, ∫⁻ v, (S.indicator (fun p => ENNReal.ofReal (max p.2 0 * phi0 p.2))) (s, v) := by
        refine lintegral_mono fun s => ?_
        have e : (gaussianPDF 0 1 * fun s => ENNReal.ofReal (1 - phi0 (s + δ) / phi0 s)) s =
            ENNReal.ofReal (phi0 s - phi0 (s + δ)) := by
          simp only [Pi.mul_apply, gaussianPDF, pdf_eq]
          rw [← ENNReal.ofReal_mul (phi0_pos s).le]
          congr 1
          field_simp [(phi0_pos s).ne']
        rw [e]
        exact pt_bound hδ s
    _ = ∫⁻ v, ∫⁻ s, (S.indicator (fun p => ENNReal.ofReal (max p.2 0 * phi0 p.2))) (s, v) :=
        lintegral_lintegral_swap ((hF.comp measurable_snd).indicator hS).aemeasurable
    _ = ∫⁻ v, ENNReal.ofReal (max v 0 * phi0 v) * ENNReal.ofReal δ := by
        refine lintegral_congr fun v => ?_
        have e : ∀ s, (S.indicator (fun p => ENNReal.ofReal (max p.2 0 * phi0 p.2))) (s, v) =
            (Set.Ico (v - δ) v).indicator (fun _ => ENNReal.ofReal (max v 0 * phi0 v)) s := by
          intro s
          by_cases h : s < v ∧ v ≤ s + δ
          · have h' : s ∈ Set.Ico (v - δ) v := ⟨by linarith [h.2], h.1⟩
            rw [Set.indicator_of_mem h', Set.indicator_of_mem (show (s, v) ∈ S from h)]
          · have h' : s ∉ Set.Ico (v - δ) v := fun hh => h ⟨hh.2, by linarith [hh.1]⟩
            rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (show (s, v) ∉ S from h)]
        simp_rw [e]
        rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, sub_sub_cancel]
    _ = ENNReal.ofReal (δ * (√(2 * π))⁻¹) := by
        rw [lintegral_mul_const _ hF, lintegral_pos_part_phi0, mul_comm,
          ← ENNReal.ofReal_mul hδ]

end Gauss

/-- Generic one-step bound from Lemma 3.2: `R' ≤ |w| + (4/7) L T² max(r, |w|)`,
`w = x - y + T (ξ - η)`. -/
lemma Rp_le {d : ℕ} {U : E d → ℝ} {L M N ℛ K : ℝ} (hU : Assumption21 U L M N ℛ K)
    {q p : ℝ → E d → E d → E d} (hflow : IsExactFlow U q p) {T : ℝ} (hT : 0 < T)
    (hLT : L * T ^ 2 ≤ 1 / 4) (x y ξ η : E d) :
    ‖q T x ξ - q T y η‖ ≤ ‖x - y + T • (ξ - η)‖ +
      L * T ^ 2 * (4 / 7) * max ‖x - y‖ ‖x - y + T • (ξ - η)‖ := by
  obtain ⟨⟨hC, _⟩, _, ⟨hLb, _, _⟩, _⟩ := hU
  have hL : 0 ≤ L := (norm_nonneg _).trans (hLb 0)
  obtain ⟨Mb, hM0, -, hMmax, -, hzb⟩ := flow_boot hL hC hLb hflow x y ξ η hT.le
  have hzT := hzb T ⟨hT.le, le_rfl⟩
  set m := max ‖x - y‖ ‖x - y + T • (ξ - η)‖ with hm
  have hM8 : 7 * Mb ≤ 8 * m := by
    have := mul_le_mul_of_nonneg_left (show (7:ℝ) / 8 ≤ 1 - L * T ^ 2 / 2 by linarith) hM0
    linarith
  have hsplit : q T x ξ - q T y η = (x - y + T • (ξ - η)) +
      (q T x ξ - q T y η - (x - y) - T • (ξ - η)) := by abel
  have h1 : ‖q T x ξ - q T y η‖ ≤ ‖x - y + T • (ξ - η)‖ +
      ‖q T x ξ - q T y η - (x - y) - T • (ξ - η)‖ := by
    conv_lhs => rw [hsplit]
    exact norm_add_le _ _
  have hLT0 : 0 ≤ L * T ^ 2 := by positivity
  have h2 : L * Mb * T ^ 2 / 2 ≤ L * T ^ 2 * (4 / 7) * m := by
    have := mul_le_mul_of_nonneg_left (show Mb ≤ 8 / 7 * m by linarith) hLT0
    linarith
  linarith

/-- Case (ii) pointwise bound (reflection coupling, `0 < |x - y| < 2ℛ`). -/
lemma caseII_pt {d : ℕ} {U : E d → ℝ} {L M N ℛ K : ℝ} (hU : Assumption21 U L M N ℛ K)
    {q p : ℝ → E d → E d → E d} (hflow : IsExactFlow U q p) {T γ : ℝ} (hT : 0 < T)
    (hLT : L * T ^ 2 ≤ 1 / 4) (hLg : L * T ^ 2 ≤ γ * T / 4) (hγ : 0 < γ) (hγT : γ * T ≤ 1)
    (x y : E d) (hr0 : 0 < ‖x - y‖) (hr2 : ‖x - y‖ < 2 * ℛ) (ξ : E d) (u : ℝ) :
    fConc (aC T) (R1C T ℛ) ‖q T x ξ - q T y (reflEta γ (x - y) ξ u)‖ ≤
      (fConc (aC T) (R1C T ℛ) ‖x - y‖ -
        6 / 7 * (γ * ‖x - y‖) * T * Real.exp (-(aC T * min ‖x - y‖ (R1C T ℛ)))) +
      (if u ≤ gaussianPDFReal 0 1 (⟪‖x - y‖⁻¹ • (x - y), ξ⟫_ℝ + γ * ‖x - y‖) /
            gaussianPDFReal 0 1 ⟪‖x - y‖⁻¹ • (x - y), ξ⟫_ℝ then 0 else
        6 / 7 * (γ * ‖x - y‖) * T * Real.exp (-(aC T * min ‖x - y‖ (R1C T ℛ))) +
        T * Real.exp (-(aC T * min ‖x - y‖ (R1C T ℛ))) +
        16 / 7 * T * Real.exp (-(aC T * R1C T ℛ)) *
          max (|⟪‖x - y‖⁻¹ • (x - y), ξ⟫_ℝ| - 1) 0) := by
  have hRp := Rp_le hU hflow hT hLT x y ξ
  obtain ⟨_, _, ⟨hLb, _, _⟩, hR0, _, _⟩ := hU
  have hL : 0 ≤ L := (norm_nonneg _).trans (hLb 0)
  have ha : 0 < aC T := inv_pos.2 hT
  have hR1 : 0 ≤ R1C T ℛ := by unfold R1C; positivity
  have hrR1 : ‖x - y‖ ≤ R1C T ℛ := by unfold R1C; linarith
  simp only [reflEta]
  set r := ‖x - y‖ with hr_def
  set e : E d := r⁻¹ • (x - y) with he_def
  set s := ⟪e, ξ⟫_ℝ with hs_def
  set g := Real.exp (-(aC T * min r (R1C T ℛ))) with hg_def
  have hg0 : 0 < g := Real.exp_pos _
  have hzre : x - y = r • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
  have hen : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le), inv_mul_cancel₀ hr0.ne']
  by_cases hacc : u ≤ gaussianPDFReal 0 1 (s + γ * r) / gaussianPDFReal 0 1 s
  · simp only [if_pos hacc, add_zero]
    have hw : x - y + T • (ξ - (ξ + γ • (x - y))) = (1 - γ * T) • (x - y) := by
      rw [sub_add_cancel_left, smul_neg, smul_smul, sub_smul, one_smul, mul_comm]; abel
    have hwn : ‖(1 - γ * T) • (x - y)‖ = (1 - γ * T) * r := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
    have hR := hRp (ξ + γ • (x - y))
    rw [hw, hwn] at hR
    have hmax : max r ((1 - γ * T) * r) = r := by
      apply max_eq_left
      have : 0 ≤ γ * T * r := by positivity
      nlinarith
    rw [hmax] at hR
    have h3 : L * T ^ 2 * (4 / 7) * r ≤ γ * T / 4 * (4 / 7) * r :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLg (by norm_num)) hr0.le
    have hcc := fC_concave (R1 := R1C T ℛ) ha r ‖q T x ξ - q T y (ξ + γ • (x - y))‖
    rw [← hg_def] at hcc
    have h4 : g * (‖q T x ξ - q T y (ξ + γ • (x - y))‖ - r) ≤ g * (-(6 / 7 * γ * T * r)) :=
      mul_le_mul_of_nonneg_left (by linarith) hg0.le
    linarith
  · simp only [if_neg hacc]
    have hw : x - y + T • (ξ - (ξ - (2 * s) • e)) = (r + 2 * T * s) • e := by
      rw [sub_sub_cancel, add_smul, ← hzre, smul_smul, show T * (2 * s) = 2 * T * s by ring]
    have hwn : ‖(r + 2 * T * s) • e‖ = |r + 2 * T * s| := by
      rw [norm_smul, hen, mul_one, Real.norm_eq_abs]
    have hR := hRp (ξ - (2 * s) • e)
    rw [hw, hwn] at hR
    have hTs : 0 ≤ T * |s| := mul_nonneg hT.le (abs_nonneg s)
    have hab : |r + 2 * T * s| ≤ r + 2 * (T * |s|) := by
      have := abs_add_le r (2 * T * s)
      rw [abs_of_pos hr0, abs_mul, abs_mul, abs_of_pos hT, abs_two] at this
      linarith
    have hm : max r |r + 2 * T * s| ≤ r + 2 * (T * |s|) := max_le (by linarith) hab
    have hm0 : 0 ≤ max r |r + 2 * T * s| := le_trans hr0.le (le_max_left _ _)
    have hLT0 : 0 ≤ L * T ^ 2 := by positivity
    have h3 : L * T ^ 2 * (4 / 7) * max r |r + 2 * T * s| ≤ 1 / 4 * (4 / 7) * max r |r + 2 * T * s| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLT (by norm_num)) hm0
    have h5 : |r + 2 * T * s| ≤ max r |r + 2 * T * s| := le_max_right _ _
    set Rp := ‖q T x ξ - q T y (ξ - (2 * s) • e)‖ with hRp_def
    have hRb : Rp ≤ 8 / 7 * (r + 2 * (T * |s|)) := by linarith
    have hst := fC_step ha hR1 hrR1 Rp
    rw [← hg_def] at hst
    have hinv : (aC T)⁻¹ = T := by unfold aC; exact inv_inv T
    rw [hinv] at hst
    have hmx : max (Rp - R1C T ℛ) 0 ≤ 16 / 7 * T * max (|s| - 1) 0 := by
      apply max_le
      · have h6 : 16 / 7 * T * (|s| - 1) ≤ 16 / 7 * T * max (|s| - 1) 0 :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
        unfold R1C
        nlinarith
      · have : 0 ≤ max (|s| - 1) 0 := le_max_right _ _
        positivity
    have hE : 0 ≤ Real.exp (-(aC T * R1C T ℛ)) := (Real.exp_pos _).le
    have h7 := mul_le_mul_of_nonneg_left hmx hE
    nlinarith

lemma exp_five_halves_gt : 12 ≤ Real.exp (5 / 2) := by
  have h5 : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_gt_d9
  have h1 : (2.7182818283 : ℝ) ^ 5 < Real.exp 1 ^ 5 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
  have h2 : (12 : ℝ) ^ 2 < 2.7182818283 ^ 5 := by norm_num
  by_contra h
  push Not at h
  have := pow_lt_pow_left₀ h (Real.exp_pos _).le two_ne_zero
  linarith

/-- Case (ii) arithmetic: the expected-value bound beats `(1 - c) f(r)`. -/
lemma caseII_real {K L T ℛ γ r : ℝ} (hT : 0 < T) (hK : 0 < K) (hKL : K ≤ L)
    (hLg : L * T ^ 2 ≤ γ * T / 4) (hγ : 0 < γ) (hr0 : 0 < r) (hr2 : r < 2 * ℛ)
    (hδ : γ * r ≤ 1 / 2) :
    (fConc (aC T) (R1C T ℛ) r - 6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ)))) +
      (6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ))) +
        T * Real.exp (-(aC T * min r (R1C T ℛ)))) * (γ * r * (√(2 * Real.pi))⁻¹) +
      16 / 7 * T * Real.exp (-(aC T * R1C T ℛ)) * (γ * r) ≤
      (1 - rateC K T ℛ) * fConc (aC T) (R1C T ℛ) r := by
  have ha : 0 < aC T := inv_pos.2 hT
  have hR0 : 0 ≤ ℛ := by linarith
  have hrR1 : r ≤ R1C T ℛ := by unfold R1C; linarith
  have hmin : min r (R1C T ℛ) = r := min_eq_left hrR1
  rw [hmin]
  set g := Real.exp (-(aC T * r)) with hg_def
  have hg0 : 0 < g := Real.exp_pos _
  have har : aC T * r = r / T := by unfold aC; ring
  set p2 := Real.exp (-(2 * ℛ / T)) with hp2
  have hgl : p2 ≤ g := by
    rw [hp2, hg_def, har]
    apply Real.exp_le_exp.2
    have : r / T ≤ 2 * ℛ / T := div_le_div_of_nonneg_right hr2.le hT.le
    linarith
  have hfr : fConc (aC T) (R1C T ℛ) r ≤ r := fC_le_self ha (by unfold R1C; positivity) hr0.le
  have hf0 : 0 ≤ fConc (aC T) (R1C T ℛ) r := fC_nonneg ha hr0.le
  -- the rate
  set E1 := Real.exp (-(ℛ / (2 * T))) with hE1
  have hE1p : 0 < E1 := Real.exp_pos _
  have hA : (1 + ℛ / T) * E1 ≤ 2 := by
    have h := Real.add_one_le_exp (ℛ / (2 * T))
    have hprod : E1 * Real.exp (ℛ / (2 * T)) = 1 := by rw [hE1, ← Real.exp_add]; simp
    have hu : ℛ / T = 2 * (ℛ / (2 * T)) := by field_simp
    have := mul_le_mul_of_nonneg_left h hE1p.le
    rw [hu]
    nlinarith
  have hKT : K * T ^ 2 ≤ L * T ^ 2 := mul_le_mul_of_nonneg_right hKL (sq_nonneg T)
  have hX : 1 / 2 * K * T ^ 2 * (1 + ℛ / T) * E1 ≤ γ * T / 4 := by
    have h0 : 0 ≤ 1 / 2 * K * T ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hA h0
    linarith
  have hp20 : 0 < p2 := Real.exp_pos _
  have hrate : rateC K T ℛ ≤ 1 / 10 * (γ * T / 4) * p2 := by
    unfold rateC
    rw [← hE1, ← hp2]
    apply mul_le_mul_of_nonneg_right _ hp20.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (min_le_right _ _).trans hX
  have hcf : rateC K T ℛ * fConc (aC T) (R1C T ℛ) r ≤ 1 / 40 * (γ * r * T * g) := by
    have h1 := mul_le_mul_of_nonneg_right hrate hf0
    have hc0 : 0 ≤ 1 / 10 * (γ * T / 4) * p2 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hfr hc0
    have h3 : 0 ≤ 1 / 40 * γ * T * r := by positivity
    have h4 := mul_le_mul_of_nonneg_left hgl h3
    linarith
  -- 1/sqrt(2π) ≤ 2/5
  have hpi := Real.pi_gt_d2
  have hsq : (5 / 2 : ℝ) ≤ √(2 * Real.pi) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hp0 : (√(2 * Real.pi))⁻¹ ≤ 2 / 5 := by
    have := inv_anti₀ (by norm_num : (0:ℝ) < 5 / 2) hsq
    norm_num at this ⊢; linarith
  have hp00 : 0 ≤ (√(2 * Real.pi))⁻¹ := by positivity
  -- e^{-aR1} ≤ g/12
  have he12 : Real.exp (-(aC T * R1C T ℛ)) ≤ g / 12 := by
    have hsplit : -(aC T * R1C T ℛ) = -(aC T * r) + -(aC T * (R1C T ℛ - r)) := by ring
    have hge : 5 / 2 ≤ aC T * (R1C T ℛ - r) := by
      have h1 : 5 / 2 * T ≤ R1C T ℛ - r := by unfold R1C; linarith
      have h2 : aC T * (5 / 2 * T) = 5 / 2 := by unfold aC; field_simp
      have h3 := mul_le_mul_of_nonneg_left h1 ha.le
      linarith
    have h3 : Real.exp (-(aC T * (R1C T ℛ - r))) ≤ 1 / 12 := by
      calc Real.exp (-(aC T * (R1C T ℛ - r))) ≤ Real.exp (-(5 / 2)) := Real.exp_le_exp.2 (by linarith)
        _ = (Real.exp (5 / 2))⁻¹ := Real.exp_neg _
        _ ≤ (12 : ℝ)⁻¹ := inv_anti₀ (by norm_num) exp_five_halves_gt
        _ = 1 / 12 := by norm_num
    rw [hsplit, Real.exp_add, ← hg_def]
    have := mul_le_mul_of_nonneg_left h3 hg0.le
    linarith
  set δ := γ * r with hδ_def
  have hδ0 : 0 ≤ δ := by positivity
  have hQ : 0 ≤ δ * T * g := by positivity
  have t1 : (6 / 7 * δ * T * g + T * g) * (δ * (√(2 * Real.pi))⁻¹) ≤ 4 / 7 * (δ * T * g) := by
    have e : (6 / 7 * δ * T * g + T * g) * (δ * (√(2 * Real.pi))⁻¹) =
        ((6 / 7 * δ + 1) * (√(2 * Real.pi))⁻¹) * (δ * T * g) := by ring
    have hm : (6 / 7 * δ + 1) * (√(2 * Real.pi))⁻¹ ≤ 10 / 7 * (2 / 5) :=
      mul_le_mul (by linarith) hp0 hp00 (by norm_num)
    have := mul_le_mul_of_nonneg_right hm hQ
    rw [e]; linarith
  have t2 : 16 / 7 * T * Real.exp (-(aC T * R1C T ℛ)) * δ ≤ 16 / 7 * T * (g / 12) * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he12 (by positivity)) hδ0
  have hcf' : rateC K T ℛ * fConc (aC T) (R1C T ℛ) r ≤ 1 / 40 * (δ * T * g) := by
    have e : γ * r * T * g = δ * T * g := by rw [hδ_def]
    linarith
  nlinarith

/-- `K ≤ L` in positive dimension. -/
lemma K_le_L {d : ℕ} {U : E d → ℝ} {L M N ℛ K : ℝ} (hU : Assumption21 U L M N ℛ K)
    (w : E d) (hw : w ≠ 0) : K ≤ L := by
  obtain ⟨⟨hC, _⟩, _, ⟨hL, _, _⟩, hR0, hK, hA3⟩ := hU
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set t : ℝ := (ℛ + 1) / ‖w‖ with ht
  have htpos : 0 < t := div_pos (by linarith) hwn
  set z : E d := t • w with hz
  have hzn : ‖z‖ = ℛ + 1 := by
    rw [hz, norm_smul, Real.norm_of_nonneg htpos.le, ht]; field_simp
  have hzpos : 0 < ‖z‖ := by rw [hzn]; linarith
  have h1 := hA3 z 0 (by rw [sub_zero, hzn]; linarith)
  rw [sub_zero] at h1
  have h2 : ⟪z, gradient U z - gradient U 0⟫_ℝ ≤ L * ‖z‖ ^ 2 := by
    have := real_inner_le_norm z (gradient U z - gradient U 0)
    have h3 := grad_lip hC hL z 0
    rw [sub_zero] at h3
    nlinarith [norm_nonneg z]
  have : K * ‖z‖ ^ 2 ≤ L * ‖z‖ ^ 2 := le_trans h1 h2
  have hz2 : 0 < ‖z‖ ^ 2 := by positivity
  exact le_of_mul_le_mul_right this hz2

lemma eta_self {d : ℕ} (γ ℛ : ℝ) (x ξ : E d) (u : ℝ) : couplingEta γ ℛ x x ξ u = ξ := by
  unfold couplingEta reflEta
  simp

lemma noise_univ (d : ℕ) : noiseLaw d Set.univ = 1 := by
  rw [noiseLaw, ← Set.univ_prod_univ, Measure.prod_prod, measure_univ,
    Measure.restrict_apply_univ, Real.volume_Ioo]
  simp

lemma ratio_eq (s δ : ℝ) :
    gaussianPDFReal 0 1 (s + δ) / gaussianPDFReal 0 1 s = Real.exp (-(δ * s) - δ ^ 2 / 2) := by
  rw [pdf_eq, pdf_eq]
  unfold phi0
  rw [mul_div_mul_left _ _ (by positivity), ← Real.exp_sub]
  congr 1; ring

lemma tail_bound {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (s : ℝ) :
    max (|s| - 1) 0 * (1 - gaussianPDFReal 0 1 (s + δ) / gaussianPDFReal 0 1 s) ≤ δ * s ^ 2 := by
  rw [ratio_eq]
  have h1 := Real.add_one_le_exp (-(δ * s) - δ ^ 2 / 2)
  have hs : δ * s ≤ δ * |s| := mul_le_mul_of_nonneg_left (le_abs_self s) hδ0
  rcases le_total (|s| - 1) 0 with h | h
  · rw [max_eq_right h, zero_mul]; positivity
  · rw [max_eq_left h]
    have hab : |s| ^ 2 = s ^ 2 := sq_abs s
    have hA : 1 - Real.exp (-(δ * s) - δ ^ 2 / 2) ≤ δ * |s| + δ ^ 2 / 2 := by linarith
    have hB := mul_le_mul_of_nonneg_left hA h
    have key : δ * |s| ^ 2 - (|s| - 1) * (δ * |s| + δ ^ 2 / 2) =
        δ * |s| * (1 - δ / 2) + δ ^ 2 / 2 := by ring
    have hC : 0 ≤ δ * |s| * (1 - δ / 2) :=
      mul_nonneg (mul_nonneg hδ0 (abs_nonneg s)) (by linarith)
    have hD : 0 ≤ δ ^ 2 / 2 := by positivity
    rw [← hab]
    linarith

/-- Integration of the case (ii) pointwise bound against the noise law
`N(0, I_d) ⊗ Unif(0,1)`. -/
lemma noise_int {d : ℕ} (e : E d) (he : ‖e‖ = 1) (F : E d × ℝ → ℝ) {F0 A β δ : ℝ}
    (hA : 0 ≤ A) (hβ : 0 ≤ β) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hF0 : 0 ≤ F0)
    (hpt : ∀ ξ u, F (ξ, u) ≤ F0 +
      (if u ≤ gaussianPDFReal 0 1 (⟪e, ξ⟫_ℝ + δ) / gaussianPDFReal 0 1 ⟪e, ξ⟫_ℝ then 0 else
        A + β * max (|⟪e, ξ⟫_ℝ| - 1) 0)) :
    ∫⁻ ω, ENNReal.ofReal (F ω) ∂(noiseLaw d) ≤
      ENNReal.ofReal (F0 + A * (δ * (√(2 * Real.pi))⁻¹) + β * δ) := by
  set ρ : ℝ → ℝ := fun s => gaussianPDFReal 0 1 (s + δ) / gaussianPDFReal 0 1 s with hρ
  set W : ℝ → ℝ := fun s => A + β * max (|s| - 1) 0 with hW
  have hρeq : ρ = fun s => Real.exp (-(δ * s) - δ ^ 2 / 2) := funext fun s => ratio_eq s δ
  have hρc : Continuous ρ := by rw [hρeq]; fun_prop
  have hρpos : ∀ s, 0 < ρ s := by intro s; rw [hρeq]; exact Real.exp_pos _
  have hWc : Continuous W :=
    continuous_const.add (continuous_const.mul
      ((continuous_abs.sub continuous_const).max continuous_const))
  have hW0 : ∀ s, 0 ≤ W s := fun s =>
    add_nonneg hA (mul_nonneg hβ (le_max_right _ _))
  have hinner : Continuous fun ξ : E d => ⟪e, ξ⟫_ℝ := continuous_const.inner continuous_id
  set G : E d × ℝ → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (if ω.2 ≤ ρ ⟪e, ω.1⟫_ℝ then 0 else W ⟪e, ω.1⟫_ℝ) with hG
  have hGm : Measurable G := by
    apply Measurable.ennreal_ofReal
    apply Measurable.ite
    · exact measurableSet_le measurable_snd ((hρc.comp (hinner.comp continuous_fst)).measurable)
    · exact measurable_const
    · exact (hWc.comp (hinner.comp continuous_fst)).measurable
  set H : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal A * ENNReal.ofReal (1 - ρ s) + ENNReal.ofReal (β * δ) * ENNReal.ofReal (s ^ 2)
    with hH
  have hm1 : Measurable fun s => ENNReal.ofReal (1 - ρ s) :=
    (measurable_const.sub hρc.measurable).ennreal_ofReal
  have hm2 : Measurable fun s : ℝ => ENNReal.ofReal (s ^ 2) :=
    (measurable_id.pow_const 2).ennreal_ofReal
  have hHm : Measurable H := (measurable_const.mul hm1).add (measurable_const.mul hm2)
  have hinnerU : ∀ ξ : E d, ∫⁻ u, G (ξ, u) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) ≤
      H ⟪e, ξ⟫_ℝ := by
    intro ξ
    set s := ⟪e, ξ⟫_ℝ with hs
    have hind : (fun u => G (ξ, u)) =
        (Set.Ioi (ρ s)).indicator (fun _ => ENNReal.ofReal (W s)) := by
      funext u
      show ENNReal.ofReal (if u ≤ ρ s then 0 else W s) = _
      by_cases h : u ≤ ρ s
      · rw [if_pos h, ENNReal.ofReal_zero]
        simp [Set.indicator_apply, not_lt.2 h]
      · rw [if_neg h, Set.indicator_of_mem (show u ∈ Set.Ioi (ρ s) from lt_of_not_ge h)]
    have hmeas : volume.restrict (Set.Ioo (0 : ℝ) 1) (Set.Ioi (ρ s)) ≤ ENNReal.ofReal (1 - ρ s) := by
      rw [Measure.restrict_apply measurableSet_Ioi]
      calc volume (Set.Ioi (ρ s) ∩ Set.Ioo 0 1) ≤ volume (Set.Ioo (ρ s) 1) :=
            measure_mono (fun v hv => ⟨hv.1, hv.2.2⟩)
        _ = ENNReal.ofReal (1 - ρ s) := Real.volume_Ioo
    have hstep : ENNReal.ofReal (W s * (1 - ρ s)) ≤ H s := by
      rcases le_total (1 - ρ s) 0 with h | h
      · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (hW0 s) h)]
        positivity
      · have ht : max (|s| - 1) 0 * (1 - ρ s) ≤ δ * s ^ 2 := tail_bound hδ0 hδ s
        have hβt := mul_le_mul_of_nonneg_left ht hβ
        show _ ≤ ENNReal.ofReal A * ENNReal.ofReal (1 - ρ s) +
          ENNReal.ofReal (β * δ) * ENNReal.ofReal (s ^ 2)
        rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hβ hδ0),
          ← ENNReal.ofReal_add (mul_nonneg hA h) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have e1 : W s * (1 - ρ s) = A * (1 - ρ s) + β * (max (|s| - 1) 0 * (1 - ρ s)) := by
          rw [hW]; ring
        have e2 : β * (δ * s ^ 2) = β * δ * s ^ 2 := by ring
        rw [e1]; linarith
    calc ∫⁻ u, G (ξ, u) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))
        = ∫⁻ u, (Set.Ioi (ρ s)).indicator (fun _ => ENNReal.ofReal (W s)) u
            ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by rw [← hind]
      _ = ENNReal.ofReal (W s) * volume.restrict (Set.Ioo (0 : ℝ) 1) (Set.Ioi (ρ s)) :=
          lintegral_indicator_const measurableSet_Ioi _
      _ ≤ ENNReal.ofReal (W s) * ENNReal.ofReal (1 - ρ s) := mul_le_mul_of_nonneg_left hmeas (by positivity)
      _ = ENNReal.ofReal (W s * (1 - ρ s)) := (ENNReal.ofReal_mul (hW0 s)).symm
      _ ≤ H s := hstep
  have hkey : ∫⁻ ξ, H ⟪e, ξ⟫_ℝ ∂(stdGaussian (E d)) = ∫⁻ s, H s ∂(gaussianReal 0 1) := by
    rw [← map_inner_stdGaussian e he, lintegral_map hHm hinner.measurable]
  have htv : ∫⁻ s, ENNReal.ofReal (1 - ρ s) ∂(gaussianReal 0 1) ≤
      ENNReal.ofReal (δ * (√(2 * Real.pi))⁻¹) := tv_bound hδ0
  have hHint : ∫⁻ s, H s ∂(gaussianReal 0 1) ≤
      ENNReal.ofReal A * ENNReal.ofReal (δ * (√(2 * Real.pi))⁻¹) + ENNReal.ofReal (β * δ) * 1 := by
    show ∫⁻ s, (ENNReal.ofReal A * ENNReal.ofReal (1 - ρ s) +
      ENNReal.ofReal (β * δ) * ENNReal.ofReal (s ^ 2)) ∂(gaussianReal 0 1) ≤ _
    rw [lintegral_add_left (hm1.const_mul (ENNReal.ofReal A)), lintegral_const_mul _ hm1,
      lintegral_const_mul _ hm2, lintegral_sq_gaussianReal]
    exact add_le_add (mul_le_mul_of_nonneg_left htv (by positivity)) le_rfl
  have hpt' : ∀ ω, ENNReal.ofReal (F ω) ≤ ENNReal.ofReal F0 + G ω := by
    intro ω
    obtain ⟨ξ, u⟩ := ω
    calc ENNReal.ofReal (F (ξ, u)) ≤ ENNReal.ofReal (F0 +
          (if u ≤ ρ ⟪e, ξ⟫_ℝ then 0 else W ⟪e, ξ⟫_ℝ)) := ENNReal.ofReal_le_ofReal (hpt ξ u)
      _ ≤ _ := ENNReal.ofReal_add_le
  calc ∫⁻ ω, ENNReal.ofReal (F ω) ∂(noiseLaw d)
      ≤ ∫⁻ ω, ENNReal.ofReal F0 + G ω ∂(noiseLaw d) := lintegral_mono hpt'
    _ = ENNReal.ofReal F0 + ∫⁻ ω, G ω ∂(noiseLaw d) := by
        rw [lintegral_add_left measurable_const, lintegral_const, noise_univ, mul_one]
    _ = ENNReal.ofReal F0 + ∫⁻ ξ, ∫⁻ u, G (ξ, u) ∂(volume.restrict (Set.Ioo (0 : ℝ) 1))
          ∂(stdGaussian (E d)) := by
        rw [noiseLaw, lintegral_prod _ hGm.aemeasurable]
    _ ≤ ENNReal.ofReal F0 + ∫⁻ ξ, H ⟪e, ξ⟫_ℝ ∂(stdGaussian (E d)) :=
        add_le_add le_rfl (lintegral_mono hinnerU)
    _ ≤ ENNReal.ofReal F0 + (ENNReal.ofReal A * ENNReal.ofReal (δ * (√(2 * Real.pi))⁻¹) +
          ENNReal.ofReal (β * δ) * 1) := by rw [hkey]; exact add_le_add le_rfl hHint
    _ = ENNReal.ofReal (F0 + A * (δ * (√(2 * Real.pi))⁻¹) + β * δ) := by
        rw [mul_one, ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add hF0 (by positivity), add_assoc]

end HMCF

open MeasureTheory ProbabilityTheory CouplingHMC.Exact in open scoped ENNReal InnerProductSpace in
theorem solution {d : ℕ} (U : E d → ℝ) (L M N ℛ K : ℝ) (hU : Assumption21 U L M N ℛ K)
    (q p : ℝ → E d → E d → E d) (hflow : IsExactFlow U q p) (T : ℝ) (hT : 0 < T)
    (hTc : StepCond L K ℛ T) (x y : E d) :
    ∫⁻ ω, ENNReal.ofReal (fConc (aC T) (R1C T ℛ) (Rprime q T (gammaC T ℛ) ℛ x y ω))
        ∂(noiseLaw d) ≤
      ENNReal.ofReal ((1 - rateC K T ℛ) * fConc (aC T) (R1C T ℛ) ‖x - y‖) := by
  have ha : 0 < aC T := inv_pos.2 hT
  obtain ⟨hTK, hT4, hTR⟩ := hTc
  have hU' := hU
  obtain ⟨⟨hC, _⟩, _, ⟨hLb, _, _⟩, hR0, hK, _⟩ := hU'
  have hL : 0 ≤ L := (norm_nonneg _).trans (hLb 0)
  by_cases hxy : x = y
  · subst hxy
    have h0 : ∀ ω : E d × ℝ, Rprime q T (gammaC T ℛ) ℛ x x ω = 0 := by
      intro ω; unfold Rprime; rw [HMCF.eta_self, sub_self, norm_zero]
    simp only [h0, sub_self, norm_zero]
    simp [fConc]
  have hw : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hKL : K ≤ L := HMCF.K_le_L hU (x - y) hw
  have hr0 : 0 < ‖x - y‖ := norm_pos_iff.2 hw
  by_cases hr2 : ‖x - y‖ < 2 * ℛ
  · have hRpos : 0 < ℛ := by linarith
    have hγeq : gammaC T ℛ = min T⁻¹ (ℛ⁻¹ / 4) := by rw [gammaC, if_neg hRpos.ne']
    set γ := gammaC T ℛ with hγdef
    have hγ : 0 < γ := by rw [hγeq]; exact lt_min (inv_pos.2 hT) (by positivity)
    have hγT : γ * T ≤ 1 := by
      have : γ ≤ T⁻¹ := by rw [hγeq]; exact min_le_left _ _
      calc γ * T ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right this hT.le
        _ = 1 := inv_mul_cancel₀ hT.ne'
    have hγR : γ ≤ ℛ⁻¹ / 4 := by rw [hγeq]; exact min_le_right _ _
    have hδ : γ * ‖x - y‖ ≤ 1 / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hγR hr0.le
      have h2 : ℛ⁻¹ / 4 * ‖x - y‖ ≤ 1 / 2 := by
        have : ℛ⁻¹ / 4 * ‖x - y‖ = ‖x - y‖ / (4 * ℛ) := by field_simp
        rw [this, div_le_iff₀ (by positivity)]; linarith
      linarith
    have h16 : 16 * L * ℛ * T ≤ 1 := by
      have h0 : 0 ≤ 16 * L * ℛ * T := by positivity
      nlinarith
    have key : 4 * L * T ≤ γ := by
      rw [hγeq]
      apply le_min
      · rw [← one_div, le_div_iff₀ hT]; nlinarith
      · have : ℛ⁻¹ / 4 = 1 / (4 * ℛ) := by field_simp
        rw [this, le_div_iff₀ (by positivity)]; nlinarith
    have hLg : L * T ^ 2 ≤ γ * T / 4 := by nlinarith [mul_le_mul_of_nonneg_right key hT.le]
    set r := ‖x - y‖ with hr_def
    have hen : ‖r⁻¹ • (x - y)‖ = 1 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le), inv_mul_cancel₀ hr0.ne']
    have hg := HMCF.g_pos (aC T) (R1C T ℛ) r
    have hF0 : 0 ≤ fConc (aC T) (R1C T ℛ) r -
        6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ))) := by
      have hl := HMCF.fC_lower (R1 := R1C T ℛ) ha hr0.le
      have : 6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ))) ≤
          r * Real.exp (-(aC T * min r (R1C T ℛ))) := by
        calc 6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ)))
            = 6 / 7 * (γ * T) * (r * Real.exp (-(aC T * min r (R1C T ℛ)))) := by ring
          _ ≤ 1 * (r * Real.exp (-(aC T * min r (R1C T ℛ)))) :=
              mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hr0.le hg.le)
          _ = r * Real.exp (-(aC T * min r (R1C T ℛ))) := one_mul _
      linarith
    have hint := HMCF.noise_int (r⁻¹ • (x - y)) hen
      (fun ω => fConc (aC T) (R1C T ℛ) (Rprime q T γ ℛ x y ω))
      (F0 := fConc (aC T) (R1C T ℛ) r -
        6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ))))
      (A := 6 / 7 * (γ * r) * T * Real.exp (-(aC T * min r (R1C T ℛ))) +
        T * Real.exp (-(aC T * min r (R1C T ℛ))))
      (β := 16 / 7 * T * Real.exp (-(aC T * R1C T ℛ))) (δ := γ * r)
      (by positivity) (by positivity) (by positivity) hδ hF0 (fun ξ u => by
        show fConc _ _ ‖q T x ξ - q T y (couplingEta γ ℛ x y ξ u)‖ ≤ _
        rw [couplingEta, if_pos hr2]
        exact HMCF.caseII_pt hU hflow hT hT4 hLg hγ hγT x y hr0 hr2 ξ u)
    exact hint.trans (ENNReal.ofReal_le_ofReal (HMCF.caseII_real hT hK hKL hLg hγ hr0 hr2 hδ))
  · have hr2' : 2 * ℛ ≤ ‖x - y‖ := not_lt.1 hr2
    have hLK : L ^ 2 * T ^ 2 ≤ K := by
      rcases hL.eq_or_lt with h | h
      · rw [← h]; nlinarith
      · have := mul_le_mul_of_nonneg_left hTK h.le
        rw [mul_div_cancel₀ _ h.ne'] at this
        nlinarith [this]
    have hKT : K * T ^ 2 ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_right hKL (sq_nonneg T)]
    have hpt : ∀ ω : E d × ℝ,
        ENNReal.ofReal (fConc (aC T) (R1C T ℛ) (Rprime q T (gammaC T ℛ) ℛ x y ω)) ≤
          ENNReal.ofReal ((1 - rateC K T ℛ) * fConc (aC T) (R1C T ℛ) ‖x - y‖) := by
      intro ω
      apply ENNReal.ofReal_le_ofReal
      show fConc _ _ ‖q T x ω.1 - q T y (couplingEta (gammaC T ℛ) ℛ x y ω.1 ω.2)‖ ≤ _
      rw [couplingEta, if_neg hr2]
      exact HMCF.caseI_pt hT hR0 hK hKT hr0.le (norm_nonneg _)
        (HMCF.sync_contract hU hflow hT hT4 hLK x y ω.1 hr2')
    calc _ ≤ ∫⁻ _, ENNReal.ofReal ((1 - rateC K T ℛ) * fConc (aC T) (R1C T ℛ) ‖x - y‖)
          ∂(noiseLaw d) := lintegral_mono hpt
      _ = _ := by rw [lintegral_const, HMCF.noise_univ, mul_one]
