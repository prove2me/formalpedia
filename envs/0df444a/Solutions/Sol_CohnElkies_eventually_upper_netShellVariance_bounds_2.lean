-- Prove2me | solution 2 for CohnElkies.eventually_upper_netShellVariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T13:36:26.457322+00:00
-- url     : https://prove2.me/submissions/6229c690-b5f0-41c4-9f10-d3c8712af6e3

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h48_margin_ev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
    ∀ a ∈ Set.Icc (shortCutoff ε) (shortEndpoint ε), 0 ≤ shortMargin ε a := by
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 160000 by norm_num)] with ε hε
  intro a ha
  obtain ⟨hε0, hε1⟩ := hε
  set t := Real.sqrt ε with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hε0
  have htt : t ^ 2 = ε := Real.sq_sqrt hε0.le
  have ht1 : t < 1 / 400 := by
    rw [ht, Real.sqrt_lt' (by norm_num)]; norm_num; linarith
  have hlog : Real.log (1 / ε) ≤ 2 / t := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (show (0:ℝ) < 1 / ε by positivity))
    rw [Real.log_sqrt (by positivity)] at h1
    have : Real.sqrt (1 / ε) = 1 / t := by rw [ht, Real.sqrt_div' _ hε0.le, Real.sqrt_one]
    rw [this] at h1
    have : 2 / t = 2 * (1 / t) := by ring
    linarith
  have haE : a ≤ 20 / t := by
    have := ha.2; unfold shortEndpoint at this
    have : 10 * Real.log (1 / ε) ≤ 20 / t := by
      have h2 : 10 * (2 / t) = 20 / t := by ring
      linarith
    linarith
  unfold shortMargin
  have : 10 * ε * (1 + a) ≤ 10 * t ^ 2 + 200 * t := by
    rw [← htt]
    have h3 : 10 * t ^ 2 * (1 + a) ≤ 10 * t ^ 2 * (1 + 20 / t) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : 10 * t ^ 2 * (1 + 20 / t) = 10 * t ^ 2 + 200 * t := by field_simp; ring
    linarith
  nlinarith

theorem solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        (99 / 100 : ℝ) *
            upperPositiveShellVariance ε δ ≤
          upperNetShellVariance ε δ ∧
        upperNetShellVariance ε δ ≤
          upperPositiveShellVariance ε δ := by
  filter_upwards [self_mem_nhdsWithin, h48_margin_ev, eventually_upper_shortCutoff_le_shortEndpoint,
    Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 50 by norm_num)]
    with ε hε hmargin horder hε40
  have hε0 : 0 < ε := hε
  intro δ hδ
  have hδ0 : 0 < δ := by linarith
  have hc0 : 0 < shortCutoff ε := by unfold shortCutoff; positivity
  set E := shortEndpoint ε with hE
  set L := shellLocation ε with hL
  set w := shellWeight ε with hw
  set x : ℝ := 1 / ε with hx
  have hx40 : 50 < x := by rw [hx, lt_div_iff₀ hε0]; linarith [hε40.2]
  have hx0 : 0 < x := by linarith
  have hεx : ε * x = 1 := by rw [hx]; field_simp
  have hLx : L = x ^ 3 := by rw [hL, hx]; unfold shellLocation; field_simp
  have hE0 : 0 < E := hc0.trans_le horder
  -- E ≤ 10x/3
  have hlog : Real.log x ≤ 2 * Real.sqrt x := by
    have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
    rw [Real.log_sqrt hx0.le] at h1; linarith
  have hsqrt : Real.sqrt x ≤ x / 6 := by
    have h6 : 6 ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) hx0.le]; linarith
    have := Real.mul_self_sqrt hx0.le
    nlinarith
  have hEx : E ≤ 10 * x / 3 := by
    rw [hE]; unfold shortEndpoint; rw [← hx]; nlinarith
  have hx2 : 2500 ≤ x ^ 2 := by nlinarith
  have hLE : E < L := by
    have : 10 * x / 3 < x ^ 3 := by nlinarith
    rw [hLx]; linarith
  -- short ≥ 0 and short ≤ (E/2) e^{(1+δ)E}
  have hsm : ∀ a ∈ Icc (shortCutoff ε) E, 0 ≤ -shortShellDensity ε a ∧
      -shortShellDensity ε a * a ^ 2 ≤ 1 / 2 := by
    intro a ha
    have ha0 : 0 < a := hc0.trans_le ha.1
    have hm := hmargin a ha
    have hm1 : shortMargin ε a ≤ 1 := by
      unfold shortMargin; have : 0 ≤ 10 * ε * (1 + a) := by positivity
      linarith
    have hcosh := Real.one_le_cosh a
    have hexp : Real.exp (-2 * a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    unfold shortShellDensity
    rw [neg_neg]
    constructor
    · positivity
    · rw [show shortMargin ε a * Real.exp (-2 * a) / (2 * a ^ 2 * Real.cosh a) * a ^ 2 =
        shortMargin ε a * Real.exp (-2 * a) / (2 * Real.cosh a) by field_simp]
      rw [div_le_iff₀ (by positivity)]
      have : shortMargin ε a * Real.exp (-2 * a) ≤ 1 := by
        calc shortMargin ε a * Real.exp (-2 * a) ≤ 1 * 1 :=
              mul_le_mul hm1 hexp (Real.exp_pos _).le zero_le_one
          _ = 1 := by ring
      nlinarith
  have hsint : IntervalIntegrable (fun a => -shortShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a))
      volume (shortCutoff ε) E := by
    have h0 := (shortShellDensity_intervalIntegrable hε0 horder).neg.mul_continuousOn
      (Continuous.continuousOn (f := fun a : ℝ => a ^ 2 * Real.cosh ((1 + δ) * a)) (by fun_prop))
    convert h0 using 1
    funext a; simp only [Pi.neg_apply]; ring
  have hshort0 : 0 ≤ upperShortShellVariance ε δ := by
    unfold upperShortShellVariance
    apply intervalIntegral.integral_nonneg horder
    intro a ha
    have := Real.cosh_pos ((1 + δ) * a)
    have h := hsm a ha
    have : 0 ≤ -shortShellDensity ε a * a ^ 2 := mul_nonneg h.1 (sq_nonneg a)
    positivity
  have hshort : upperShortShellVariance ε δ ≤ (E / 2) * Real.exp ((1 + δ) * E) := by
    unfold upperShortShellVariance
    have hb : ∀ a ∈ Icc (shortCutoff ε) E, -shortShellDensity ε a * a ^ 2 * Real.cosh ((1 + δ) * a) ≤
        1 / 2 * Real.exp ((1 + δ) * E) := by
      intro a ha
      have ha0 : 0 < a := hc0.trans_le ha.1
      have h := hsm a ha
      have hch : Real.cosh ((1 + δ) * a) ≤ Real.exp ((1 + δ) * E) := by
        have hy : 0 ≤ (1 + δ) * a := by positivity
        have hc1 : Real.cosh ((1 + δ) * a) ≤ Real.exp ((1 + δ) * a) := by
          rw [Real.cosh_eq]
          have : Real.exp (-((1 + δ) * a)) ≤ Real.exp ((1 + δ) * a) := Real.exp_le_exp.mpr (by linarith)
          linarith
        refine hc1.trans (Real.exp_le_exp.mpr ?_)
        exact mul_le_mul_of_nonneg_left ha.2 (by linarith)
      exact mul_le_mul h.2 hch (Real.cosh_pos _).le (by norm_num)
    have := intervalIntegral.integral_mono_on horder hsint intervalIntegrable_const hb
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hlen : E - shortCutoff ε ≤ E := by linarith
    calc _ ≤ (E - shortCutoff ε) * (1 / 2 * Real.exp ((1 + δ) * E)) := this
      _ ≤ E * (1 / 2 * Real.exp ((1 + δ) * E)) :=
          mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = _ := by ring
  -- pos ≥ (w L^2 / 2) e^{δ L}
  have hL0 : 0 < L := by linarith
  have hw0 : 0 < w := shellWeight_pos ε
  have hpos : w * L ^ 2 / 2 * Real.exp (δ * L) ≤ upperPositiveShellVariance ε δ := by
    unfold upperPositiveShellVariance
    have hconst : (∫ a in L..L + 1, w * L ^ 2 / 2 * Real.exp (δ * L)) = w * L ^ 2 / 2 * Real.exp (δ * L) := by
      simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    · exact (Continuous.intervalIntegrable (by
        have := positiveShellDensity_continuous ε; fun_prop) _ _)
    · intro a ha
      have ha0 : 0 < a := hL0.trans_le ha.1
      unfold positiveShellDensity
      rw [← hw]
      have hca := Real.cosh_pos a
      have h1 : Real.exp ((1 + δ) * a) / 2 ≤ Real.cosh ((1 + δ) * a) := by
        rw [Real.cosh_eq]; have := Real.exp_pos (-((1 + δ) * a)); linarith
      have h2 : Real.cosh a ≤ Real.exp a := by
        rw [Real.cosh_eq]; have : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
        linarith
      have h3 : Real.exp ((1 + δ) * a) = Real.exp a * Real.exp (δ * a) := by
        rw [← Real.exp_add]; ring_nf
      have h4 : Real.exp (δ * L) ≤ Real.exp (δ * a) := Real.exp_le_exp.mpr (by nlinarith [ha.1])
      have hL2 : L ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hL0.le ha.1 2
      have key : Real.exp (δ * a) / 2 ≤ Real.cosh ((1 + δ) * a) / Real.cosh a := by
        rw [le_div_iff₀ hca]
        calc Real.exp (δ * a) / 2 * Real.cosh a ≤ Real.exp (δ * a) / 2 * Real.exp a := by
              apply mul_le_mul_of_nonneg_left h2; positivity
          _ = Real.exp ((1 + δ) * a) / 2 := by rw [h3]; ring
          _ ≤ _ := h1
      calc w * L ^ 2 / 2 * Real.exp (δ * L) ≤ w * a ^ 2 * (Real.exp (δ * a) / 2) := by
            have := mul_le_mul hL2 h4 (Real.exp_pos _).le (sq_nonneg a)
            nlinarith
        _ ≤ w * a ^ 2 * (Real.cosh ((1 + δ) * a) / Real.cosh a) := by
            apply mul_le_mul_of_nonneg_left key; positivity
        _ = w / Real.cosh a * a ^ 2 * Real.cosh ((1 + δ) * a) := by field_simp
  -- comparison
  have hcmp : 100 * ((E / 2) * Real.exp ((1 + δ) * E)) ≤ w * L ^ 2 / 2 * Real.exp (δ * L) := by
    have h100 : 100 * E ≤ Real.exp x := by
      have := Real.pow_div_factorial_le_exp x hx0.le 3
      simp [Nat.factorial] at this
      have : 1000 * x / 3 ≤ x ^ 3 / 6 := by nlinarith
      linarith
    have hexpo : x + E ≤ -(3 * ε * L / 8) + ε / 2 * (L - E) := by
      have hεL : ε * L = x ^ 2 := by rw [hLx]; have := hεx; nlinarith
      have hεE : ε * E ≤ 10 / 3 := by
        have := mul_le_mul_of_nonneg_left hEx hε0.le
        have e : ε * (10 * x / 3) = 10 / 3 := by rw [mul_div_assoc', ← mul_assoc, mul_comm ε 10, mul_assoc, hεx]; ring
        linarith
      nlinarith
    have hwexp : w = Real.exp (-(3 * ε * L / 8)) := by
      rw [hw]; unfold shellWeight; congr 1; rw [hL]; ring
    have hL1 : 1 ≤ L ^ 2 := by
      have : 1 ≤ x ^ 3 := one_le_pow₀ (by linarith)
      rw [hLx]; nlinarith
    have hδLE : ε / 2 * (L - E) ≤ δ * (L - E) := mul_le_mul_of_nonneg_right hδ (by linarith)
    have step : 100 * E * Real.exp E ≤ Real.exp (-(3 * ε * L / 8) + δ * (L - E)) := by
      calc 100 * E * Real.exp E ≤ Real.exp x * Real.exp E :=
            mul_le_mul_of_nonneg_right h100 (Real.exp_pos _).le
        _ = Real.exp (x + E) := by rw [Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have e1 : Real.exp ((1 + δ) * E) = Real.exp E * Real.exp (δ * E) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : w * Real.exp (δ * L) = Real.exp (-(3 * ε * L / 8) + δ * (L - E)) * Real.exp (δ * E) := by
      rw [hwexp, ← Real.exp_add, ← Real.exp_add]; ring_nf
    have hdE := Real.exp_pos (δ * E)
    calc 100 * ((E / 2) * Real.exp ((1 + δ) * E)) = (100 * E * Real.exp E) * Real.exp (δ * E) / 2 := by
          rw [e1]; ring
      _ ≤ Real.exp (-(3 * ε * L / 8) + δ * (L - E)) * Real.exp (δ * E) / 2 := by
          gcongr
      _ = w * Real.exp (δ * L) / 2 := by rw [e2]
      _ ≤ w * L ^ 2 / 2 * Real.exp (δ * L) := by
          have := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ w * Real.exp (δ * L) by positivity)
          nlinarith
  unfold upperNetShellVariance
  constructor <;> nlinarith

