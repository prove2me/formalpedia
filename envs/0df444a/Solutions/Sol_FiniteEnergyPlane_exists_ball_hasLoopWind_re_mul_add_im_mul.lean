-- Prove2me | solution 1 for FiniteEnergyPlane.exists_ball_hasLoopWind_re_mul_add_im_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T20:50:26.920098+00:00
-- url     : https://prove2.me/submissions/a3ad17f4-23e8-499c-a9d5-f4a924b37883

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

lemma c1w_ccwLoop_periodic (R : ℝ) : Function.Periodic (ccwLoop R) 1 := by
  intro t
  simp only [ccwLoop]
  congr 1
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma c1w_ccwLoop_continuous (R : ℝ) : Continuous (ccwLoop R) := by
  unfold ccwLoop
  fun_prop

lemma c1w_norm_ccwLoop (R t : ℝ) (hR : 0 ≤ R) : ‖ccwLoop R t‖ = R := by
  simp only [ccwLoop, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

lemma c1w_ccwLoop_pow (R t : ℝ) (m : ℕ) :
    ccwLoop R t ^ m = ((R ^ m : ℝ) : ℂ) * Complex.exp (((2 * π * m * t : ℝ) : ℂ) * Complex.I) := by
  simp only [ccwLoop, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- The loop `t ↦ a ρ^m e^{2πimt}` (`a ≠ 0`, `ρ > 0`) has winding number `m`. -/
lemma c1w_hasLoopWind_const_mul_pow (a : ℂ) (ha : a ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) :
    HasLoopWind (fun t => a * ccwLoop ρ t ^ m) m := by
  have hc : Continuous (fun t => a * ccwLoop ρ t ^ m) :=
    continuous_const.mul ((c1w_ccwLoop_continuous ρ).pow m)
  refine ⟨hc, fun t => by simp only [c1w_ccwLoop_periodic ρ t], fun t => ?_, ?_⟩
  · refine mul_ne_zero ha (pow_ne_zero _ ?_)
    intro h
    have := c1w_norm_ccwLoop ρ t hρ.le
    rw [h, norm_zero] at this
    linarith
  · refine ⟨fun t => Complex.arg a + 2 * π * m * t, by fun_prop, fun t => ?_, by push_cast; ring⟩
    have hn : ‖a * ccwLoop ρ t ^ m‖ = ‖a‖ * ρ ^ m := by
      rw [norm_mul, norm_pow, c1w_norm_ccwLoop ρ t hρ.le]
    dsimp only
    rw [hn, c1w_ccwLoop_pow]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I a]
    push_cast
    rw [show ((Complex.arg a : ℂ) + 2 * π * m * t) * Complex.I =
        (Complex.arg a : ℂ) * Complex.I + 2 * π * m * t * Complex.I by ring, Complex.exp_add]
    ring

lemma c1w_alg (w p q : ℂ) : (w.re : ℂ) * p + (w.im : ℂ) * q =
    (p - Complex.I * q) / 2 * w + (p + Complex.I * q) / 2 * starRingEnd ℂ w := by
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  have h2 : starRingEnd ℂ w = (w.re : ℂ) - (w.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(p - Complex.I * q) / 2) * hw + (-(p + Complex.I * q) / 2) * h2 +
    (q * (w.im : ℂ)) * Complex.I_sq

/-- Let `p, q` be continuous on `B(z₀, R)` with `Im(conj p(z₀) · q(z₀)) > 0` (so that
`w ↦ Re(w) p(z₀) + Im(w) q(z₀)` is an orientation-preserving real-linear isomorphism of `ℂ`), and let
`F(z) = Re((z - z₀)^m) p(z) + Im((z - z₀)^m) q(z)` on `B(z₀, R)`. Then on some smaller disc
`B(z₀, r)`, `F` has no zero other than `z₀`, and `F` has winding number `m` along every
counterclockwise circle `t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
theorem exists_ball_hasLoopWind_re_mul_add_im_mul_aux (F p q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hp : ContinuousOn p (ball z₀ R)) (hq : ContinuousOn q (ball z₀ R))
    (hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im)
    (hF : ∀ z ∈ ball z₀ R,
      F z = (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z) :
    ∃ r > (0 : ℝ), r ≤ R ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → F z ≠ 0) ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => F (z₀ + ccwLoop ρ t)) m := by
  set A : ℂ → ℂ := fun z => (p z - Complex.I * q z) / 2 with hA
  set B : ℂ → ℂ := fun z => (p z + Complex.I * q z) / 2 with hB
  have hFAB : ∀ z ∈ ball z₀ R, F z = A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) := by
    intro z hz
    rw [hF z hz]
    exact c1w_alg _ _ _
  -- `‖B z₀‖ < ‖A z₀‖`
  have hAB : ‖B z₀‖ < ‖A z₀‖ := by
    have key : Complex.normSq (A z₀) - Complex.normSq (B z₀) =
        (starRingEnd ℂ (p z₀) * q z₀).im := by
      simp only [hA, hB, Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
      norm_num
      ring
    have h2 : ‖B z₀‖ ^ 2 < ‖A z₀‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  set κ := ‖A z₀‖ - ‖B z₀‖ with hκ
  have hκ0 : 0 < κ := by linarith
  have hA0 : A z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hAB; exact absurd hAB (not_lt.2 (norm_nonneg _))
  have hzR : ball z₀ R ∈ 𝓝 z₀ := isOpen_ball.mem_nhds (mem_ball_self hR)
  have hAc : ContinuousAt A z₀ :=
    ((hp.continuousAt hzR).sub (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hBc : ContinuousAt B z₀ :=
    ((hp.continuousAt hzR).add (continuousAt_const.mul (hq.continuousAt hzR))).div_const _
  have hev : ∀ᶠ z in 𝓝 z₀, ‖A z - A z₀‖ < κ / 2 ∧ ‖B z - B z₀‖ < κ / 2 ∧ z ∈ ball z₀ R := by
    refine ((hAc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and
      (((hBc.sub continuousAt_const).norm.eventually (gt_mem_nhds ?_)).and hzR)
    · simp only [Pi.sub_apply, hA, sub_self, norm_zero]; exact half_pos hκ0
    · simp only [Pi.sub_apply, hB, sub_self, norm_zero]; exact half_pos hκ0
  obtain ⟨r, hr, hrs⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r' := min r R
  have hr' : 0 < r' := lt_min hr hR
  -- the key estimate `‖F z - A z₀ w‖ < ‖A z₀‖ ‖w‖` for `w = (z - z₀)^m ≠ 0`
  have hest : ∀ z ∈ ball z₀ r', z ≠ z₀ →
      ‖F z - A z₀ * (z - z₀) ^ m‖ < ‖A z₀ * (z - z₀) ^ m‖ := by
    intro z hz hne
    obtain ⟨h1, h2, h3⟩ := hrs z (ball_subset_ball (min_le_left _ _) hz)
    have hw : 0 < ‖(z - z₀) ^ m‖ := norm_pos_iff.2 (pow_ne_zero _ (sub_ne_zero.2 hne))
    rw [hFAB z h3, show A z * (z - z₀) ^ m + B z * starRingEnd ℂ ((z - z₀) ^ m) -
        A z₀ * (z - z₀) ^ m = (A z - A z₀) * (z - z₀) ^ m +
          B z * starRingEnd ℂ ((z - z₀) ^ m) by ring]
    have hBz : ‖B z‖ < ‖B z₀‖ + κ / 2 := by
      have := norm_sub_norm_le (B z) (B z₀)
      linarith
    calc _ ≤ ‖(A z - A z₀) * (z - z₀) ^ m‖ + ‖B z * starRingEnd ℂ ((z - z₀) ^ m)‖ :=
          norm_add_le _ _
      _ = (‖A z - A z₀‖ + ‖B z‖) * ‖(z - z₀) ^ m‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj]; ring
      _ < ‖A z₀‖ * ‖(z - z₀) ^ m‖ := by
          refine mul_lt_mul_of_pos_right ?_ hw; linarith
      _ = _ := (norm_mul _ _).symm
  refine ⟨r', hr', min_le_right _ _, fun z hz hne h0 => ?_, fun ρ hρ => ?_⟩
  · have := hest z hz hne
    rw [h0, zero_sub, norm_neg] at this
    exact lt_irrefl _ this
  · obtain ⟨hρ0, hρr⟩ := hρ
    set γ : ℝ → ℂ := fun t => z₀ + ccwLoop ρ t with hγ
    have hγb : ∀ t, γ t ∈ ball z₀ r' := fun t => by
      rw [mem_ball, dist_eq_norm, hγ, add_sub_cancel_left, c1w_norm_ccwLoop ρ t hρ0.le]
      exact hρr
    have hγne : ∀ t, γ t ≠ z₀ := fun t h => by
      have := c1w_norm_ccwLoop ρ t hρ0.le
      rw [show ccwLoop ρ t = γ t - z₀ by simp [hγ], h, sub_self, norm_zero] at this
      linarith
    have hγR : ∀ t, γ t ∈ ball z₀ R := fun t => ball_subset_ball (min_le_right _ _) (hγb t)
    have hγc : Continuous γ := continuous_const.add (c1w_ccwLoop_continuous ρ)
    have hFγ : (fun t => F (γ t)) = fun t => (((γ t - z₀) ^ m).re : ℂ) * p (γ t) +
        (((γ t - z₀) ^ m).im : ℂ) * q (γ t) := funext fun t => hF _ (hγR t)
    have hFc : Continuous (fun t => F (γ t)) := by
      rw [hFγ]
      have hpc : Continuous (fun t => p (γ t)) := hp.comp_continuous hγc hγR
      have hqc : Continuous (fun t => q (γ t)) := hq.comp_continuous hγc hγR
      have hw : Continuous (fun t => (γ t - z₀) ^ m) := (hγc.sub continuous_const).pow m
      exact ((Complex.continuous_ofReal.comp (Complex.continuous_re.comp hw)).mul hpc).add
        ((Complex.continuous_ofReal.comp (Complex.continuous_im.comp hw)).mul hqc)
    set L : ℝ → ℂ := fun t => A z₀ * ccwLoop ρ t ^ m with hL
    have hLw : HasLoopWind L m := c1w_hasLoopWind_const_mul_pow _ hA0 ρ hρ0 m
    have hL0 : ∀ t, L t ≠ 0 := hLw.2.2.1
    have hLγ : ∀ t, L t = A z₀ * (γ t - z₀) ^ m := fun t => by simp [hL, hγ]
    set Q : ℝ → ℂ := fun t => F (γ t) / L t with hQ
    have hQre : ∀ t, 0 < (Q t).re := by
      intro t
      have he := hest (γ t) (hγb t) (hγne t)
      rw [← hLγ] at he
      have hd : ‖Q t - 1‖ < 1 := by
        rw [hQ, show F (γ t) / L t - 1 = (F (γ t) - L t) / L t by field_simp [hL0 t],
          norm_div, div_lt_one (norm_pos_iff.2 (hL0 t))]
        exact he
      have := Complex.abs_re_le_norm (Q t - 1)
      rw [Complex.sub_re, Complex.one_re] at this
      have := abs_le.1 this
      linarith [this.1]
    have hQw : HasLoopWind Q 0 := by
      refine hasLoopWind_zero_of_forall_ne_ray Q (hFc.div (continuous_const.mul
        ((c1w_ccwLoop_continuous ρ).pow m)) hL0) ?_ (-1) (by norm_num) ?_
      · intro t
        simp only [hQ, hL, hγ, c1w_ccwLoop_periodic ρ t]
      · intro t s hs h
        have := hQre t
        rw [h] at this
        simp at this
        linarith
    have hprod := hasLoopWind_mul hLw hQw
    rw [add_zero] at hprod
    have heq : (fun t => L t * Q t) = fun t => F (z₀ + ccwLoop ρ t) := funext fun t => by
      simp only [hQ]
      field_simp [hL0 t]
      try rfl
    rw [heq] at hprod
    exact hprod

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped Real

theorem solution (F p q : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hp : ContinuousOn p (ball z₀ R)) (hq : ContinuousOn q (ball z₀ R))
    (hpq : 0 < (starRingEnd ℂ (p z₀) * q z₀).im)
    (hF : ∀ z ∈ ball z₀ R,
      F z = (((z - z₀) ^ m).re : ℂ) * p z + (((z - z₀) ^ m).im : ℂ) * q z) :
    ∃ r > (0 : ℝ), r ≤ R ∧ (∀ z ∈ ball z₀ r, z ≠ z₀ → F z ≠ 0) ∧
      ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => F (z₀ + ccwLoop ρ t)) m :=
  exists_ball_hasLoopWind_re_mul_add_im_mul_aux F p q z₀ R hR m hp hq hpq hF
