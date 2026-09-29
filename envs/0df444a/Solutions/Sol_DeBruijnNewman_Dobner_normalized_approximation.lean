-- Prove2me | solution 1 for DeBruijnNewman.Dobner.normalized_approximation
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T22:35:24.385696+00:00
-- url     : https://prove2.me/submissions/e0c5de93-89aa-4e72-b43f-28fc18b49372

import Theorems.Thm_DeBruijnNewman_H_entire_negative
import Theorems.Thm_DeBruijnNewman_Dobner_mellin_series_representation
import Theorems.Thm_DeBruijnNewman_Dobner_mellin_mode_approximation
import Theorems.Thm_DeBruijnNewman_Dobner_mellin_uniform_majorant

open Filter Set Metric DeBruijnNewman DeBruijnNewman.Dobner
open scoped Topology

/-!
Dobner's fixed-time, fixed-strip approximation, reduced to the
Gaussian–Mellin series representation and two coefficient estimates.
Holomorphy is proved from the negative-time entirety of the canonical
heat integral. The passage from coefficient estimates to the uniform
strip approximation is a dominated-convergence argument.
-/

private theorem gamma_arguments_avoid_poles (s : ℂ) (hs : 0 < s.im) :
    ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
  intro n hn
  have hi := congrArg Complex.im hn
  norm_num at hi
  linarith

private theorem gammaT_nonzero (t : ℝ) (s : ℂ) (hs : 0 < s.im) :
    gammaT t s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have he : s = 1 := sub_eq_zero.mp h
    simp [he] at hs
  unfold gammaT gammaFactor
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (div_ne_zero (mul_ne_zero hs0 hs1) (by norm_num))
        (Complex.exp_ne_zero _))
      (Complex.Gamma_ne_zero (gamma_arguments_avoid_poles s hs)))
    (Complex.exp_ne_zero _)

private theorem J_differentiable (t : ℝ) (s : ℂ) (hs : 0 < s.im) :
    DifferentiableAt ℂ (J t) s := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hq : s / ((2 * Real.pi : ℝ) : ℂ) ∈ Complex.slitPlane := by
    right
    have hi : (s / ((2 * Real.pi : ℝ) : ℂ)).im = s.im / (2 * Real.pi) :=
      Complex.div_ofReal_im _ _
    rw [hi]
    exact ne_of_gt (div_pos hs hpi)
  have hlog := (Complex.differentiableAt_log hq).comp s
    (differentiableAt_id.div_const ((2 * Real.pi : ℝ) : ℂ))
  unfold J
  exact differentiableAt_id.add (hlog.const_mul ((|t| / 4 : ℝ) : ℂ))

private theorem gammaT_differentiable (t : ℝ) (s : ℂ) (hs : 0 < s.im) :
    DifferentiableAt ℂ (gammaT t) s := by
  have hG : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w / 2)) s :=
    (Complex.differentiableAt_Gamma (s / 2) (gamma_arguments_avoid_poles s hs)).comp s
      (differentiableAt_id.div_const 2)
  have hfactor : DifferentiableAt ℂ gammaFactor s := by
    unfold gammaFactor
    fun_prop
  unfold gammaT
  exact hfactor.mul (((differentiableAt_id.sub (J_differentiable t s hs)).pow 2).div_const
    ((|t| : ℝ) : ℂ)).cexp

private theorem normalized_holomorphic (t : ℝ) (ht : t < 0) :
    DifferentiableOn ℂ (normalizedXi t) {s : ℂ | 0 < s.im} := by
  have hH := H_entire_negative t ht
  have hxi : Differentiable ℂ (xiT t) := by
    unfold xiT
    fun_prop
  intro s hs
  exact (((hxi (J t s)).comp s (J_differentiable t s hs)).div
    (gammaT_differentiable t s hs) (gammaT_nonzero t s hs)).differentiableWithinAt

private noncomputable def weight (t a : ℝ) (n : ℕ) : ℝ :=
  Real.exp (t / 4 * Real.log ((n : ℝ) + 1) ^ 2
    - a * Real.log ((n : ℝ) + 1))

private theorem weights_summable (t a : ℝ) (ht : t < 0) :
    Summable (weight t a) := by
  let K : ℝ := (a - 2) ^ 2 / (-t)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 1).mpr h0
  apply (hbase.mul_left (Real.exp K)).of_norm_bounded
  intro n
  unfold weight
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.rpow_def_of_pos (by positivity : 0 < (n : ℝ) + 1), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hquad :
      t / 4 * Real.log ((n : ℝ) + 1) ^ 2
        + (2 - a) * Real.log ((n : ℝ) + 1) ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ (neg_pos.mpr ht)).mpr
    nlinarith [sq_nonneg (t / 2 * Real.log ((n : ℝ) + 1) + (2 - a))]
  linarith

private theorem term_norm_bound (t a : ℝ) (s : ℂ) (hs : a ≤ s.re) (n : ℕ) :
    ‖zetaTerm t s n‖ ≤ weight t a n := by
  unfold zetaTerm weight
  rw [Complex.norm_exp]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  nlinarith

private theorem gaussian_log_weights_summable (t : ℝ) (ht : t < 0) :
    Summable (fun n : ℕ => Real.exp (t / 40 * Real.log ((n : ℝ) + 1) ^ 2)) := by
  convert! weights_summable (t / 10) 0 (div_neg_of_neg_of_pos ht (by norm_num)) using 1
  ext n
  unfold weight
  congr 1
  ring

private theorem error_hasSum (t : ℝ) (ht : t < 0) (s : ℂ) :
    HasSum (fun n : ℕ => normalizedMellinTerm t s n - zetaTerm t s n)
      (normalizedXi t s - zetaT t s) := by
  have hM : HasSum (normalizedMellinTerm t s) (normalizedXi t s) := by
    simpa only [normalizedMellinTerm, normalizedXi] using!
      (mellin_series_representation t ht s).div_const (gammaT t s)
  have hZ : Summable (zetaTerm t s) :=
    (weights_summable t s.re ht).of_norm_bounded (term_norm_bound t s.re s le_rfl)
  have hZ' : HasSum (zetaTerm t s) (zetaT t s) := by
    simpa only [zetaTerm, zetaT] using! hZ.hasSum
  exact hM.sub hZ'

private theorem uniform_strip_approximation (t : ℝ) (ht : t < 0)
    (a b : ℝ) (hab : a < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
      ‖normalizedXi t s - zetaT t s‖ < ε := by
  classical
  by_contra! hbad
  choose s hs using fun k : ℕ => hbad (k : ℝ)
  have hheight : Tendsto (fun k : ℕ => (s k).im) atTop atTop :=
    tendsto_atTop_mono (fun k => (hs k).2.2.1) tendsto_natCast_atTop_atTop
  obtain ⟨C, Y, hC, _hY, hmajor⟩ := mellin_uniform_majorant t ht a b hab
  let bound : ℕ → ℝ := fun n =>
    C * Real.exp (t / 40 * Real.log ((n : ℝ) + 1) ^ 2) + weight t a n
  have hsum : Summable bound :=
    ((gaussian_log_weights_summable t ht).mul_left C).add (weights_summable t a ht)
  have hlim (n : ℕ) : Tendsto
      (fun k : ℕ => normalizedMellinTerm t (s k) n - zetaTerm t (s k) n)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨Yn, hn⟩ := mellin_mode_approximation t ht a b hab n η hη
    filter_upwards [(tendsto_atTop.mp hheight) Yn] with k hk
    simpa only [dist_zero_right] using hn (s k) (hs k).1 (hs k).2.1 hk
  have hdom : ∀ᶠ k : ℕ in atTop, ∀ n : ℕ,
      ‖normalizedMellinTerm t (s k) n - zetaTerm t (s k) n‖ ≤ bound n := by
    filter_upwards [(tendsto_atTop.mp hheight) Y] with k hk n
    calc
      _ ≤ ‖normalizedMellinTerm t (s k) n‖ + ‖zetaTerm t (s k) n‖ := norm_sub_le _ _
      _ ≤ bound n := add_le_add
        (hmajor (s k) (hs k).1 (hs k).2.1 hk n)
        (term_norm_bound t a (s k) (hs k).1 n)
  have hconv := tendsto_tsum_of_dominated_convergence hsum hlim hdom
  have htotal : Tendsto (fun k : ℕ => normalizedXi t (s k) - zetaT t (s k))
      atTop (𝓝 0) := by
    simpa only [(error_hasSum t ht _).tsum_eq, tsum_zero] using hconv
  have hevent : ∀ᶠ k : ℕ in atTop, ‖normalizedXi t (s k) - zetaT t (s k)‖ < ε := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp htotal) ε hε
  obtain ⟨k, hk⟩ := hevent.exists
  exact (not_lt_of_ge (hs k).2.2.2) hk

theorem solution (t : ℝ) (ht : t < 0) :
    DifferentiableOn ℂ (DeBruijnNewman.Dobner.normalizedXi t) {s : ℂ | 0 < s.im} ∧
      ∀ (a b : ℝ), a < b → ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ,
        ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
          ‖DeBruijnNewman.Dobner.normalizedXi t s
            - DeBruijnNewman.Dobner.zetaT t s‖ < ε := by
  exact ⟨normalized_holomorphic t ht, uniform_strip_approximation t ht⟩
