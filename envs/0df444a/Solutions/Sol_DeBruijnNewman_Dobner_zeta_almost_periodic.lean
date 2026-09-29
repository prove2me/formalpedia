-- Prove2me | solution 1 for DeBruijnNewman.Dobner.zeta_almost_periodic
-- status  : ACCEPTED   (prove)
-- author  : @adobner
-- created : 2026-09-24T22:01:26.264711+00:00
-- url     : https://prove2.me/submissions/34ddcb4f-ed86-430f-804e-59337ac1cedc

import Definitions.Def_DeBruijnNewman_Dobner

open Filter
open scoped Topology

/-!
Almost periodicity of the Gaussian-damped zeta Dirichlet series.

The proof uses only proved Mathlib results. Completing the square gives
a summable majorant on each right half-plane. Compact-group recurrence
in the product of unit circles then makes the weighted sum of the phase
errors arbitrarily small at arbitrarily large integer times.
-/

private theorem damped_weights_summable (t a : ℝ) (ht : t < 0) :
    Summable (fun n : ℕ =>
      Real.exp (t / 4 * Real.log ((n : ℝ) + 1) ^ 2
        - a * Real.log ((n : ℝ) + 1))) := by
  let K : ℝ := (a - 2) ^ 2 / (-t)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) 1).mpr h0
  apply (hbase.mul_left (Real.exp K)).of_norm_bounded
  intro n
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

private theorem circle_sub_one_norm_le_two (u : Circle) :
    ‖(u : ℂ) - 1‖ ≤ 2 := by
  calc
    ‖(u : ℂ) - 1‖ ≤ ‖(u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [Circle.norm_coe]

private noncomputable def phaseError (w : ℕ → ℝ) (u : ℕ → Circle) : ℝ :=
  ∑' n : ℕ, w n * ‖(u n : ℂ) - 1‖

private theorem phase_error_summable (w : ℕ → ℝ) (hw : Summable w)
    (hw0 : ∀ n, 0 ≤ w n) (u : ℕ → Circle) :
    Summable (fun n : ℕ => w n * ‖(u n : ℂ) - 1‖) := by
  apply (hw.mul_right 2).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 n) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (circle_sub_one_norm_le_two (u n)) (hw0 n)

private theorem phase_error_continuous (w : ℕ → ℝ) (hw : Summable w)
    (hw0 : ∀ n, 0 ≤ w n) : Continuous (phaseError w) := by
  apply continuous_tsum
  · intro n
    fun_prop
  · exact hw.mul_right 2
  · intro n u
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 n) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (circle_sub_one_norm_le_two (u n)) (hw0 n)

private theorem exists_large_weighted_almost_period
    (w frequency : ℕ → ℝ) (hw : Summable w) (hw0 : ∀ n, 0 ≤ w n)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    ∃ τ : ℝ, T ≤ τ ∧
      phaseError w (fun n => Circle.exp (-τ * frequency n)) < ε := by
  let x : ℕ → Circle := fun n => Circle.exp (-frequency n)
  have hcluster : MapClusterPt (0 : ℝ) atTop
      (fun m : ℕ => phaseError w (x ^ m)) := by
    have h := (mapClusterPt_one_atTop_pow x).continuousAt_comp
      (phase_error_continuous w hw hw0).continuousAt
    simpa [phaseError, Function.comp_def] using h
  have hfrequent : ∃ᶠ m : ℕ in atTop, phaseError w (x ^ m) < ε :=
    hcluster.frequently (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := exists_nat_ge T
  obtain ⟨m, hm, he⟩ := frequently_atTop.mp hfrequent N
  refine ⟨(m : ℝ), hN.trans (by exact_mod_cast hm), ?_⟩
  have hpow : x ^ m = fun n => Circle.exp (-(m : ℝ) * frequency n) := by
    funext n
    simp only [Pi.pow_apply, x, ← Circle.exp_natCast_mul]
    congr 1
    ring
  simpa only [hpow] using he

private noncomputable def dirichletTerm (t : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  Complex.exp
    (((t / 4 * Real.log ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ)
      - s * (Real.log ((n : ℝ) + 1) : ℂ))

private theorem term_norm_bound (t a : ℝ) (s : ℂ) (hs : a ≤ s.re) (n : ℕ) :
    ‖dirichletTerm t s n‖ ≤
      Real.exp (t / 4 * Real.log ((n : ℝ) + 1) ^ 2
        - a * Real.log ((n : ℝ) + 1)) := by
  unfold dirichletTerm
  rw [Complex.norm_exp]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg n))
  nlinarith

private theorem term_shift (t τ : ℝ) (s : ℂ) (n : ℕ) :
    dirichletTerm t (s + (τ : ℂ) * Complex.I) n =
      dirichletTerm t s n *
        (Circle.exp (-τ * Real.log ((n : ℝ) + 1)) : ℂ) := by
  unfold dirichletTerm
  rw [Circle.coe_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem solution (t : ℝ) (ht : t < 0)
    (a b : ℝ) (_hab : a < b) (ε : ℝ) (hε : 0 < ε) (T : ℝ) :
    ∃ τ : ℝ, T ≤ τ ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
        ‖DeBruijnNewman.Dobner.zetaT t (s + (τ : ℂ) * Complex.I)
          - DeBruijnNewman.Dobner.zetaT t s‖ < ε := by
  let w : ℕ → ℝ := fun n =>
    Real.exp (t / 4 * Real.log ((n : ℝ) + 1) ^ 2
      - a * Real.log ((n : ℝ) + 1))
  have hw : Summable w := damped_weights_summable t a ht
  have hw0 : ∀ n, 0 ≤ w n := fun n => (Real.exp_pos _).le
  obtain ⟨τ, hτ, he⟩ := exists_large_weighted_almost_period w
    (fun n => Real.log ((n : ℝ) + 1)) hw hw0 ε hε T
  refine ⟨τ, hτ, ?_⟩
  intro s hs _hsb
  let u : ℕ → Circle := fun n => Circle.exp (-τ * Real.log ((n : ℝ) + 1))
  have hsum (v : ℂ) (hv : a ≤ v.re) : Summable (dirichletTerm t v) :=
    hw.of_norm_bounded (term_norm_bound t a v hv)
  have hs' : a ≤ (s + (τ : ℂ) * Complex.I).re := by simpa using hs
  have hbound (n : ℕ) :
      ‖dirichletTerm t (s + (τ : ℂ) * Complex.I) n - dirichletTerm t s n‖
        ≤ w n * ‖(u n : ℂ) - 1‖ := by
    rw [term_shift]
    change ‖dirichletTerm t s n * (u n : ℂ) - dirichletTerm t s n‖ ≤ _
    rw [← mul_sub_one, norm_mul]
    exact mul_le_mul_of_nonneg_right (term_norm_bound t a s hs n) (norm_nonneg _)
  change ‖(∑' n, dirichletTerm t (s + (τ : ℂ) * Complex.I) n)
    - ∑' n, dirichletTerm t s n‖ < ε
  rw [← (hsum _ hs').tsum_sub (hsum _ hs)]
  exact (tsum_of_norm_bounded (phase_error_summable w hw hw0 u).hasSum hbound).trans_lt he
