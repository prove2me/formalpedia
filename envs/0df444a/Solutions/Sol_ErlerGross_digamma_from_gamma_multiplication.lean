-- Prove2me | solution 1 for ErlerGross.digamma_from_gamma_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T19:56:15.714989+00:00
-- url     : https://prove2.me/submissions/751541de-e0c8-4a09-8cd9-633267aaea69

import Mathlib

theorem solution (n : Nat) (hn : 0 < n) (z : Complex)
    (hz : 0 < z.re) (c : Complex) (hc : c ≠ 0)
    (hmul : ∀ w : Complex,
      Finset.prod (Finset.range n) (fun k => Complex.Gamma (w + (k : Complex) / n)) =
        c * Complex.exp (-(n : Complex) * w * (Real.log n : Complex)) *
          Complex.Gamma ((n : Complex) * w)) :
    Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) =
      n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
  let F : Complex → Complex := fun w =>
    Finset.prod (Finset.range n) (fun k => Complex.Gamma (w + (k : Complex) / n))
  let G : Complex → Complex := fun w =>
    c * Complex.exp (-(n : Complex) * w * (Real.log n : Complex)) *
      Complex.Gamma ((n : Complex) * w)
  have hFG : F = G := funext hmul
  have hlog := congrArg (fun f : Complex → Complex => logDeriv f z) hFG
  have harg : ∀ k ∈ Finset.range n, 0 < (z + (k : Complex) / n).re := by
    intro k hk
    rw [Complex.add_re]
    have hcast : ((k : Complex) / n).re = (k : ℝ) / n := by
      rw [Complex.div_re]
      simp [Complex.normSq_natCast]
      field_simp
    rw [hcast]
    positivity
  have hprod_nonzero : ∀ k ∈ Finset.range n, Complex.Gamma (z + (k : Complex) / n) ≠ 0 := by
    intro k hk
    exact Complex.Gamma_ne_zero_of_re_pos (harg k hk)
  have hprod_diff : ∀ k ∈ Finset.range n,
      DifferentiableAt Complex (fun w => Complex.Gamma (w + (k : Complex) / n)) z := by
    intro k hk
    refine (Complex.differentiableAt_Gamma (z + (k : Complex) / n) ?_).comp z (by fun_prop)
    intro m hm
    have hp := harg k hk
    rw [hm] at hp
    norm_num at hp
    exact (not_lt_of_ge (Nat.cast_nonneg m) hp)
  have hleft := logDeriv_prod hprod_nonzero hprod_diff
  have hleft' : logDeriv F z =
      Finset.sum (Finset.range n) (fun k => Complex.digamma (z + (k : Complex) / n)) := by
    rw [show F = (fun x => Finset.prod (Finset.range n)
      (fun k => Complex.Gamma (x + (k : Complex) / n))) by rfl, hleft]
    apply Finset.sum_congr rfl
    intro k hk
    change logDeriv (Complex.Gamma ∘ (fun w => w + (k : Complex) / n)) z = _
    rw [logDeriv_comp]
    · simp [Complex.digamma_def, deriv_const_add]
    · apply Complex.differentiableAt_Gamma
      intro m hm
      have hp := harg k hk
      rw [hm] at hp
      norm_num at hp
      exact (not_lt_of_ge (Nat.cast_nonneg m) hp)
    · fun_prop
  have hscaled : Complex.Gamma ((n : Complex) * z) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [Complex.mul_re]
    simp
    nlinarith [mul_pos hnR hz]
  have hscaled_diff : DifferentiableAt Complex
      (fun w => Complex.Gamma ((n : Complex) * w)) z := by
    refine (Complex.differentiableAt_Gamma ((n : Complex) * z) ?_).comp z (by fun_prop)
    intro m hm
    have hp : 0 < ((n : Complex) * z).re := by
      rw [Complex.mul_re]
      simp
      nlinarith [mul_pos (Nat.cast_pos.mpr hn) hz]
    have hre := congrArg Complex.re hm
    rw [hm] at hp
    norm_num at hp
    exact (not_lt_of_ge (Nat.cast_nonneg m) hp)
  have hexp_diff : DifferentiableAt Complex
      (fun w => Complex.exp (-(n : Complex) * w * (Real.log n : Complex))) z := by
    fun_prop
  have hright : logDeriv G z =
      n * Complex.digamma ((n : Complex) * z) - n * (Real.log n : Complex) := by
    have hsplit := logDeriv_mul
      (f := fun w => c * Complex.exp (-(n : Complex) * w * (Real.log n : Complex)))
      (g := fun w => Complex.Gamma ((n : Complex) * w)) z
      (mul_ne_zero hc (Complex.exp_ne_zero _)) hscaled (by fun_prop) hscaled_diff
    change logDeriv G z = _
    rw [hsplit]
    rw [logDeriv_const_mul _ _ hc]
    change logDeriv (Complex.exp ∘ (fun w => -(n : Complex) * w * (Real.log n : Complex))) z +
        logDeriv (Complex.Gamma ∘ (fun w => (n : Complex) * w)) z = _
    rw [logDeriv_comp, logDeriv_comp]
    · simp [Complex.logDeriv_exp, Complex.digamma_def, deriv_const_mul,
        mul_comm, mul_left_comm, mul_assoc]
      ring
    · exact Complex.differentiableAt_Gamma _ (by
        intro m hm
        have hp : 0 < ((n : Complex) * z).re := by
          rw [Complex.mul_re]
          simp
          nlinarith [mul_pos (Nat.cast_pos.mpr hn) hz]
        rw [hm] at hp
        norm_num at hp
        exact (not_lt_of_ge (Nat.cast_nonneg m) hp))
    · fun_prop
    · fun_prop
    · fun_prop
  rw [hleft'] at hlog
  rw [hright] at hlog
  exact hlog
