-- Prove2me | solution 4 for ErlerGross.B3_series_digamma
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T11:32:39.326803+00:00
-- url     : https://prove2.me/submissions/da9e6273-d744-47e7-936f-7e0eb842d820

import Mathlib
import Definitions.Def_ErlerGross_defs

set_option autoImplicit false

open Real Filter Topology

namespace P2MBe529892

noncomputable def ff : ℝ → ℝ := Real.log ∘ Real.Gamma

lemma hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ ff x := by
  refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])

lemma h_rec (x : ℝ) (hx : 0 < x) : ff (x + 1) = ff x + Real.log x := by
  simp only [ff, Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]

lemma hder_rec (x : ℝ) (hx : 0 < x) : deriv ff (x + 1) = deriv ff x + 1 / x := by
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (hder hx) (Real.differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] using h_rec

lemma hder_nat (x : ℝ) (hx : 0 < x) (N : ℕ) :
    deriv ff (x + N) = deriv ff x + ∑ k ∈ Finset.range N, 1 / (x + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc,
      hder_rec (x + N) (by positivity), ih]
    ring

lemma mono : MonotoneOn (deriv ff) (Set.Ioi 0) :=
  Real.convexOn_log_Gamma.monotoneOn_deriv (fun _ hx => hder hx)

lemma main (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    HasSum (fun k : ℕ => 1 / (x + k) - 1 / (1 + k)) (deriv ff 1 - deriv ff x) := by
  have hnn : ∀ k : ℕ, 0 ≤ 1 / (x + k) - 1 / (1 + k) := fun k =>
    sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hs : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / (x + k) - 1 / (1 + k)) =
      (deriv ff 1 - deriv ff x) - (deriv ff (1 + N) - deriv ff (x + N)) := by
    intro N
    rw [Finset.sum_sub_distrib, hder_nat x hx N, hder_nat 1 one_pos N]
    ring
  simp_rw [hs]
  have he : Tendsto (fun N : ℕ => deriv ff (1 + N) - deriv ff (x + N)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun N : ℕ => 1 / (N : ℝ))
    · filter_upwards with N
      have := mono (a := x + N) (b := 1 + N) (by simp; positivity) (by simp; positivity)
        (by linarith)
      linarith
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 := hder_rec (N : ℝ) hN'
      have h2 := mono (a := (N : ℝ)) (b := x + N) (by simpa using hN') (by simp; positivity)
        (by linarith)
      rw [add_comm (1 : ℝ) N, h1]
      linarith
    · exact tendsto_one_div_atTop_nhds_zero_nat
  simpa using (tendsto_const_nhds (x := deriv ff 1 - deriv ff x)).sub he

private lemma complex_of_real' {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

lemma digamma_ofReal' (x : ℝ) (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv ff x : ℝ) : ℂ) := by
  have hne : ∀ m : ℕ, x ≠ -m := fun m => ne_of_gt (by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
  have hdR : DifferentiableAt ℝ Real.Gamma x := Real.differentiableAt_Gamma hne
  have hdC : DifferentiableAt ℂ Complex.Gamma (x : ℂ) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    apply hne m
    exact_mod_cast h
  have hD := complex_of_real' hdC hdR.hasDerivAt Complex.Gamma_ofReal
  have hff : deriv ff x = deriv Real.Gamma x / Real.Gamma x := by
    unfold ff
    rw [Function.comp_def, deriv.log hdR (Real.Gamma_pos_of_pos hx).ne']
  rw [Complex.digamma_def, logDeriv_apply, hD.deriv, Complex.Gamma_ofReal, hff,
    Complex.ofReal_div]

end P2MBe529892

open P2MBe529892 in
open Real Filter Topology MeasureTheory in
open ErlerGross in
theorem solution :
    HasSum (fun n : ℕ => ((b3Term (n + 1) : ℝ) : ℂ))
      (Complex.digamma ((2 : ℂ) / 3) / 2 + Complex.digamma ((1 : ℂ) / 3) / 2 -
        Complex.digamma ((1 : ℂ) / 2)) := by
  have h1 := main (1 / 2) (by norm_num) (by norm_num)
  have h2 := main (1 / 3) (by norm_num) (by norm_num)
  have h3 := main (2 / 3) (by norm_num) (by norm_num)
  have hR : HasSum (fun n : ℕ => ErlerGross.b3Term (n + 1))
      ((deriv ff 1 - deriv ff (1 / 2)) - 1 / 2 * (deriv ff 1 - deriv ff (2 / 3)) -
        1 / 2 * (deriv ff 1 - deriv ff (1 / 3))) := by
    have key : (fun n : ℕ => ErlerGross.b3Term (n + 1)) = fun n : ℕ =>
        (1 / (1 / 2 + (n : ℝ)) - 1 / (1 + (n : ℝ))) -
          1 / 2 * (1 / (2 / 3 + (n : ℝ)) - 1 / (1 + (n : ℝ))) -
          1 / 2 * (1 / (1 / 3 + (n : ℝ)) - 1 / (1 + (n : ℝ))) := by
      funext n
      unfold ErlerGross.b3Term
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have a1 : (2 * ((n : ℝ) + 1) - 1) ≠ 0 := by linarith
      have a2 : (2 * ((n : ℝ) + 1) - 2 / 3) ≠ 0 := by linarith
      have a3 : (2 * ((n : ℝ) + 1) - 4 / 3) ≠ 0 := by linarith
      have b1 : (1 / 2 + (n : ℝ)) ≠ 0 := by linarith
      have b2 : (1 / 3 + (n : ℝ)) ≠ 0 := by linarith
      have b3 : (2 / 3 + (n : ℝ)) ≠ 0 := by linarith
      have b4 : (1 + (n : ℝ)) ≠ 0 := by linarith
      push_cast
      rw [show (2 * ((n : ℝ) + 1) - 1) = 2 * (1 / 2 + n) by ring,
        show (2 * ((n : ℝ) + 1) - 2 / 3) = 2 * (2 / 3 + n) by ring,
        show (2 * ((n : ℝ) + 1) - 4 / 3) = 2 * (1 / 3 + n) by ring]
      generalize (1 / 2 + (n : ℝ)) = A
      generalize (2 / 3 + (n : ℝ)) = B
      generalize (1 / 3 + (n : ℝ)) = C
      ring
    rw [key]
    exact (h1.sub (h3.mul_left (1 / 2))).sub (h2.mul_left (1 / 2))
  have hC := (Complex.hasSum_ofReal).mpr hR
  convert hC using 1
  have e1 : ((2 : ℂ) / 3) = (((2 : ℝ) / 3 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((1 : ℂ) / 3) = (((1 : ℝ) / 3 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2, e3, digamma_ofReal' _ (by norm_num), digamma_ofReal' _ (by norm_num),
    digamma_ofReal' _ (by norm_num)]
  push_cast
  ring
