-- Prove2me | solution 1 for Gelbart.hecke_mellin_representation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T23:44:18.09559+00:00
-- url     : https://prove2.me/submissions/d9b509b0-b99d-4297-9855-8a1d67b8041b

import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_Gelbart_hecke_series
import Theorems.Thm_Gelbart_hecke_LSeriesSummable
import Theorems.Thm_Gelbart_heckeForm_summable

open scoped BigOperators
open MeasureTheory Set

namespace Gelbart

private lemma term_on_imaginary (a : ℕ → ℂ) (h t : ℝ) (n : ℕ) :
    a n * Complex.exp (2 * Real.pi * Complex.I * n * (Complex.I * t) / h) =
      a n * (Real.exp (-(2*Real.pi/h) * n * t) : ℂ) := by
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  calc
    2 * ↑Real.pi * Complex.I * ↑n * (Complex.I * ↑t) / ↑h =
        (Complex.I * Complex.I) * (2 * ↑Real.pi / ↑h * ↑n * ↑t) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

private lemma form_on_imaginary (a : ℕ → ℂ) (h t : ℝ) :
    heckeForm a h (Complex.I * t) =
      ∑' n : ℕ, a n * (Real.exp (-(2*Real.pi/h) * n * t) : ℂ) :=
  tsum_congr (term_on_imaginary a h t)

theorem hecke_mellin_representation
    (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : HeckeCoeffGrowth a c) {s : ℂ} (hs : c + 1 < s.re) :
    heckeCompletedLSeries a h s =
      ∫ y in Set.Ioi (0 : ℝ),
        (heckeForm a h (Complex.I * y) - a 0) * (y : ℂ) ^ (s - 1) := by
  let b : ℝ := 2 * Real.pi / h
  have hb : 0 < b := div_pos (mul_pos (by norm_num) Real.pi_pos) hh
  have hs0 : 0 < s.re := by linarith
  have hls := hecke_LSeriesSummable a c hc hgrowth hs
  have hnorm : Summable (fun n : ℕ => ‖a (n+1)‖ / ((n+1:ℕ):ℝ)^s.re) := by
    simpa only [LSeries.norm_term_eq, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, ↓reduceIte] using (summable_nat_add_iff 1).2 hls.norm
  have hL : HasSum (fun n : ℕ => a (n+1) / ((n+1:ℕ):ℂ)^s) (LSeries a s) := by
    have hh : HasSum (fun n : ℕ => LSeries.term a s (n+1)) (LSeries a s) :=
      (hasSum_nat_add_iff 1 (f := LSeries.term a s)).2 (by simpa [LSeries] using hls.hasSum)
    simpa [LSeries.term] using hh
  have hF : ∀ t ∈ Ioi (0:ℝ),
      HasSum (fun n : ℕ => a (n+1) * (Real.exp (-(b*((n+1:ℕ):ℝ))*t) : ℂ))
        (heckeForm a h (Complex.I*t)-a 0) := by
    intro t ht
    have hfull : Summable (fun n : ℕ => a n * (Real.exp (-b*n*t) : ℂ)) := by
      have hz : 0 < (Complex.I * (t:ℂ)).im := by simpa using ht
      exact (heckeForm_summable a c h hc hh hgrowth hz).congr
        (term_on_imaginary a h t)
    have htail : HasSum
        (fun n : ℕ => a (n+1) * (Real.exp (-b * ((n+1:ℕ):ℝ) * t) : ℂ))
        (heckeForm a h (Complex.I*t)-a 0) := by
      apply (hasSum_nat_add_iff 1
        (f := fun n : ℕ => a n * (Real.exp (-b * n * t) : ℂ))).2
      convert! hfull.hasSum using 1
      rw [form_on_imaginary]
      simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_mul,
        Real.exp_zero, Complex.ofReal_one, mul_one]
      dsimp [b]
      ring
    convert! htail using 1
    funext n
    congr 2
    ring
  have hnorm' : Summable (fun n : ℕ => ‖a (n+1)‖ / (b*((n+1:ℕ):ℝ))^s.re) := by
    apply (hnorm.div_const (b^s.re)).congr
    intro n
    rw [Real.mul_rpow hb.le (by positivity)]
    ring
  have hM := hasSum_mellin (a := fun n : ℕ => a (n+1))
    (p := fun n : ℕ => b*((n+1:ℕ):ℝ))
    (F := fun t => heckeForm a h (Complex.I*t)-a 0)
    (fun n => Or.inr (mul_pos hb (by positivity))) hs0 hF hnorm'
  have hM' : HasSum
      (fun n : ℕ => ((b:ℂ)^(-s)*Complex.Gamma s) * (a (n+1)/((n+1:ℕ):ℂ)^s))
      (mellin (fun t => heckeForm a h (Complex.I*t)-a 0) s) := by
    apply hM.congr_fun
    intro n
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hb.le (by positivity),
      Complex.cpow_neg]
    push_cast
    ring
  have heq := hM'.unique (hL.mul_left ((b:ℂ)^(-s)*Complex.Gamma s))
  rw [heckeCompletedLSeries]
  have hbcast : (b:ℂ) = (2*Real.pi/h:ℂ) := by dsimp [b]; push_cast; rfl
  rw [← hbcast, ← heq]
  simp only [mellin, smul_eq_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  ring

end Gelbart

theorem solution
    (a : ℕ → ℂ) (c h : ℝ) (hc : 0 < c) (hh : 0 < h)
    (hgrowth : Gelbart.HeckeCoeffGrowth a c) {s : ℂ} (hs : c + 1 < s.re) :
    Gelbart.heckeCompletedLSeries a h s =
      ∫ y in Set.Ioi (0 : ℝ),
        (Gelbart.heckeForm a h (Complex.I * y) - a 0) * (y : ℂ) ^ (s - 1) :=
  Gelbart.hecke_mellin_representation a c h hc hh hgrowth hs

#print axioms Gelbart.hecke_mellin_representation
#print axioms solution
