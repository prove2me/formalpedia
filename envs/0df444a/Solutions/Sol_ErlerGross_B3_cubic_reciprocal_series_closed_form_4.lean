-- Prove2me | solution 4 for ErlerGross.B3_cubic_reciprocal_series_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:42:13.074108+00:00
-- url     : https://prove2.me/submissions/49b2c484-c32f-48da-8692-6ca3c0311d10

import Mathlib
import Definitions.Def_ErlerGross_defs
open scoped BigOperators
open Real Filter Topology MeasureTheory

private lemma b3_cubic_term (n : ℕ) :
    1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))) =
      3 / (3 * (n : Real) + 1) + 3 / (3 * (n : Real) + 2) - 4 / (2 * (n : Real) + 1) := by
  have h1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < 3 * (n : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < 3 * (n : ℝ) + 2 := by positivity
  field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
  ring

private lemma b3_harmonic_three_rec (N : ℕ) :
    (harmonic (3 * (N + 1)) : ℝ) =
      (harmonic (3 * N) : ℝ) + 1 / (3 * (N : ℝ) + 1) +
        1 / (3 * (N : ℝ) + 2) + 1 / (3 * (N : ℝ) + 3) := by
  simp only [Nat.mul_succ]
  rw [show 3 * N + 3 = (3 * N + 2) + 1 by omega, harmonic_succ]
  rw [show 3 * N + 2 = (3 * N + 1) + 1 by omega, harmonic_succ]
  rw [show 3 * N + 1 = (3 * N) + 1 by omega, harmonic_succ]
  push_cast
  norm_num at *
  ring

private lemma b3_harmonic_two_rec (N : ℕ) :
    (harmonic (2 * (N + 1)) : ℝ) =
      (harmonic (2 * N) : ℝ) + 1 / (2 * (N : ℝ) + 1) + 1 / (2 * (N : ℝ) + 2) := by
  simp only [Nat.mul_succ]
  rw [show 2 * N + 2 = (2 * N + 1) + 1 by omega, harmonic_succ]
  rw [show 2 * N + 1 = (2 * N) + 1 by omega, harmonic_succ]
  push_cast
  ring

private lemma b3_harmonic_one_rec (N : ℕ) :
    (harmonic (N + 1) : ℝ) = (harmonic N : ℝ) + 1 / ((N : ℝ) + 1) := by
  rw [harmonic_succ]
  push_cast
  ring

private lemma b3_harmonic_three (N : ℕ) :
    (∑ n ∈ Finset.range N, (3 : ℝ) / (3 * (n : ℝ) + 1)) +
      ∑ n ∈ Finset.range N, (3 : ℝ) / (3 * (n : ℝ) + 2) =
      3 * (harmonic (3 * N) : ℝ) - (harmonic N : ℝ) := by
  induction N with
  | zero => norm_num [harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    calc
      (∑ x ∈ Finset.range N, 3 / (3 * (x : ℝ) + 1) + 3 / (3 * (N : ℝ) + 1)) +
          (∑ x ∈ Finset.range N, 3 / (3 * (x : ℝ) + 2) + 3 / (3 * (N : ℝ) + 2)) =
          ((∑ x ∈ Finset.range N, 3 / (3 * (x : ℝ) + 1)) +
            ∑ x ∈ Finset.range N, 3 / (3 * (x : ℝ) + 2)) +
            (3 / (3 * (N : ℝ) + 1) + 3 / (3 * (N : ℝ) + 2)) := by ring
      _ = (3 * (harmonic (3 * N) : ℝ) - (harmonic N : ℝ)) +
            (3 / (3 * (N : ℝ) + 1) + 3 / (3 * (N : ℝ) + 2)) := by rw [ih]
      _ = 3 * (harmonic (3 * (N + 1)) : ℝ) - (harmonic (N + 1) : ℝ) := by
        rw [b3_harmonic_three_rec, b3_harmonic_one_rec]
        field_simp
        ring

private lemma b3_harmonic_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (4 : ℝ) / (2 * (n : ℝ) + 1)) =
      4 * (harmonic (2 * N) : ℝ) - 2 * (harmonic N : ℝ) := by
  induction N with
  | zero => norm_num [harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    calc
      (∑ x ∈ Finset.range N, 4 / (2 * (x : ℝ) + 1)) + 4 / (2 * (N : ℝ) + 1) =
          (4 * (harmonic (2 * N) : ℝ) - 2 * (harmonic N : ℝ)) + 4 / (2 * (N : ℝ) + 1) := by rw [ih]
      _ = 4 * (harmonic (2 * (N + 1)) : ℝ) - 2 * (harmonic (N + 1) : ℝ) := by
        rw [b3_harmonic_two_rec, b3_harmonic_one_rec]
        field_simp
        ring
private lemma b3_cubic_sum (N : ℕ) :
    (∑ n ∈ Finset.range N,
      1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2)))) =
      3 * (harmonic (3 * N) : ℝ) - 4 * (harmonic (2 * N) : ℝ) + (harmonic N : ℝ) := by
  simp_rw [b3_cubic_term]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [b3_harmonic_three, b3_harmonic_two]
  ring

private noncomputable def cubic (n : ℕ) : ℝ :=
  1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2)))

private lemma b3_cubic_summable : Summable cubic := by
  have hmajor0 := (Real.summable_one_div_nat_add_rpow 1 3).2 (by norm_num)
  have hmajor : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
    exact hmajor0.congr (fun n => by
      rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
      norm_num [Real.rpow_natCast])
  apply Summable.of_norm_bounded hmajor
  intro n
  dsimp [cubic]
  have h1 : 0 < 2 * (n : ℝ) + 1 := by positivity
  have h2 : 0 < 3 * (n : ℝ) + 1 := by positivity
  have h3 : 0 < 3 * (n : ℝ) + 2 := by positivity
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hfpos : 0 < 1 / ((2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)) := by positivity
  rw [abs_of_pos hfpos]
  apply one_div_le_one_div_of_le (by positivity)
  calc
    ((n : ℝ) + 1) ^ 3 = ((n : ℝ) + 1) * ((n : ℝ) + 1) * ((n : ℝ) + 1) := by ring
    _ ≤ (2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) := by
      gcongr <;> nlinarith



private lemma b3_cubic_limit : Tendsto
    (fun N : ℕ => 3 * (harmonic (3 * N) : ℝ) - 4 * (harmonic (2 * N) : ℝ) + (harmonic N : ℝ))
    atTop (𝓝 (Real.log (27 / 16))) := by
  have hscale3 : Tendsto (fun n : ℕ => 3 * n) atTop atTop := by
    have h := (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop).const_mul_atTop' (by norm_num : (0 : ℕ) < 3)
    simpa [Function.comp_def] using h
  have hscale2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    have h := (tendsto_id : Tendsto (id : ℕ → ℕ) atTop atTop).const_mul_atTop' (by norm_num : (0 : ℕ) < 2)
    simpa [Function.comp_def] using h
  have hh3 : Tendsto
      (fun n : ℕ => (harmonic (3 * n) : ℝ) - Real.log ((3 * n : ℕ) : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h := Real.tendsto_harmonic_sub_log.comp hscale3
    simpa [Function.comp_def] using h
  have hh2 : Tendsto
      (fun n : ℕ => (harmonic (2 * n) : ℝ) - Real.log ((2 * n : ℕ) : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    have h := Real.tendsto_harmonic_sub_log.comp hscale2
    simpa [Function.comp_def] using h
  have hh1 : Tendsto
      (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := Real.tendsto_harmonic_sub_log
  have hpart3 : Tendsto
      (fun n : ℕ => 3 * ((harmonic (3 * n) : ℝ) - Real.log ((3 * n : ℕ) : ℝ)))
      atTop (𝓝 (3 * Real.eulerMascheroniConstant)) := by
    simpa using hh3.const_mul 3
  have hpart2 : Tendsto
      (fun n : ℕ => 4 * ((harmonic (2 * n) : ℝ) - Real.log ((2 * n : ℕ) : ℝ)))
      atTop (𝓝 (4 * Real.eulerMascheroniConstant)) := by
    simpa using hh2.const_mul 4
  have hpart : Tendsto
      (fun n : ℕ =>
        3 * ((harmonic (3 * n) : ℝ) - Real.log ((3 * n : ℕ) : ℝ)) -
          4 * ((harmonic (2 * n) : ℝ) - Real.log ((2 * n : ℕ) : ℝ)) +
          ((harmonic n : ℝ) - Real.log (n : ℝ)))
      atTop
      (𝓝 (3 * Real.eulerMascheroniConstant - 4 * Real.eulerMascheroniConstant +
        Real.eulerMascheroniConstant)) := by
    have h := (hpart3.sub hpart2).add hh1
    simpa using h
  have hlogs : Tendsto
      (fun n : ℕ => 3 * Real.log (3 * (n : ℝ)) - 4 * Real.log (2 * (n : ℝ)) + Real.log (n : ℝ))
      atTop (𝓝 (3 * Real.log 3 - 4 * Real.log 2)) := by
    have hevent : ∀ᶠ n : ℕ in atTop,
        3 * Real.log (3 * (n : ℝ)) - 4 * Real.log (2 * (n : ℝ)) + Real.log (n : ℝ) =
          3 * Real.log 3 - 4 * Real.log 2 := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      rw [Real.log_mul (by norm_num) hn0, Real.log_mul (by norm_num) hn0]
      ring
    have hevent' : (fun _ : ℕ => 3 * Real.log 3 - 4 * Real.log 2) =ᶠ[atTop]
        (fun n : ℕ => 3 * Real.log (3 * (n : ℝ)) - 4 * Real.log (2 * (n : ℝ)) + Real.log (n : ℝ)) :=
      hevent.mono (fun n h => h.symm)
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => 3 * Real.log 3 - 4 * Real.log 2) atTop _).congr' hevent'
  have hfull := hpart.add hlogs
  have hfull' : Tendsto
      (fun n : ℕ => 3 * (harmonic (3 * n) : ℝ) - 4 * (harmonic (2 * n) : ℝ) + (harmonic n : ℝ))
      atTop
      (𝓝 (3 * Real.eulerMascheroniConstant - 4 * Real.eulerMascheroniConstant +
        Real.eulerMascheroniConstant + (3 * Real.log 3 - 4 * Real.log 2))) := by
    convert hfull using 1
    funext n
    push_cast
    ring
  have hlog : 3 * Real.log 3 - 4 * Real.log 2 = Real.log (27 / 16) := by
    calc
      3 * Real.log 3 - 4 * Real.log 2 = Real.log ((3 : ℝ) ^ 3) - Real.log ((2 : ℝ) ^ 4) := by
        rw [Real.log_pow, Real.log_pow]
        norm_num
      _ = Real.log (((3 : ℝ) ^ 3) / ((2 : ℝ) ^ 4)) := by
        rw [Real.log_div] <;> norm_num
      _ = Real.log (27 / 16) := by norm_num
  convert hfull' using 1
  rw [hlog]
  ring

theorem solution :
    HasSum (fun n : Nat => 1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))))
      (Real.log (27 / 16)) := by
  have hc : HasSum cubic (Real.log (27 / 16)) := by
    refine (Summable.hasSum_iff_tendsto_nat b3_cubic_summable).2 ?_
    convert b3_cubic_limit using 1
    funext N
    exact b3_cubic_sum N
  convert hc using 1
  funext n
  rfl


