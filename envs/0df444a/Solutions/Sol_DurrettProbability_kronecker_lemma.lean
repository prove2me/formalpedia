-- Prove2me | solution 1 for DurrettProbability.kronecker_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:52:22.799004+00:00
-- url     : https://prove2.me/submissions/5e9afc15-f1bf-4b41-8878-cfee33a7c7d2

import Mathlib
import Definitions.Def_DurrettProbability_Series

open MeasureTheory ProbabilityTheory Filter


namespace DurrettProbability

theorem kr_main (a x : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (hamono : Monotone a)
    (hatop : Tendsto a atTop atTop)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, x n / a n) atTop (nhds L)) :
    Tendsto (fun n => (∑ m ∈ Finset.range n, x m) / a n) atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := hconv
  set B : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, x n / a n with hB
  have habel : ∀ n, ∑ m ∈ Finset.range n, x m =
      a n * B n - ∑ m ∈ Finset.range n, (a (m + 1) - a m) * B (m + 1) := by
    intro n
    induction n with
    | zero => simp [hB]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih,
        Finset.sum_range_succ (fun m => (a (m + 1) - a m) * B (m + 1))]
      have hBs : B (n + 1) = B n + x n / a n := by
        simp only [hB]; rw [Finset.sum_range_succ]
      rw [hBs]
      have := (hapos n).ne'
      field_simp
      ring
  set E : ℕ → ℝ := fun n =>
    (∑ m ∈ Finset.range n, (a (m + 1) - a m) * (B (m + 1) - L)) / a n with hEdef
  have hw0 : ∀ m, 0 ≤ a (m + 1) - a m := fun m => sub_nonneg.mpr (hamono (Nat.le_succ m))
  have hE : Tendsto E atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hB1 : Tendsto (fun m => B (m + 1)) atTop (nhds L) := hL.comp (tendsto_add_atTop_nat 1)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hB1 (ε / 2) (by linarith)
    set C := ∑ m ∈ Finset.range N, (a (m + 1) - a m) * (B (m + 1) - L) with hC
    have hCa : Tendsto (fun n => |C| / a n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hatop
    obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hCa (ε / 2) (by linarith)
    refine ⟨max N N2, fun n hn => ?_⟩
    have hnN : N ≤ n := le_of_max_le_left hn
    have hnN2 : N2 ≤ n := le_of_max_le_right hn
    have han := hapos n
    have hN2n := hN2 n hnN2
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hN2n
    have htail : |∑ m ∈ Finset.Ico N n, (a (m + 1) - a m) * (B (m + 1) - L)|
        ≤ ε / 2 * (a n - a N) := by
      calc |∑ m ∈ Finset.Ico N n, (a (m + 1) - a m) * (B (m + 1) - L)|
          ≤ ∑ m ∈ Finset.Ico N n, |(a (m + 1) - a m) * (B (m + 1) - L)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Ico N n, (a (m + 1) - a m) * (ε / 2) := by
            refine Finset.sum_le_sum fun m hm => ?_
            rw [abs_mul, abs_of_nonneg (hw0 m)]
            have hmN : N ≤ m := (Finset.mem_Ico.mp hm).1
            have := hN m hmN
            rw [Real.dist_eq] at this
            exact mul_le_mul_of_nonneg_left this.le (hw0 m)
        _ = ε / 2 * (a n - a N) := by
            rw [← Finset.sum_mul, Finset.sum_Ico_eq_sub _ hnN, Finset.sum_range_sub,
              Finset.sum_range_sub]
            ring
    have haN : 0 < a N := hapos N
    have hsplit : ∑ m ∈ Finset.range n, (a (m + 1) - a m) * (B (m + 1) - L)
        = C + ∑ m ∈ Finset.Ico N n, (a (m + 1) - a m) * (B (m + 1) - L) := by
      rw [hC, Finset.sum_range_add_sum_Ico _ hnN]
    rw [Real.dist_eq, sub_zero]
    simp only [hEdef]
    rw [hsplit, abs_div, abs_of_pos han, div_lt_iff₀ han]
    have h1 := abs_add_le C (∑ m ∈ Finset.Ico N n, (a (m + 1) - a m) * (B (m + 1) - L))
    have h2 : |C| < ε / 2 * a n := by
      rw [div_lt_iff₀ han] at hN2n; linarith
    nlinarith
  have hwsum : ∀ n, ∑ m ∈ Finset.range n, (a (m + 1) - a m) = a n - a 0 :=
    fun n => Finset.sum_range_sub a n
  have hid : ∀ n, (∑ m ∈ Finset.range n, x m) / a n = B n - E n - L + L * a 0 / a n := by
    intro n
    have h1 : ∑ m ∈ Finset.range n, (a (m + 1) - a m) * (B (m + 1) - L) =
        ∑ m ∈ Finset.range n, (a (m + 1) - a m) * B (m + 1) - L * (a n - a 0) := by
      rw [← hwsum n, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp only [hEdef]
    rw [habel n, h1]
    have := (hapos n).ne'
    field_simp
    ring
  have hlim : Tendsto (fun n => B n - E n - L + L * a 0 / a n) atTop (nhds (L - 0 - L + 0)) :=
    ((hL.sub hE).sub_const L).add (tendsto_const_nhds.div_atTop hatop)
  rw [show (fun n => (∑ m ∈ Finset.range n, x m) / a n) =
      fun n => B n - E n - L + L * a 0 / a n from funext hid]
  simpa using hlim

end DurrettProbability

open DurrettProbability

theorem solution (a x : ℕ → ℝ) (hapos : ∀ n, 0 < a n) (hamono : Monotone a)
    (hatop : Tendsto a atTop atTop)
    (hconv : ∃ L : ℝ, Tendsto (fun N => ∑ n ∈ Finset.range N, x n / a n) atTop (nhds L)) :
    Tendsto (fun n => (∑ m ∈ Finset.range n, x m) / a n) atTop (nhds 0) := by
  exact kr_main a x hapos hamono hatop hconv
