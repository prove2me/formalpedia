-- Prove2me | solution 2 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T08:16:05.231806+00:00
-- url     : https://prove2.me/submissions/daba75a7-092e-4f3d-8c1b-ee38b3be09c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_small_product_and_diagonal
import Theorems.Thm_GRH_centered_moebius_large_product_upper_triangle_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators

noncomputable section

private def summand (q : ℕ) [NeZero q] (a : ZMod q) (N d e : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
    (GRH.moebiusProgressionCount q a N d e -
      if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by 
  classical
  obtain ⟨K, hK, hsmall⟩ := GRH.centered_moebius_small_product_and_diagonal σ hhalf
  obtain ⟨C, hC, hlarge⟩ := GRH.centered_moebius_large_product_upper_triangle_bound q a ha σ hhalf hone
  refine ⟨K + C + C, by linarith, ?_⟩
  intro N
  let U := N.sqrt
  let S := Ioc 0 U
  let f := summand q a N
  let small (d e : ℕ) := d * e ≤ U ∨ d = e
  let upper (d e : ℕ) := d < e ∧ U < d * e
  let R := ∑ d ∈ S, ∑ e ∈ S.filter (small d), f d e
  let T := ∑ d ∈ S, ∑ e ∈ S.filter (upper d), f d e
  have hsym (d e : ℕ) : f d e = f e d := by
    dsimp only [f, summand, GRH.moebiusProgressionCount]
    rw [Nat.mul_comm d e, mul_comm (ArithmeticFunction.moebius d : ℝ) (ArithmeticFunction.moebius e : ℝ),
        mul_comm (d : ℝ) (e : ℝ)]
    simp only [and_comm]
  have hpart (d e : ℕ) : f d e = (if small d e then f d e else 0) +
      (if upper d e then f d e else 0) + (if upper e d then f e d else 0) := by
    dsimp only [small, upper]
    by_cases h : d * e ≤ U
    · have h' : ¬ U < e * d := by simpa only [Nat.mul_comm e d] using (not_lt.mpr h)
      simp [h, not_lt.mpr h, h']
    · have hp := lt_of_not_ge h
      have hp' : U < e * d := by simpa only [Nat.mul_comm e d] using hp
      rcases lt_trichotomy d e with hde | rfl | hed
      · simp [h, hp, hp', hde, hde.ne, not_lt.mpr hde.le]
      · simp
      · simp [h, hp, hp', hed, hed.ne', not_lt.mpr hed.le, hsym d e]
  have hflip : (∑ d ∈ S, ∑ e ∈ S, if upper e d then f e d else 0) = T := by
    rw [sum_comm]
    simp only [T, sum_filter]
  have hsplit : GRH.centeredMoebiusBilinear q a N = R + T + T := calc
    _ = ∑ d ∈ S, ∑ e ∈ S, f d e := by
      simp only [GRH.centeredMoebiusBilinear, f, summand, S, U, mul_sum, mul_assoc]
    _ = ∑ d ∈ S, ∑ e ∈ S, ((if small d e then f d e else 0) +
        (if upper d e then f d e else 0) + (if upper e d then f e d else 0)) :=
      sum_congr rfl (fun d _ => sum_congr rfl (fun e _ => hpart d e))
    _ = R + T + T := by
      simp only [sum_add_distrib]
      rw [hflip]
      simp only [R, T, sum_filter]
  have hr : |R| ≤ K * ((N : ℝ) + 1)^σ := calc
    _ ≤ ∑ d ∈ S, |∑ e ∈ S.filter (small d), f d e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ S, ∑ e ∈ S.filter (small d), |f d e| :=
      sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _ ≤ K * ((N : ℝ) + 1)^σ := hsmall q a ha N
  have ht : |T| ≤ C * ((N : ℝ) + 1)^σ := hlarge N
  rw [hsplit]
  calc
    _ ≤ |R + T| + |T| := abs_add_le _ _
    _ ≤ (|R| + |T|) + |T| := add_le_add_left (abs_add_le _ _) _
    _ ≤ (K * ((N : ℝ) + 1)^σ + C * ((N : ℝ) + 1)^σ) + C * ((N : ℝ) + 1)^σ :=
      add_le_add (add_le_add hr ht) ht
    _ = _ := by ring
