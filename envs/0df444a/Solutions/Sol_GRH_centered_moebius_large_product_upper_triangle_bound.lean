-- Prove2me | solution 1 for GRH.centered_moebius_large_product_upper_triangle_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:10:13.088001+00:00
-- url     : https://prove2.me/submissions/d06d5dd7-448c-45eb-837a-2bab930eb443
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_moebius_square_mertens_harmonic_residual_below_boundary
import Theorems.Thm_GRH_centered_moebius_square_block_control
import Theorems.Thm_GRH_centered_moebius_small_product_and_diagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset
open scoped BigOperators

noncomputable section

private def summand (q : ℕ) [NeZero q] (a : ZMod q) (N d e : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
    (GRH.moebiusProgressionCount q a N d e -
      if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
        (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)

private theorem centered_of_square
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |GRH.centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by 
  by_cases hrecord : (0.8749570698 : ℝ) < σ
  · exact (GRH.centered_moebius_square_block_control q a ha).2 σ hrecord hone
  · apply (GRH.centered_moebius_bound_iff_square_mertens_residual q a σ hhalf.le).2
    exact GRH.moebius_square_mertens_harmonic_residual_below_boundary
      q a ha σ hhalf (le_of_not_gt hrecord)


theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1/2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |∑ d ∈ Ioc 0 N.sqrt,
        ∑ e ∈ (Ioc 0 N.sqrt).filter (fun e => d < e ∧ N.sqrt < d * e),
          (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
          (GRH.moebiusProgressionCount q a N d e -
            if IsUnit (d : ZMod q) ∧ IsUnit (e : ZMod q) then
              (1 / (q : ℝ)) * N / ((d : ℝ) * e) else 0)| ≤ C * ((N : ℝ) + 1) ^ σ := by 
  classical
  obtain ⟨K, hK, hsmall⟩ := GRH.centered_moebius_small_product_and_diagonal σ hhalf
  obtain ⟨C, hC, hfull⟩ := centered_of_square q a ha σ hhalf hone
  refine ⟨(C+K)/2, by positivity, fun N => ?_⟩
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
  let P := ((N:ℝ)+1)^σ
  have h2 : 2*|T| ≤ (C+K)*P := calc
    2*|T| = |T+T| := by rw [← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ = |GRH.centeredMoebiusBilinear q a N - R| := by rw [hsplit]; congr 1; ring
    _ ≤ |GRH.centeredMoebiusBilinear q a N|+|R| := abs_sub _ _
    _ ≤ C*P+K*P := add_le_add (hfull N) hr
    _ = _ := by ring
  change |T| ≤ (C+K)/2*P
  linarith only [h2]
