-- Prove2me | solution 1 for GRH.reduced_liouville_harmonic_power_decay
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:42:02.414148+00:00
-- url     : https://prove2.me/submissions/e87e9854-dba7-4bb6-9fe7-e23f23a0a723
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_finite_remainder_zero_obstruction
import Theorems.Thm_NymanBeurling_arbitrarily_small_remainder_certificates



import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib
import Definitions.Def_GRH_SquarefreeBilinear
import Theorems.Thm_moebius_summatory_rpow_bound_of_riemannHypothesis
import Theorems.Thm_moebius_dirichlet_partialSum_tendsto_of_moebius_bound
import Theorems.Thm_GRH_moebius_harmonic_decay_of_bounded_dirichlet_prefixes
import Theorems.Thm_GRH_liouville_harmonic_le_of_moebius_harmonic_le
import Theorems.Thm_GRH_reduced_liouville_harmonic_le_of_modulus_one

open Finset ArithmeticFunction Filter Topology

open GRH

private theorem harmonic_of_RH
    (hRH : RiemannHypothesis) (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1/2 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ,
      |reducedLiouvilleHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by
  classical
  let f (n : ℕ) := (moebius n:ℝ)*(n:ℝ)^(-σ)
  obtain ⟨L,hL⟩ := moebius_dirichlet_partialSum_tendsto_of_moebius_bound σ hhalf
    (moebius_summatory_rpow_bound_of_riemannHypothesis hRH)
  obtain ⟨B,hB⟩ := (Metric.isBounded_range_of_tendsto _ hL.abs).bddAbove
  have hbound (N : ℕ) : |∑ n ∈ range N, f n| ≤ max 0 B := by
    cases N with
    | zero => simp
    | succ N =>
      have he : range (N+1) = insert 0 (Icc 1 N) := by ext k; simp; omega
      rw [he, sum_insert (by simp),show f 0 = 0 by simp [f],zero_add]
      exact (hB ⟨N,rfl⟩).trans (le_max_right ..)
  have hC : 0 ≤ max 0 B := le_max_left .. 
  let Z := ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  let D := ∑ d ∈ q.divisors, |(moebius d:ℝ)| * (d:ℝ)^(-σ)
  have hZ : 0 ≤ Z := tsum_nonneg (fun d => by positivity)
  have hD : 0 ≤ D := sum_nonneg (fun d _ => by positivity)
  refine ⟨((2 * max 0 B) * Z) * D, by positivity, ?_⟩
  intro U
  apply reduced_liouville_harmonic_le_of_modulus_one q σ _ hone.le (by positivity) _ U
  intro V
  apply liouville_harmonic_le_of_moebius_harmonic_le σ _ hhalf hone.le (by positivity) _ V
  exact moebius_harmonic_decay_of_bounded_dirichlet_prefixes σ _ hone.le hC hbound


-- Finite rational zero obstruction, following the campaign solution of 12360d46.
private theorem right_zero_free (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hpos : 0 < 2*s.re-1 := by linarith
  obtain ⟨J,hJ⟩ := exists_nat_gt (‖s‖^2 / (2*s.re-1))
  obtain ⟨c,H,hC⟩ := NymanBeurling.arbitrarily_small_remainder_certificates J
  let M : ℚ := ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ)
  change M < 1/(J+1 : ℚ) at hC
  have hc : (M:ℝ) < 1/(J+1:ℝ) := by
    have ht := (Rat.cast_lt (K := ℝ)).mpr hC
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_add,Rat.cast_natCast] using ht
  have hh := NymanBeurling.finite_remainder_zero_obstruction s hs hs_one hz c H
  change 2*s.re-1 ≤ (M:ℝ)*‖s‖^2 at hh
  apply (not_lt_of_ge hh)
  calc
    _ ≤ (1/(J+1:ℝ))*‖s‖^2 := mul_le_mul_of_nonneg_right hc.le (sq_nonneg _)
    _ < 2*s.re-1 := by
      rw [one_div,inv_mul_eq_div,div_lt_iff₀ (by positivity)]
      have hh := (div_lt_iff₀ hpos).mp hJ
      nlinarith

private theorem rh_of_remainder_certificates : RiemannHypothesis := by
  apply riemannHypothesis_iff_zeros_in_strip_on_line.mpr
  intro s hz hpos hlt
  have hne : s ≠ 1 := by rintro rfl; norm_num at hlt
  apply le_antisymm
  · exact le_of_not_gt (fun h => right_zero_free s h hne hz)
  · by_contra! hleft
    have hzero : riemannZeta (1-s) = 0 := by
      rw [riemannZeta_one_sub _ hne,hz,mul_zero]
      intro n he
      rw [he] at hpos
      simp at hpos
      exact (Nat.cast_nonneg (α:=ℝ) n).not_gt hpos
    apply right_zero_free (1-s) (by simp; linarith) _ hzero
    intro he
    have h := congrArg Complex.re he
    simp at h
    linarith

theorem solution (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1/2 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ, |GRH.reducedLiouvilleHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) :=
  harmonic_of_RH rh_of_remainder_certificates q σ hhalf hone
