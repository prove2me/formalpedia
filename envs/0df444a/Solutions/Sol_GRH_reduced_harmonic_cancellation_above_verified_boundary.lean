-- Prove2me | solution 1 for GRH.reduced_harmonic_cancellation_above_verified_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:19:35.992737+00:00
-- url     : https://prove2.me/submissions/fb5b50f4-8dbf-495b-999d-76118ada7f21

import Definitions.Def_GRH_MoebiusBilinear
import Theorems.Thm_GRH_mobius_character_and_progression_bounds_above_record
import Theorems.Thm_GRH_moebius_harmonic_decay_of_bounded_dirichlet_prefixes
import Theorems.Thm_GRH_liouville_harmonic_le_of_moebius_harmonic_le
import Theorems.Thm_GRH_reduced_liouville_harmonic_le_of_modulus_one
import Theorems.Thm_GRH_reduced_moebius_harmonic_le_of_liouville_harmonic_le
import Mathlib

open Finset ArithmeticFunction Filter Topology Asymptotics MeasureTheory
open GRH
private theorem natural_prefix_converges (σ : ℝ) (hσ : 0.8749570698 < σ) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, (moebius n : ℝ) * (n : ℝ)^(-σ)) atTop (𝓝 L) := by
  let r := (0.8749570698+σ)/2
  have hrs : r < σ := by dsimp [r]; linarith
  have hr : 0 ≤ r := by dsimp [r]; linarith
  let c : ℕ → ℝ := fun n => (moebius n:ℝ)
  have hc : c 0 = 0 := by simp [c]
  have hZ := (mobius_character_and_progression_bounds_above_record 1 r (by dsimp [r]; linarith)).2
    (1 : ZMod 1) isUnit_one
  have hO : (fun N => ∑ k ∈ Icc 0 N, c k) =O[atTop] fun N => (N : ℝ)^r := by
    apply (Complex.isBigO_ofReal_left.mp ?_)
    have e (N : ℕ) : Icc 0 N = range (N+1) := by ext k; simp
    convert hZ using 1
    funext N
    rw [Complex.ofReal_sum,e]
    apply sum_congr rfl
    intro k _
    rw [if_pos (Subsingleton.elim _ _)]
    simp [c]
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-σ) * ∑ k ∈ Icc 0 N, c k)
      atTop (𝓝 0) := by
    have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(σ - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hrs)).comp tendsto_natCast_atTop_atTop
    exact (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-σ) r (-(σ - r))
      (isBigO_refl _ _) hO (by linarith)).trans_tendsto hp
  have hfloor : (fun t : ℝ => ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ r :=
    (hO.comp_tendsto tendsto_nat_floor_atTop).trans
      (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  have hdom : (fun t : ℝ => deriv (fun x : ℝ => x ^ (-σ)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ (-σ - 1 + r) :=
    IsBigO.mul_atTop_rpow_of_isBigO_rpow (-σ - 1) r (-σ - 1 + r)
      (isBigO_deriv_rpow_const_atTop (-σ)) hfloor le_rfl
  have hint : LocallyIntegrableOn (deriv (fun x : ℝ => x ^ (-σ))) (Set.Ici 1) := by
    rw [Real.deriv_rpow_const']
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ici
    exact continuousOn_const.mul (fun t ht =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans_le ht).ne')).continuousWithinAt)
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc
    (f := fun x : ℝ => x ^ (-σ))
    (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (zero_lt_one.trans_le ht).ne')
    hint hlim hdom (integrableAtFilter_rpow_atTop_iff.mpr (by linarith : -σ - 1 + r < -1))
  refine ⟨_, hconv.congr (fun N => ?_)⟩
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc, mul_zero, zero_add]
  simp only [zero_add]
  exact sum_congr rfl fun n _ => mul_comm _ _

private theorem lambda_record (q : ℕ) [NeZero q] (σ : ℝ) (hσ : 0.8749570698 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ, |reducedLiouvilleHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by
  classical
  have hhalf : (1/2:ℝ) < σ := by linarith
  let f (n : ℕ) := (moebius n:ℝ)*(n:ℝ)^(-σ)
  obtain ⟨L,hL⟩ := natural_prefix_converges σ hσ
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



theorem solution (q : ℕ) [NeZero q] (σ : ℝ)
    (hσ : 0.8749570698 < σ) (hone : σ < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ U : ℕ,
      max |reducedLiouvilleHarmonic q U| |reducedMoebiusHarmonic q U| ≤ K*((U:ℝ)+1)^(σ-1) := by
  obtain ⟨C,hC,hlambda⟩ := lambda_record q σ hσ hone
  let Z := ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹
  have hZ : 0 ≤ Z := tsum_nonneg fun d => by positivity
  refine ⟨max C (C*Z), hC.trans (le_max_left ..), fun U => max_le ?_ ?_⟩
  · exact (hlambda U).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
  · exact (reduced_moebius_harmonic_le_of_liouville_harmonic_le q σ C (by linarith) hone.le hC hlambda U).trans
      (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
