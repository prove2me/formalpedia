-- Prove2me | solution 1 for Disjunctive.LiftProject.mip_cut_lifting_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T07:43:06.510238+00:00
-- url     : https://prove2.me/submissions/00fd287d-4196-4cca-ba9a-795bdc711396

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows

set_option autoImplicit false

namespace Disjunctive.LiftProject.Aux08382a40

lemma int_choice (a1 a2 u0 v0 mb : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hmb : mb = (a2 - a1) / (u0 + v0)) :
    ∃ z : ℤ, a1 + u0 * (z : ℝ) ≤ min (a1 + u0 * (⌈mb⌉ : ℝ)) (a2 - v0 * (⌊mb⌋ : ℝ)) ∧
      a2 - v0 * (z : ℝ) ≤ min (a1 + u0 * (⌈mb⌉ : ℝ)) (a2 - v0 * (⌊mb⌋ : ℝ)) := by
  have hs : 0 < u0 + v0 := by linarith
  have h1 : (u0 + v0) * mb = a2 - a1 := by
    rw [hmb]; field_simp
  have key : a1 + u0 * mb = a2 - v0 * mb := by linear_combination h1
  have hc := Int.le_ceil mb
  have hf := Int.floor_le mb
  by_cases h : a1 + u0 * (⌈mb⌉ : ℝ) ≤ a2 - v0 * (⌊mb⌋ : ℝ)
  · refine ⟨⌈mb⌉, ?_, ?_⟩
    · rw [min_eq_left h]
    · rw [min_eq_left h]
      have := mul_le_mul_of_nonneg_left hc hv0.le
      have := mul_le_mul_of_nonneg_left hc hu0.le
      linarith
  · rw [not_le] at h
    refine ⟨⌊mb⌋, ?_, ?_⟩
    · rw [min_eq_right h.le]
      have := mul_le_mul_of_nonneg_left hf hv0.le
      have := mul_le_mul_of_nonneg_left hf hu0.le
      linarith
    · rw [min_eq_right h.le]

lemma swap_sum {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (u : Fin m → ℝ) (x : Fin n → ℝ) :
    ∑ ρ, u ρ * (A.mulVec x) ρ = ∑ i, (∑ ρ, u ρ * A ρ i) * x i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end Disjunctive.LiftProject.Aux08382a40

open Disjunctive.LiftProject in
theorem solution {n m : ℕ} (Atil : Matrix (Fin m) (Fin n) ℝ)
    (btil : Fin m → ℝ) (Nprime : Finset (Fin n)) (hP : HasBoundRows Atil btil Nprime)
    (j : Fin n) (hj : j ∈ Nprime)
    (u v : Fin m → ℝ) (u0 v0 : ℝ) (hu0 : 0 < u0) (hv0 : 0 < v0) (α : Fin n → ℝ) (β : ℝ)
    (hAlpha : ∀ i, α i = max (Alpha1_64 Atil u u0 j i) (Alpha2_64 Atil v v0 j i))
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbeta1 : β = ∑ ρ, u ρ * btil ρ) (hbeta2 : β = (∑ ρ, v ρ * btil ρ) + v0)
    (γ mbar : Fin n → ℝ)
    (hmbar : ∀ k ∈ Nprime, mbar k = (Alpha2_64 Atil v v0 j k - Alpha1_64 Atil u u0 j k) / (u0 + v0))
    (hgamma1 : ∀ k ∈ Nprime, γ k = min (Alpha1_64 Atil u u0 j k + u0 * (⌈mbar k⌉ : ℝ))
      (Alpha2_64 Atil v v0 j k - v0 * (⌊mbar k⌋ : ℝ)))
    (hgamma2 : ∀ k ∉ Nprime, γ k = α k) :
    ∀ x ∈ MIPDisjunctiveSet Atil btil Nprime, β ≤ dotProduct γ x := by
  intro x hx
  obtain ⟨hpoly, hzo⟩ := hx
  have hpoly' : ∀ i, btil i ≤ (Atil.mulVec x) i := hpoly
  simp only [Set.mem_iInter] at hzo
  have hzo' : ∀ k ∈ Nprime, x k = 0 ∨ x k = 1 := fun k hk => hzo k hk
  -- nonnegativity from the bound rows
  have hxnn : ∀ k, 0 ≤ x k := by
    intro k
    obtain ⟨ρ, hρA, hρb⟩ := hP.1 k
    have h1 := hpoly' ρ
    have h2 : (Atil.mulVec x) ρ = x k := by
      simp [Matrix.mulVec, dotProduct, hρA, Pi.single_apply]
    rw [h2, hρb] at h1
    exact h1
  -- integer multipliers
  have hm : ∀ k, ∃ z : ℤ, (Alpha1_64 Atil u u0 j k + u0 * (z : ℝ) ≤ γ k ∧
      Alpha2_64 Atil v v0 j k - v0 * (z : ℝ) ≤ γ k) ∧ (k ∉ Nprime → z = 0) := by
    intro k
    by_cases hk : k ∈ Nprime
    · obtain ⟨z, hz1, hz2⟩ := Disjunctive.LiftProject.Aux08382a40.int_choice (Alpha1_64 Atil u u0 j k) (Alpha2_64 Atil v v0 j k)
        u0 v0 (mbar k) hu0 hv0 (hmbar k hk)
      exact ⟨z, ⟨by rw [hgamma1 k hk]; exact hz1, by rw [hgamma1 k hk]; exact hz2⟩,
        fun h => absurd hk h⟩
    · refine ⟨0, ⟨?_, ?_⟩, fun _ => rfl⟩
      · rw [hgamma2 k hk, hAlpha k]; simp
      · rw [hgamma2 k hk, hAlpha k]; simp
  choose mm hmm using hm
  -- the integer quantity x_j - Σ mm_k x_k
  set c : Fin n → ℤ := fun k => if x k = 1 then 1 else 0 with hc
  have hxc : ∀ k ∈ Nprime, x k = (c k : ℝ) := by
    intro k hk
    rcases hzo' k hk with h | h <;> simp [hc, h]
  have hmc : ∀ k, (mm k : ℝ) * x k = ((mm k * c k : ℤ) : ℝ) := by
    intro k
    by_cases hk : k ∈ Nprime
    · rw [hxc k hk]; push_cast; ring
    · rw [(hmm k).2 hk]; simp
  set t : ℝ := x j - ∑ k, (mm k : ℝ) * x k with ht
  have htz : t = ((c j - ∑ k, mm k * c k : ℤ) : ℝ) := by
    rw [ht, hxc j hj, Finset.sum_congr rfl (fun k _ => hmc k)]
    push_cast; ring
  have hdisj : t ≤ 0 ∨ 1 ≤ t := by
    rw [htz]
    rcases le_or_gt (c j - ∑ k, mm k * c k) 0 with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hdot : dotProduct γ x = ∑ i, γ i * x i := rfl
  have hU : β ≤ ∑ i, (∑ ρ, u ρ * Atil ρ i) * x i := by
    rw [hbeta1, ← Disjunctive.LiftProject.Aux08382a40.swap_sum]
    exact Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hpoly' ρ) (hu ρ)
  have hV : β - v0 ≤ ∑ i, (∑ ρ, v ρ * Atil ρ i) * x i := by
    rw [hbeta2, add_sub_cancel_right, ← Disjunctive.LiftProject.Aux08382a40.swap_sum]
    exact Finset.sum_le_sum fun ρ _ => mul_le_mul_of_nonneg_left (hpoly' ρ) (hv ρ)
  have hS1 : ∑ i, (Alpha1_64 Atil u u0 j i + u0 * (mm i : ℝ)) * x i =
      (∑ i, (∑ ρ, u ρ * Atil ρ i) * x i) - u0 * t := by
    rw [ht]
    simp only [Alpha1_64, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_sub, Finset.mul_sum,
      mul_assoc]
    ring
  have hS2 : ∑ i, (Alpha2_64 Atil v v0 j i - v0 * (mm i : ℝ)) * x i =
      (∑ i, (∑ ρ, v ρ * Atil ρ i) * x i) + v0 * t := by
    rw [ht]
    simp only [Alpha2_64, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_sub, Finset.mul_sum,
      mul_assoc]
    ring
  rw [hdot]
  rcases hdisj with h | h
  · have hle : ∑ i, (Alpha1_64 Atil u u0 j i + u0 * (mm i : ℝ)) * x i ≤ ∑ i, γ i * x i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmm i).1.1 (hxnn i)
    have : 0 ≤ u0 * (-t) := mul_nonneg hu0.le (by linarith)
    linarith
  · have hle : ∑ i, (Alpha2_64 Atil v v0 j i - v0 * (mm i : ℝ)) * x i ≤ ∑ i, γ i * x i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmm i).1.2 (hxnn i)
    have : 0 ≤ v0 * (t - 1) := mul_nonneg hv0.le (by linarith)
    linarith
