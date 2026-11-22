-- Prove2me | solution 1 for BellSampling.Learn.sum_outcomes_uniform
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:36:53.435059+00:00
-- url     : https://prove2.me/submissions/ea938e59-35d8-48a6-9000-bd1152945b81

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
import Theorems.Thm_BellSampling_Learn_bell_outcome_uniform
import Theorems.Thm_BellSampling_Learn_stabSet_subspace
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

theorem solution {n : ℕ} (ψ : QState n) (hψ : IsStabilizerState ψ)
    (t : PStr n) :
    (t ∈ stabSet ψ →
      ∑ r₁, ∑ r₂, (if r₁ + r₂ = t then bellProb ψ r₁ * bellProb ψ r₂ else 0) = 1 / 2 ^ n) ∧
    (t ∉ stabSet ψ →
      ∑ r₁, ∑ r₂, (if r₁ + r₂ = t then bellProb ψ r₁ * bellProb ψ r₂ else 0) = 0) := by
  classical
  obtain ⟨s, hs⟩ := BellSampling.Learn.bell_outcome_uniform ψ hψ
  obtain ⟨W, hW_set, hW_rank⟩ := BellSampling.Learn.stabSet_subspace ψ hψ
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  have h_add_self : ∀ x : PStr n, x + x = 0 := by
    intro x
    ext i <;> exact h2 _
  have h_inner : ∀ r₁ : PStr n,
      (∑ r₂ : PStr n, if r₁ + r₂ = t then bellProb ψ r₁ * bellProb ψ r₂ else 0) =
        bellProb ψ r₁ * bellProb ψ (r₁ + t) := by
    intro r₁
    have hiff : ∀ r₂ : PStr n, r₁ + r₂ = t ↔ r₂ = r₁ + t := by
      intro r₂
      constructor
      · intro h
        rw [← h, ← add_assoc, h_add_self, zero_add]
      · intro h
        rw [h, ← add_assoc, h_add_self, zero_add]
    simp_rw [hiff]
    simp
  have h_memW : ∀ x : PStr n, x ∈ stabSet ψ ↔ x ∈ W := by
    intro x
    rw [← hW_set]
    rfl
  refine ⟨?_, ?_⟩
  · intro ht
    have htW : t ∈ W := (h_memW t).mp ht
    simp_rw [h_inner]
    have hterm : ∀ r₁ : PStr n,
        bellProb ψ r₁ * bellProb ψ (r₁ + t) =
          if r₁ + s ∈ W then (1 / 2 ^ n : ℝ) * (1 / 2 ^ n) else 0 := by
      intro r₁
      have h_shift : r₁ + t + s ∈ W ↔ r₁ + s ∈ W := by
        have heq : r₁ + t + s = (r₁ + s) + t := by abel
        rw [heq]
        exact Submodule.add_mem_iff_left W htW
      by_cases hr₁ : r₁ + s ∈ W
      · have hr₁_stab : r₁ + s ∈ stabSet ψ := (h_memW (r₁ + s)).mpr hr₁
        have hr₂_stab : r₁ + t + s ∈ stabSet ψ :=
          (h_memW (r₁ + t + s)).mpr (h_shift.mpr hr₁)
        rw [if_pos hr₁, (hs r₁).1 hr₁_stab, (hs (r₁ + t)).1 hr₂_stab]
      · have hr₁_not : r₁ + s ∉ stabSet ψ := fun h => hr₁ ((h_memW (r₁ + s)).mp h)
        rw [if_neg hr₁, (hs r₁).2 hr₁_not, zero_mul]
    simp_rw [hterm]
    have h_equiv : (∑ r₁ : PStr n, if r₁ + s ∈ W then (1 / 2 ^ n : ℝ) * (1 / 2 ^ n) else 0) =
        ∑ u : PStr n, if u ∈ W then (1 / 2 ^ n : ℝ) * (1 / 2 ^ n) else 0 := by
      refine Equiv.sum_comp (Equiv.addRight s)
        (fun u : PStr n => if u ∈ W then (1 / 2 ^ n : ℝ) * (1 / 2 ^ n) else 0)
    rw [h_equiv]
    have h_sub : (∑ u : PStr n, if u ∈ W then (1 / 2 ^ n : ℝ) * (1 / 2 ^ n) else 0) =
        ∑ _w : W, (1 / 2 ^ n : ℝ) * (1 / 2 ^ n) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter fun u : PStr n => u ∈ W)
        (fun u => by simp) (fun _ => (1 / 2 ^ n : ℝ) * (1 / 2 ^ n))
    rw [h_sub, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcardW : Fintype.card W = 2 ^ n := by
      have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
      simpa [ZMod.card, hW_rank] using hc
    rw [hcardW, Nat.cast_pow, Nat.cast_ofNat]
    have h2n_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [h2n_ne]
  · intro ht
    have htW : t ∉ W := fun h => ht ((h_memW t).mpr h)
    simp_rw [h_inner]
    refine Finset.sum_eq_zero fun r₁ _ => ?_
    by_cases hr₁ : r₁ + s ∈ stabSet ψ
    · have hr₁W : r₁ + s ∈ W := (h_memW (r₁ + s)).mp hr₁
      have hr₂_not : r₁ + t + s ∉ stabSet ψ := by
        intro hr₂
        have hr₂W : r₁ + t + s ∈ W := (h_memW (r₁ + t + s)).mp hr₂
        have hsumW : (r₁ + s) + (r₁ + t + s) ∈ W := W.add_mem hr₁W hr₂W
        have heq : (r₁ + s) + (r₁ + t + s) = t := by
          calc
            (r₁ + s) + (r₁ + t + s) = ((r₁ + s) + (r₁ + s)) + t := by abel
            _ = 0 + t := by rw [h_add_self (r₁ + s)]
            _ = t := zero_add t
        rw [heq] at hsumW
        exact htW hsumW
      rw [(hs (r₁ + t)).2 hr₂_not, mul_zero]
    · rw [(hs r₁).2 hr₁, zero_mul]
