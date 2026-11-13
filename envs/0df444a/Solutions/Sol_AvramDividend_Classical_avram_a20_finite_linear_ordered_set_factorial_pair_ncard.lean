-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_linear_ordered_set_factorial_pair_ncard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:20:53.154685+00:00
-- url     : https://prove2.me/submissions/97e1f080-3f1c-4957-810a-8e23a122be6c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (S : Set ℝ≥0) (hS : S.Finite) :
    (S.ncard : ℝ) * ((S.ncard : ℝ) - 1) =
      2 * (((S ×ˢ S) ∩
        {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard : ℝ) := by
  classical
  let F : Finset ℝ≥0 := hS.toFinset
  have hPair :
      ((S ×ˢ S) ∩ {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard =
      ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by
    have heq :
        (S ×ˢ S) ∩ {p : ℝ≥0 × ℝ≥0 | p.1 < p.2} =
          (↑((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2))
            : Set (ℝ≥0 × ℝ≥0)) := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_setOf_eq,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨ha, hb⟩, hp⟩
        exact ⟨⟨(hS.mem_toFinset).mpr ha,
          (hS.mem_toFinset).mpr hb⟩, hp⟩
      · rintro ⟨⟨ha, hb⟩, hp⟩
        exact ⟨⟨(hS.mem_toFinset).mp ha,
          (hS.mem_toFinset).mp hb⟩, hp⟩
    rw [heq]
    exact Set.ncard_coe_finset _
  let K : ℕ := ((F ×ˢ F).filter
    (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  have hChoice : (F.card * (F.card - 1)) / 2 = K := by
    simpa only [K, Finset.card_product_filter_lt, Nat.choose_two_right]
  have hNat : 2 * K = F.card * (F.card - 1) := by
    calc
      2 * K = K * 2 := Nat.mul_comm _ _
      _ = ((F.card * (F.card - 1)) / 2) * 2 := by rw [hChoice]
      _ = F.card * (F.card - 1) :=
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self F.card)
  have hReal : (F.card : ℝ) * ((F.card : ℝ) - 1) =
      (2 : ℝ) * (K : ℝ) := by
    have hCast := congrArg (fun k : ℕ => (k : ℝ)) hNat
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hCast
    by_cases hz : F.card = 0
    · have hK : K = 0 := by simpa [hz] using hNat
      simp [hz, hK]
    · have hk : 1 ≤ F.card := Nat.one_le_iff_ne_zero.mpr hz
      simpa only [Nat.cast_sub hk, Nat.cast_one] using hCast.symm
  simpa only [Set.ncard_eq_toFinset_card S hS, hPair, K, F] using hReal
