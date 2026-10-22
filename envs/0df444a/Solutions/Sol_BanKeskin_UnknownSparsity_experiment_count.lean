-- Prove2me | solution 1 for BanKeskin.UnknownSparsity.experiment_count
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:19:38.641718+00:00
-- url     : https://prove2.me/submissions/8129c852-1a75-40be-896a-8c00884a5802

import Mathlib
import Definitions.Def_BanKeskin_UnknownSparsity_Model
set_option autoImplicit false
open Classical in
theorem gg_cnt (t c m : ℕ) (Q : ℕ → Prop) (hm : m ^ 2 + c ≤ t)
    (hQ : ∀ L, 1 ≤ L → L ≤ m → Q (L ^ 2 + c)) :
    m ≤ (((Finset.Icc 1 t).filter fun k => Q k).card) := by
  have h := Finset.card_le_card_of_injOn (s := Finset.Icc 1 m)
    (t := (Finset.Icc 1 t).filter fun k => Q k) (fun L => L ^ 2 + c) ?_ ?_
  · simpa using h
  · intro L hL
    simp only [Finset.coe_Icc, Set.mem_Icc] at hL
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq]
    refine ⟨⟨by nlinarith [Nat.zero_le c], ?_⟩, hQ L hL.1 hL.2⟩
    have : L ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hL.2 2
    omega
  · intro a _ b _ hab
    simp only at hab
    have : a ^ 2 = b ^ 2 := by omega
    exact (Nat.pow_left_injective (by norm_num : (2:ℕ) ≠ 0)) this

theorem gg_real (t m : ℕ) (hm : 2 ≤ m) (ht : t ≤ (m + 1) ^ 2) :
    (1 / 4 : ℝ) * Real.sqrt t ≤ m := by
  have h1 : Real.sqrt t ≤ 4 * m := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : (t : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by exact_mod_cast ht
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  linarith

open Classical in
theorem solution (t : ℕ) (ht : 5 ≤ t) :
    (1 / 4 : ℝ) * Real.sqrt t ≤ (((Finset.Icc 1 t).filter fun k => BanKeskin.KnownSparsity.inM1 k).card : ℝ) ∧
      (1 / 4 : ℝ) * Real.sqrt t ≤ (((Finset.Icc 1 t).filter fun k => BanKeskin.KnownSparsity.inM2 k).card : ℝ) := by
  constructor
  · have h1 := Nat.sqrt_le' t
    have h2 := Nat.lt_succ_sqrt' t
    have h3 : 2 ≤ Nat.sqrt t := by rw [Nat.le_sqrt]; omega
    have h2' : t < (Nat.sqrt t + 1) ^ 2 := h2
    clear h2
    generalize Nat.sqrt t = m at *
    have hc := gg_cnt t 0 m BanKeskin.KnownSparsity.inM1 (by omega)
      (fun L hL _ => ⟨L, hL, by simp⟩)
    calc (1 / 4 : ℝ) * Real.sqrt t ≤ m := gg_real t m h3 (by omega)
      _ ≤ _ := by exact_mod_cast hc
  · have h1 := Nat.sqrt_le' (t - 1)
    have h2 := Nat.lt_succ_sqrt' (t - 1)
    have h3 : 2 ≤ Nat.sqrt (t - 1) := by rw [Nat.le_sqrt]; omega
    have h2' : t - 1 < (Nat.sqrt (t - 1) + 1) ^ 2 := h2
    clear h2
    generalize Nat.sqrt (t - 1) = m at *
    have hc := gg_cnt t 1 m BanKeskin.KnownSparsity.inM2 (by omega)
      (fun L hL _ => ⟨L, hL, rfl⟩)
    calc (1 / 4 : ℝ) * Real.sqrt t ≤ m := gg_real t m h3 (by omega)
      _ ≤ _ := by exact_mod_cast hc
