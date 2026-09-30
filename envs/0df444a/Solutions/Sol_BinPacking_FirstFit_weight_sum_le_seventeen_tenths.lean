-- Prove2me | solution 1 for BinPacking.FirstFit.weight_sum_le_seventeen_tenths
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T00:10:57.834201+00:00
-- url     : https://prove2.me/submissions/cb2095f4-5a8c-41d9-8b38-e22d421e0bf2

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W

namespace BinPacking.FirstFit

theorem W_superadd_pv449 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ 1 / 2) :
    W a + W b ≤ W (a + b) := by
  unfold W
  split_ifs <;> linarith

theorem W_list_le_pv449 : ∀ l : List ℝ, (∀ x ∈ l, 0 ≤ x) → l.sum ≤ 1 / 2 →
    (l.map W).sum ≤ W l.sum
  | [], _, _ => by simp [W]
  | a :: l, hl, hs => by
    have ha : 0 ≤ a := hl a (by simp)
    have hl' : ∀ x ∈ l, 0 ≤ x := fun x hx => hl x (by simp [hx])
    have hsl : 0 ≤ l.sum := List.sum_nonneg hl'
    simp only [List.map_cons, List.sum_cons] at hs ⊢
    have ih := W_list_le_pv449 l hl' (by linarith)
    have := W_superadd_pv449 a l.sum ha hsl hs
    linarith

theorem W_le_small_pv449 (a : ℝ) (ha : 0 < a) (h : a ≤ 1 / 2) : W a ≤ 3 / 2 * a := by
  unfold W
  split_ifs <;> linarith

theorem W_half_pv449 (s : ℝ) (h0 : 0 ≤ s) (h : s ≤ 1 / 2) : W s ≤ 7 / 10 := by
  unfold W
  split_ifs <;> linarith

end BinPacking.FirstFit

open BinPacking.FirstFit in
theorem solution (bs : List ℝ) (hbs : IsList bs) (hsum : bs.sum ≤ 1) :
    (bs.map W).sum ≤ 17 / 10 := by
  by_cases hbig : ∃ b ∈ bs, 1 / 2 < b
  · obtain ⟨b, hb, hb2⟩ := hbig
    have p := List.perm_cons_erase hb
    have hs1 : bs.sum = b + (bs.erase b).sum := by rw [p.sum_eq, List.sum_cons]
    have hs2 : (bs.map W).sum = W b + ((bs.erase b).map W).sum := by
      rw [(p.map W).sum_eq, List.map_cons, List.sum_cons]
    have hrest : ∀ x ∈ bs.erase b, 0 ≤ x := fun x hx => (hbs x (List.mem_of_mem_erase hx)).1.le
    have hWb : W b = 1 := by
      unfold W
      have h1 : ¬ b ≤ 1 / 6 := by linarith
      have h2 : ¬ b ≤ 1 / 3 := by linarith
      have h3 : ¬ b ≤ 1 / 2 := by linarith
      rw [if_neg h1, if_neg h2, if_neg h3]
    have hrs : (bs.erase b).sum ≤ 1 / 2 := by linarith
    have := W_list_le_pv449 _ hrest hrs
    have := W_half_pv449 _ (List.sum_nonneg hrest) hrs
    linarith
  · simp only [not_exists, not_and, not_lt] at hbig
    have h1 : (bs.map W).sum ≤ (bs.map (fun x => 3 / 2 * x)).sum :=
      List.sum_le_sum (fun x hx => W_le_small_pv449 x (hbs x hx).1 (hbig x hx))
    rw [List.sum_map_mul_left, List.map_id'] at h1
    linarith
