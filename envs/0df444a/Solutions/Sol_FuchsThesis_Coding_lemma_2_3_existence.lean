-- Prove2me | solution 1 for FuchsThesis.Coding.lemma_2_3_existence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:04:11.182647+00:00
-- url     : https://prove2.me/submissions/d59bd3ba-66fc-48f3-b8f3-1cb351f29108

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous

namespace Aux_Fuchs_Kraft

def lists (L : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (List.Vector Bool L)).map ⟨List.Vector.toList, List.Vector.toList_injective⟩

lemma mem_lists (L : ℕ) (l : List Bool) : l ∈ lists L ↔ l.length = L := by
  unfold lists
  constructor
  · intro h
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.1 h
    exact v.toList_length
  · intro h
    exact Finset.mem_map.2 ⟨⟨l, h⟩, Finset.mem_univ _, rfl⟩

lemma card_lists (L : ℕ) : (lists L).card = 2 ^ L := by
  unfold lists
  rw [Finset.card_map, Finset.card_univ, card_vector]
  simp

lemma card_prefix_le (p : List Bool) (m : ℕ) (hp : p.length ≤ m) :
    ((lists m).filter (fun w => p <+: w)).card ≤ 2 ^ (m - p.length) := by
  rw [← card_lists (m - p.length)]
  apply Finset.card_le_card_of_injOn (fun w => w.drop p.length)
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter, mem_lists] at hw
    rw [Finset.mem_coe, mem_lists, List.length_drop, hw.1]
  · intro w1 hw1 w2 hw2 h
    rw [Finset.mem_coe, Finset.mem_filter] at hw1 hw2
    simp only at h
    have e1 : w1 = p ++ w1.drop p.length := by
      conv_lhs => rw [← List.take_append_drop p.length w1]
      rw [← List.prefix_iff_eq_take.1 hw1.2]
    have e2 : w2 = p ++ w2.drop p.length := by
      conv_lhs => rw [← List.take_append_drop p.length w2]
      rw [← List.prefix_iff_eq_take.1 hw2.2]
    rw [e1, e2, h]

lemma main {ι : Type*} [DecidableEq ι] (n : ι → ℕ) (s : Finset ι) :
    ∑ i ∈ s, ((2 : ℝ) ^ n i)⁻¹ ≤ 1 →
      ∃ c : ι → List Bool, (∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ c x <+: c y) ∧
        ∀ i ∈ s, (c i).length = n i := by
  induction s using Finset.induction_on_max_value n with
  | empty => intro _; exact ⟨fun _ => [], by simp, by simp⟩
  | insert a s ha hmax ih =>
    intro hsum
    rw [Finset.sum_insert ha] at hsum
    have hpos : 0 < ((2 : ℝ) ^ n a)⁻¹ := by positivity
    obtain ⟨c, hpf, hlen⟩ := ih (by linarith)
    set m := n a with hm
    -- counting
    have hreal : ∑ x ∈ s, ((2 : ℝ) ^ (m - n x)) ≤ (2 : ℝ) ^ m - 1 := by
      have e : ∀ x ∈ s, ((2 : ℝ) ^ (m - n x)) = 2 ^ m * ((2 : ℝ) ^ n x)⁻¹ := by
        intro x hx
        rw [pow_sub₀ (2 : ℝ) two_ne_zero (hmax x hx)]
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
      have h2 : (0 : ℝ) < 2 ^ m := by positivity
      have : ∑ x ∈ s, ((2 : ℝ) ^ n x)⁻¹ ≤ 1 - ((2 : ℝ) ^ m)⁻¹ := by linarith
      calc 2 ^ m * ∑ x ∈ s, ((2 : ℝ) ^ n x)⁻¹ ≤ 2 ^ m * (1 - ((2 : ℝ) ^ m)⁻¹) :=
            mul_le_mul_of_nonneg_left this h2.le
        _ = 2 ^ m - 1 := by field_simp
    have hnat : ∑ x ∈ s, 2 ^ (m - n x) < 2 ^ m := by
      have h1 : ((∑ x ∈ s, 2 ^ (m - n x) : ℕ) : ℝ) ≤ (2 : ℝ) ^ m - 1 := by
        push_cast; exact hreal
      have h2 : ((∑ x ∈ s, 2 ^ (m - n x) : ℕ) : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast h2
    have hblock : ((lists m).filter (fun w => ∃ x ∈ s, c x <+: w)).card < (lists m).card := by
      rw [card_lists]
      refine lt_of_le_of_lt ?_ hnat
      calc ((lists m).filter (fun w => ∃ x ∈ s, c x <+: w)).card
          ≤ (s.biUnion (fun x => (lists m).filter (fun w => c x <+: w))).card := by
            apply Finset.card_le_card
            intro w hw
            rw [Finset.mem_filter] at hw
            obtain ⟨x, hx, hpre⟩ := hw.2
            exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hw.1, hpre⟩⟩
        _ ≤ ∑ x ∈ s, ((lists m).filter (fun w => c x <+: w)).card := Finset.card_biUnion_le
        _ ≤ ∑ x ∈ s, 2 ^ (m - n x) := by
            apply Finset.sum_le_sum
            intro x hx
            have := card_prefix_le (c x) m (by rw [hlen x hx]; exact hmax x hx)
            rw [hlen x hx] at this
            exact this
    obtain ⟨w, hw, hwnot⟩ : ∃ w ∈ lists m, w ∉ (lists m).filter (fun w => ∃ x ∈ s, c x <+: w) := by
      by_contra hcon
      push_neg at hcon
      have : lists m ⊆ (lists m).filter (fun w => ∃ x ∈ s, c x <+: w) := fun w hw => hcon w hw
      have := Finset.card_le_card this
      omega
    have hwlen : w.length = m := (mem_lists m w).1 hw
    have hwfree : ∀ x ∈ s, ¬ c x <+: w := by
      intro x hx hpre
      exact hwnot (Finset.mem_filter.2 ⟨hw, x, hx, hpre⟩)
    refine ⟨Function.update c a w, ?_, ?_⟩
    · intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · rw [Function.update_self, Function.update_of_ne (fun h => ha (by rw [← h]; exact hy))]
        intro hpre
        have hle := hpre.sublist.length_le
        rw [hwlen, hlen y hy] at hle
        have heq : w = c y := hpre.sublist.eq_of_length (by rw [hwlen, hlen y hy]; exact le_antisymm hle (hmax y hy))
        exact hwfree y hy (by rw [← heq])
      · rw [Function.update_self, Function.update_of_ne (fun h => ha (by rw [← h]; exact hx))]
        exact hwfree x hx
      · rw [Function.update_of_ne (fun h => ha (by rw [← h]; exact hx)),
          Function.update_of_ne (fun h => ha (by rw [← h]; exact hy))]
        exact hpf x hx y hy hxy
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [Function.update_self, hwlen]
      · rw [Function.update_of_ne (fun h => ha (by rw [← h]; exact hi))]
        exact hlen i hi

end Aux_Fuchs_Kraft

open FuchsThesis.Coding Aux_Fuchs_Kraft in
theorem solution {ι : Type*} [Fintype ι] (k : ι → ℤ)
    (hK : ∑ i, (2 : ℝ) ^ (-(k i)) ≤ 1) :
    ∃ c : ι → List Bool, IsInstantaneous c ∧ ∀ i, ((c i).length : ℤ) = k i := by
  classical
  have hk : ∀ i, 0 ≤ k i := by
    intro i
    by_contra hneg
    push_neg at hneg
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ (-(k i)) := by
      calc (2 : ℝ) = 2 ^ (1 : ℤ) := by norm_num
        _ ≤ 2 ^ (-(k i)) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (-(k i)) ≤ ∑ j, (2 : ℝ) ^ (-(k j)) :=
      Finset.single_le_sum (f := fun j => (2 : ℝ) ^ (-(k j)))
        (fun j _ => (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le) (Finset.mem_univ i)
    linarith
  set n : ι → ℕ := fun i => (k i).toNat with hn
  have hkn : ∀ i, k i = (n i : ℤ) := fun i => (Int.toNat_of_nonneg (hk i)).symm
  have hsum : ∑ i ∈ Finset.univ, ((2 : ℝ) ^ n i)⁻¹ ≤ 1 := by
    have e : ∀ i, (2 : ℝ) ^ (-(k i)) = ((2 : ℝ) ^ n i)⁻¹ := by
      intro i; rw [hkn i, zpow_neg, zpow_natCast]
    simpa [e] using hK
  obtain ⟨c, hpf, hlen⟩ := main n Finset.univ hsum
  refine ⟨c, fun x y hxy => hpf x (Finset.mem_univ _) y (Finset.mem_univ _) hxy, fun i => ?_⟩
  rw [hlen i (Finset.mem_univ _), hkn i]
