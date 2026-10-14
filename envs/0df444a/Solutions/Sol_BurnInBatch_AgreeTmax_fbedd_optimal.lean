-- Prove2me | solution 1 for BurnInBatch.AgreeTmax.fbedd_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T02:34:45.90123+00:00
-- url     : https://prove2.me/submissions/fe39df41-9757-4e7c-a0a5-4c2d54479d92

import Mathlib
import Definitions.Def_BurnInBatch_AgreeTmax_Model
import Definitions.Def_BurnInBatch_AgreeTmax_FBEDD



namespace BurnInBatch.AgreeTmax
namespace FB

set_option linter.unusedSectionVars false

def blk (n B k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => k * B ≤ i.val ∧ i.val < (k + 1) * B

theorem mem_blk {n B k : ℕ} {i : Fin n} : i ∈ blk n B k ↔ k * B ≤ i.val ∧ i.val < (k + 1) * B := by
  simp [blk]

theorem blk_nonempty {n B k : ℕ} (hB : 0 < B) (hk : k < (n + B - 1) / B) : (blk n B k).Nonempty := by
  have h1 : (k + 1) * B ≤ n + B - 1 := (Nat.le_div_iff_mul_le hB).mp hk
  have h2 : k * B < n := by
    have : (k + 1) * B = k * B + B := by ring
    omega
  refine ⟨⟨k * B, h2⟩, ?_⟩
  rw [mem_blk]
  have : 0 < B := hB
  constructor
  · exact le_rfl
  · show k * B < (k + 1) * B
    nlinarith

theorem blk_card {n B k : ℕ} : (blk n B k).card ≤ B := by
  calc (blk n B k).card ≤ (Finset.range B).card := by
        apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val - k * B)
        · intro i hi
          have := mem_blk.mp hi
          simp only [Finset.coe_range, Set.mem_Iio]
          have : (k + 1) * B = k * B + B := by ring
          omega
        · intro i hi j hj h
          have h1 := mem_blk.mp hi
          have h2 := mem_blk.mp hj
          apply Fin.ext
          simp only at h
          omega
    _ = B := Finset.card_range B

theorem blk_disjoint {n B a b : ℕ} (hab : a < b) : Disjoint (blk n B a) (blk n B b) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  have h1 := mem_blk.mp hi
  have h2 := mem_blk.mp hj
  have : (a + 1) * B ≤ b * B := Nat.mul_le_mul_right B hab
  omega

theorem fbedd_valid {n B : ℕ} (hB : 0 < B) : IsValid B Finset.univ (fbedd n B) := by
  unfold fbedd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hP
    exact blk_nonempty hB (List.mem_range.mp hk)
  · intro P hP
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hP
    exact blk_card
  · intro P _; exact Finset.subset_univ _
  · rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun {a b} h => blk_disjoint h)
  · intro i _
    refine ⟨blk n B (i.val / B), List.mem_map.mpr ⟨i.val / B, List.mem_range.mpr ?_, rfl⟩, ?_⟩
    · have h1 := Nat.div_add_mod i.val B
      have h2 := Nat.mod_lt i.val hB
      have h3 := i.2
      have h4 : (i.val / B + 1) * B = i.val / B * B + B := by ring
      have h5 : B * (i.val / B) = i.val / B * B := mul_comm _ _
      rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hB]
      omega
    · rw [mem_blk]
      have h1 := Nat.div_add_mod i.val B
      have h2 := Nat.mod_lt i.val hB
      have h4 : (i.val / B + 1) * B = i.val / B * B + B := by ring
      have h5 : B * (i.val / B) = i.val / B * B := mul_comm _ _
      constructor <;> omega


theorem batchCompletion_const {n : ℕ} (c : ℕ) (S : List (Finset (Fin n)))
    (hne : ∀ P ∈ S, P.Nonempty) (k : ℕ) (hk : k < S.length) :
    batchCompletion (fun _ : Fin n => c) S k = (k + 1) * c := by
  unfold batchCompletion
  have h : (S.take (k + 1)).map (batchTime (fun _ : Fin n => c)) = (S.take (k + 1)).map (fun _ => c) :=
    List.map_congr_left (fun P hP => by
      unfold batchTime; exact Finset.sup_const (hne P (List.mem_of_mem_take hP)) c)
  rw [h, List.map_const', List.sum_replicate, List.length_take, smul_eq_mul]
  have : min (k + 1) S.length = k + 1 := min_eq_left (by omega)
  rw [this]

theorem lower {n B : ℕ} (hB : 0 < B) (c : ℕ) (d : Fin n → ℕ) (hd : Monotone d)
    (S : List (Finset (Fin n))) (hS : IsValid B Finset.univ S) (i : Fin n) :
    (i.val / B + 1) * c - d i ≤ Tmax (fun _ => c) d S := by
  obtain ⟨hne, hcard, -, -, hcov⟩ := hS
  have hpos : ∀ x : Fin n, ∃ k : Fin S.length, x ∈ S.get k := by
    intro x
    obtain ⟨P, hP, hx⟩ := hcov x (Finset.mem_univ x)
    obtain ⟨k, hk⟩ := List.get_of_mem hP
    exact ⟨k, hk ▸ hx⟩
  choose pos hpos using hpos
  obtain ⟨x0, hx0V, hmax⟩ := Finset.exists_max_image (Finset.Iic i) (fun x => (pos x).val)
    ⟨i, Finset.mem_Iic.mpr le_rfl⟩
  set K := pos x0 with hK
  have hVU : Finset.Iic i ⊆ (Finset.Iic K).biUnion (fun k => S.get k) := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨pos x, Finset.mem_Iic.mpr (Fin.le_def.mpr (hmax x hx)), hpos x⟩
  have hcardV : i.val + 1 ≤ (K.val + 1) * B := by
    calc i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ ((Finset.Iic K).biUnion (fun k => S.get k)).card := Finset.card_le_card hVU
      _ ≤ ∑ k ∈ Finset.Iic K, (S.get k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ Finset.Iic K, B := Finset.sum_le_sum (fun k _ => hcard _ (List.get_mem _ _))
      _ = (K.val + 1) * B := by rw [Finset.sum_const, Fin.card_Iic, smul_eq_mul]
  have hdiv : i.val / B < K.val + 1 := (Nat.div_lt_iff_lt_mul hB).mpr (by omega)
  have hbc := batchCompletion_const c S hne K.val K.2
  have hx0 : x0 ∈ S.get K := hpos x0
  have hdx : d x0 ≤ d i := hd (Finset.mem_Iic.mp hx0V)
  have hle : batchCompletion (fun _ : Fin n => c) S K.val - d x0 ≤ Tmax (fun _ => c) d S := by
    unfold Tmax
    exact le_trans (Finset.le_sup (f := fun j => batchCompletion (fun _ : Fin n => c) S K.val - d j) hx0)
      (Finset.le_sup (f := fun k : Fin S.length =>
        (S.get k).sup fun j => batchCompletion (fun _ : Fin n => c) S k.val - d j) (Finset.mem_univ K))
  have hm : (i.val / B + 1) * c ≤ (K.val + 1) * c := Nat.mul_le_mul_right c hdiv
  rw [hbc] at hle
  omega

theorem fbedd_core {n B : ℕ} (hB : 0 < B) (c : ℕ) (d : Fin n → ℕ) (hd : Monotone d) :
    IsValid B Finset.univ (fbedd n B) ∧
      ∀ S : List (Finset (Fin n)), IsValid B Finset.univ S →
        Tmax (fun _ => c) d (fbedd n B) ≤ Tmax (fun _ => c) d S := by
  refine ⟨fbedd_valid hB, fun S hS => ?_⟩
  unfold Tmax
  refine Finset.sup_le (fun k _ => Finset.sup_le (fun i hi => ?_))
  have hk : (fbedd n B).get k = blk n B k.val := by
    rw [List.get_eq_getElem]
    unfold fbedd
    rw [List.getElem_map, List.getElem_range]
    rfl
  rw [hk] at hi
  have hi' := mem_blk.mp hi
  have hbc := batchCompletion_const c (fbedd n B) (fbedd_valid hB).1 k.val k.2
  have hdiv : i.val / B = k.val := Nat.div_eq_of_lt_le (by omega) (by omega)
  have := lower hB c d hd S hS i
  rw [hdiv] at this
  unfold Tmax at this
  rw [hbc]
  exact this

end FB
end BurnInBatch.AgreeTmax

open BurnInBatch.AgreeTmax


theorem solution {n B : ℕ} (hB : 0 < B) (c : ℕ) (d : Fin n → ℕ) (hd : Monotone d) :
    IsValid B Finset.univ (fbedd n B) ∧
      ∀ S : List (Finset (Fin n)), IsValid B Finset.univ S →
        Tmax (fun _ => c) d (fbedd n B) ≤ Tmax (fun _ => c) d S := by
  exact FB.fbedd_core hB c d hd
