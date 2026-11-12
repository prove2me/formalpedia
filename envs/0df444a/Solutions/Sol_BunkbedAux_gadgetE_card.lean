-- Prove2me | solution 1 for BunkbedAux.gadgetE_card
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T04:07:35.501312+00:00
-- url     : https://prove2.me/submissions/e5fa055c-b11c-4661-9a8b-4d6d25a759c0

import Definitions.Def_BunkbedPercolation

set_option maxRecDepth 8000

open Bunkbed SimpleGraph Finset

/-! ## The edge count of the gadget `Gₙ`: `2n - 1` -/

/-- Reduction `ℕ → Fin (n+1)`; this Mathlib has no `NatCast (Fin _)` instance. -/
def fc (n : ℕ) (m : ℕ) : Fin (n + 1) := ⟨m % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩

lemma fc_val (n m : ℕ) (h : m < n + 1) : (fc n m).val = m := Nat.mod_eq_of_lt h

lemma fc_self {n : ℕ} (k : Fin (n + 1)) : fc n k.val = k := Fin.ext (fc_val n k.val k.isLt)

lemma mem_gadgetE_iff {n : ℕ} (e : Sym2 (Fin (n + 1))) :
    e ∈ gadgetE n ↔ ∃ p : Fin (n + 1) × Fin (n + 1),
      ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (1 ≤ p.1.val ∧ p.2.val = p.1.val + 1)) ∧ s(p.1, p.2) = e := by
  simp only [gadgetE, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The `n` spokes of `Gₙ`. -/
def spokeS (n : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (Finset.Ico 1 (n + 1)).image (fun m : ℕ => s((0 : Fin (n + 1)), fc n m))

/-- The `n - 1` path edges of `Gₙ`. -/
def pathS (n : ℕ) : Finset (Sym2 (Fin (n + 1))) :=
  (Finset.Ico 1 n).image (fun m : ℕ => s(fc n m, fc n (m + 1)))

lemma gadgetE_eq (n : ℕ) : gadgetE n = spokeS n ∪ pathS n := by
  ext e
  rw [mem_gadgetE_iff, Finset.mem_union]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine Finset.mem_image.2 ⟨p.2.val, Finset.mem_Ico.2 ⟨?_, p.2.isLt⟩, ?_⟩
      · rcases Nat.eq_zero_or_pos p.2.val with h | h
        · exact absurd (Fin.ext h : p.2 = 0) h2
        · exact h
      · show s((0 : Fin (n + 1)), fc n p.2.val) = s(p.1, p.2)
        rw [h1, fc_self]
    · right
      have h3 := p.2.isLt
      refine Finset.mem_image.2 ⟨p.1.val, Finset.mem_Ico.2 ⟨h1, by omega⟩, ?_⟩
      show s(fc n p.1.val, fc n (p.1.val + 1)) = s(p.1, p.2)
      rw [fc_self]
      congr 1
      exact Fin.ext (by rw [fc_val n _ (by omega), h2])
  · rintro (h | h)
    · obtain ⟨m, hm, he⟩ := Finset.mem_image.1 h
      rw [Finset.mem_Ico] at hm
      refine ⟨(0, fc n m), Or.inl ⟨rfl, ?_⟩, he⟩
      intro hc
      have hc' : fc n m = 0 := hc
      have hv : (fc n m).val = 0 := by rw [hc']; rfl
      rw [fc_val n m (by omega)] at hv
      omega
    · obtain ⟨m, hm, he⟩ := Finset.mem_image.1 h
      rw [Finset.mem_Ico] at hm
      refine ⟨(fc n m, fc n (m + 1)), Or.inr ⟨?_, ?_⟩, he⟩
      · rw [fc_val n m (by omega)]; omega
      · rw [fc_val n m (by omega), fc_val n (m + 1) (by omega)]

lemma spokeS_card (n : ℕ) : (spokeS n).card = n := by
  have hinj : Set.InjOn (fun m : ℕ => s((0 : Fin (n + 1)), fc n m))
      (Finset.Ico 1 (n + 1)) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    rcases Sym2.eq_iff.mp hab with ⟨-, h⟩ | ⟨h1, -⟩
    · have hv : (fc n a).val = (fc n b).val := by rw [h]
      rw [fc_val n a (by omega), fc_val n b (by omega)] at hv
      exact hv
    · exfalso
      have hv : (0 : Fin (n + 1)).val = (fc n b).val := by rw [h1]
      rw [fc_val n b (by omega)] at hv
      simp only [Fin.val_zero] at hv
      omega
  have hc : (Finset.Ico 1 (n + 1)).card = n := by rw [Nat.card_Ico]; omega
  rw [spokeS, Finset.card_image_of_injOn hinj, hc]

lemma pathS_card (n : ℕ) : (pathS n).card = n - 1 := by
  have hinj : Set.InjOn (fun m : ℕ => s(fc n m, fc n (m + 1))) (Finset.Ico 1 n) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    rcases Sym2.eq_iff.mp hab with ⟨h, -⟩ | ⟨h1, h2⟩
    · have hv : (fc n a).val = (fc n b).val := by rw [h]
      rw [fc_val n a (by omega), fc_val n b (by omega)] at hv
      exact hv
    · exfalso
      have e1 : (fc n a).val = (fc n (b + 1)).val := by rw [h1]
      have e2 : (fc n (a + 1)).val = (fc n b).val := by rw [h2]
      rw [fc_val n a (by omega), fc_val n (b + 1) (by omega)] at e1
      rw [fc_val n (a + 1) (by omega), fc_val n b (by omega)] at e2
      omega
  have hc : (Finset.Ico 1 n).card = n - 1 := by rw [Nat.card_Ico]
  rw [pathS, Finset.card_image_of_injOn hinj, hc]

lemma spokeS_disjoint_pathS (n : ℕ) : Disjoint (spokeS n) (pathS n) := by
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨b, hb, hb2⟩ := Finset.mem_image.1 he'
  rw [Finset.mem_Ico] at ha hb
  rcases Sym2.eq_iff.mp hb2 with ⟨h1, -⟩ | ⟨-, h2⟩
  · have hv : (fc n b).val = (0 : Fin (n + 1)).val := by rw [h1]
    rw [fc_val n b (by omega)] at hv
    simp only [Fin.val_zero] at hv
    omega
  · have hv : (fc n (b + 1)).val = (0 : Fin (n + 1)).val := by rw [h2]
    rw [fc_val n (b + 1) (by omega)] at hv
    simp only [Fin.val_zero] at hv
    omega

theorem solution (n : ℕ) : (gadgetE n).card = 2 * n - 1 := by
  rw [gadgetE_eq, Finset.card_union_of_disjoint (spokeS_disjoint_pathS n), spokeS_card,
    pathS_card]
  omega
