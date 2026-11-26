-- Prove2me | solution 1 for Bsv.Merkle.mutatedW_eq
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:31:54.971888+00:00
-- url     : https://prove2.me/submissions/877d4b77-f801-4db9-86f5-e24cea0b10b5

import Definitions.Def_bsv_merkle_width
import Theorems.Thm_Bsv_Merkle_mutatedLit_eq_mutatedTree
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle.Proof_mutatedW_eq

section

variable {α : Type} (H : α → α → α)

end

section

variable {α : Type} [DecidableEq α] (H : α → α → α)

end

section

variable {α : Type} (H : α → α → α)

theorem bitClear_eq_not_testBit (c l : Nat) : bitClear c l = !c.testBit l := by
  unfold bitClear
  rw [Nat.one_shiftLeft]
  cases hb : c.testBit l
  · have : c &&& 2 ^ l = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : l = j
      · subst hj; simp [Nat.testBit_and, hb]
      · simp [Nat.testBit_and, hj]
    simp [this]
  · have : (c &&& 2 ^ l).testBit l = true := by simp [Nat.testBit_and, hb]
    have hne : c &&& 2 ^ l ≠ 0 := by
      intro h0; rw [h0] at this; simp at this
    simp [hne]

theorem bitClear_eq (c l : Nat) : bitClear c l = decide (c / 2 ^ l % 2 = 0) := by
  rw [bitClear_eq_not_testBit, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : c / 2 ^ l % 2 = 1
  · simp [h]
  · have : c / 2 ^ l % 2 = 0 := by omega
    simp [this]

theorem absFrom_zero (inner : Nat → α) (lvl : Nat) : absFrom inner lvl 0 = [] := by
  rw [absFrom]; simp

theorem absFrom_pos (inner : Nat → α) (lvl q : Nat) (h : q ≠ 0) :
    absFrom inner lvl q =
      (if q % 2 = 1 then some (inner lvl) else none) :: absFrom inner (lvl + 1) (q / 2) := by
  rw [absFrom]; simp [h]

theorem absFrom_congr (f g : Nat → α) : ∀ (q lvl : Nat), (∀ k, lvl ≤ k → f k = g k) →
    absFrom f lvl q = absFrom g lvl q := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl hfg
    by_cases hq : q = 0
    · subst hq; rw [absFrom_zero, absFrom_zero]
    · rw [absFrom_pos f lvl q hq, absFrom_pos g lvl q hq, hfg lvl (Nat.le_refl _),
        ih (q / 2) (by omega) (lvl + 1) (fun k hk => hfg k (by omega))]

theorem length_absFrom_le (inner : Nat → α) : ∀ (q lvl : Nat),
    (absFrom inner lvl q).length ≤ q := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl
    by_cases hq : q = 0
    · subst hq; rw [absFrom_zero]; simp
    · rw [absFrom_pos inner lvl q hq]
      have := ih (q / 2) (by omega) (lvl + 1)
      simp only [List.length_cons]
      omega

section leaf

variable [DecidableEq α]

theorem leafCarry_spec (inner : Nat → α) (c : Nat) : ∀ (q lvl fuel : Nat) (h : α) (m : Bool),
    c / 2 ^ lvl = q + 1 → (absFrom inner lvl q).length < fuel →
    absFrom (upd inner (leafCarry H inner c fuel lvl h m).1 (leafCarry H inner c fuel lvl h m).2.1)
        lvl (q + 1) = insert H h (absFrom inner lvl q) ∧
    (leafCarry H inner c fuel lvl h m).2.2 = (m || insertMut H h (absFrom inner lvl q)) ∧
    lvl ≤ (leafCarry H inner c fuel lvl h m).1 := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fuel h m hc hfuel
    match fuel, hfuel with
    | 0, hfuel => omega
    | f + 1, hfuel =>
      have hbit : bitClear c lvl = decide ((q + 1) % 2 = 0) := by rw [bitClear_eq, hc]
      by_cases hodd : q % 2 = 1
      · -- the slot is occupied: combine and carry on
        have hq : q ≠ 0 := by omega
        have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
        have hc' : c / 2 ^ (lvl + 1) = q / 2 + 1 := by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hc]; omega
        have hold := absFrom_pos inner lvl q hq
        simp only [hodd, ite_true] at hold
        have hlen : (absFrom inner (lvl + 1) (q / 2)).length < f := by
          rw [hold] at hfuel; simpa using hfuel
        obtain ⟨h1, h2, h3⟩ := ih (q / 2) (by omega) (lvl + 1) f (H (inner lvl) h)
          (m || inner lvl == h) hc' hlen
        simp only [leafCarry, hclear, ite_true]
        refine ⟨?_, ?_, by omega⟩
        · rw [absFrom_pos _ lvl (q + 1) (by omega), hold]
          have he : ¬ (q + 1) % 2 = 1 := by omega
          have hd : (q + 1) / 2 = q / 2 + 1 := by omega
          simp only [he, ite_false, hd, insert, h1]
        · rw [h2, hold]; simp [insertMut, Bool.or_assoc]
      · -- the slot is free: store here
        have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
        simp only [leafCarry, hstop, Bool.false_eq_true, ite_false]
        refine ⟨?_, ?_, Nat.le_refl _⟩
        · rw [absFrom_pos _ lvl (q + 1) (by omega)]
          have ho : (q + 1) % 2 = 1 := by omega
          have hd : (q + 1) / 2 = q / 2 := by omega
          have hcg : absFrom (upd inner lvl h) (lvl + 1) (q / 2) = absFrom inner (lvl + 1) (q / 2) :=
            absFrom_congr _ _ _ _ (fun k hk => by simp [upd]; omega)
          simp only [ho, ite_true, hd, hcg, upd]
          by_cases hq : q = 0
          · subst hq; simp [absFrom_zero, insert]
          · rw [absFrom_pos inner lvl q hq]; simp [hodd, insert]
        · by_cases hq : q = 0
          · subst hq; simp [absFrom_zero, insertMut]
          · rw [absFrom_pos inner lvl q hq]; simp [hodd, insertMut]

theorem addLeaf_spec (s : Lit α) (leaf : α) :
    absFrom (addLeaf H s leaf).inner 0 (addLeaf H s leaf).count =
        insert H leaf (absFrom s.inner 0 s.count) ∧
    (addLeaf H s leaf).mutated = (s.mutated || insertMut H leaf (absFrom s.inner 0 s.count)) ∧
    (addLeaf H s leaf).count = s.count + 1 := by
  have hlen := length_absFrom_le s.inner s.count 0
  obtain ⟨h1, h2, _⟩ := leafCarry_spec H s.inner (s.count + 1) s.count 0 (s.count + 1) leaf
    s.mutated (by simp) (by omega)
  exact ⟨h1, h2, rfl⟩

end leaf

section whole

variable [DecidableEq α] [Inhabited α]

end whole

end

section

variable {α : Type} (H : α → α → α)

section

variable [DecidableEq α]

end

section

variable [DecidableEq α] [Inhabited α]

end

theorem level_lt_of_pow_le {W c lvl : Nat} (h1 : 2 ^ lvl ≤ c) (h2 : c < 2 ^ W) : lvl < W := by
  apply Nat.lt_of_not_le
  intro hle
  have := Nat.pow_le_pow_right (by decide : 0 < 2) hle
  omega

theorem pow_le_of_div_pos {c lvl q : Nat} (h : c / 2 ^ lvl = q + 1) : 2 ^ lvl ≤ c := by
  apply Nat.le_of_not_lt
  intro hlt
  rw [Nat.div_eq_of_lt hlt] at h
  omega

section

variable [DecidableEq α]

theorem leafCarryW_eq (W : Nat) (inner : Nat → α) (c : Nat) (hc : c < 2 ^ W) :
    ∀ (q lvl fuel : Nat) (h : α) (m : Bool),
    c / 2 ^ lvl = q + 1 → (absFrom inner lvl q).length < fuel →
    leafCarryW H W inner c fuel lvl h m = .ok (leafCarry H inner c fuel lvl h m) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fuel h m hq hfuel
    match fuel, hfuel with
    | 0, hfuel => omega
    | f + 1, hfuel =>
      have hlvl : lvl < W := level_lt_of_pow_le (pow_le_of_div_pos hq) hc
      have hbit : bitClear c lvl = decide ((q + 1) % 2 = 0) := by rw [bitClear_eq, hq]
      by_cases hodd : q % 2 = 1
      · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
        have hq' : c / 2 ^ (lvl + 1) = q / 2 + 1 := by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hq]; omega
        have hold := absFrom_pos inner lvl q (by omega)
        simp only [hodd, ite_true] at hold
        have hlen : (absFrom inner (lvl + 1) (q / 2)).length < f := by
          rw [hold] at hfuel; simpa using hfuel
        simp only [leafCarryW, leafCarry, bitClearW, hlvl, ite_true, hclear]
        exact ih (q / 2) (by omega) (lvl + 1) f _ _ hq' hlen
      · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
        simp [leafCarryW, leafCarry, bitClearW, hlvl, hstop]

theorem addLeafW_eq (W : Nat) (s : Lit α) (leaf : α) (hc : s.count + 1 < 2 ^ W) :
    addLeafW H W s leaf = .ok (addLeaf H s leaf) := by
  have hlen := length_absFrom_le s.inner s.count 0
  have hmod : (s.count + 1) % 2 ^ W = s.count + 1 := Nat.mod_eq_of_lt hc
  have := leafCarryW_eq H W s.inner (s.count + 1) hc s.count 0 (s.count + 1) leaf s.mutated
    (by simp) (by omega)
  simp only [addLeafW, hmod, this, addLeaf]

theorem runLeavesW_eq (W : Nat) : ∀ (l : List α) (s : Lit α), s.count + l.length < 2 ^ W →
    runLeavesW H W s l = .ok (runLeaves H s l)
  | [], s, _ => rfl
  | a :: t, s, hc => by
    simp only [List.length_cons] at hc
    have h3 := (addLeaf_spec H s a).2.2
    simp only [runLeavesW, addLeafW_eq H W s a (by omega)]
    exact runLeavesW_eq W t (addLeaf H s a) (by rw [h3]; omega)

end

section

variable [DecidableEq α] [Inhabited α]

end

section

variable [DecidableEq α] [Inhabited α]

theorem mutatedW_eq (W : Nat) (l : List α) (hl : l.length < 2 ^ W) :
    mutatedW H W l = .ok (mutatedTree H l) := by
  rw [← mutatedLit_eq_mutatedTree]
  simp [mutatedW, runLeavesW_eq H W l (start : Lit α) (by simp only [start]; omega),
    mutatedLit, Except.map]

end

end

end Bsv.Merkle.Proof_mutatedW_eq

open Bsv.Merkle

theorem solution {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α]
    (W : Nat) (l : List α) (hl : l.length < 2 ^ W) :
    mutatedW H W l = .ok (mutatedTree H l) :=
  Bsv.Merkle.Proof_mutatedW_eq.mutatedW_eq H W l hl
