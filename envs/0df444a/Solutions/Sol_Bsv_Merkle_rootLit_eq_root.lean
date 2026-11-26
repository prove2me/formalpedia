-- Prove2me | solution 1 for Bsv.Merkle.rootLit_eq_root
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:29:37.797369+00:00
-- url     : https://prove2.me/submissions/8fefbe1f-1b88-45f6-8062-a27c487387e1

import Definitions.Def_bsv_merkle_literal
import Theorems.Thm_Bsv_Merkle_rootCS_eq_root
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle.Proof_rootLit_eq_root

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

theorem bitClear_mul (q l : Nat) : bitClear (q * 2 ^ l) l = decide (q % 2 = 0) := by
  rw [bitClear_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos l)]

theorem mul_pow_succ_of_even (q l : Nat) (h : q % 2 = 0) :
    q * 2 ^ l = (q / 2) * 2 ^ (l + 1) := by
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (q / 2 * 2 ^ l) 2, ← Nat.mul_assoc,
    Nat.mul_comm 2 (q / 2)]
  congr 1
  omega

theorem ne_one_shiftLeft (q l : Nat) : (q * 2 ^ l != 1 <<< l) = decide (q ≠ 1) := by
  rw [Nat.one_shiftLeft]
  have hp : 0 < 2 ^ l := Nat.two_pow_pos l
  by_cases h : q = 1
  · subst h; simp
  · have : q * 2 ^ l ≠ 2 ^ l := by
      intro he
      have : q * 2 ^ l = 1 * 2 ^ l := by rw [he, Nat.one_mul]
      exact h (Nat.eq_of_mul_eq_mul_right hp this)
    simp [h, this]

theorem add_one_shiftLeft (q l : Nat) : q * 2 ^ l + 1 <<< l = (q + 1) * 2 ^ l := by
  rw [Nat.one_shiftLeft, Nat.add_mul, Nat.one_mul]

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

theorem absFrom_not_all_none (inner : Nat → α) : ∀ (q lvl : Nat), q ≠ 0 →
    (absFrom inner lvl q).all Option.isNone = false := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl hq
    rw [absFrom_pos inner lvl q hq]
    by_cases hodd : q % 2 = 1
    · simp [hodd]
    · have := ih (q / 2) (by omega) (lvl + 1) (by omega)
      simp [hodd, this]

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

theorem runLeaves_spec : ∀ (l : List α) (s : Lit α),
    absFrom (runLeaves H s l).inner 0 (runLeaves H s l).count =
        counter H l (absFrom s.inner 0 s.count) ∧
    (runLeaves H s l).mutated = (s.mutated || mutCounter H l (absFrom s.inner 0 s.count)) ∧
    (runLeaves H s l).count = s.count + l.length
  | [], s => by simp [runLeaves, counter, mutCounter]
  | a :: t, s => by
    obtain ⟨h1, h2, h3⟩ := addLeaf_spec H s a
    obtain ⟨g1, g2, g3⟩ := runLeaves_spec t (addLeaf H s a)
    have e : runLeaves H s (a :: t) = runLeaves H (addLeaf H s a) t := rfl
    rw [e]
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, h1]; rfl
    · rw [g2, h2, h1]; simp [mutCounter, Bool.or_assoc]
    · rw [g3, h3]; simp only [List.length_cons]; omega

end leaf

theorem sweep_carry (inner : Nat → α) (F : Nat) : ∀ (p L fi fo : Nat) (h : α) (cc : Nat),
    cc = (p + 1) * 2 ^ L →
    (absFrom inner L p).length < fi → (absFrom inner L p).length < F →
    (absFrom inner L p).length ≤ fo →
    sweepOuter H inner F fo cc (sweepInner H inner cc fi L h).1 (sweepInner H inner cc fi L h).2 =
      carry H h (absFrom inner L p) := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h cc hcc hfi hF hfo
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      by_cases hp : p = 0
      · subst hp
        have hstop : bitClear cc L = false := by rw [hbit]; simp
        simp only [sweepInner, hstop, Bool.false_eq_true, ite_false, absFrom_zero, carry]
        match fo with
        | 0 => rfl
        | g + 1 =>
          have hne : (cc != 1 <<< L) = false := by rw [hcc, ne_one_shiftLeft]; simp
          simp only [sweepOuter, hne, Bool.false_eq_true, ite_false]
      · have hold := absFrom_pos inner L p hp
        by_cases hodd : p % 2 = 1
        · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
          simp only [hodd, ite_true] at hold
          have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
            congr 1; omega
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          simp only [sweepInner, hclear, ite_true, hold, carry]
          exact ih (p / 2) (by omega) (L + 1) f fo _ cc hcc' (by omega) (by omega) (by omega)
        · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
          simp only [hodd, ite_false] at hold
          have hrest : (absFrom inner (L + 1) (p / 2)).all Option.isNone = false :=
            absFrom_not_all_none inner _ _ (by omega)
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          simp only [sweepInner, hstop, Bool.false_eq_true, ite_false, hold, carry, hrest]
          match fo, hfo with
          | 0, hfo => omega
          | g + 1, hfo =>
            have hne : (cc != 1 <<< L) = true := by
              rw [hcc, ne_one_shiftLeft]; simp; omega
            have hcc' : cc + 1 <<< L = (p / 2 + 1) * 2 ^ (L + 1) := by
              rw [hcc, add_one_shiftLeft, mul_pow_succ_of_even (p + 1 + 1) L (by omega)]
              congr 1; omega
            simp only [sweepOuter, hne, ite_true]
            exact ih (p / 2) (by omega) (L + 1) F g _ _ hcc' (by omega) (by omega) (by omega)

theorem sweep_top (inner : Nat → α) (F : Nat) (q lvl fo : Nat) (h : α) (c : Nat)
    (hc : c = q * 2 ^ lvl) (hodd : q % 2 = 1)
    (hF : (absFrom inner (lvl + 1) (q / 2)).length < F)
    (hfo : (absFrom inner (lvl + 1) (q / 2)).length < fo) :
    sweepOuter H inner F fo c lvl h = top H h (absFrom inner (lvl + 1) (q / 2)) := by
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    by_cases hq : q = 1
    · subst hq
      have hne : (c != 1 <<< lvl) = false := by rw [hc, ne_one_shiftLeft]; simp
      simp [sweepOuter, hne, top, absFrom_zero]
    · have hne : (c != 1 <<< lvl) = true := by rw [hc, ne_one_shiftLeft]; simp [hq]
      have hrest : (absFrom inner (lvl + 1) (q / 2)).all Option.isNone = false :=
        absFrom_not_all_none inner _ _ (by omega)
      have hcc' : c + 1 <<< lvl = (q / 2 + 1) * 2 ^ (lvl + 1) := by
        rw [hc, add_one_shiftLeft, mul_pow_succ_of_even (q + 1) lvl (by omega)]
        congr 1; omega
      simp only [sweepOuter, hne, ite_true, top, hrest, Bool.false_eq_true, ite_false]
      exact sweep_carry H inner F (q / 2) (lvl + 1) F g _ _ hcc' hF hF (by omega)

theorem sweep_finish (inner : Nat → α) (F fo : Nat) : ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → q ≠ 0 →
    (absFrom inner lvl q).length ≤ fs → (absFrom inner lvl q).length ≤ F →
    (absFrom inner lvl q).length ≤ fo →
    some (sweepOuter H inner F fo c (skipLow c fs lvl) (inner (skipLow c fs lvl))) =
      finish H (absFrom inner lvl q) := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hq hfs hF hfo
    have hbit : bitClear c lvl = decide (q % 2 = 0) := by rw [hc, bitClear_mul]
    have hold := absFrom_pos inner lvl q hq
    by_cases hodd : q % 2 = 1
    · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
      have hskip : skipLow c fs lvl = lvl := by
        cases fs <;> simp [skipLow, hstop]
      simp only [hodd, ite_true] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      rw [hskip, hold, finish]
      congr 1
      exact sweep_top H inner F q lvl fo _ c hc hodd (by omega) (by omega)
    · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
      simp only [hodd, ite_false] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        have hc' : c = (q / 2) * 2 ^ (lvl + 1) := by
          rw [hc, mul_pow_succ_of_even q lvl (by omega)]
        rw [hold, finish]
        simp only [skipLow, hclear, ite_true]
        exact ih (q / 2) (by omega) (lvl + 1) f c hc' (by omega) (by omega) (by omega) (by omega)

section whole

variable [DecidableEq α] [Inhabited α]

theorem rootLit_eq_root (l : List α) : rootLit H l = root H l := by
  rw [← rootCS_eq_root]
  match l with
  | [] => simp [rootLit, rootCS, counter, finish]
  | a :: t =>
    obtain ⟨h1, _, h3⟩ := runLeaves_spec H (a :: t) (start : Lit α)
    have hcount : (runLeaves H start (a :: t)).count ≠ 0 := by
      rw [h3]; simp [start]
    have hlen := length_absFrom_le (runLeaves H start (a :: t)).inner
      (runLeaves H start (a :: t)).count 0
    simp only [rootLit, rootCS]
    rw [sweep_finish H _ _ _ _ 0 _ _ (by simp) hcount (by omega) (by omega) (by omega), h1]
    simp [start, absFrom_zero]

end whole

end

end Bsv.Merkle.Proof_rootLit_eq_root

open Bsv.Merkle

theorem solution {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α] (l : List α) :
    rootLit H l = root H l :=
  Bsv.Merkle.Proof_rootLit_eq_root.rootLit_eq_root H l
