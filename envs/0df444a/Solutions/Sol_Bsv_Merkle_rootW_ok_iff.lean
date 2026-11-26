-- Prove2me | solution 1 for Bsv.Merkle.rootW_ok_iff
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:32:32.316269+00:00
-- url     : https://prove2.me/submissions/04816945-9e5f-43ea-b2b7-e9570920347b

import Definitions.Def_bsv_merkle_width
import Theorems.Thm_Bsv_Merkle_rootW_eq
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle.Proof_rootW_ok_iff

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

theorem pow_le_mul {q lvl : Nat} (hq : q ≠ 0) : 2 ^ lvl ≤ q * 2 ^ lvl :=
  Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)

theorem sweep_bound {p L B : Nat} (h : (p + 1) * 2 ^ L ≤ 2 ^ B) (heven : p % 2 = 0)
    (hp : p ≠ 0) : (p + 2) * 2 ^ L ≤ 2 ^ B := by
  have hL : L < B := by
    apply Nat.lt_of_not_le
    intro hle
    have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) hle
    have h2 : 3 * 2 ^ L ≤ (p + 1) * 2 ^ L := Nat.mul_le_mul_right _ (by omega)
    have h3 := Nat.two_pow_pos L
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hL
  have hB : 2 ^ B = 2 ^ (k + 1) * 2 ^ L := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hB] at h ⊢
  have h1 : p + 1 ≤ 2 ^ (k + 1) := Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos L)
  have h2 : 2 ^ (k + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
  exact Nat.mul_le_mul_right _ (by omega)

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

end

end

section

variable {α : Type} (H : α → α → α)

theorem bitClear_zero (l : Nat) : bitClear 0 l = true := by
  simp [bitClear]

theorem le_two_pow_pred (W : Nat) (hW : 0 < W) : W ≤ 2 ^ (W - 1) := by
  have := Nat.lt_two_pow_self (n := W - 1)
  omega

theorem sweepInnerW_zero (W : Nat) (inner : Nat → α) : ∀ (fuel lvl : Nat) (h : α),
    lvl ≤ W → W - lvl < fuel → sweepInnerW H W inner 0 fuel lvl h = .error .shift
  | 0, _, _, _, hf => by omega
  | f + 1, lvl, h, hle, hf => by
    by_cases hl : lvl < W
    · simp only [sweepInnerW, bitClearW, hl, ite_true, bitClear_zero]
      exact sweepInnerW_zero W inner f (lvl + 1) _ (by omega) (by omega)
    · simp [sweepInnerW, bitClearW, hl]

section

variable [DecidableEq α]

theorem leafCarryW_zero (W : Nat) (inner : Nat → α) : ∀ (fuel lvl : Nat) (h : α) (m : Bool),
    lvl ≤ W → W - lvl < fuel → leafCarryW H W inner 0 fuel lvl h m = .error .shift
  | 0, _, _, _, _, hf => by omega
  | f + 1, lvl, h, m, hle, hf => by
    by_cases hl : lvl < W
    · simp only [leafCarryW, bitClearW, hl, ite_true, bitClear_zero]
      exact leafCarryW_zero W inner f (lvl + 1) _ _ (by omega) (by omega)
    · simp [leafCarryW, bitClearW, hl]

end

theorem sweepW_carry_fault (W : Nat) (hW : 0 < W) (inner : Nat → α) (F : Nat) (hF0 : W < F) :
    ∀ (p L fi fo : Nat) (h : α) (cc : Nat),
    cc = (p + 1) * 2 ^ L → 2 ^ (W - 1) < cc → cc < 2 ^ W →
    (absFrom inner L p).length < fi → (absFrom inner L p).length < F →
    (absFrom inner L p).length < fo →
    (sweepInnerW H W inner cc fi L h).bind (fun r => sweepOuterW H W inner F fo cc r.1 r.2) =
      .error .shift := by
  have hpow : 2 ^ W = 2 * 2 ^ (W - 1) := by
    obtain ⟨k, rfl⟩ : ∃ k, W = k + 1 := ⟨W - 1, by omega⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h cc hcc hlow hhigh hfi hF hfo
    have hL : L < W := level_lt_of_pow_le (c := cc) (by rw [hcc]; exact pow_le_mul (by omega))
      hhigh
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      match fo, hfo with
      | 0, hfo => omega
      | g + 1, hfo =>
        by_cases hodd : p % 2 = 1
        · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
          have hold := absFrom_pos inner L p (by omega)
          simp only [hodd, ite_true] at hold
          have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
            congr 1; omega
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          simp only [sweepInnerW, bitClearW, hL, ite_true, hclear]
          exact ih (p / 2) (by omega) (L + 1) f (g + 1) _ cc hcc' hlow hhigh (by omega)
            (by omega) (by omega)
        · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
          have hp : p ≠ 0 := by
            intro hp0
            subst hp0
            have h1 : cc = 2 ^ L := by rw [hcc]; simp
            have h2 : 2 ^ L ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by decide) (by omega)
            omega
          have hold := absFrom_pos inner L p hp
          simp only [hodd, ite_false] at hold
          rw [hold] at hfi hF hfo
          simp only [List.length_cons] at hfi hF hfo
          have e1 : sweepInnerW H W inner cc (f + 1) L h = .ok (L, h) := by
            simp [sweepInnerW, bitClearW, hL, hstop]
          have hne : (cc != 1 <<< L) = true := by
            rw [hcc, ne_one_shiftLeft]; simp; omega
          have hstep : cc + 1 <<< L = (p / 2 + 1) * 2 ^ (L + 1) := by
            rw [hcc, add_one_shiftLeft, mul_pow_succ_of_even (p + 1 + 1) L (by omega)]
            congr 1; omega
          have hb2 : cc + 1 <<< L ≤ 2 ^ W := by
            rw [hcc, add_one_shiftLeft]
            exact sweep_bound (by rw [← hcc]; omega) (by omega) hp
          have hpos : 0 < 1 <<< L := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos L
          rw [e1]
          change sweepOuterW H W inner F (g + 1) cc L h = .error .shift
          by_cases hwrap : cc + 1 <<< L = 2 ^ W
          · have hmod : (cc + 1 <<< L) % 2 ^ W = 0 := by rw [hwrap]; simp
            simp only [sweepOuterW, hL, ite_true, hne, hmod]
            rw [sweepInnerW_zero H W inner F (L + 1) _ (by omega) (by omega)]
            rfl
          · have hlt : cc + 1 <<< L < 2 ^ W := by omega
            have hmod : (cc + 1 <<< L) % 2 ^ W = cc + 1 <<< L := Nat.mod_eq_of_lt hlt
            simp only [sweepOuterW, hL, ite_true, hne, hmod]
            exact ih (p / 2) (by omega) (L + 1) F g _ _ hstep (by omega) hlt (by omega)
              (by omega) (by omega)

theorem sweepW_top_fault (W : Nat) (hW : 0 < W) (inner : Nat → α) (F : Nat) (hF0 : W < F)
    (q lvl fo : Nat) (h : α) (c : Nat) (hc : c = q * 2 ^ lvl)
    (hlow : 2 ^ (W - 1) < c) (hhigh : c < 2 ^ W) (hodd : q % 2 = 1)
    (hF : (absFrom inner (lvl + 1) (q / 2)).length < F)
    (hfo : (absFrom inner (lvl + 1) (q / 2)).length + 1 < fo) :
    sweepOuterW H W inner F fo c lvl h = .error .shift := by
  have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul (by omega))
    hhigh
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    have hq : q ≠ 1 := by
      intro hq1
      subst hq1
      have h1 : c = 2 ^ lvl := by rw [hc]; simp
      have h2 : 2 ^ lvl ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have hne : (c != 1 <<< lvl) = true := by rw [hc, ne_one_shiftLeft]; simp [hq]
    have hstep : c + 1 <<< lvl = (q / 2 + 1) * 2 ^ (lvl + 1) := by
      rw [hc, add_one_shiftLeft, mul_pow_succ_of_even (q + 1) lvl (by omega)]
      congr 1; omega
    have hb2 : c + 1 <<< lvl ≤ 2 ^ W := by
      rw [hc, add_one_shiftLeft]
      have : (q - 1 + 1) * 2 ^ lvl ≤ 2 ^ W := by
        have e : q - 1 + 1 = q := by omega
        rw [e, ← hc]; omega
      have := sweep_bound this (by omega) (by omega)
      have e : q - 1 + 2 = q + 1 := by omega
      rwa [e] at this
    have hpos : 0 < 1 <<< lvl := by rw [Nat.one_shiftLeft]; exact Nat.two_pow_pos lvl
    by_cases hwrap : c + 1 <<< lvl = 2 ^ W
    · have hmod : (c + 1 <<< lvl) % 2 ^ W = 0 := by rw [hwrap]; simp
      simp only [sweepOuterW, hL, ite_true, hne, hmod]
      rw [sweepInnerW_zero H W inner F (lvl + 1) _ (by omega) (by omega)]
      rfl
    · have hlt : c + 1 <<< lvl < 2 ^ W := by omega
      have hmod : (c + 1 <<< lvl) % 2 ^ W = c + 1 <<< lvl := Nat.mod_eq_of_lt hlt
      simp only [sweepOuterW, hL, ite_true, hne, hmod]
      exact sweepW_carry_fault H W hW inner F hF0 (q / 2) (lvl + 1) F g _ _ hstep (by omega) hlt
        hF hF (by omega)

theorem finishW_fault (W : Nat) (hW : 0 < W) (inner : Nat → α) (F fo : Nat) (hF0 : W < F) :
    ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → 2 ^ (W - 1) < c → c < 2 ^ W → q ≠ 0 →
    (absFrom inner lvl q).length ≤ fs → (absFrom inner lvl q).length ≤ F →
    (absFrom inner lvl q).length < fo →
    finishW H W inner F fo c fs lvl = .error .shift := by
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hlow hhigh hq hfs hF hfo
    have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul hq) hhigh
    have hbit : bitClear c lvl = decide (q % 2 = 0) := by rw [hc, bitClear_mul]
    have hold := absFrom_pos inner lvl q hq
    by_cases hodd : q % 2 = 1
    · have hstop : bitClear c lvl = false := by rw [hbit]; simp; omega
      simp only [hodd, ite_true] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        simp only [finishW, skipLowW, bitClearW, hL, ite_true, hstop, Except.bind]
        rw [sweepW_top_fault H W hW inner F hF0 q lvl fo _ c hc hlow hhigh hodd (by omega)
          (by omega)]
    · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
      simp only [hodd, ite_false] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        have hc' : c = (q / 2) * 2 ^ (lvl + 1) := by
          rw [hc, mul_pow_succ_of_even q lvl (by omega)]
        have := ih (q / 2) (by omega) (lvl + 1) f c hc' hlow hhigh (by omega) (by omega)
          (by omega) (by omega)
        simp only [finishW, skipLowW, bitClearW, hL, ite_true, hclear] at this ⊢
        exact this

section

variable [DecidableEq α] [Inhabited α]

theorem runLeavesW_fault (W : Nat) (hW : 0 < W) : ∀ (l : List α) (s : Lit α),
    s.count < 2 ^ W → 2 ^ W ≤ s.count + l.length →
    runLeavesW H W s l = .error .shift
  | [], s, h1, h2 => by simp at h2; omega
  | a :: t, s, h1, h2 => by
    simp only [List.length_cons] at h2
    by_cases hlast : s.count + 1 = 2 ^ W
    · have hmod : (s.count + 1) % 2 ^ W = 0 := by rw [hlast]; simp
      have hWlt : W < 2 ^ W := Nat.lt_two_pow_self
      have := leafCarryW_zero H W s.inner (s.count + 1) 0 a s.mutated (by omega) (by omega)
      simp [runLeavesW, addLeafW, hmod, this]
    · have h3 := (addLeaf_spec H s a).2.2
      simp only [runLeavesW, addLeafW_eq H W s a (by omega)]
      exact runLeavesW_fault W hW t (addLeaf H s a) (by rw [h3]; omega) (by rw [h3]; omega)

theorem rootW_fault (W : Nat) (hW : 0 < W) (l : List α) (hl : 2 ^ (W - 1) < l.length) :
    rootW H W l = .error .shift := by
  have hWle := le_two_pow_pred W hW
  match l, hl with
  | [], hl => simp at hl
  | a :: t, hl =>
    by_cases hbig : 2 ^ W ≤ (a :: t).length
    · have := runLeavesW_fault H W hW (a :: t) (start : Lit α)
        (by simp only [start]; exact Nat.two_pow_pos W) (by simp only [start]; omega)
      simp [rootW, this, Except.bind]
    · have hlt : (a :: t).length < 2 ^ W := by omega
      obtain ⟨_, _, h3⟩ := runLeaves_spec H (a :: t) (start : Lit α)
      have hcnt : (runLeaves H start (a :: t)).count = (a :: t).length := by
        rw [h3]; simp [start]
      have hlen := length_absFrom_le (runLeaves H start (a :: t)).inner
        (runLeaves H start (a :: t)).count 0
      have hrun := runLeavesW_eq H W (a :: t) (start : Lit α) (by simp only [start]; omega)
      have hf := finishW_fault H W hW (runLeaves H start (a :: t)).inner
        ((runLeaves H start (a :: t)).count + 1) ((runLeaves H start (a :: t)).count + 1)
        (by omega) (runLeaves H start (a :: t)).count 0
        ((runLeaves H start (a :: t)).count + 1) (runLeaves H start (a :: t)).count (by simp)
        (by rw [hcnt]; exact hl) (by rw [hcnt]; exact hlt) (by rw [hcnt]; simp) (by omega)
        (by omega) (by omega)
      simp only [rootW, hrun]
      change finishW H W _ _ _ _ _ 0 = _
      rw [hf]

theorem rootW_ok_iff (W : Nat) (hW : 0 < W) (l : List α) :
    (∃ r, rootW H W l = .ok r) ↔ l.length ≤ 2 ^ (W - 1) := by
  constructor
  · intro ⟨r, hr⟩
    apply Nat.le_of_not_lt
    intro hlt
    rw [rootW_fault H W hW l hlt] at hr
    cases hr
  · intro hle
    exact ⟨_, rootW_eq H W hW l hle⟩

end

end

end Bsv.Merkle.Proof_rootW_ok_iff

open Bsv.Merkle

theorem solution {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α]
    (W : Nat) (hW : 0 < W) (l : List α) :
    (∃ r, rootW H W l = .ok r) ↔ l.length ≤ 2 ^ (W - 1) :=
  Bsv.Merkle.Proof_rootW_ok_iff.rootW_ok_iff H W hW l
