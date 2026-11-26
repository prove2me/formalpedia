-- Prove2me | solution 1 for Bsv.Merkle.rootW_eq
-- status  : ACCEPTED   (prove)
-- author  : @GregoryJWard
-- created : 2026-11-26T14:31:03.033803+00:00
-- url     : https://prove2.me/submissions/9b3de0b4-a5b0-4439-ba38-5ffedd9db1f5

import Definitions.Def_bsv_merkle_width
import Theorems.Thm_Bsv_Merkle_rootLit_eq_root
/-!
Authors: Gregory J. Ward, Bryan W. Daugherty, Shawn M. Ryan.
Source: https://github.com/codenlighten/bsv-lean-proofs (41c4bfd), Apache-2.0.
-/

namespace Bsv.Merkle.Proof_rootW_eq

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

theorem sweepW_carry (W B : Nat) (hB : B < W) (inner : Nat → α) (F : Nat) :
    ∀ (p L fi fo : Nat) (h : α) (cc : Nat),
    cc = (p + 1) * 2 ^ L → cc ≤ 2 ^ B →
    (absFrom inner L p).length < fi → (absFrom inner L p).length < F →
    (absFrom inner L p).length < fo →
    (sweepInnerW H W inner cc fi L h).bind (fun r => sweepOuterW H W inner F fo cc r.1 r.2) =
      .ok (sweepOuter H inner F fo cc (sweepInner H inner cc fi L h).1
        (sweepInner H inner cc fi L h).2) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro L fi fo h cc hcc hbound hfi hF hfo
    have hL : L < W := level_lt_of_pow_le (c := cc) (by rw [hcc]; exact pow_le_mul (by omega))
      (by omega)
    match fi, hfi with
    | 0, hfi => omega
    | f + 1, hfi =>
      have hbit : bitClear cc L = decide ((p + 1) % 2 = 0) := by rw [hcc, bitClear_mul]
      match fo, hfo with
      | 0, hfo => omega
      | g + 1, hfo =>
        by_cases hp : p = 0
        · subst hp
          have hstop : bitClear cc L = false := by rw [hbit]; simp
          have hne : (cc != 1 <<< L) = false := by rw [hcc, ne_one_shiftLeft]; simp
          simp [sweepInnerW, sweepInner, bitClearW, hL, hstop, Except.bind, sweepOuterW,
            sweepOuter, hne]
        · have hold := absFrom_pos inner L p hp
          by_cases hodd : p % 2 = 1
          · have hclear : bitClear cc L = true := by rw [hbit]; simp; omega
            simp only [hodd, ite_true] at hold
            have hcc' : cc = (p / 2 + 1) * 2 ^ (L + 1) := by
              rw [hcc, mul_pow_succ_of_even (p + 1) L (by omega)]
              congr 1; omega
            rw [hold] at hfi hF hfo
            simp only [List.length_cons] at hfi hF hfo
            simp only [sweepInnerW, sweepInner, bitClearW, hL, ite_true, hclear]
            exact ih (p / 2) (by omega) (L + 1) f (g + 1) _ cc hcc' hbound (by omega) (by omega)
              (by omega)
          · have hstop : bitClear cc L = false := by rw [hbit]; simp; omega
            simp only [hodd, ite_false] at hold
            rw [hold] at hfi hF hfo
            simp only [List.length_cons] at hfi hF hfo
            have hne : (cc != 1 <<< L) = true := by
              rw [hcc, ne_one_shiftLeft]; simp; omega
            have hstep : cc + 1 <<< L = (p / 2 + 1) * 2 ^ (L + 1) := by
              rw [hcc, add_one_shiftLeft, mul_pow_succ_of_even (p + 1 + 1) L (by omega)]
              congr 1; omega
            have hb2 : cc + 1 <<< L ≤ 2 ^ B := by
              rw [hcc, add_one_shiftLeft]
              exact sweep_bound (by rw [← hcc]; exact hbound) (by omega) hp
            have hmod : (cc + 1 <<< L) % 2 ^ W = cc + 1 <<< L := Nat.mod_eq_of_lt (by omega)
            have e1 : sweepInnerW H W inner cc (f + 1) L h = .ok (L, h) := by
              simp [sweepInnerW, bitClearW, hL, hstop]
            have e2 : sweepInner H inner cc (f + 1) L h = (L, h) := by
              simp [sweepInner, hstop]
            have e3 : sweepOuterW H W inner F (g + 1) cc L h =
                (sweepInnerW H W inner (cc + 1 <<< L) F (L + 1) (H h h)).bind
                  (fun r => sweepOuterW H W inner F g (cc + 1 <<< L) r.1 r.2) := by
              simp only [sweepOuterW, hL, ite_true, hne, hmod]
            have e4 : sweepOuter H inner F (g + 1) cc L h =
                sweepOuter H inner F g (cc + 1 <<< L)
                  (sweepInner H inner (cc + 1 <<< L) F (L + 1) (H h h)).1
                  (sweepInner H inner (cc + 1 <<< L) F (L + 1) (H h h)).2 := by
              simp only [sweepOuter, hne, ite_true]
            rw [e1, e2]
            change sweepOuterW H W inner F (g + 1) cc L h = .ok (sweepOuter H inner F (g + 1) cc L h)
            rw [e3, e4]
            exact ih (p / 2) (by omega) (L + 1) F g _ _ hstep hb2 (by omega) (by omega) (by omega)

theorem sweepW_top (W B : Nat) (hB : B < W) (inner : Nat → α) (F : Nat) (q lvl fo : Nat) (h : α)
    (c : Nat) (hc : c = q * 2 ^ lvl) (hbound : c ≤ 2 ^ B) (hodd : q % 2 = 1)
    (hF : (absFrom inner (lvl + 1) (q / 2)).length < F)
    (hfo : (absFrom inner (lvl + 1) (q / 2)).length + 1 < fo) :
    sweepOuterW H W inner F fo c lvl h = .ok (sweepOuter H inner F fo c lvl h) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul (by omega))
    (by omega)
  match fo, hfo with
  | 0, hfo => omega
  | g + 1, hfo =>
    by_cases hq : q = 1
    · subst hq
      have hne : (c != 1 <<< lvl) = false := by rw [hc, ne_one_shiftLeft]; simp
      simp [sweepOuterW, sweepOuter, hL, hne]
    · have hne : (c != 1 <<< lvl) = true := by rw [hc, ne_one_shiftLeft]; simp [hq]
      have hstep : c + 1 <<< lvl = (q / 2 + 1) * 2 ^ (lvl + 1) := by
        rw [hc, add_one_shiftLeft, mul_pow_succ_of_even (q + 1) lvl (by omega)]
        congr 1; omega
      have hb2 : c + 1 <<< lvl ≤ 2 ^ B := by
        rw [hc, add_one_shiftLeft]
        have : (q - 1 + 1) * 2 ^ lvl ≤ 2 ^ B := by
          have e : q - 1 + 1 = q := by omega
          rw [e, ← hc]; exact hbound
        have := sweep_bound this (by omega) (by omega)
        have e : q - 1 + 2 = q + 1 := by omega
        rwa [e] at this
      have hmod : (c + 1 <<< lvl) % 2 ^ W = c + 1 <<< lvl := Nat.mod_eq_of_lt (by omega)
      simp only [sweepOuterW, sweepOuter, hL, ite_true, hne, hmod]
      exact sweepW_carry H W B hB inner F (q / 2) (lvl + 1) F g _ _ hstep hb2 hF hF (by omega)

theorem finishW_eq (W B : Nat) (hB : B < W) (inner : Nat → α) (F fo : Nat) :
    ∀ (q lvl fs : Nat) (c : Nat),
    c = q * 2 ^ lvl → c ≤ 2 ^ B → q ≠ 0 →
    (absFrom inner lvl q).length ≤ fs → (absFrom inner lvl q).length ≤ F →
    (absFrom inner lvl q).length < fo →
    finishW H W inner F fo c fs lvl =
      .ok (some (sweepOuter H inner F fo c (skipLow c fs lvl) (inner (skipLow c fs lvl)))) := by
  have hBW : 2 ^ B < 2 ^ W := Nat.pow_lt_pow_right (by decide) hB
  intro q
  induction q using Nat.strongRecOn with
  | _ q ih =>
    intro lvl fs c hc hbound hq hfs hF hfo
    have hL : lvl < W := level_lt_of_pow_le (c := c) (by rw [hc]; exact pow_le_mul hq) (by omega)
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
        simp only [finishW, skipLowW, skipLow, bitClearW, hL, ite_true, hstop, Except.bind,
          Bool.false_eq_true, ite_false]
        rw [sweepW_top H W B hB inner F q lvl fo _ c hc hbound hodd (by omega) (by omega)]
    · have hclear : bitClear c lvl = true := by rw [hbit]; simp; omega
      simp only [hodd, ite_false] at hold
      rw [hold] at hfs hF hfo
      simp only [List.length_cons] at hfs hF hfo
      match fs, hfs with
      | 0, hfs => omega
      | f + 1, hfs =>
        have hc' : c = (q / 2) * 2 ^ (lvl + 1) := by
          rw [hc, mul_pow_succ_of_even q lvl (by omega)]
        have := ih (q / 2) (by omega) (lvl + 1) f c hc' hbound (by omega) (by omega) (by omega)
          (by omega)
        simp only [finishW, skipLowW, skipLow, bitClearW, hL, ite_true, hclear] at this ⊢
        exact this

section

variable [DecidableEq α] [Inhabited α]

theorem rootW_eq (W : Nat) (hW : 0 < W) (l : List α) (hl : l.length ≤ 2 ^ (W - 1)) :
    rootW H W l = .ok (root H l) := by
  rw [← rootLit_eq_root]
  have hBW : 2 ^ (W - 1) < 2 ^ W := Nat.pow_lt_pow_right (by decide) (by omega)
  match l, hl with
  | [], _ => rfl
  | a :: t, hl =>
    obtain ⟨_, _, h3⟩ := runLeaves_spec H (a :: t) (start : Lit α)
    have hcnt : (runLeaves H start (a :: t)).count = (a :: t).length := by
      rw [h3]; simp [start]
    have hlen := length_absFrom_le (runLeaves H start (a :: t)).inner
      (runLeaves H start (a :: t)).count 0
    have hrun := runLeavesW_eq H W (a :: t) (start : Lit α) (by simp only [start]; omega)
    have hf := finishW_eq H W (W - 1) (by omega) (runLeaves H start (a :: t)).inner
      ((runLeaves H start (a :: t)).count + 1) ((runLeaves H start (a :: t)).count + 1)
      (runLeaves H start (a :: t)).count 0 ((runLeaves H start (a :: t)).count + 1)
      (runLeaves H start (a :: t)).count (by simp) (by rw [hcnt]; exact hl)
      (by rw [hcnt]; simp) (by omega) (by omega) (by omega)
    simp only [rootW, hrun, rootLit]
    change finishW H W _ _ _ _ _ 0 = _
    rw [hf]

end

section

variable [DecidableEq α] [Inhabited α]

end

end

end Bsv.Merkle.Proof_rootW_eq

open Bsv.Merkle

theorem solution {α : Type} (H : α → α → α) [DecidableEq α] [Inhabited α]
    (W : Nat) (hW : 0 < W) (l : List α) (hl : l.length ≤ 2 ^ (W - 1)) :
    rootW H W l = .ok (root H l) :=
  Bsv.Merkle.Proof_rootW_eq.rootW_eq H W hW l hl
