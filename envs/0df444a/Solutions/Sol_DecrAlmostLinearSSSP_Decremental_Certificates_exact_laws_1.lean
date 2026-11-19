-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:14:36.317993+00:00
-- url     : https://prove2.me/submissions/10f35294-e69b-4a24-b49f-02889c9acec0

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable
section s0
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
lemma entries_card {height : ℕ} (t : Trie height) (low : ℕ) : (entries t low).card = count t := by
  induction t generalizing low with
  | empty => rfl
  | leaf items => simp [entries,count]
  | @node height left right ihl ihr => simp only [entries,count,Multiset.card_add,ihl,ihr]
lemma entries_range {height : ℕ} (t : Trie height) (low key value : ℕ)
    (hmem : (key,value) ∈ entries t low) : low ≤ key ∧ key < low+2^height := by
  induction t generalizing low key value with
  | empty => simp [entries] at hmem
  | leaf items =>
    simp only [entries,Multiset.mem_coe,List.mem_map,Prod.mk.injEq] at hmem
    obtain ⟨v,_,hkey,_⟩ := hmem
    subst key
    norm_num
  | @node height left right ihl ihr =>
    simp only [entries,Multiset.mem_add] at hmem
    have hp : 2^(height+1) = 2^height+2^height := by rw [pow_succ];omega
    rw [hp]
    rcases hmem with hmem | hmem
    · obtain ⟨hlo,hhi⟩ := ihl low key value hmem
      constructor
      · exact hlo
      · omega
    · obtain ⟨hlo,hhi⟩ := ihr (low+2^height) key value hmem
      constructor <;> omega
lemma count_insert (height key value : ℕ) (t : Trie height) : count (insert height key value t) = count t+1 := by
  induction height generalizing key with
  | zero => cases t <;> simp [insert,count]
  | succ height ih =>
    cases t with
    | empty =>
      simp only [insert]
      split_ifs <;> simp only [count,ih] <;> omega
    | node left right =>
      simp only [insert]
      split_ifs <;> simp only [count,ih] <;> omega
lemma entries_insert (height key value : ℕ) (t : Trie height) (low : ℕ)
    (hkey : key < 2^height) :
    entries (insert height key value t) low = (low+key,value) ::ₘ entries t low := by
  induction height generalizing key low with
  | zero =>
    have hk : key = 0 := by norm_num at hkey;omega
    subst key
    cases t <;> simp [insert,entries]
  | succ height ih =>
    have hp : 2^(height+1) = 2^height+2^height := by rw [pow_succ];omega
    have hrange : key-2^height < 2^height := by rw [hp] at hkey;omega
    cases t with
    | empty =>
      simp only [insert]
      split_ifs with hleft
      · simp only [entries,ih key Trie.empty low hleft,Multiset.add_zero]
      · have hsum : low+2^height+(key-2^height) = low+key := by omega
        simp only [entries,Multiset.zero_add,ih (key-2^height) Trie.empty (low+2^height) hrange,hsum]
    | node left right =>
      simp only [insert]
      split_ifs with hleft
      · simp only [entries,ih key left low hleft,Multiset.cons_add]
      · have hsum : low+2^height+(key-2^height) = low+key := by omega
        simp only [entries,ih (key-2^height) right (low+2^height) hrange,hsum,Multiset.add_cons]
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end s0
section s1
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
lemma pop_none_iff {height : ℕ} (t : Trie height) : pop t = none ↔ count t = 0 := by
  induction t with
  | empty => simp [pop,count]
  | leaf items => cases items <;> simp [pop,count]
  | @node h left right ihl ihr =>
    by_cases hcl : count left = 0
    · cases hr : pop right with
      | none => simp [pop,hcl,hr,count,ihr.mp hr]
      | some result =>
        rcases result with ⟨key,value,next⟩
        have hcr : count right ≠ 0 := by intro hz;have hh := ihr.mpr hz;rw [hr] at hh;contradiction
        simp [pop,hcl,hr,count,hcr]
    · cases hl : pop left with
      | none => exact False.elim (hcl (ihl.mp hl))
      | some result =>
        rcases result with ⟨key,value,next⟩
        simp [pop,hcl,hl,count]
lemma entries_empty_of_pop_none {height : ℕ} (t : Trie height) (low : ℕ) (h : pop t = none) :
    entries t low = 0 := by
  apply Multiset.card_eq_zero.mp
  rw [entries_card,(pop_none_iff t).mp h]
lemma pop_spec {height : ℕ} (t : Trie height) (low key value : ℕ) (next : Trie height)
    (hp : pop t = some (key,value,next)) :
    entries t low = (low+key,value) ::ₘ entries next low ∧
      (∀ item ∈ entries t low, low+key ≤ item.1) := by
  induction t generalizing low key value with
  | empty => simp [pop] at hp
  | leaf items =>
    cases items with
    | nil => simp [pop] at hp
    | cons v rest =>
      simp only [pop,Option.some.injEq,Prod.mk.injEq] at hp
      rcases hp with ⟨rfl,rfl,rfl⟩
      refine ⟨by simp [entries],?_⟩
      intro item hitem
      have hr := entries_range (Trie.leaf (v::rest)) low item.1 item.2 hitem
      simpa only [Nat.add_zero] using hr.1
  | @node h left right ihl ihr =>
    by_cases hcl : count left = 0
    · cases hr : pop right with
      | none => simp [pop,hcl,hr] at hp
      | some result =>
        rcases result with ⟨rkey,rvalue,rnext⟩
        simp only [pop,if_pos hcl,hr,Option.some.injEq,Prod.mk.injEq] at hp
        rcases hp with ⟨rfl,rfl,rfl⟩
        obtain ⟨hbag,hmin⟩ := ihr (low+2^h) rkey rvalue rnext hr
        have hempty : entries left low = 0 := Multiset.card_eq_zero.mp (by rwa [entries_card])
        refine ⟨?_,?_⟩
        · simpa only [entries,hempty,Multiset.zero_add,Nat.add_assoc] using hbag
        · intro item hitem
          simp only [entries,hempty,Multiset.zero_add] at hitem
          simpa only [Nat.add_assoc] using hmin item hitem
    · cases hl : pop left with
      | none => simp [pop,hcl,hl] at hp
      | some result =>
        rcases result with ⟨lkey,lvalue,lnext⟩
        simp only [pop,if_neg hcl,hl,Option.some.injEq,Prod.mk.injEq] at hp
        rcases hp with ⟨rfl,rfl,rfl⟩
        obtain ⟨hbag,hmin⟩ := ihl low lkey lvalue lnext hl
        have hchosen : (low+lkey,lvalue) ∈ entries left low := by rw [hbag];exact Multiset.mem_cons_self _ _
        have hkeybound := (entries_range left low (low+lkey) lvalue hchosen).2
        refine ⟨?_,?_⟩
        · simp only [entries,hbag,Multiset.cons_add]
        · intro item hitem
          simp only [entries,Multiset.mem_add] at hitem
          rcases hitem with hitem | hitem
          · exact hmin item hitem
          · have hlo := (entries_range right (low+2^h) item.1 item.2 hitem).1
            omega
lemma count_pop {height : ℕ} (t : Trie height) (key value : ℕ) (next : Trie height)
    (hp : pop t = some (key,value,next)) : count next+1 = count t := by
  have hh := congrArg Multiset.card (pop_spec t 0 key value next hp).1
  simp only [Multiset.card_cons,entries_card] at hh
  omega
lemma pop_key_bound {height : ℕ} (t : Trie height) (key value : ℕ) (next : Trie height)
    (hp : pop t = some (key,value,next)) : key < 2^height := by
  have hbag := (pop_spec t 0 key value next hp).1
  have hmem : (key,value) ∈ entries t 0 := by rw [hbag];simp
  simpa only [Nat.zero_add] using (entries_range t 0 key value hmem).2
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end s1
section s2
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.RadixQueue
lemma popVisits_bound {height : ℕ} (t : Trie height) : popVisits t ≤ height+1 := by
  induction t with
  | empty => simp [popVisits]
  | leaf items => rfl
  | @node height left right ihl ihr =>
    simp only [popVisits]
    split_ifs <;> omega
lemma pop_nonempty {height : ℕ} (t : Trie height) (ht : 0 < count t) :
    ∃ key value next, pop t = some (key,value,next) := by
  cases hp : pop t with
  | none => have hh := (pop_none_iff t).mp hp;omega
  | some result =>
    rcases result with ⟨key,value,next⟩
    exact ⟨key,value,next,rfl⟩
lemma selected_child_positive {height : ℕ} (left right : Trie height)
    (ht : 0 < count (Trie.node left right)) :
    (count left = 0 → 0 < count right) ∧ (count left ≠ 0 → 0 < count left) := by
  simp only [count] at ht
  constructor <;> omega
end DecrAlmostLinearSSSP.Decremental.RadixQueue
end s2
section s3
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma guestAddress_injective (base : ℕ) : Function.Injective (guestAddress base) := by
  intro a b hab
  dsimp [guestAddress] at hab
  omega
lemma guestReg_injective : Function.Injective guestReg := by
  intro a b hab
  dsimp [guestReg] at hab
  omega
lemma update_guest_register {α : Type} (f : ℕ → α) (a : ℕ) (v : α) :
    (fun j => Function.update f (guestReg a) v (guestReg j)) =
      Function.update (fun j => f (guestReg j)) a v := by
  classical
  funext j
  by_cases hj : j = a
  · subst j; simp
  · have hh : guestReg j ≠ guestReg a := guestReg_injective.ne hj
    simp only [Function.update_of_ne hj, Function.update_of_ne hh]
lemma update_guest_memory {α : Type} (f : ℕ → α) (base a : ℕ) (v : α) :
    (fun j => Function.update f (guestAddress base a) v (guestAddress base j)) =
      Function.update (fun j => f (guestAddress base j)) a v := by
  classical
  funext j
  by_cases hj : j = a
  · subst j; simp
  · have hh : guestAddress base j ≠ guestAddress base a := (guestAddress_injective base).ne hj
    simp only [Function.update_of_ne hj, Function.update_of_ne hh]
lemma guestReg_ne_meta (j k : ℕ) (hk : k < 7) : guestReg j ≠ k := by
  dsimp [guestReg]
  omega
lemma guest_reg_write_preserves_even {α : Type} (f : ℕ → α) (a b : ℕ) (v : α) :
    Function.update f (guestReg a) v (2 * b) = f (2 * b) := by
  classical
  apply Function.update_of_ne
  dsimp [guestReg]
  omega
lemma guest_write_preserves_even {α : Type} (f : ℕ → α) (base a b : ℕ) (v : α) :
    Function.update f (guestAddress base a) v (base + 2 * b) = f (base + 2 * b) := by
  classical
  apply Function.update_of_ne
  dsimp [guestAddress]
  omega
lemma guest_write_preserves_prefix {α : Type} (f : ℕ → α) (base a b : ℕ) (v : α)
    (hb : b < base) : Function.update f (guestAddress base a) v b = f b := by
  classical
  apply Function.update_of_ne
  dsimp [guestAddress]
  omega
lemma embeddedInstruction_length (offset returnPC pc : ℕ) (ins : Instruction) :
    (embeddedInstruction offset returnPC pc ins).length = 8 := by
  cases ins <;> rfl
end DecrAlmostLinearSSSP.Decremental
end s3
section s4
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma machine_ext {c d : Machine} (hpc : c.pc = d.pc) (hreal : c.realReg = d.realReg)
    (hnat : c.natReg = d.natReg) (hrmem : c.realMem = d.realMem) (hnmem : c.natMem = d.natMem)
    (hhalt : c.halted = d.halted) (hfault : c.fault = d.fault) (hwork : c.work = d.work) : c = d := by
  cases c
  cases d
  simp_all
lemma decodeGuest_metadata (c : Machine) (pc work hostPC : ℕ) :
    decodeGuest {c with pc := hostPC, natReg := Function.update (Function.update c.natReg 2 pc) 3 work} =
      {decodeGuest c with pc := pc, work := work} := by
  classical
  have hg2 (j : ℕ) : guestReg j ≠ 2 := guestReg_ne_meta j 2 (by norm_num)
  have hg3 (j : ℕ) : guestReg j ≠ 3 := guestReg_ne_meta j 3 (by norm_num)
  apply machine_ext
  · simp [decodeGuest]
  · rfl
  · funext j
    simp only [decodeGuest, Function.update_of_ne (hg2 j), Function.update_of_ne (hg3 j)]
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [decodeGuest]
lemma embedded_header (host : Program) (c : Machine) (pc : ℕ)
    (hhalt : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1)) :
    decodeGuest (execute host c 2) = {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} := by
  classical
  let c1 : Machine := {c with pc := c.pc + 1, natReg := Function.update c.natReg 2 (pc + 1), work := c.work + 1}
  let c2 : Machine := {c1 with pc := c.pc + 2, natReg := Function.update c1.natReg 3 (c.natReg 3 + 1), work := c.work + 2}
  have hs1 : step host c = c1 := by simp [step, c1, hhalt, h0]
  have hs2 : step host c1 = c2 := by simp [step, c1, c2, hhalt, h1, hone]
  have hex : execute host c 2 = c2 := by
    change step host (step host c) = c2
    rw [hs1, hs2]
  rw [hex]
  exact decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
end DecrAlmostLinearSSSP.Decremental
end s4
section s5
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma step_eq_effect (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) :
    step p c = instructionEffect ins {c with pc := c.pc + 1, work := c.work + 1} := by
  cases ins <;> simp only [step, hh, Bool.false_eq_true, if_false, hc, instructionEffect]
lemma decodeGuest_host_clock (c : Machine) (pc work : ℕ) :
    decodeGuest {c with pc := pc, work := work} = decodeGuest c := rfl
lemma decodeGuest_step_effect (p : Program) (c : Machine) (ins : Instruction)
    (hh : c.halted = false) (hc : p.code[c.pc]? = some ins) :
    decodeGuest (step p c) = decodeGuest (instructionEffect ins c) := by
  rw [step_eq_effect p c ins hh hc]
  cases ins <;> simp only [instructionEffect]
  all_goals try split_ifs
  all_goals rfl
lemma decodeGuest_real_register (c : Machine) (a : ℕ) (value : ℝ) :
    decodeGuest {c with realReg := Function.update c.realReg (guestReg a) value} =
      {decodeGuest c with realReg := Function.update (decodeGuest c).realReg a value} := by
  classical
  apply machine_ext
  · rfl
  · exact update_guest_register _ _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
lemma decodeGuest_nat_register (c : Machine) (a value : ℕ) :
    decodeGuest {c with natReg := Function.update c.natReg (guestReg a) value} =
      {decodeGuest c with natReg := Function.update (decodeGuest c).natReg a value} := by
  classical
  have hm (k : ℕ) (hk : k < 7) :
      Function.update c.natReg (guestReg a) value k = c.natReg k :=
    Function.update_of_ne (guestReg_ne_meta a k hk).symm _ _
  apply machine_ext
  · exact hm 2 (by norm_num)
  · rfl
  · exact update_guest_register _ _ _
  · simp only [decodeGuest, hm 0 (by norm_num)]
  · simp only [decodeGuest, hm 0 (by norm_num)]
  · simp only [decodeGuest, hm 4 (by norm_num)]
  · simp only [decodeGuest, hm 5 (by norm_num)]
  · exact hm 3 (by norm_num)
lemma decodeGuest_real_memory (c : Machine) (a : ℕ) (value : ℝ) :
    decodeGuest {c with realMem := Function.update c.realMem (guestAddress (c.natReg 0) a) value} =
      {decodeGuest c with realMem := Function.update (decodeGuest c).realMem a value} := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · rfl
  · exact update_guest_memory _ _ _ _
  · rfl
  · rfl
  · rfl
  · rfl
lemma decodeGuest_nat_memory (c : Machine) (a value : ℕ) :
    decodeGuest {c with natMem := Function.update c.natMem (guestAddress (c.natReg 0) a) value} =
      {decodeGuest c with natMem := Function.update (decodeGuest c).natMem a value} := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · exact update_guest_memory _ _ _ _
  · rfl
  · rfl
  · rfl
lemma decodeGuest_scratch (c : Machine) (a : ℕ) :
    decodeGuest {c with natReg := Function.update c.natReg 6 a} = decodeGuest c := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · funext j
    exact Function.update_of_ne (guestReg_ne_meta j 6 (by norm_num)) _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
end DecrAlmostLinearSSSP.Decremental
end s5
section s6
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
lemma decodeGuest_scalar (ins translated : Instruction) (h : scalarTranslation ins = some translated)
    (c : Machine) : decodeGuest (instructionEffect translated c) = instructionEffect ins (decodeGuest c) := by
  cases ins <;> simp only [scalarTranslation] at h
  all_goals cases h
  all_goals simp only [instructionEffect, decodeGuest_real_register, decodeGuest_nat_register]
  all_goals rfl
lemma decodeGuest_load (c : Machine) (d a : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.load (guestReg d) 6) c) =
      instructionEffect (.load d a) (decodeGuest c) := by
  simp only [instructionEffect, decodeGuest_real_register, ha]
  rfl
lemma decodeGuest_loadN (c : Machine) (d a : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.loadN (guestReg d) 6) c) =
      instructionEffect (.loadN d a) (decodeGuest c) := by
  simp only [instructionEffect, decodeGuest_nat_register, ha]
  rfl
lemma decodeGuest_store (c : Machine) (a d : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.store 6 (guestReg d)) c) =
      instructionEffect (.store a d) (decodeGuest c) := by
  simp only [instructionEffect, ha, decodeGuest_real_memory]
  rfl
lemma decodeGuest_storeN (c : Machine) (a d : ℕ)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect (.storeN 6 (guestReg d)) c) =
      instructionEffect (.storeN a d) (decodeGuest c) := by
  simp only [instructionEffect, ha, decodeGuest_nat_memory]
  rfl
end DecrAlmostLinearSSSP.Decremental
end s6
section s7
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma execute_add (p : Program) (c : Machine) (a b : ℕ) :
    execute p c (a + b) = execute p (execute p c a) b := by
  unfold execute
  rw [Nat.add_comm a b, Function.iterate_add_apply]
lemma host_jump (host : Program) (c : Machine) (target : ℕ)
    (hh : c.halted = false) (hc : host.code[c.pc]? = some (.jump target)) :
    execute host c 1 = {c with pc := target, work := c.work + 1} := by
  change step host c = _
  simp only [step, hh, Bool.false_eq_true, if_false, hc]
lemma host_scalar (host : Program) (c : Machine) (ins translated : Instruction)
    (htranslation : scalarTranslation ins = some translated)
    (hh : c.halted = false) (hc : host.code[c.pc]? = some translated) :
    decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) ∧
      (execute host c 1).pc = c.pc + 1 ∧ (execute host c 1).halted = false ∧
      (execute host c 1).work = c.work + 1 := by
  have hdecode : decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) := by
    change decodeGuest (step host c) = _
    rw [decodeGuest_step_effect host c translated hh hc, decodeGuest_scalar ins translated htranslation c]
  refine ⟨hdecode, ?_, ?_, ?_⟩
  all_goals cases ins <;> simp only [scalarTranslation] at htranslation
  all_goals cases htranslation
  all_goals simp only [execute, Function.iterate_one, step, hh, Bool.false_eq_true, if_false, hc]
end DecrAlmostLinearSSSP.Decremental
end s7
section s8
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma embedded_address (host : Program) (c : Machine) (a : ℕ)
    (hhalt : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.nadd 6 (guestReg a) (guestReg a)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 6 6 0))
    (h2 : host.code[c.pc + 2]? = some (.nadd 6 6 1)) :
    ∃ d, execute host c 3 = d ∧ decodeGuest d = decodeGuest c ∧
      d.natReg 6 = guestAddress (d.natReg 0) (d.natReg (guestReg a)) ∧
      d.pc = c.pc + 3 ∧ d.halted = false ∧ d.work = c.work + 3 ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let c1 : Machine := { c with pc := c.pc + 1, natReg := Function.update c.natReg 6 (c.natReg (guestReg a) + c.natReg (guestReg a)), work := c.work + 1 }
  let c2 : Machine := { c1 with pc := c.pc + 2, natReg := Function.update c1.natReg 6 (c1.natReg 6 + c1.natReg 0), work := c.work + 2 }
  let c3 : Machine := { c2 with pc := c.pc + 3, natReg := Function.update c2.natReg 6 (c2.natReg 6 + 1), work := c.work + 3 }
  have hs1 : step host c = c1 := by simp [step, c1, hhalt, h0]
  have hs2 : step host c1 = c2 := by simp [step, c1, c2, hhalt, h1]
  have hs3 : step host c2 = c3 := by simp [step, c1, c2, c3, hhalt, h2, hone]
  have hex : execute host c 3 = c3 := by
    change step host (step host (step host c)) = c3
    rw [hs1, hs2, hs3]
  have hd1 : decodeGuest c1 = decodeGuest c := decodeGuest_scratch c _
  have hd2 : decodeGuest c2 = decodeGuest c1 := decodeGuest_scratch c1 _
  have hd3 : decodeGuest c3 = decodeGuest c2 := decodeGuest_scratch c2 _
  refine ⟨c3, hex, hd3.trans (hd2.trans hd1), ?_, rfl, hhalt, rfl, rfl, rfl⟩
  have ha6 : guestReg a ≠ 6 := guestReg_ne_meta a 6 (by norm_num)
  simp [c3, c2, c1, guestAddress, ha6, Nat.two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
end DecrAlmostLinearSSSP.Decremental
end s8
section s9
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma embeddedCodeAux_length (offset returnPC start : ℕ) (code : List Instruction) :
    (embeddedCodeAux offset returnPC start code).length = 8 * code.length := by
  induction code generalizing start with
  | nil => rfl
  | cons ins rest ih =>
    simp only [embeddedCodeAux, List.length_append, embeddedInstruction_length, ih, List.length_cons]
    omega
lemma embeddedCode_length (offset returnPC : ℕ) (code : List Instruction) :
    (embeddedCode offset returnPC code).length = 8 * code.length := embeddedCodeAux_length _ _ _ _
lemma embeddedCodeAux_get (offset returnPC start : ℕ) (code : List Instruction)
    (pc slot : ℕ) (ins : Instruction) (hslot : slot < 8) (hins : code[pc]? = some ins) :
    (embeddedCodeAux offset returnPC start code)[8 * pc + slot]? =
      (embeddedInstruction offset returnPC (start + pc) ins)[slot]? := by
  induction code generalizing start pc with
  | nil => simp at hins
  | cons first rest ih =>
    cases pc with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hins
      subst ins
      simp only [embeddedCodeAux, Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      rw [List.getElem?_append_left (by simpa only [embeddedInstruction_length] using hslot)]
    | succ pc =>
      simp only [List.getElem?_cons_succ] at hins
      rw [embeddedCodeAux, List.getElem?_append_right (by rw [embeddedInstruction_length]; omega)]
      have hidx : 8 * (pc + 1) + slot - 8 = 8 * pc + slot := by omega
      rw [embeddedInstruction_length, hidx]
      have hh := ih (start + 1) pc hins
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
lemma embeddedCode_get (offset returnPC : ℕ) (code : List Instruction)
    (pc slot : ℕ) (ins : Instruction) (hslot : slot < 8) (hins : code[pc]? = some ins) :
    (embeddedCode offset returnPC code)[8 * pc + slot]? = (embeddedInstruction offset returnPC pc ins)[slot]? := by
  simpa only [embeddedCode, Nat.zero_add] using embeddedCodeAux_get offset returnPC 0 code pc slot ins hslot hins
end DecrAlmostLinearSSSP.Decremental
end s9
section s10
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma embedded_header_exact (host : Program) (c : Machine) (pc : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1)) :
    execute host c 2 = headerState c pc := by
  classical
  change step host (step host c) = _
  simp [step, hh, h0, h1, hone, headerState]
lemma scalar_metadata (ins translated : Instruction) (ht : scalarTranslation ins = some translated)
    (c : Machine) :
    (instructionEffect translated c).natReg 0 = c.natReg 0 ∧
      (instructionEffect translated c).natReg 1 = c.natReg 1 ∧
      (instructionEffect translated c).fault = c.fault := by
  classical
  cases ins <;> simp only [scalarTranslation] at ht
  all_goals cases ht
  all_goals simp only [instructionEffect]
  all_goals try exact ⟨rfl, rfl, rfl⟩
  all_goals simp [Function.update_of_ne (guestReg_ne_meta _ 0 (by norm_num)).symm,
    Function.update_of_ne (guestReg_ne_meta _ 1 (by norm_num)).symm]
lemma embedded_scalar_macro (host : Program) (c : Machine) (pc offset : ℕ)
    (ins translated : Instruction) (ht : scalarTranslation ins = some translated)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some translated)
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1)))) :
    ∃ d, execute host c 4 = d ∧
      decodeGuest d = instructionEffect ins {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * (pc + 1) ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hbdecode : decodeGuest b = {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} :=
    decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
  have hbhalt : b.halted = false := hh
  have hbc : host.code[b.pc]? = some translated := h2
  obtain ⟨hdec, hpc, hh3, hw3⟩ := host_scalar host b ins translated ht hbhalt hbc
  let t := execute host b 1
  have hjc : host.code[t.pc]? = some (.jump (offset + 8 * (pc + 1))) := by
    change host.code[(execute host b 1).pc]? = _
    rw [hpc]
    simpa [b, headerState, Nat.add_assoc] using h3
  have hj := host_jump host t (offset + 8 * (pc + 1)) hh3 hjc
  let d : Machine := {t with pc := offset + 8 * (pc + 1), work := t.work + 1}
  have hd : execute host c 4 = d := by
    rw [show 4 = 2 + (1 + 1) by omega, execute_add, hb, execute_add]
    exact hj
  refine ⟨d, hd, ?_, rfl, ?_, hh3, ?_, ?_⟩
  · change decodeGuest t = _
    exact hdec.trans (congrArg (instructionEffect ins) hbdecode)
  · change (execute host b 1).work + 1 = c.work + 4
    rw [hw3]
    simp [b, headerState]
  · change (execute host b 1).natReg 0 = c.natReg 0
    change (step host b).natReg 0 = _
    rw [step_eq_effect host b translated hbhalt hbc]
    exact (scalar_metadata ins translated ht _).1
  · change (execute host b 1).natReg 1 = c.natReg 1
    change (step host b).natReg 1 = _
    rw [step_eq_effect host b translated hbhalt hbc]
    exact (scalar_metadata ins translated ht _).2.1
end DecrAlmostLinearSSSP.Decremental
end s10
section s11
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma decodeGuest_pc (c : Machine) (pc : ℕ) :
    decodeGuest {c with natReg := Function.update c.natReg 2 pc} = {decodeGuest c with pc := pc} := by
  classical
  apply machine_ext
  · simp [decodeGuest]
  · rfl
  · funext j
    exact Function.update_of_ne (guestReg_ne_meta j 2 (by norm_num)) _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
lemma decodeGuest_halt (c : Machine) :
    decodeGuest {c with natReg := Function.update c.natReg 4 1} = {decodeGuest c with halted := true} := by
  classical
  apply machine_ext
  · rfl
  · rfl
  · funext j
    exact Function.update_of_ne (guestReg_ne_meta j 4 (by norm_num)) _ _
  · rfl
  · rfl
  · simp [decodeGuest]
  · rfl
  · rfl
lemma host_natural_jump (host : Program) (c : Machine) (reg value target : ℕ)
    (hh : c.halted = false)
    (h0 : host.code[c.pc]? = some (.natural reg value))
    (h1 : host.code[c.pc + 1]? = some (.jump target)) :
    execute host c 2 = {c with
      pc := target
      work := c.work + 2
      natReg := Function.update c.natReg reg value} := by
  classical
  change step host (step host c) = _
  simp [step, hh, h0, h1]
lemma embedded_jump_macro (host : Program) (c : Machine) (pc offset target : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural 2 target))
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * target))) :
    ∃ d, execute host c 4 = d ∧
      decodeGuest d = instructionEffect (.jump target) {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * target ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  let d : Machine := {b with pc := offset + 8 * target, work := b.work + 2, natReg := Function.update b.natReg 2 target}
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hd : execute host b 2 = d := host_natural_jump host b 2 target (offset + 8 * target) hh h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  refine ⟨d, ?_, ?_, rfl, ?_, hh, rfl, rfl⟩
  · rw [show 4 = 2 + 2 by omega, execute_add, hb, hd]
  · change decodeGuest {b with natReg := Function.update b.natReg 2 target} = _
    rw [decodeGuest_pc]
    have hbdec := decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
    change decodeGuest b = _ at hbdec
    rw [hbdec]
    rfl
  · dsimp [d, b, headerState]
lemma embedded_halt_macro (host : Program) (c : Machine) (pc returnPC : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.natural 4 1))
    (h3 : host.code[c.pc + 3]? = some (.jump returnPC)) :
    ∃ d, execute host c 4 = d ∧
      decodeGuest d = instructionEffect .halt {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = returnPC ∧ d.work = c.work + 4 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  let d : Machine := {b with pc := returnPC, work := b.work + 2, natReg := Function.update b.natReg 4 1}
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hd : execute host b 2 = d := host_natural_jump host b 4 1 returnPC hh h2 (by simpa [b, headerState, Nat.add_assoc] using h3)
  refine ⟨d, ?_, ?_, rfl, ?_, hh, rfl, rfl⟩
  · rw [show 4 = 2 + 2 by omega, execute_add, hb, hd]
  · change decodeGuest {b with natReg := Function.update b.natReg 4 1} = _
    rw [decodeGuest_halt]
    have hbdec := decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
    change decodeGuest b = _ at hbdec
    rw [hbdec]
    rfl
  · dsimp [d, b, headerState]
end DecrAlmostLinearSSSP.Decremental
end s11
section s12
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
attribute [local instance] Classical.propDecidable
lemma host_branch (host : Program) (c : Machine) (natural : Bool) (a b target : ℕ)
    (hh : c.halted = false)
    (hc : host.code[c.pc]? = some (branchInstruction natural (guestReg a) (guestReg b) target)) :
    execute host c 1 = {c with
      pc := if branchTest natural (decodeGuest c) a b then target else c.pc + 1
      work := c.work + 1} := by
  cases natural <;> simp [execute, step, branchInstruction, branchTest, hh, hc, decodeGuest]
  all_goals split_ifs <;> rfl
lemma branchTest_header (natural : Bool) (c : Machine) (pc a b : ℕ) :
    branchTest natural (decodeGuest (headerState c pc)) a b = branchTest natural (decodeGuest c) a b := by
  cases natural
  · rfl
  · simp [branchTest, decodeGuest, headerState,
      Function.update_of_ne (guestReg_ne_meta a 2 (by norm_num)),
      Function.update_of_ne (guestReg_ne_meta a 3 (by norm_num)),
      Function.update_of_ne (guestReg_ne_meta b 2 (by norm_num)),
      Function.update_of_ne (guestReg_ne_meta b 3 (by norm_num))]
lemma branch_effect (natural : Bool) (c : Machine) (a b target : ℕ) :
    instructionEffect (branchInstruction natural a b target) c =
      if branchTest natural c a b then {c with pc := target} else c := by
  cases natural <;> simp [instructionEffect, branchInstruction, branchTest]
lemma embedded_branch_macro (host : Program) (c : Machine) (pc offset target : ℕ)
    (natural : Bool) (a b : ℕ)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (branchInstruction natural (guestReg a) (guestReg b) (c.pc + 5)))
    (h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))))
    (h5 : host.code[c.pc + 5]? = some (.natural 2 target))
    (h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * target))) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 5 ∧ execute host c steps = d ∧
      decodeGuest d = instructionEffect (branchInstruction natural a b target) {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * (decodeGuest d).pc ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let s := headerState c pc
  let g : Machine := {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1}
  have hs : execute host c 2 = s := embedded_header_exact host c pc hh hone h0 h1
  have hsdec : decodeGuest s = g := decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
  by_cases htake : branchTest natural g a b
  · let t : Machine := {s with pc := c.pc + 5, work := s.work + 1}
    have ht : execute host s 1 = t := by
      rw [host_branch host s natural a b (c.pc + 5) hh h2, hsdec, if_pos htake]
    let d : Machine := {t with pc := offset + 8 * target, work := t.work + 2, natReg := Function.update t.natReg 2 target}
    have hd : execute host t 2 = d := host_natural_jump host t 2 target (offset + 8 * target) hh h5 (by simpa [t, Nat.add_assoc] using h6)
    refine ⟨5, d, le_rfl, ?_, ?_, ?_, ?_, hh, rfl, rfl⟩
    · rw [show 5 = 2 + (1 + 2) by omega, execute_add, hs, execute_add, ht, hd]
    · change decodeGuest {t with natReg := Function.update t.natReg 2 target} = _
      rw [decodeGuest_pc, branch_effect, if_pos htake]
      exact congrArg (fun m : Machine => {m with pc := target}) hsdec
    · change offset + 8 * target = offset + 8 * (decodeGuest {t with natReg := Function.update t.natReg 2 target}).pc
      rw [decodeGuest_pc]
    · dsimp [d, t, s, headerState]
  · let t : Machine := {s with pc := c.pc + 3, work := s.work + 1}
    have ht : execute host s 1 = t := by
      rw [host_branch host s natural a b (c.pc + 5) hh h2, hsdec, if_neg htake]
      simp [t, s, headerState, Nat.add_assoc]
    let d : Machine := {t with pc := offset + 8 * (pc + 1), work := t.work + 1}
    have hd : execute host t 1 = d := host_jump host t (offset + 8 * (pc + 1)) hh h3
    refine ⟨4, d, by omega, ?_, ?_, ?_, ?_, hh, rfl, rfl⟩
    · rw [show 4 = 2 + (1 + 1) by omega, execute_add, hs, execute_add, ht, hd]
    · change decodeGuest s = _
      rw [branch_effect, if_neg htake]
      exact hsdec
    · change offset + 8 * (pc + 1) = offset + 8 * (decodeGuest s).pc
      rw [hsdec]
    · dsimp [d, t, s, headerState]
end DecrAlmostLinearSSSP.Decremental
end s12
section s13
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma decodeGuest_memory (ins translated : Instruction) (a : ℕ)
    (ht : memoryTranslation ins = some (translated, a)) (c : Machine)
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a))) :
    decodeGuest (instructionEffect translated c) = instructionEffect ins (decodeGuest c) := by
  cases ins <;> simp only [memoryTranslation] at ht
  all_goals cases ht
  · exact decodeGuest_load c _ _ ha
  · exact decodeGuest_store c _ _ ha
  · exact decodeGuest_loadN c _ _ ha
  · exact decodeGuest_storeN c _ _ ha
lemma host_memory (host : Program) (c : Machine) (ins translated : Instruction) (a : ℕ)
    (ht : memoryTranslation ins = some (translated, a))
    (ha : c.natReg 6 = guestAddress (c.natReg 0) (c.natReg (guestReg a)))
    (hh : c.halted = false) (hc : host.code[c.pc]? = some translated) :
    decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) ∧
      (execute host c 1).pc = c.pc + 1 ∧ (execute host c 1).halted = false ∧
      (execute host c 1).work = c.work + 1 ∧
      (execute host c 1).natReg 0 = c.natReg 0 ∧ (execute host c 1).natReg 1 = c.natReg 1 := by
  have hd : decodeGuest (execute host c 1) = instructionEffect ins (decodeGuest c) := by
    change decodeGuest (step host c) = _
    rw [decodeGuest_step_effect host c translated hh hc, decodeGuest_memory ins translated a ht c ha]
  refine ⟨hd, ?_, ?_, ?_, ?_, ?_⟩
  all_goals cases ins <;> simp only [memoryTranslation] at ht
  all_goals cases ht
  all_goals simp [execute, step, hh, hc,
    Function.update_of_ne (guestReg_ne_meta _ 0 (by norm_num)).symm,
    Function.update_of_ne (guestReg_ne_meta _ 1 (by norm_num)).symm]
lemma embedded_memory_macro (host : Program) (c : Machine) (pc offset : ℕ)
    (ins translated : Instruction) (a : ℕ) (ht : memoryTranslation ins = some (translated, a))
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)))
    (h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1))
    (h2 : host.code[c.pc + 2]? = some (.nadd 6 (guestReg a) (guestReg a)))
    (h3 : host.code[c.pc + 3]? = some (.nadd 6 6 0))
    (h4 : host.code[c.pc + 4]? = some (.nadd 6 6 1))
    (h5 : host.code[c.pc + 5]? = some translated)
    (h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * (pc + 1)))) :
    ∃ d, execute host c 7 = d ∧
      decodeGuest d = instructionEffect ins {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = offset + 8 * (pc + 1) ∧ d.work = c.work + 7 ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  let b := headerState c pc
  have hb : execute host c 2 = b := embedded_header_exact host c pc hh hone h0 h1
  have hbdec : decodeGuest b = {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} :=
    decodeGuest_metadata c (pc + 1) (c.natReg 3 + 1) (c.pc + 2)
  obtain ⟨t, htx, htdec, hta, htpc, hth, htw, ht0, ht1⟩ :=
    embedded_address host b a hh hone h2
      (by simpa [b, headerState, Nat.add_assoc] using h3)
      (by simpa [b, headerState, Nat.add_assoc] using h4)
  have htc : host.code[t.pc]? = some translated := by
    rw [htpc]
    simpa [b, headerState, Nat.add_assoc] using h5
  obtain ⟨hdec, hpc, hhalt, hwork, hmeta0, hmeta1⟩ := host_memory host t ins translated a ht hta hth htc
  let u := execute host t 1
  have hjc : host.code[u.pc]? = some (.jump (offset + 8 * (pc + 1))) := by
    change host.code[(execute host t 1).pc]? = _
    rw [hpc, htpc]
    simpa [b, headerState, Nat.add_assoc] using h6
  have hj := host_jump host u (offset + 8 * (pc + 1)) hhalt hjc
  let d : Machine := {u with pc := offset + 8 * (pc + 1), work := u.work + 1}
  refine ⟨d, ?_, ?_, rfl, ?_, hhalt, ?_, ?_⟩
  · rw [show 7 = 2 + (3 + (1 + 1)) by omega, execute_add, hb, execute_add, htx, execute_add]
    exact hj
  · change decodeGuest u = _
    exact hdec.trans (congrArg (instructionEffect ins) (htdec.trans hbdec))
  · change (execute host t 1).work + 1 = c.work + 7
    rw [hwork, htw]
    simp [b, headerState]
  · change (execute host t 1).natReg 0 = c.natReg 0
    rw [hmeta0, ht0]
    rfl
  · change (execute host t 1).natReg 1 = c.natReg 1
    rw [hmeta1, ht1]
    rfl
end DecrAlmostLinearSSSP.Decremental
end s13
section s14
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma scalar_effect_control (ins tr : Instruction) (ht : scalarTranslation ins = some tr)
    (c : Machine) : (instructionEffect ins c).pc = c.pc ∧ (instructionEffect ins c).halted = c.halted := by
  cases ins <;> simp only [scalarTranslation] at ht
  all_goals cases ht
  all_goals exact ⟨rfl, rfl⟩
lemma memory_effect_control (ins tr : Instruction) (a : ℕ) (ht : memoryTranslation ins = some (tr, a))
    (c : Machine) : (instructionEffect ins c).pc = c.pc ∧ (instructionEffect ins c).halted = c.halted := by
  cases ins <;> simp only [memoryTranslation] at ht
  all_goals cases ht
  all_goals exact ⟨rfl, rfl⟩
lemma embedded_instruction_header (offset returnPC pc : ℕ) (ins : Instruction) :
    (embeddedInstruction offset returnPC pc ins)[0]? = some (.natural 2 (pc + 1)) ∧
    (embeddedInstruction offset returnPC pc ins)[1]? = some (.nadd 3 3 1) := by
  cases ins <;> exact ⟨rfl, rfl⟩
lemma embedded_macro (host : Program) (c : Machine) (pc offset returnPC : ℕ) (ins : Instruction)
    (hh : c.halted = false) (hone : c.natReg 1 = 1) (hgh : (decodeGuest c).halted = false)
    (hpos : c.pc = offset + 8 * pc)
    (hcode : ∀ slot < 8, host.code[c.pc + slot]? = (embeddedInstruction offset returnPC pc ins)[slot]?) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 7 ∧ execute host c steps = d ∧
      decodeGuest d = instructionEffect ins {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1} ∧
      d.pc = embeddedDestination offset returnPC (decodeGuest d) ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  classical
  have h0 : host.code[c.pc]? = some (.natural 2 (pc + 1)) := by
    simpa only [Nat.add_zero] using (hcode 0 (by omega)).trans (embedded_instruction_header offset returnPC pc ins).1
  have h1 : host.code[c.pc + 1]? = some (.nadd 3 3 1) :=
    (hcode 1 (by omega)).trans (embedded_instruction_header offset returnPC pc ins).2
  let g : Machine := {decodeGuest c with pc := pc + 1, work := (decodeGuest c).work + 1}
  by_cases hscalar : ∃ tr, scalarTranslation ins = some tr
  · obtain ⟨tr, ht⟩ := hscalar
    have h2 : host.code[c.pc + 2]? = some tr := by
      rw [hcode 2 (by omega)]
      cases ins <;> simp only [scalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))) := by
      rw [hcode 3 (by omega)]
      cases ins <;> simp only [scalarTranslation] at ht
      all_goals cases ht
      all_goals rfl
    obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_scalar_macro host c pc offset ins tr ht hh hone h0 h1 h2 h3
    refine ⟨4, d, by omega, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
    rw [hpc, hdec]
    have hg := scalar_effect_control ins tr ht g
    change offset + 8 * (pc + 1) = embeddedDestination offset returnPC (instructionEffect ins g)
    simp only [embeddedDestination, hg.1, hg.2]
    simp [g, hgh]
  · by_cases hmemory : ∃ tr a, memoryTranslation ins = some (tr, a)
    · obtain ⟨tr, a, ht⟩ := hmemory
      have h2 : host.code[c.pc + 2]? = some (.nadd 6 (guestReg a) (guestReg a)) := by
        rw [hcode 2 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h3 : host.code[c.pc + 3]? = some (.nadd 6 6 0) := by
        rw [hcode 3 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h4 : host.code[c.pc + 4]? = some (.nadd 6 6 1) := by
        rw [hcode 4 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h5 : host.code[c.pc + 5]? = some tr := by
        rw [hcode 5 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      have h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * (pc + 1))) := by
        rw [hcode 6 (by omega)]
        cases ins <;> simp only [memoryTranslation] at ht
        all_goals cases ht
        all_goals rfl
      obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_memory_macro host c pc offset ins tr a ht hh hone h0 h1 h2 h3 h4 h5 h6
      refine ⟨7, d, le_rfl, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
      rw [hpc, hdec]
      have hg := memory_effect_control ins tr a ht g
      change offset + 8 * (pc + 1) = embeddedDestination offset returnPC (instructionEffect ins g)
      simp only [embeddedDestination, hg.1, hg.2]
      simp [g, hgh]
    · cases ins with
      | jump target =>
        have h2 : host.code[c.pc + 2]? = some (.natural 2 target) := by simpa [embeddedInstruction] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * target)) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_jump_macro host c pc offset target hh hone h0 h1 h2 h3
        refine ⟨4, d, by omega, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        rw [hpc, hdec]
        simp [embeddedDestination, instructionEffect, hgh]
      | halt =>
        have h2 : host.code[c.pc + 2]? = some (.natural 4 1) := by simpa [embeddedInstruction] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump returnPC) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        obtain ⟨d, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_halt_macro host c pc returnPC hh hone h0 h1 h2 h3
        refine ⟨4, d, by omega, hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        rw [hpc, hdec]
        simp [embeddedDestination, instructionEffect]
      | less a b target =>
        have h2 : host.code[c.pc + 2]? = some (branchInstruction false (guestReg a) (guestReg b) (c.pc + 5)) := by
          simpa [embeddedInstruction, branchInstruction, hpos] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        have h5 : host.code[c.pc + 5]? = some (.natural 2 target) := by simpa [embeddedInstruction] using hcode 5 (by omega)
        have h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * target)) := by simpa [embeddedInstruction] using hcode 6 (by omega)
        obtain ⟨t, d, ht, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_branch_macro host c pc offset target false a b hh hone h0 h1 h2 h3 h5 h6
        refine ⟨t, d, ht.trans (by omega), hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        have hdh : (decodeGuest d).halted = false := by
          rw [hdec, branch_effect]
          split_ifs <;> exact hgh
        simpa [embeddedDestination, hdh] using hpc
      | lessN a b target =>
        have h2 : host.code[c.pc + 2]? = some (branchInstruction true (guestReg a) (guestReg b) (c.pc + 5)) := by
          simpa [embeddedInstruction, branchInstruction, hpos] using hcode 2 (by omega)
        have h3 : host.code[c.pc + 3]? = some (.jump (offset + 8 * (pc + 1))) := by simpa [embeddedInstruction] using hcode 3 (by omega)
        have h5 : host.code[c.pc + 5]? = some (.natural 2 target) := by simpa [embeddedInstruction] using hcode 5 (by omega)
        have h6 : host.code[c.pc + 6]? = some (.jump (offset + 8 * target)) := by simpa [embeddedInstruction] using hcode 6 (by omega)
        obtain ⟨t, d, ht, hd, hdec, hpc, hw, hhalt, hm0, hm1⟩ := embedded_branch_macro host c pc offset target true a b hh hone h0 h1 h2 h3 h5 h6
        refine ⟨t, d, ht.trans (by omega), hd, hdec, ?_, hw, hhalt, hm0, hm1⟩
        have hdh : (decodeGuest d).halted = false := by
          rw [hdec, branch_effect]
          split_ifs <;> exact hgh
        simpa [embeddedDestination, hdh] using hpc
      | _ => simp_all [scalarTranslation, memoryTranslation]
end DecrAlmostLinearSSSP.Decremental
end s14
section s15
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma embedded_single_step (host guest : Program) (offset returnPC : ℕ)
    (hcode : EmbedsCode host guest offset returnPC) (c : Machine)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hgh : (decodeGuest c).halted = false)
    (hpos : c.pc = embeddedDestination offset returnPC (decodeGuest c))
    (ins : Instruction) (hc : guest.code[(decodeGuest c).pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 7 ∧ execute host c steps = d ∧
      decodeGuest d = step guest (decodeGuest c) ∧
      d.pc = embeddedDestination offset returnPC (decodeGuest d) ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  have hp : c.pc = offset + 8 * (decodeGuest c).pc := by simpa [embeddedDestination, hgh] using hpos
  obtain ⟨steps, d, hs, hd, hdec, hdpc, hw, hhalt, hm0, hm1⟩ :=
    embedded_macro host c (decodeGuest c).pc offset returnPC ins hh hone hgh hp
      (fun slot hslot => by rw [hp]; exact hcode _ _ hc slot hslot)
  refine ⟨steps, d, hs, hd, ?_, hdpc, hw, hhalt, hm0, hm1⟩
  rw [step_eq_effect guest (decodeGuest c) ins hgh hc]
  exact hdec
lemma execute_halted (p : Program) (c : Machine) (hh : c.halted = true) (t : ℕ) : execute p c t = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show t + 1 = t + 1 by rfl, execute_add, ih]
    change step p c = c
    simp [step, hh]
lemma execute_succ_front (p : Program) (c : Machine) (t : ℕ) :
    execute p c (t + 1) = execute p (step p c) t := by
  rw [show t + 1 = 1 + t by omega, execute_add]
  rfl
lemma embedded_execution (host guest : Program) (offset returnPC : ℕ)
    (hcode : EmbedsCode host guest offset returnPC) (t : ℕ) (c : Machine)
    (hh : c.halted = false) (hone : c.natReg 1 = 1)
    (hpos : c.pc = embeddedDestination offset returnPC (decodeGuest c))
    (hvalid : ∀ j < t, (execute guest (decodeGuest c) j).halted = false →
      ∃ ins, guest.code[(execute guest (decodeGuest c) j).pc]? = some ins) :
    ∃ (steps : ℕ) (d : Machine), steps ≤ 7 * t ∧ execute host c steps = d ∧
      decodeGuest d = execute guest (decodeGuest c) t ∧
      d.pc = embeddedDestination offset returnPC (decodeGuest d) ∧ d.work = c.work + steps ∧ d.halted = false ∧
      d.natReg 0 = c.natReg 0 ∧ d.natReg 1 = c.natReg 1 := by
  induction t generalizing c with
  | zero => exact ⟨0, c, le_rfl, rfl, rfl, hpos, rfl, hh, rfl, rfl⟩
  | succ t ih =>
    by_cases hgh : (decodeGuest c).halted = true
    · refine ⟨0, c, Nat.zero_le _, rfl, ?_, hpos, rfl, hh, rfl, rfl⟩
      exact (execute_halted guest (decodeGuest c) hgh (t + 1)).symm
    · have hghfalse : (decodeGuest c).halted = false := Bool.eq_false_iff.mpr hgh
      obtain ⟨ins, hins⟩ := hvalid 0 (by omega) hghfalse
      obtain ⟨s, b, hs, hb, hbdec, hbpos, hbw, hbh, hb0, hb1⟩ :=
        embedded_single_step host guest offset returnPC hcode c hh hone hghfalse hpos ins hins
      have hbvalid : ∀ j < t, (execute guest (decodeGuest b) j).halted = false →
          ∃ ins, guest.code[(execute guest (decodeGuest b) j).pc]? = some ins := by
        intro j hj hhj
        rw [hbdec, ← execute_succ_front] at hhj ⊢
        exact hvalid (j + 1) (by omega) hhj
      obtain ⟨r, d, hr, hd, hddec, hdpos, hdw, hdh, hd0, hd1⟩ :=
        ih b hbh (hb1.trans hone) hbpos hbvalid
      refine ⟨s + r, d, ?_, ?_, ?_, hdpos, ?_, hdh, hd0.trans hb0, hd1.trans hb1⟩
      · omega
      · rw [execute_add, hb, hd]
      · rw [hddec, hbdec, ← execute_succ_front]
      · omega
end DecrAlmostLinearSSSP.Decremental
end s15
section s16
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
lemma fault_step_persists (p : Program) (c : Machine) (hf : c.fault = true) : (step p c).fault = true := by
  classical
  unfold step
  split_ifs with hh
  · exact hf
  · cases hc : p.code[c.pc]? with
    | none => rfl
    | some ins =>
      cases ins <;> simp only
      all_goals try exact hf
      all_goals split_ifs <;> exact hf
lemma fault_execute_persists (p : Program) (c : Machine) (hf : c.fault = true) (t : ℕ) :
    (execute p c t).fault = true := by
  induction t with
  | zero => exact hf
  | succ t ih =>
    rw [execute_add]
    exact fault_step_persists p _ ih
lemma execution_prefix_no_fault (p : Program) (c : Machine) (t j : ℕ)
    (hj : j ≤ t) (hf : (execute p c t).fault = false) : (execute p c j).fault = false := by
  by_contra hh
  have ht : (execute p c j).fault = true := by
    cases hx : (execute p c j).fault <;> simp_all
  have hlast := fault_execute_persists p (execute p c j) ht (t - j)
  rw [← execute_add, Nat.add_sub_of_le hj, hf] at hlast
  contradiction
lemma execution_valid_code (p : Program) (c : Machine) (t : ℕ)
    (hf : (execute p c t).fault = false) :
    ∀ j < t, (execute p c j).halted = false → ∃ ins, p.code[(execute p c j).pc]? = some ins := by
  intro j hj hh
  cases hc : p.code[(execute p c j).pc]? with
  | some ins => exact ⟨ins, rfl⟩
  | none =>
    have hnof := execution_prefix_no_fault p c t (j + 1) (by omega) hf
    rw [execute_add] at hnof
    change (step p (execute p c j)).fault = false at hnof
    simp [step, hh, hc] at hnof
lemma step_work (p : Program) (c : Machine) (hh : c.halted = false) :
    (step p c).work = c.work + 1 := by
  classical
  unfold step
  rw [hh]
  simp only [Bool.false_eq_true, if_false]
  cases hc : p.code[c.pc]? with
  | none => rfl
  | some ins =>
    cases ins <;> simp only
    all_goals try rfl
    all_goals split_ifs <;> rfl
lemma step_of_halted (p : Program) (c : Machine) (hh : c.halted = true) : step p c = c := by
  unfold step
  rw [hh]
  rfl
lemma step_work_mono (p : Program) (c : Machine) : c.work ≤ (step p c).work := by
  by_cases hh : c.halted = true
  · rw [step_of_halted p c hh]
  · rw [step_work p c (Bool.eq_false_iff.mpr hh)]
    omega
end DecrAlmostLinearSSSP.Decremental
end s16
section s17
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s17
section s18
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Structured
end s18
section s19
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Payload
end Payload
end DecrAlmostLinearSSSP.Decremental.Exact
end s19
section s20
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace LocatedTrie
end LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact
end s20
section s21
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s21
section s22
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s22
section s23
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s23
section s24
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s24
section s25
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s25
section s26
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s26
section s27
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s27
section s28
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s28
section s29
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s29
section s30
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Allocate
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Allocate
end s30
section s31
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s31
section s32
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace TriePush
end TriePush
end DecrAlmostLinearSSSP.Decremental.Exact
end s32
section s33
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s33
section s34
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s34
section s35
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s35
section s36
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s36
section s37
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s37
section s38
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s38
section s39
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s39
section s40
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s40
section s41
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s41
section s42
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s42
section s43
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s43
section s44
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s44
section s45
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s45
section s46
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s46
section s47
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s47
section s48
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s48
section s49
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s49
section s50
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s50
section s51
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePush
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePush
end s51
section s52
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s52
section s53
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s53
section s54
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s54
section s55
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s55
section s56
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s56
section s57
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace TriePop
end TriePop
end DecrAlmostLinearSSSP.Decremental.Exact
end s57
section s58
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
end s58
section s59
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s59
section s60
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.TriePop
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.TriePop
end s60
section s61
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s61
section s62
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s62
section s63
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s63
section s64
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s64
section s65
set_option autoImplicit false
open Filter
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s65
section s66
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s66
section s67
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s67
section s68
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s68
section s69
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s69
section s70
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s70
section s71
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s71
section s72
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s72
section s73
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s73
section s74
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s74
section s75
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
open Structured
end DecrAlmostLinearSSSP.Decremental
end s75
section s76
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s76
section s77
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Powers
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Powers
end s77
section s78
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s78
section s79
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Clear
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Clear
end s79
section s80
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s80
section s81
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s81
section s82
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s82
section s83
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s83
section s84
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s84
section s85
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s85
section s86
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s86
section s87
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s87
section s88
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s88
section s89
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s89
section s90
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s90
section s91
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s91
section s92
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s92
section s93
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s93
section s94
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s94
section s95
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s95
section s96
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
namespace Adjacency
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s96
section s97
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s97
section s98
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s98
section s99
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s99
section s100
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
attribute [local irreducible] advanced
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s100
section s101
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s101
section s102
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild
end s102
section s103
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s103
section s104
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
namespace Adjacency
end Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact
end s104
section s105
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s105
section s106
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact
end s106
section s107
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Layout
end DecrAlmostLinearSSSP.Decremental.Exact.Layout
end s107
section s108
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s108
section s109
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s109
section s110
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s110
section s111
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s111
section s112
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s112
section s113
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s113
section s114
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s114
section s115
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s115
section s116
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s116
section s117
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s117
section s118
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Heap
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Heap
end s118
section s119
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s119
section s120
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact
end s120
section s121
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s121
section s122
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s122
section s123
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s123
section s124
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s124
section s125
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s125
section s126
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s126
section s127
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Exact
end s127
section s128
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s128
section s129
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s129
section s130
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s130
section s131
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s131
section s132
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s132
section s133
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s133
section s134
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end DecrAlmostLinearSSSP.Decremental.Exact.Adjacency
end s134
section s135
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s135
section s136
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
end DecrAlmostLinearSSSP.Decremental.Exact
end s136
section s137
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s137
section s138
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s138
section s139
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s139
section s140
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s140
section s141
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact
attribute [local instance] Classical.propDecidable
end DecrAlmostLinearSSSP.Decremental.Exact
end s141
section s142
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Structured
end DecrAlmostLinearSSSP.Decremental.Structured
end s142
section s143
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s143
section s144
set_option autoImplicit false
open scoped ENNReal NNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s144
section s145
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s145
section s146
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s146
section s147
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s147
section s148
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s148
section s149
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s149
section s150
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s150
section s151
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s151
section s152
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.InputCapture
open Structured
end DecrAlmostLinearSSSP.Decremental.InputCapture
end s152
section s153
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s153
section s154
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s154
section s155
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s155
section s156
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s156
section s157
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s157
section s158
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s158
section s159
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s159
section s160
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
open Structured
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s160
section s161
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s161
section s162
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s162
section s163
set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s163
section s164
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s164
section s165
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental
end DecrAlmostLinearSSSP.Decremental
end s165
section s166
set_option autoImplicit false
set_option maxRecDepth 10000
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s166
section s167
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s167
section s168
set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra
end s168
open DecrAlmostLinearSSSP.Decremental
set_option autoImplicit false
theorem solution : (((((((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @Eq.{1} Nat
    (@Multiset.card.{0} (Prod.{0, 0} Nat Nat) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low))
    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low key value : Nat),
  @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Multiset.{0} (Prod.{0, 0} Nat Nat))
      (@Multiset.instMembership.{0} (Prod.{0, 0} Nat Nat))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low) (@Prod.mk.{0, 0} Nat Nat key value) →
    And (@LE.le.{0} Nat instLENat low key)
      (@LT.lt.{0} Nat instLTNat key
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height))))) ∧ ((∀ (height key value : Nat) (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
      (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value t))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (height key value : Nat) (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @LT.lt.{0} Nat instLTNat key
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height) →
    @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height
        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value t) low)
      (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat)
        (@Prod.mk.{0, 0} Nat Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key) value)
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low))))) ∧ (((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  Iff
    (@Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.none.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))))
    (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.none.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))) →
    @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low)
      (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (nat_lit 0)
        (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@Multiset.instZero.{0} (Prod.{0, 0} Nat Nat)))))) ∧ ((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    And
      (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low)
        (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat)
          (@Prod.mk.{0, 0} Nat Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key) value)
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height next low)))
      (∀ (item : Prod.{0, 0} Nat Nat),
        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Multiset.{0} (Prod.{0, 0} Nat Nat))
            (@Multiset.instMembership.{0} (Prod.{0, 0} Nat Nat))
            (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low) item →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key)
            (@Prod.fst.{0, 0} Nat Nat item))) ∧ ((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height next)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    @LT.lt.{0} Nat instLTNat key
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height)))))) ∧ ((((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.popVisits height t)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t) →
    ∃ key value next,
      @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
        (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
            (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))))) ∧ ((∀ {height : Nat} (left right : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie.node height left right)) →
    And
      (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height left)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height right))
      (@Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height left)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height left))) ∧ (∀ (base : Nat), @Function.Injective.{1, 1} Nat Nat (DecrAlmostLinearSSSP.Decremental.guestAddress base)))) ∧ (((@Function.Injective.{1, 1} Nat Nat DecrAlmostLinearSSSP.Decremental.guestReg) ∧ (∀ {α : Type} (f : Nat → α) (a : Nat) (v : α),
  @Eq.{1} (Nat → α)
    (fun j =>
      @Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f (DecrAlmostLinearSSSP.Decremental.guestReg a) v
        (DecrAlmostLinearSSSP.Decremental.guestReg j))
    (@Function.update.{1, 1} Nat (fun j => α) instDecidableEqNat
      (fun j => f (DecrAlmostLinearSSSP.Decremental.guestReg j)) a v))) ∧ ((∀ {α : Type} (f : Nat → α) (base a : Nat) (v : α),
  @Eq.{1} (Nat → α)
    (fun j =>
      @Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f
        (DecrAlmostLinearSSSP.Decremental.guestAddress base a) v (DecrAlmostLinearSSSP.Decremental.guestAddress base j))
    (@Function.update.{1, 1} Nat (fun j => α) instDecidableEqNat
      (fun j => f (DecrAlmostLinearSSSP.Decremental.guestAddress base j)) a v)) ∧ ((∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.guestReg j) k) ∧ (∀ {α : Type} (f : Nat → α) (a b : Nat) (v : α),
  @Eq.{1} α
    (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f (DecrAlmostLinearSSSP.Decremental.guestReg a) v
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b))
    (f
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)))))))) ∧ (((((∀ {α : Type} (f : Nat → α) (base a b : Nat) (v : α),
  @Eq.{1} α
    (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f
      (DecrAlmostLinearSSSP.Decremental.guestAddress base a) v
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)))
    (f
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)))) ∧ (∀ {α : Type} (f : Nat → α) (base a b : Nat) (v : α),
  @LT.lt.{0} Nat instLTNat b base →
    @Eq.{1} α
      (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f
        (DecrAlmostLinearSSSP.Decremental.guestAddress base a) v b)
      (f b))) ∧ ((∀ (offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins))
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) ∧ (∀ {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  @Eq.{1} Nat c.pc d.pc →
    @Eq.{1} (Nat → Real) c.realReg d.realReg →
      @Eq.{1} (Nat → Nat) c.natReg d.natReg →
        @Eq.{1} (Nat → Real) c.realMem d.realMem →
          @Eq.{1} (Nat → Nat) c.natMem d.natMem →
            @Eq.{1} Bool c.halted d.halted →
              @Eq.{1} Bool c.fault d.fault →
                @Eq.{1} Nat c.work d.work → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine c d))) ∧ (((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc work hostPC : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := hostPC, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) work,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem,
      halted := __src.halted, fault := __src.fault, work := work })) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.decodeGuest
              (DecrAlmostLinearSSSP.Decremental.execute host c
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
            {
              pc :=
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
              realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem,
              halted := __src.halted, fault := __src.fault,
              work :=
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c)
        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
          {
            pc :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
            realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted,
            fault := c.fault,
            work :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc work : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := work })
    (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.step p c))
        (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c))))))) ∧ ((((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat) (value : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc,
        realReg :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realReg
            (DecrAlmostLinearSSSP.Decremental.guestReg a) value,
        natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
        work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc,
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).realReg a value,
      natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted,
      fault := __src.fault, work := __src.work })) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a value : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (DecrAlmostLinearSSSP.Decremental.guestReg a) value,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).natReg a value,
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work }))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat) (value : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg, natReg := c.natReg,
        realMem :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realMem
            (DecrAlmostLinearSSSP.Decremental.guestAddress
              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) a)
            value,
        natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg, natReg := __src.natReg,
      realMem :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).realMem a value,
      natMem := __src.natMem, halted := __src.halted, fault := __src.fault, work := __src.work })) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a value : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem,
        natMem :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natMem
            (DecrAlmostLinearSSSP.Decremental.guestAddress
              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) a)
            value,
        halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
      natMem :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).natMem a value,
      halted := __src.halted, fault := __src.fault, work := __src.work })) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) a,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (DecrAlmostLinearSSSP.Decremental.decodeGuest c))))) ∧ (((∀ (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.instructionEffect translated c))
        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c))) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (d a : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.load (DecrAlmostLinearSSSP.Decremental.guestReg d)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.load d a)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (d a : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.loadN (DecrAlmostLinearSSSP.Decremental.guestReg d)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.loadN d a)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a d : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.store
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (DecrAlmostLinearSSSP.Decremental.guestReg d))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c))) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a d : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (DecrAlmostLinearSSSP.Decremental.guestReg d))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c))))))))) ∧ ((((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.execute p c a) b)) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.execute host c (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        { pc := target, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
          halted := c.halted, fault := c.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
        And
          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.decodeGuest
              (DecrAlmostLinearSSSP.Decremental.execute host c
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))
          (And
            (@Eq.{1} Nat
              (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (And
              (@Eq.{1} Bool
                (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
                Bool.false)
              (@Eq.{1} Nat
                (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
              (DecrAlmostLinearSSSP.Decremental.guestReg a) (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            ∃ d,
              And
                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                  (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  d)
                (And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                    (DecrAlmostLinearSSSP.Decremental.decodeGuest c))
                  (And
                    (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (DecrAlmostLinearSSSP.Decremental.guestAddress
                        (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (d.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))))
                    (And
                      (@Eq.{1} Nat d.pc
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (And (@Eq.{1} Bool d.halted Bool.false)
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))) ∧ (((∀ (offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.embeddedCodeAux offset returnPC start code))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction code))) ∧ (∀ (offset returnPC : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.embeddedCode offset returnPC code))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction code)))) ∧ ((∀ (offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc slot : Nat)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedCodeAux offset returnPC start code)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) pc)
            slot))
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start pc) ins)
          slot)) ∧ ((∀ (offset returnPC : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc slot : Nat)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedCode offset returnPC code)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) pc)
            slot))
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins) slot)) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.execute host c
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.headerState c pc)))))) ∧ ((((∀ (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.instructionEffect translated c).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.instructionEffect translated c).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect translated c).fault c.fault))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc offset : Nat)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                ∃ d,
                  And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (DecrAlmostLinearSSSP.Decremental.execute host c
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      d)
                    (And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                          (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                          {
                            pc :=
                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                            realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                            natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                            work :=
                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                      (And
                        (@Eq.{1} Nat d.pc
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                          (And (@Eq.{1} Bool d.halted Bool.false)
                            (And
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem,
      halted := __src.halted, fault := __src.fault, work := __src.work })) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
      natMem := __src.natMem, halted := Bool.true, fault := __src.fault, work := __src.work })) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (reg value target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.natural reg value)) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
        @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
          (DecrAlmostLinearSSSP.Decremental.execute host c
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          { pc := target, realReg := c.realReg,
            natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg reg value,
            realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
            work :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) })))) ∧ (((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (pc offset target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) target)))) →
              ∃ d,
                And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect
                        (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)
                        (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                          natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                    (And
                      (@Eq.{1} Nat d.pc
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) target)))
                      (And
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc returnPC : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.jump returnPC)) →
              ∃ d,
                And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect
                        DecrAlmostLinearSSSP.Decremental.Instruction.halt
                        (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                          natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                    (And (@Eq.{1} Nat d.pc returnPC)
                      (And
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (natural : Bool)
  (a b target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.branchInstruction natural (DecrAlmostLinearSSSP.Decremental.guestReg a)
            (DecrAlmostLinearSSSP.Decremental.guestReg b) target)) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.execute host c (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        {
          pc :=
            @ite.{1} Nat
              (DecrAlmostLinearSSSP.Decremental.branchTest natural (DecrAlmostLinearSSSP.Decremental.decodeGuest c) a b)
              (Classical.propDecidable
                (DecrAlmostLinearSSSP.Decremental.branchTest natural (DecrAlmostLinearSSSP.Decremental.decodeGuest c) a
                  b))
              target
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
          realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted,
          fault := c.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) ∧ ((∀ (natural : Bool) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc a b : Nat),
  @Eq.{1} Prop
    (DecrAlmostLinearSSSP.Decremental.branchTest natural
      (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.headerState c pc)) a b)
    (DecrAlmostLinearSSSP.Decremental.branchTest natural (DecrAlmostLinearSSSP.Decremental.decodeGuest c) a b)) ∧ (∀ (natural : Bool) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b target : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.instructionEffect
      (DecrAlmostLinearSSSP.Decremental.branchInstruction natural a b target) c)
    (@ite.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.branchTest natural c a b)
      (Classical.propDecidable (DecrAlmostLinearSSSP.Decremental.branchTest natural c a b))
      { pc := target, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := c.work }
      c))))))) ∧ (((((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (pc offset target : Nat) (natural : Bool) (a b : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.branchInstruction natural
                  (DecrAlmostLinearSSSP.Decremental.guestReg a) (DecrAlmostLinearSSSP.Decremental.guestReg b)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) target)))) →
                  ∃ steps d,
                    And (@LE.le.{0} Nat instLENat steps (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                          (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                        (And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                            (DecrAlmostLinearSSSP.Decremental.instructionEffect
                              (DecrAlmostLinearSSSP.Decremental.branchInstruction natural a b target)
                              (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                              {
                                pc :=
                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                                natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                                work :=
                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                          (And
                            (@Eq.{1} Nat d.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                  (DecrAlmostLinearSSSP.Decremental.decodeGuest d).pc)))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ (∀ (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat translated a)) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (DecrAlmostLinearSSSP.Decremental.guestAddress
            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
        @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
          (DecrAlmostLinearSSSP.Decremental.decodeGuest
            (DecrAlmostLinearSSSP.Decremental.instructionEffect translated c))
          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat translated a)) →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (DecrAlmostLinearSSSP.Decremental.guestAddress
          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
          And
            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
              (DecrAlmostLinearSSSP.Decremental.decodeGuest
                (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))
            (And
              (@Eq.{1} Nat
                (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (And
                (@Eq.{1} Bool
                  (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
                  Bool.false)
                (And
                  (@Eq.{1} Nat
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.execute host c
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.execute host c
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc offset : Nat)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat translated a)) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (DecrAlmostLinearSSSP.Decremental.guestReg a) (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                      ∃ d,
                        And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.execute host c
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            d)
                          (And
                            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                              (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                                {
                                  pc :=
                                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                  realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                                  natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                                  work :=
                                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                            (And
                              (@Eq.{1} Nat d.pc
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              (And
                                (@Eq.{1} Nat d.work
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                (And (@Eq.{1} Bool d.halted Bool.false)
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))) ∧ (((∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      And (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).pc c.pc)
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).halted c.halted)) ∧ (∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat tr a)) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      And (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).pc c.pc)
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).halted c.halted))) ∧ ((∀ (offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  And
    (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.natural
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.nadd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (pc offset returnPC : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.decodeGuest c).halted Bool.false →
        @Eq.{1} Nat c.pc
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) pc)) →
          (∀ (slot : Nat),
              @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins) slot)) →
            ∃ steps d,
              And (@LE.le.{0} Nat instLENat steps (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                        (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                          natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                    (And
                      (@Eq.{1} Nat d.pc
                        (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                          (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                      (And
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ (∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.decodeGuest c).halted Bool.false →
            @Eq.{1} Nat c.pc
                (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                  (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
              ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                      (DecrAlmostLinearSSSP.Decremental.decodeGuest c).pc)
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                  ∃ steps d,
                    And (@LE.le.{0} Nat instLENat steps (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                          (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                        (And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                            (DecrAlmostLinearSSSP.Decremental.step guest
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))
                          (And
                            (@Eq.{1} Nat d.pc
                              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                                (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))))) ∧ ((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    ∀ (t : Nat), @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c t) c) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.step p c) t))) ∧ ((∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (t : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat c.pc
              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j t →
                  @Eq.{1} Bool
                      (DecrAlmostLinearSSSP.Decremental.execute guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c)
                          j).halted
                      Bool.false →
                    ∃ ins,
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                          (DecrAlmostLinearSSSP.Decremental.execute guest
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c) j).pc)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
              ∃ steps d,
                And
                  (@LE.le.{0} Nat instLENat steps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t))
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                    (And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                        (DecrAlmostLinearSSSP.Decremental.execute guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c)
                          t))
                      (And
                        (@Eq.{1} Nat d.pc
                          (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                          (And (@Eq.{1} Bool d.halted Bool.false)
                            (And
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.fault Bool.true → @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).fault Bool.true) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.fault Bool.true →
    ∀ (t : Nat), @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.true)))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t j : Nat),
  @LE.le.{0} Nat instLENat j t →
    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false →
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).fault Bool.false) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false →
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).halted Bool.false →
          ∃ ins,
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c) c) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat c.work (DecrAlmostLinearSSSP.Decremental.step p c).work)))))))) := by
  exact ⟨⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.entries_card,DecrAlmostLinearSSSP.Decremental.RadixQueue.entries_range⟩,⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.count_insert,DecrAlmostLinearSSSP.Decremental.RadixQueue.entries_insert⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.pop_none_iff,DecrAlmostLinearSSSP.Decremental.RadixQueue.entries_empty_of_pop_none⟩,⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.pop_spec,⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.count_pop,DecrAlmostLinearSSSP.Decremental.RadixQueue.pop_key_bound⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.popVisits_bound,DecrAlmostLinearSSSP.Decremental.RadixQueue.pop_nonempty⟩,⟨DecrAlmostLinearSSSP.Decremental.RadixQueue.selected_child_positive,DecrAlmostLinearSSSP.Decremental.guestAddress_injective⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.guestReg_injective,DecrAlmostLinearSSSP.Decremental.update_guest_register⟩,⟨DecrAlmostLinearSSSP.Decremental.update_guest_memory,⟨DecrAlmostLinearSSSP.Decremental.guestReg_ne_meta,DecrAlmostLinearSSSP.Decremental.guest_reg_write_preserves_even⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.guest_write_preserves_even,DecrAlmostLinearSSSP.Decremental.guest_write_preserves_prefix⟩,⟨DecrAlmostLinearSSSP.Decremental.embeddedInstruction_length,DecrAlmostLinearSSSP.Decremental.machine_ext⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_metadata,DecrAlmostLinearSSSP.Decremental.embedded_header⟩,⟨DecrAlmostLinearSSSP.Decremental.step_eq_effect,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_host_clock,DecrAlmostLinearSSSP.Decremental.decodeGuest_step_effect⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_real_register,DecrAlmostLinearSSSP.Decremental.decodeGuest_nat_register⟩,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_real_memory,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_nat_memory,DecrAlmostLinearSSSP.Decremental.decodeGuest_scratch⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_scalar,DecrAlmostLinearSSSP.Decremental.decodeGuest_load⟩,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_loadN,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_store,DecrAlmostLinearSSSP.Decremental.decodeGuest_storeN⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.execute_add,DecrAlmostLinearSSSP.Decremental.host_jump⟩,⟨DecrAlmostLinearSSSP.Decremental.host_scalar,DecrAlmostLinearSSSP.Decremental.embedded_address⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.embeddedCodeAux_length,DecrAlmostLinearSSSP.Decremental.embeddedCode_length⟩,⟨DecrAlmostLinearSSSP.Decremental.embeddedCodeAux_get,⟨DecrAlmostLinearSSSP.Decremental.embeddedCode_get,DecrAlmostLinearSSSP.Decremental.embedded_header_exact⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.scalar_metadata,DecrAlmostLinearSSSP.Decremental.embedded_scalar_macro⟩,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_pc,⟨DecrAlmostLinearSSSP.Decremental.decodeGuest_halt,DecrAlmostLinearSSSP.Decremental.host_natural_jump⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.embedded_jump_macro,DecrAlmostLinearSSSP.Decremental.embedded_halt_macro⟩,⟨DecrAlmostLinearSSSP.Decremental.host_branch,⟨DecrAlmostLinearSSSP.Decremental.branchTest_header,DecrAlmostLinearSSSP.Decremental.branch_effect⟩⟩⟩⟩⟩,⟨⟨⟨⟨DecrAlmostLinearSSSP.Decremental.embedded_branch_macro,DecrAlmostLinearSSSP.Decremental.decodeGuest_memory⟩,⟨DecrAlmostLinearSSSP.Decremental.host_memory,DecrAlmostLinearSSSP.Decremental.embedded_memory_macro⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.scalar_effect_control,DecrAlmostLinearSSSP.Decremental.memory_effect_control⟩,⟨DecrAlmostLinearSSSP.Decremental.embedded_instruction_header,⟨DecrAlmostLinearSSSP.Decremental.embedded_macro,DecrAlmostLinearSSSP.Decremental.embedded_single_step⟩⟩⟩⟩,⟨⟨⟨DecrAlmostLinearSSSP.Decremental.execute_halted,DecrAlmostLinearSSSP.Decremental.execute_succ_front⟩,⟨DecrAlmostLinearSSSP.Decremental.embedded_execution,⟨DecrAlmostLinearSSSP.Decremental.fault_step_persists,DecrAlmostLinearSSSP.Decremental.fault_execute_persists⟩⟩⟩,⟨⟨DecrAlmostLinearSSSP.Decremental.execution_prefix_no_fault,DecrAlmostLinearSSSP.Decremental.execution_valid_code⟩,⟨DecrAlmostLinearSSSP.Decremental.step_work,⟨DecrAlmostLinearSSSP.Decremental.step_of_halted,DecrAlmostLinearSSSP.Decremental.step_work_mono⟩⟩⟩⟩⟩⟩⟩
