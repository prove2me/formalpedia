-- Prove2me | solution 1 for CountingMatroid.Bridge.setMembershipBitProgram_finset_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T16:19:16.874542+00:00
-- url     : https://prove2.me/submissions/2220b7b4-15e0-4070-8e24-0478c9c8239a

import Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram
import Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_correct

set_option autoImplicit false
open CountingMatroid.Bridge OAI.CommonBasesFPRAS

theorem solution {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 11) (s : Finset (Fin n)) (i : Fin n)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits s)
    (h7 : c.registers 7 = List.replicate i.val true)
    (h8 : c.registers 8 = []) :
    let out := execution (setMembershipBitProgram value next) O c bits
      (5 * i.val + 5)
    out.control = next ∧
      out.registers 6 = finsetMembershipBits (if value then insert i s else s.erase i) ∧
    out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
    out.oracleCalls = c.oracleCalls ∧
    out.bitOperations = c.bitOperations + (5 * i.val + 5) := by
  let L := finsetMembershipBits s
  have hlen : L.length = n := by simp [L, finsetMembershipBits]
  have hi : i.val < L.length := by rw [hlen]; exact i.isLt
  have hget : L[i.val] = decide (i ∈ s) := by simp [L, finsetMembershipBits]
  have htakeLen : (L.take i.val).length = i.val := by
    simp only [List.length_take]
    omega
  have hsplit : L = L.take i.val ++ L[i.val] :: L.drop (i.val + 1) := by
    calc
      L = L.take i.val ++ L.drop i.val := (List.take_append_drop _ _).symm
      _ = L.take i.val ++ L[i.val] :: L.drop (i.val + 1) := by
        rw [List.drop_eq_getElem_cons hi]
  have hrun := setMembershipBitProgram_correct value next O bits c
    (L.take i.val) (decide (i ∈ s)) (L.drop (i.val + 1)) hc ho
    (by rw [h6]; exact hsplit.trans (by rw [hget]))
    (by simpa [htakeLen] using h7) h8
  have hrun' :
      let out := execution (setMembershipBitProgram value next) O c bits
        (5 * i.val + 5)
      out.control = next ∧ out.registers 6 = L.take i.val ++ value :: L.drop (i.val + 1) ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧ out.bitOperations = c.bitOperations + (5 * i.val + 5) := by
    simpa [htakeLen] using hrun
  rcases hrun' with ⟨hcontrol, hvector, h7', h8', hout, hcalls, hcost⟩
  have hset : (List.ofFn (fun j : Fin n => decide (j ∈ s))).set i.val value =
      List.ofFn (Function.update (fun j : Fin n => decide (j ∈ s)) i value) := by
    apply List.ext_getElem
    · simp
    · intro j hj₁ hj₂
      have hjn : j < n := by simpa using hj₁
      by_cases hEq : j = i.val
      · subst j
        simp [Function.update]
      · have hneq : (⟨j, hjn⟩ : Fin n) ≠ i := by
          intro h
          exact hEq (congrArg Fin.val h)
        rw [List.getElem_set_of_ne (Ne.symm hEq) value (by simpa using hj₂)]
        simp [Function.update, hneq]
  have hslice : L.take i.val ++ value :: L.drop (i.val + 1) =
      List.ofFn (Function.update (fun j : Fin n => decide (j ∈ s)) i value) := by
    rw [← hset, List.set_eq_take_cons_drop value (by simpa [L, finsetMembershipBits] using i.isLt)]
    simp [L, finsetMembershipBits]
  have hfinset : List.ofFn (Function.update (fun j : Fin n => decide (j ∈ s)) i value) =
      finsetMembershipBits (if value then insert i s else s.erase i) := by
    change List.ofFn (Function.update (fun j : Fin n => decide (j ∈ s)) i value) =
      List.ofFn (fun j : Fin n => decide (j ∈ if value then insert i s else s.erase i))
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      cases value <;> simp [Function.update]
    · cases value <;>
        simp [Function.update, Finset.mem_insert, Finset.mem_erase, hji]
  refine ⟨hcontrol, ?_, h7', h8', hout, hcalls, hcost⟩
  rw [hvector, hslice, hfinset]

#print axioms solution
