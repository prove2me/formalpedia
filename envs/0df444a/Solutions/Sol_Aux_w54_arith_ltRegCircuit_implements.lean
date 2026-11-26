-- Prove2me | solution 1 for Aux_w54_arith.ltRegCircuit_implements
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:16.399033+00:00
-- url     : https://prove2.me/submissions/719d00f6-21ef-41ae-a551-e7e8e74bc443

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Mathlib
import Theorems.Thm_Aux_w54_arith_act_cuccaroCarryOut_ket
import Theorems.Thm_Aux_w54_arith_bitsToNatLSB_add_two_pow_rev
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router


























lemma bitsToNatLSB_complement_lt_iff (w : ℕ) (a b : Qubits w) :
    (2 ^ w ≤ bitsToNatLSB (fun i => !a i) + bitsToNatLSB b) ↔
      bitsToNatLSB a < bitsToNatLSB b := by
  have hc := bitsToNatLSB_add_two_pow_rev w a
  have ha := bitsToNatLSB_lt w a
  omega

/-! ### Part 2: Zero-Ancilla Register Primitives -/












































































/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/































































private lemma act_flipRegCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits w) :
    act (flipRegCircuit w k hk).unitary (ket z) =
      ket (fun i => if i.1 < k then !z i else z i) := by
  induction k with
  | zero => simp [flipRegCircuit, LayeredCircuit.id_unitary, act_one]
  | succ k ih =>
    dsimp only [flipRegCircuit]; rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega),
      act_pauliXGate_ket]
    congr 1; funext i
    by_cases hik : i = ⟨k, by omega⟩
    · subst hik; simp [Function.update_self]
    · rw [Function.update_of_ne hik]
      have hne : i.1 ≠ k := fun h => hik (Fin.ext h)
      by_cases hi : i.1 < k <;> simp [hi, show i.1 < k + 1 ↔ i.1 < k ∨ i.1 = k by omega, hne]



@[simp] private lemma ltFlipEmb_val (w : ℕ) (i : Fin w) : (ltFlipEmb w i).1 = i.1 := rfl



@[simp] private lemma ltCarryEmb_val (w : ℕ) (u : Fin (1 + 2 * w + 1)) :
    (ltCarryEmb w u).1 =
      if u.1 = 0 then w + w + 1
      else if u.1 = 1 + 2 * w then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w + 1, _⟩ : Fin ((w + w + 1) + 1))
    else if u.1 = 1 + 2 * w then ⟨w + w, _⟩
    else if (u.1 - 1) % 2 = 0 then ⟨(u.1 - 1) / 2, _⟩ else ⟨w + (u.1 - 1) / 2, _⟩).1 = _
  split_ifs <;> rfl









/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/



















































































/-! ### MSB-First Circuit Wrappers via Zero-Gate `Fin.revPerm` Conjugation -/













-- 1. setConstMSBCircuit






-- 2. ctrlConstXorMSBCircuit






-- 3. eqConstMSBCircuit






-- 4. ltConstMSBCircuit






-- 5. ltRegMSBCircuit






-- 6 & 7. addInPlaceMSBCircuit & subInPlaceMSBCircuit
















-- 8 & 9. ctrlAddInPlaceMSBCircuit & ctrlSubInPlaceMSBCircuit
















-- 10 & 11. ctrlAddConstInPlaceMSBCircuit & ctrlSubConstInPlaceMSBCircuit












end Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Aux_w54_arith




end
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router
theorem solution (w : ℕ) :
    (Aux_w54_arith.ltRegCircuit w).ImplementsOnClean (permMat (Aux_w54_arith.ltRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + w + 1) 1 x
  let tgt : Fin ((w + w + 1) + 1) := ⟨w + w, by omega⟩
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let flipA := (Aux_w54_arith.flipRegCircuit w w le_rfl).mapWires (Aux_w54_arith.ltFlipEmb w)
  let carry := (Aux_w54_arith.cuccaroCarryOut w).mapWires (Aux_w54_arith.ltCarryEmb w)
  let z1 : Qubits ((w + w + 1) + 1) := fun u =>
    if u.1 < w then !z0 u else z0 u
  have hflip1 : act flipA.unitary (ket z0) = ket z1 := by
    refine act_mapWires_ket (Aux_w54_arith.flipRegCircuit w w le_rfl) (Aux_w54_arith.ltFlipEmb w) z0 _
      (act_flipRegCircuit_ket w w le_rfl _) z1 ?_ ?_
    · funext i
      simp [Function.comp_apply, z1, i.isLt]
    · intro u hu
      have hge : w ≤ u.1 := by
        by_contra hlt; exact hu ⟨⟨u.1, by omega⟩, Fin.ext rfl⟩
      simp [z1, hge]
  let z2 := Function.update z1 tgt (xor (z1 tgt) (decide (bitsToNatLSB a < bitsToNatLSB b)))
  have hz1_comp : z1 ∘ Aux_w54_arith.ltCarryEmb w = fun u : Fin (1 + 2 * w + 1) =>
      if h0 : u.1 = 0 then false
      else if ht : u.1 = 1 + 2 * w then z1 tgt
      else if hm : (u.1 - 1) % 2 = 0 then (!a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩)
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
    funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]
      have he : Aux_w54_arith.ltCarryEmb w u = Fin.natAdd (w + w + 1) ⟨0, by omega⟩ := Fin.ext (by simp [h0])
      rw [he]; dsimp only [z1, z0]; rw [if_neg (by simp; omega), padZero_natAdd]
    · rw [dif_neg h0]
      by_cases ht : u.1 = 1 + 2 * w
      · rw [dif_pos ht]
        have he : Aux_w54_arith.ltCarryEmb w u = tgt := Fin.ext (by dsimp [tgt]; simp [ht])
        rw [he]
      · rw [dif_neg ht]
        by_cases hm : (u.1 - 1) % 2 = 0
        · rw [dif_pos hm]
          have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
          have hev : (Aux_w54_arith.ltCarryEmb w u).1 = (u.1 - 1) / 2 := by simp [h0, ht, hm]
          dsimp only [z1, z0]; rw [if_pos (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg Bool.not (congrArg x (Fin.ext (by dsimp [a]; exact hev)))
        · rw [dif_neg hm]
          have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
          have hev : (Aux_w54_arith.ltCarryEmb w u).1 = w + (u.1 - 1) / 2 := by simp [h0, ht, hm]
          dsimp only [z1, z0]; rw [if_neg (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext (by dsimp [b]; exact hev))
  have hcarry_eq : decide (2 ^ w ≤ bitsToNatLSB (fun i => !a i) + bitsToNatLSB b + (if false then 1 else 0)) =
      decide (bitsToNatLSB a < bitsToNatLSB b) := by
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
    exact Aux_w54_arith.bitsToNatLSB_complement_lt_iff w a b
  have hcarry : act carry.unitary (ket z1) = ket z2 := by
    have hact_c := Aux_w54_arith.act_cuccaroCarryOut_ket w false (z1 tgt) (fun i => !a i) b
    dsimp only at hact_c
    rw [hcarry_eq] at hact_c
    refine act_mapWires_ket (Aux_w54_arith.cuccaroCarryOut w) (Aux_w54_arith.ltCarryEmb w) z1 _ (by rw [hz1_comp]; exact hact_c) z2 ?_ ?_
    · funext u
      dsimp only [Function.comp_apply]
      by_cases ht : u.1 = 1 + 2 * w
      · have he : Aux_w54_arith.ltCarryEmb w u = tgt := Fin.ext (by dsimp [tgt]; simp [ht])
        have hu_eq : u = ⟨1 + 2 * w, by omega⟩ := Fin.ext ht
        rw [he, hu_eq]; dsimp only [z2]; rw [Function.update_self, Function.update_self]
      · have hne1 : Aux_w54_arith.ltCarryEmb w u ≠ tgt := Fin.ne_of_val_ne (by
          dsimp [tgt]
          by_cases h0 : u.1 = 0
          · simp [h0]
          · by_cases hm : (u.1 - 1) % 2 = 0 <;> simp [h0, ht, hm] <;> omega)
        have hne2 : u ≠ ⟨1 + 2 * w, by omega⟩ := Fin.ne_of_val_ne ht
        dsimp only [z2]; rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
        exact congrFun hz1_comp u
    · intro u hu
      have hne : u ≠ tgt := fun heq => hu ⟨⟨1 + 2 * w, by omega⟩, Fin.ext (by
        simp [heq, tgt])⟩
      dsimp only [z2]; rw [Function.update_of_ne hne]
  have hflip2 : act flipA.unitary (ket z2) = ket (padZero (w + w + 1) 1 (Aux_w54_arith.ltRegFn w x)) := by
    refine act_mapWires_ket (Aux_w54_arith.flipRegCircuit w w le_rfl) (Aux_w54_arith.ltFlipEmb w) z2 _
      (act_flipRegCircuit_ket w w le_rfl _) (padZero (w + w + 1) 1 (Aux_w54_arith.ltRegFn w x)) ?_ ?_
    · funext i
      have hne_t : Aux_w54_arith.ltFlipEmb w i ≠ tgt := Fin.ne_of_val_ne (by rw [ltFlipEmb_val]; dsimp [tgt]; omega)
      have hne_x : (⟨i.1, by omega⟩ : Fin (w + w + 1)) ≠ ⟨w + w, by omega⟩ :=
        Fin.ne_of_val_ne (by simp; omega)
      simp only [Function.comp_apply, i.isLt, ↓reduceIte]
      dsimp only [z2]; rw [Function.update_of_ne hne_t]
      dsimp only [z1, z0]; rw [if_pos (by simp [i.isLt]), Bool.not_not,
        padZero_val_lt x _ (by simp; omega), padZero_val_lt _ _ (by simp; omega), Aux_w54_arith.ltRegFn]
      have hfl : (⟨(Aux_w54_arith.ltFlipEmb w i).1, by simp; omega⟩ : Fin (w + w + 1)) = ⟨i.1, by omega⟩ := Fin.ext rfl
      rw [hfl, Function.update_of_ne hne_x]
    · intro u hu
      have hge : w ≤ u.1 := by
        by_contra hlt; exact hu ⟨⟨u.1, by omega⟩, Fin.ext rfl⟩
      by_cases huw : u = tgt
      · subst huw
        dsimp only [z2]; rw [Function.update_self]
        dsimp only [z1, z0]; rw [if_neg (by dsimp [tgt]; omega),
          padZero_val_lt x tgt (by dsimp [tgt]; omega),
          padZero_val_lt _ tgt (by dsimp [tgt]; omega),
          Aux_w54_arith.ltRegFn, Function.update_self]
      · dsimp only [z2]; rw [Function.update_of_ne huw]
        dsimp only [z1, z0]; rw [if_neg (by omega : ¬ u.1 < w)]
        by_cases hlt_main : u.1 < w + w + 1
        · have hne_x : (⟨u.1, hlt_main⟩ : Fin (w + w + 1)) ≠ ⟨w + w, by omega⟩ :=
            Fin.ne_of_val_ne (fun h => huw (Fin.ext h))
          rw [padZero_val_lt x u hlt_main, padZero_val_lt _ u hlt_main,
            Aux_w54_arith.ltRegFn, Function.update_of_ne hne_x]
        · rw [padZero_val_ge x u (by omega), padZero_val_ge _ u (by omega)]
  dsimp only [Aux_w54_arith.ltRegCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act flipA.unitary (act carry.unitary (act flipA.unitary (ket z0))) = _
  rw [hflip1, hcarry, hflip2]
