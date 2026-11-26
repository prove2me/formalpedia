-- Prove2me | solution 1 for Aux_w54_arith.ctrlAddConstInPlaceCircuit_implements
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:46.596351+00:00
-- url     : https://prove2.me/submissions/e575b56b-4d0e-4fb3-90dc-4441aa654dff

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
import Theorems.Thm_Aux_w54_arith_addInPlaceCircuit_implements
import Theorems.Thm_Aux_w54_arith_ctrlConstXorCircuit_implements
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router

lemma act_subReg_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (embMain : Fin main ↪ Fin m) (embAnc : Fin anc ↪ Fin m)
    (hdisj : ∀ i j, embMain i ≠ embAnc j) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (embAnc j) = false) :
    act (lc.mapWires (combineEmb embMain embAnc hdisj)).unitary (ket z) =
      ket (updateOn embMain z (f (z ∘ embMain))) := by
  have hact := act_mapWires_implementsOnClean lc (permMat f) hlc
    (combineEmb embMain embAnc hdisj) z (fun j => by simpa using hclean j)
  dsimp only at hact
  rw [hact, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans (combineEmb embMain embAnc hdisj))))]
  · simp [permMat, castAddEmb_trans_combineEmb]
  · intro y _ hy; simp [permMat, hy]
  · intro hm; exact absurd (Finset.mem_univ _) hm











lemma act_mapWires_perm {main anc m : ℕ} (lc : LayeredCircuit (main + anc))
    (f : Qubits main → Qubits main) (hlc : lc.ImplementsOnClean (permMat f))
    (emb : Fin (main + anc) ↪ Fin m) (z : Qubits m)
    (hclean : ∀ j : Fin anc, z (emb (Fin.natAdd main j)) = false) :
    let embMain : Fin main ↪ Fin m := (Fin.castAddEmb anc).trans emb
    act (lc.mapWires emb).unitary (ket z) = ket (updateOn embMain z (f (z ∘ embMain))) := by
  intro embMain
  have h := act_mapWires_implementsOnClean lc (permMat f) hlc emb z hclean
  dsimp only at h
  dsimp only [embMain]
  rw [h, Finset.sum_eq_single (f (z ∘ ((Fin.castAddEmb anc).trans emb)))]
  · simp [permMat]
  · intro y _ hy; simp [permMat, hy]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem








lemma bitsToNatLSB_all_false (w : ℕ) : bitsToNatLSB (fun _ : Fin w => false) = 0 := by
  simp [bitsToNatLSB]





/-! ### Part 2: Zero-Ancilla Register Primitives -/












































































/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

















































































/-! ### Part 5: Sub-register Combinators, Controlled Arithmetic & Bit-Reversal -/



















































@[simp] private lemma cacXorEmb_val (w : ℕ) (u : Fin (1 + w)) :
    (cacXorEmb w u).1 = if u.1 = 0 then 0 else 1 + w + (u.1 - 1) := by
  change (if u.1 = 0 then (⟨0, _⟩ : Fin ((1 + w) + (w + 1))) else ⟨1 + w + (u.1 - 1), _⟩).1 = _
  split_ifs <;> rfl

@[simp] private lemma castAdd0_cacXorEmb_val (w : ℕ) (u : Fin (1 + w)) :
    (((Fin.castAddEmb 0).trans (cacXorEmb w)) u).1 = if u.1 = 0 then 0 else 1 + w + (u.1 - 1) := by
  change (cacXorEmb w (Fin.castAdd 0 u)).1 = _
  rw [cacXorEmb_val]; rfl





























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
theorem solution (w c : ℕ) :
    (Aux_w54_arith.ctrlAddConstInPlaceCircuit w c).ImplementsOnClean (permMat (Aux_w54_arith.ctrlAddConstInPlaceFn w c)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (1 + w) (w + 1) x
  let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let pat := natToBitsLSB w c
  have hpat_mod : pat = natToBitsLSB w (c % 2 ^ w) := by
    funext i; simp [pat, natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
  let sc := (Aux_w54_arith.ctrlConstXorCircuit w c).mapWires (Aux_w54_arith.cacXorEmb w)
  let addC := (Aux_w54_arith.addInPlaceCircuit w).mapWires
    (combineEmb (Aux_w54_arith.cacAddMainEmb w) (Aux_w54_arith.cacAddAncEmb w) (Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddDisj w))
  let z1 : Qubits ((1 + w) + (w + 1)) := fun u =>
    if h : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w then
      if x ⟨0, by omega⟩ then pat ⟨u.1 - (1 + w), by omega⟩ else false
    else z0 u
  have h1 : act sc.unitary (ket z0) = ket z1 := by
    have hact := Aux_w54_arith.act_mapWires_perm (Aux_w54_arith.ctrlConstXorCircuit w c) (Aux_w54_arith.ctrlConstXorFn w c)
      (Aux_w54_arith.ctrlConstXorCircuit_implements w c) (Aux_w54_arith.cacXorEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hS : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨1 + (u.1 - (1 + w)), by change 1 + (u.1 - (1 + w)) < 1 + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cacXorEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [Aux_w54_arith.ctrlConstXorFn, Function.comp_apply]
      have hz0c : z0 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z0]
        have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
          rw [castAdd0_cacXorEmb_val]; rfl
        rw [padZero_val_lt x _ (by omega)]; exact congrArg x (Fin.ext h0v)
      simp only [hz0c]
      have hzu : z0 u = false := padZero_val_ge x u hS.1
      dsimp only [z1]; conv_rhs => rw [← hu_eq, dif_pos hS]
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_pos (by omega), ← hu_eq, hzu, Bool.false_xor, if_pos hx]
        exact congrArg (natToBitsLSB w c) (Fin.ext (by dsimp only; omega))
      · rw [if_neg hx, ← hu_eq, hzu, if_neg hx]
    · by_cases hu0 : u.1 = 0
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cacXorEmb_val, if_pos rfl]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [Aux_w54_arith.ctrlConstXorFn, Function.comp_apply]
        have hz0c : z0 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
          dsimp only [z0]
          have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
            rw [castAdd0_cacXorEmb_val]; rfl
          rw [padZero_val_lt x _ (by omega)]; exact congrArg x (Fin.ext h0v)
        simp only [hz0c]
        dsimp only [z1]; conv_rhs => rw [← hu_eq, dif_neg hS]
        have hzx : z0 u = x ⟨0, by omega⟩ := by
          dsimp only [z0]; rw [padZero_val_lt x u (by omega)]; exact congrArg x (Fin.ext hu0)
        cases hx : x ⟨0, by omega⟩
        · rw [if_neg (by simp), hzx, hx]
        · rw [if_pos rfl, dif_neg (by omega), hzx, hx]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; rw [castAdd0_cacXorEmb_val] at hv
          have hjlt : j.1 < 1 + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z1]; rw [dif_neg hS]
  have hclean_z1 : ∀ j : Fin 1, z1 (Aux_w54_arith.cacAddAncEmb w j) = false := fun j => by
    have hjv : (Aux_w54_arith.cacAddAncEmb w j).1 = 1 + w + w := Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddAncEmb_val w j
    dsimp only [z1]; rw [dif_neg (by omega)]; exact padZero_val_ge x _ (by omega)
  let z2 : Qubits ((1 + w) + (w + 1)) := fun u =>
    if h : 1 ≤ u.1 ∧ u.1 < 1 + w then
      if x ⟨0, by omega⟩ then natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b) ⟨u.1 - 1, by omega⟩
      else b ⟨u.1 - 1, by omega⟩
    else z1 u
  have h2 : act addC.unitary (ket z1) = ket z2 := by
    have hact := Aux_w54_arith.act_subReg_perm (Aux_w54_arith.addInPlaceCircuit w) (Aux_w54_arith.addInPlaceFn w) (Aux_w54_arith.addInPlaceCircuit_implements w)
      (Aux_w54_arith.cacAddMainEmb w) (Aux_w54_arith.cacAddAncEmb w) (Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddDisj w) z1 hclean_z1
    rw [hact]; congr 1; funext u
    have hcomp_s : (fun i : Fin w => (z1 ∘ Aux_w54_arith.cacAddMainEmb w) ⟨i.1, by omega⟩) =
        (if x ⟨0, by omega⟩ then pat else fun _ => false) := by
      funext i; dsimp only [Function.comp_apply, z1]
      have hv : (Aux_w54_arith.cacAddMainEmb w ⟨i.1, by omega⟩).1 = 1 + w + i.1 := by simp [i.isLt]
      rw [dif_pos (by omega)]
      cases x ⟨0, by omega⟩
      · simp
      · simp only [↓reduceIte]; exact congrArg pat (Fin.ext (by dsimp only; omega))
    have hcomp_b : (fun i : Fin w => (z1 ∘ Aux_w54_arith.cacAddMainEmb w) ⟨w + i.1, by omega⟩) = b := by
      funext i; dsimp only [Function.comp_apply, z1]
      have hv : (Aux_w54_arith.cacAddMainEmb w ⟨w + i.1, by omega⟩).1 = 1 + i.1 := by
        simp [show ¬ w + i.1 < w by omega]
      rw [dif_neg (by omega)]
      dsimp only [z0]; rw [padZero_val_lt x _ (by omega)]
      exact congrArg x (Fin.ext (by dsimp only [b]; omega))
    by_cases hb : 1 ≤ u.1 ∧ u.1 < 1 + w
    · have hu_eq : u = Aux_w54_arith.cacAddMainEmb w ⟨w + (u.1 - 1), by omega⟩ := Fin.ext (by
        simp [show ¬ w + (u.1 - 1) < w by omega]; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [Aux_w54_arith.addInPlaceFn]
      rw [dif_neg (by omega), hcomp_s, hcomp_b]
      dsimp only [z2]; rw [← hu_eq, dif_pos hb]
      cases hx : x ⟨0, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Aux_w54_arith.bitsToNatLSB_all_false, zero_add, natToBitsLSB_bitsToNatLSB]
        exact congrArg b (Fin.ext (by dsimp only; omega))
      · simp only [↓reduceIte]
        rw [hpat_mod, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
        exact congrArg (natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b)) (Fin.ext (by dsimp only; omega))
    · by_cases hS : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
      · have hu_eq : u = Aux_w54_arith.cacAddMainEmb w ⟨u.1 - (1 + w), by omega⟩ := Fin.ext (by
          simp [show u.1 - (1 + w) < w by omega]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [Aux_w54_arith.addInPlaceFn]; rw [dif_pos (by omega)]
        dsimp only [Function.comp_apply, z2]; rw [← hu_eq, dif_neg hb]
      · have hnot : u ∉ Set.range (Aux_w54_arith.cacAddMainEmb w) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cacAddMainEmb_val] at hv
          split_ifs at hv <;> have := j.isLt <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z2]; rw [dif_neg hb]
  have h3 : act sc.unitary (ket z2) = ket (padZero (1 + w) (w + 1) (Aux_w54_arith.ctrlAddConstInPlaceFn w c x)) := by
    have hact := Aux_w54_arith.act_mapWires_perm (Aux_w54_arith.ctrlConstXorCircuit w c) (Aux_w54_arith.ctrlConstXorFn w c)
      (Aux_w54_arith.ctrlConstXorCircuit_implements w c) (Aux_w54_arith.cacXorEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hS : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨1 + (u.1 - (1 + w)), by change 1 + (u.1 - (1 + w)) < 1 + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cacXorEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [Aux_w54_arith.ctrlConstXorFn, Function.comp_apply]
      have hz2c : z2 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z2, z1, z0]
        have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
          rw [castAdd0_cacXorEmb_val]; rfl
        rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext h0v)
      simp only [hz2c]; conv_rhs => rw [← hu_eq, padZero_val_ge _ u hS.1]
      have hzu : z2 u = if x ⟨0, by omega⟩ then pat ⟨u.1 - (1 + w), by omega⟩ else false := by
        dsimp only [z2, z1]; rw [dif_neg (by omega), dif_pos hS]
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_pos (by omega), ← hu_eq, hzu, if_pos hx]
        have heq_b : natToBitsLSB w c ⟨1 + (u.1 - (1 + w)) - 1, by omega⟩ = pat ⟨u.1 - (1 + w), by omega⟩ :=
          congrArg (natToBitsLSB w c) (Fin.ext (by dsimp only; omega))
        rw [heq_b, Bool.xor_self]
      · rw [if_neg hx, ← hu_eq, hzu, if_neg hx]
    · by_cases hu0 : u.1 = 0
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cacXorEmb_val, if_pos rfl]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [Aux_w54_arith.ctrlConstXorFn, Function.comp_apply]
        have hz2c : z2 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩) = x ⟨0, by omega⟩ := by
          dsimp only [z2, z1, z0]
          have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) ⟨0, by change 0 < 1 + w; omega⟩).1 = 0 := by
            rw [castAdd0_cacXorEmb_val]; rfl
          rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext h0v)
        simp only [hz2c]; conv_rhs => rw [← hu_eq, padZero_val_lt _ u (by omega)]
        have hx_rhs : Aux_w54_arith.ctrlAddConstInPlaceFn w c x ⟨u.1, by omega⟩ = x ⟨0, by omega⟩ := by
          dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn]
          by_cases hx : x ⟨0, by omega⟩ = true
          · rw [if_pos hx, dif_neg (by omega)]; exact congrArg x (Fin.ext hu0)
          · rw [if_neg hx]; exact congrArg x (Fin.ext hu0)
        by_cases hx : x ⟨0, by omega⟩ = true
        · rw [if_pos hx, dif_neg (by omega), hx_rhs, hx]
        · rw [if_neg hx, hx_rhs]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (Aux_w54_arith.cacXorEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj; rw [castAdd0_cacXorEmb_val] at hv
          have hjlt : j.1 < 1 + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        by_cases hb : 1 ≤ u.1 ∧ u.1 < 1 + w
        · rw [padZero_val_lt _ u hb.2]; dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn, z2]; rw [dif_pos hb, dif_pos hb.1]
          cases hx : x ⟨0, by omega⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrArg x (Fin.ext (by dsimp only [b]; omega))
          · rfl
        · have hanc : u.1 = 1 + w + w := by have := u.isLt; omega
          rw [padZero_val_ge _ u (by omega)]
          dsimp only [z2, z1, z0]; rw [dif_neg hb, dif_neg hS, padZero_val_ge x u (by omega)]
  dsimp only [Aux_w54_arith.ctrlAddConstInPlaceCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act sc.unitary (act addC.unitary (act sc.unitary (ket z0))) = _
  rw [h1, h2, h3]
