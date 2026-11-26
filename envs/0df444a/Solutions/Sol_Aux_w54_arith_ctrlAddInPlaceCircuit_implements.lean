-- Prove2me | solution 1 for Aux_w54_arith.ctrlAddInPlaceCircuit_implements
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:50:26.35148+00:00
-- url     : https://prove2.me/submissions/bee39f7a-51f7-4765-ba00-c2ae511e35ac

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






private lemma act_ctrlCopyPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w + w)) :
    act (ctrlCopyPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then
          if h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k then
            xor (z u) (z ⟨u.1 - w, by omega⟩)
          else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [ctrlCopyPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [ctrlCopyPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_toffoliOn_ket]
    congr 1; funext u
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hc_v : c.1 = 0 := rfl
    have ha_v : a.1 = 1 + k := rfl
    have hb_v : b.1 = 1 + w + k := rfl
    by_cases hz0 : z ⟨0, by omega⟩ = true
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then xor (z c) (z ⟨c.1 - w, by omega⟩) else z c
        else z c) = true := by
        rw [if_pos hz0, dif_neg (by omega)]; exact hz0
      have hza_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ a.1 ∧ a.1 < 1 + w + k then xor (z a) (z ⟨a.1 - w, by omega⟩) else z a
        else z a) = z a := by
        rw [if_pos hz0, dif_neg (by omega)]
      have hz0' : z ⟨0, by omega⟩ = true := hz0
      rw [hzc_out, hza_out, if_pos hz0]
      by_cases hub : u = b
      · subst hub
        have hb_n : ¬ (1 + w ≤ b.1 ∧ b.1 < 1 + w + k) := by dsimp only [b]; omega
        have hb_new : 1 + w ≤ b.1 ∧ b.1 < 1 + w + (k + 1) := by dsimp only [b]; omega
        rw [Function.update_self, dif_neg hb_n, dif_pos hb_new]
        have hsub : (⟨b.1 - w, by omega⟩ : Fin (1 + w + w)) = a := Fin.ext (by dsimp only [a, b]; omega)
        rw [hsub]
        rw [if_pos hz0']
        rfl
      · rw [Function.update_of_ne hub]
        by_cases h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k
        · rw [dif_pos h2, dif_pos (by omega)]
        · have h2' : ¬ (1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1)) := by
            intro h; apply hub; apply Fin.ext; omega
          rw [dif_neg h2, dif_neg h2']
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then xor (z c) (z ⟨c.1 - w, by omega⟩) else z c
        else z c) = false := by
        rw [if_neg hz0]
        cases hz_c : z ⟨0, by omega⟩
        · rfl
        · exact absurd hz_c hz0
      rw [hzc_out, Bool.false_and, Bool.xor_false, Function.update_eq_self, if_neg hz0, if_neg hz0]






theorem ctrlCopyRegCircuit_implements (w : ℕ) :
    (ctrlCopyRegCircuit w).ImplementsOnClean (permMat (ctrlCopyRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [ctrlCopyRegCircuit]
  have h0 : padZero (1 + w + w) 0 x = x := by funext u; simp
  have h0' : padZero (1 + w + w) 0 (ctrlCopyRegFn w x) = ctrlCopyRegFn w x := by funext u; simp
  rw [h0, h0', act_ctrlCopyPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [ctrlCopyRegFn]; rw [if_pos hx, if_pos hx]
    by_cases h2 : 1 + w ≤ u.1
    · rw [dif_pos ⟨h2, hu⟩, dif_pos h2]
    · rw [dif_neg (by omega), dif_neg h2]
  · dsimp only [ctrlCopyRegFn]; rw [if_neg hx, if_neg hx]



@[simp] private lemma cAddCopyEmb_val (w : ℕ) (u : Fin (1 + w + w)) :
    (cAddCopyEmb w u).1 = if u.1 < 1 + w then u.1 else u.1 + w := by
  change (if u.1 < 1 + w then (⟨u.1, _⟩ : Fin ((1 + w + w) + (w + 1))) else ⟨u.1 + w, _⟩).1 = _
  split_ifs <;> rfl

@[simp] private lemma castAdd0_cAddCopyEmb_val (w : ℕ) (u : Fin (1 + w + w)) :
    (((Fin.castAddEmb 0).trans (cAddCopyEmb w)) u).1 = if u.1 < 1 + w then u.1 else u.1 + w := by
  change (cAddCopyEmb w (Fin.castAdd 0 u)).1 = _
  rw [cAddCopyEmb_val]; rfl































































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
    (Aux_w54_arith.ctrlAddInPlaceCircuit w).ImplementsOnClean (permMat (Aux_w54_arith.ctrlAddInPlaceFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (1 + w + w) (w + 1) x
  let a : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨1 + w + i.1, by omega⟩
  let cpy := (Aux_w54_arith.ctrlCopyRegCircuit w).mapWires (Aux_w54_arith.cAddCopyEmb w)
  let addC := (Aux_w54_arith.addInPlaceCircuit w).mapWires
    (combineEmb (Aux_w54_arith.cAddCoreMainEmb w) (Aux_w54_arith.cAddCoreAncEmb w) (Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreDisj w))
  let z1 : Qubits ((1 + w + w) + (w + 1)) := fun u =>
    if h : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w then
      if x ⟨0, by omega⟩ then a ⟨u.1 - (1 + w + w), by omega⟩ else false
    else z0 u
  have h1 : act cpy.unitary (ket z0) = ket z1 := by
    have hact := Aux_w54_arith.act_mapWires_perm (Aux_w54_arith.ctrlCopyRegCircuit w) (ctrlCopyRegFn w)
      (Aux_w54_arith.ctrlCopyRegCircuit_implements w) (Aux_w54_arith.cAddCopyEmb w) z0 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < 1 + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨u.1, by change u.1 < 1 + w + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; exact hu)])
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [ctrlCopyRegFn, Function.comp_apply]
      have hz0c : z0 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z0]
        have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
          rw [castAdd0_cAddCopyEmb_val]; simp
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext h0v)
      simp only [hz0c]
      have hnot : ¬ (1 + w ≤ (⟨u.1, by change u.1 < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1) := by dsimp only; omega
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_neg hnot, ← hu_eq]; dsimp only [z1]; rw [dif_neg (by omega)]
      · rw [if_neg hx, ← hu_eq]; dsimp only [z1]; rw [dif_neg (by omega)]
    · by_cases hS : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [ctrlCopyRegFn, Function.comp_apply]
        have hz0c : z0 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) =
            x ⟨0, by omega⟩ := by
          dsimp only [z0]
          have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
            rw [castAdd0_cAddCopyEmb_val]; simp
          rw [padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext h0v)
        simp only [hz0c]
        have h1w : 1 + w ≤ (⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1 := by dsimp only; omega
        have hzu : z0 u = false := padZero_val_ge x u hS.1
        have he_sub : ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨u.1 - w - w, by change u.1 - w - w < 1 + w + w; omega⟩ =
            ⟨1 + (u.1 - (1 + w + w)), by omega⟩ := Fin.ext (by
          rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; omega)]; dsimp only; omega)
        dsimp only [z1]; conv_rhs => rw [← hu_eq, dif_pos hS]
        cases hx0 : x ⟨0, by omega⟩
        · rw [if_neg (by decide), if_neg (by decide), ← hu_eq, hzu]
        · rw [if_pos rfl, if_pos rfl, dif_pos h1w, ← hu_eq, hzu, Bool.false_xor, he_sub]
          dsimp only [z0]; rw [padZero_val_lt x _ (by dsimp only; omega)]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [castAdd0_cAddCopyEmb_val] at hv
          have hjlt : j.1 < 1 + w + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z1]; rw [dif_neg hS]
  have hclean_z1 : ∀ j : Fin 1, z1 (Aux_w54_arith.cAddCoreAncEmb w j) = false := fun j => by
    have hjv : (Aux_w54_arith.cAddCoreAncEmb w j).1 = 1 + w + w + w := Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreAncEmb_val w j
    dsimp only [z1]
    rw [dif_neg (by omega)]
    exact padZero_val_ge x _ (by omega)
  let z2 : Qubits ((1 + w + w) + (w + 1)) := fun u =>
    if h : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w then
      if x ⟨0, by omega⟩ then natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b) ⟨u.1 - (1 + w), by omega⟩
      else b ⟨u.1 - (1 + w), by omega⟩
    else z1 u
  have h2 : act addC.unitary (ket z1) = ket z2 := by
    have hact := Aux_w54_arith.act_subReg_perm (Aux_w54_arith.addInPlaceCircuit w) (Aux_w54_arith.addInPlaceFn w) (Aux_w54_arith.addInPlaceCircuit_implements w)
      (Aux_w54_arith.cAddCoreMainEmb w) (Aux_w54_arith.cAddCoreAncEmb w) (Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreDisj w) z1 hclean_z1
    rw [hact]; congr 1; funext u
    have hcomp_s : (fun i : Fin w => (z1 ∘ Aux_w54_arith.cAddCoreMainEmb w) ⟨i.1, by omega⟩) =
        (if x ⟨0, by omega⟩ then a else fun _ => false) := by
      funext i
      dsimp only [Function.comp_apply, z1]
      have hv : (Aux_w54_arith.cAddCoreMainEmb w ⟨i.1, by omega⟩).1 = 1 + w + w + i.1 := by
        simp [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val, i.isLt]
      rw [dif_pos (by omega)]
      cases x ⟨0, by omega⟩
      · simp
      · simp only [↓reduceIte]; exact congrArg a (Fin.ext (by dsimp only; omega))
    have hcomp_b : (fun i : Fin w => (z1 ∘ Aux_w54_arith.cAddCoreMainEmb w) ⟨w + i.1, by omega⟩) = b := by
      funext i
      dsimp only [Function.comp_apply, z1]
      have hv : (Aux_w54_arith.cAddCoreMainEmb w ⟨w + i.1, by omega⟩).1 = 1 + w + i.1 := by
        simp [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val, show ¬ w + i.1 < w by omega]; omega
      rw [dif_neg (by omega)]
      dsimp only [z0]; rw [padZero_val_lt x _ (by omega)]
      exact congrArg x (Fin.ext (by dsimp only [b]; omega))
    by_cases hb : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
    · have hu_eq : u = Aux_w54_arith.cAddCoreMainEmb w ⟨w + (u.1 - (1 + w)), by omega⟩ := Fin.ext (by
        simp [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val, show ¬ w + (u.1 - (1 + w)) < w by omega]; omega)
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [Aux_w54_arith.addInPlaceFn]
      rw [dif_neg (by omega), hcomp_s, hcomp_b]
      dsimp only [z2]; rw [← hu_eq, dif_pos hb]
      cases hx : x ⟨0, by omega⟩
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Aux_w54_arith.bitsToNatLSB_all_false, zero_add, natToBitsLSB_bitsToNatLSB]
        exact congrArg b (Fin.ext (by dsimp only; omega))
      · simp only [↓reduceIte]
        exact congrArg (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) (Fin.ext (by dsimp only; omega))
    · by_cases hS : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w
      · have hu_eq : u = Aux_w54_arith.cAddCoreMainEmb w ⟨u.1 - (1 + w + w), by omega⟩ := Fin.ext (by
          simp [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val, show u.1 - (1 + w + w) < w by omega]; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [Aux_w54_arith.addInPlaceFn]
        rw [dif_pos (by omega)]
        dsimp only [Function.comp_apply, z2]; rw [← hu_eq, dif_neg hb]
      · have hnot : u ∉ Set.range (Aux_w54_arith.cAddCoreMainEmb w) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [Section5UploadPrivate.Section5LcgArithmeticFoundation.Aux_w54_arith.cAddCoreMainEmb_val] at hv
          split_ifs at hv <;> have := j.isLt <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        dsimp only [z2]; rw [dif_neg hb]
  have h3 : act cpy.unitary (ket z2) = ket (padZero (1 + w + w) (w + 1) (Aux_w54_arith.ctrlAddInPlaceFn w x)) := by
    have hact := Aux_w54_arith.act_mapWires_perm (Aux_w54_arith.ctrlCopyRegCircuit w) (ctrlCopyRegFn w)
      (Aux_w54_arith.ctrlCopyRegCircuit_implements w) (Aux_w54_arith.cAddCopyEmb w) z2 (fun j => Fin.elim0 j)
    rw [hact]; congr 1; funext u
    by_cases hu : u.1 < 1 + w
    · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨u.1, by change u.1 < 1 + w + w; omega⟩ :=
        Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; exact hu)])
      rw [hu_eq, updateOn_apply_emb]
      dsimp only [ctrlCopyRegFn, Function.comp_apply]
      have hz2c : z2 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) = x ⟨0, by omega⟩ := by
        dsimp only [z2, z1, z0]
        have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
          rw [castAdd0_cAddCopyEmb_val]; simp
        rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext h0v)
      simp only [hz2c]
      have hnot : ¬ (1 + w ≤ (⟨u.1, by change u.1 < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1) := by dsimp only; omega
      have h1w : u.1 < 1 + w + w := by omega
      conv_rhs => rw [← hu_eq, padZero_val_lt _ u h1w]
      dsimp only [Aux_w54_arith.ctrlAddInPlaceFn]
      have h1w' : ¬ (1 + w ≤ u.1) := by omega
      by_cases hx : x ⟨0, by omega⟩ = true
      · rw [if_pos hx, dif_neg hnot, ← hu_eq, if_pos hx, dif_neg h1w']
        dsimp only [z2, z1, z0]; rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
      · rw [if_neg hx, ← hu_eq, if_neg hx]
        dsimp only [z2, z1, z0]; rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
    · by_cases hS : 1 + w + w ≤ u.1 ∧ u.1 < 1 + w + w + w
      · have hu_eq : u = ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ :=
          Fin.ext (by rw [castAdd0_cAddCopyEmb_val, if_neg (by dsimp only; omega)]; dsimp only; omega)
        rw [hu_eq, updateOn_apply_emb]
        dsimp only [ctrlCopyRegFn, Function.comp_apply]
        have hz2c : z2 (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩) = x ⟨0, by omega⟩ := by
          dsimp only [z2, z1, z0]
          have h0v : (((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨0, by change 0 < 1 + w + w; omega⟩).1 = 0 := by
            rw [castAdd0_cAddCopyEmb_val]; simp
          rw [dif_neg (by omega), dif_neg (by omega), padZero_val_lt x _ (by omega)]
          exact congrArg x (Fin.ext h0v)
        simp only [hz2c]
        have h1w : 1 + w ≤ (⟨u.1 - w, by change u.1 - w < 1 + w + w; omega⟩ : Fin ((1 + w + w) + 0)).1 := by dsimp only; omega
        have he_S : z2 u = if x ⟨0, by omega⟩ then a ⟨u.1 - (1 + w + w), by omega⟩ else false := by
          dsimp only [z2, z1]; rw [dif_neg (by omega), dif_pos hS]
        have he_sub : ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) ⟨u.1 - w - w, by change u.1 - w - w < 1 + w + w; omega⟩ =
            ⟨1 + (u.1 - (1 + w + w)), by omega⟩ := Fin.ext (by
          rw [castAdd0_cAddCopyEmb_val, if_pos (by dsimp only; omega)]; dsimp only; omega)
        have he_a : z2 ⟨1 + (u.1 - (1 + w + w)), by omega⟩ = a ⟨u.1 - (1 + w + w), by omega⟩ := by
          dsimp only [z2, z1, z0]
          rw [dif_neg (by omega), dif_neg (by omega),
            padZero_val_lt x _ (by dsimp only; omega)]
        conv_rhs => rw [← hu_eq, padZero_val_ge _ u hS.1]
        by_cases hx : x ⟨0, by omega⟩ = true
        · rw [if_pos hx, dif_pos h1w, ← hu_eq, he_S, if_pos hx, he_sub, he_a, Bool.xor_self]
        · rw [if_neg hx, ← hu_eq, he_S, if_neg hx]
      · have hnot : u ∉ Set.range ((Fin.castAddEmb 0).trans (Aux_w54_arith.cAddCopyEmb w)) := by
          rintro ⟨j, hj⟩; have hv := congrArg Fin.val hj
          rw [castAdd0_cAddCopyEmb_val] at hv
          have hjlt : j.1 < 1 + w + w := Nat.lt_of_lt_of_eq j.isLt (Nat.add_zero _)
          split_ifs at hv <;> omega
        rw [updateOn_apply_not_mem _ _ _ hnot]
        by_cases hb : 1 + w ≤ u.1 ∧ u.1 < 1 + w + w
        · rw [padZero_val_lt _ u hb.2]; dsimp only [Aux_w54_arith.ctrlAddInPlaceFn, z2]; rw [dif_pos hb, dif_pos hb.1]
          cases hx : x ⟨0, by omega⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact congrArg x (Fin.ext (by dsimp only [b]; omega))
          · rfl
        · have hanc : u.1 = 1 + w + w + w := by have := u.isLt; omega
          rw [padZero_val_ge _ u (by omega)]
          dsimp only [z2, z1, z0]; rw [dif_neg hb, dif_neg hS, padZero_val_ge x u (by omega)]
  dsimp only [Aux_w54_arith.ctrlAddInPlaceCircuit]
  simp only [LayeredCircuit.seq_unitary, act_mul]
  change act cpy.unitary (act addC.unitary (act cpy.unitary (ket z0))) = _
  rw [h1, h2, h3]
