-- Prove2me | solution 1 for Aux_w54_arith.addInPlaceCircuit_implements
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:32.285796+00:00
-- url     : https://prove2.me/submissions/13641161-bd2b-401a-8794-080362247fbf

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
import Theorems.Thm_Aux_w54_arith_act_cuccaroCore_ket
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router




























/-! ### Part 2: Zero-Ancilla Register Primitives -/












































































/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/





























@[simp] private lemma cuccaroWireEmb_val (w : ℕ) (u : Fin (1 + 2 * w)) :
    (cuccaroWireEmb w u).1 =
      if u.1 = 0 then w + w
      else if (u.1 - 1) % 2 = 0 then (u.1 - 1) / 2
      else w + (u.1 - 1) / 2 := by
  change (if u.1 = 0 then (⟨w + w, _⟩ : Fin ((w + w) + 1))
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
    (Aux_w54_arith.addInPlaceCircuit w).ImplementsOnClean (permMat (Aux_w54_arith.addInPlaceFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  let z0 := padZero (w + w) 1 x
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  let emb := Aux_w54_arith.cuccaroWireEmb w
  have hz0_comp : z0 ∘ emb = fun u : Fin (1 + 2 * w) =>
      if h0 : u.1 = 0 then false
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
    funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]; dsimp only [z0]; exact padZero_val_ge x _ (by simp [emb, h0])
    · rw [dif_neg h0]
      by_cases hm : (u.1 - 1) % 2 = 0
      · have hev : (emb u).1 = (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_pos hm]; dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · have hev : (emb u).1 = w + (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_neg hm]; dsimp only [z0]
        rw [padZero_val_lt x _ (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
  have hact_core := Aux_w54_arith.act_cuccaroCore_ket w false a b
  dsimp only at hact_core
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hact_core
  have hact := act_mapWires_ket (Aux_w54_arith.cuccaroCore w) emb z0 _ (by rw [hz0_comp]; exact hact_core)
    (padZero (w + w) 1 (Aux_w54_arith.addInPlaceFn w x)) ?_ ?_
  · exact hact
  · funext u
    dsimp only [Function.comp_apply]
    by_cases h0 : u.1 = 0
    · rw [dif_pos h0]
      have hev : (emb u).1 = w + w := by simp [emb, h0]
      exact padZero_val_ge (Aux_w54_arith.addInPlaceFn w x) (emb u) (by omega)
    · rw [dif_neg h0]
      by_cases hm : (u.1 - 1) % 2 = 0
      · have hev : (emb u).1 = (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_pos hm, padZero_val_lt _ _ (by omega)]
        dsimp only [Aux_w54_arith.addInPlaceFn]; rw [dif_pos (by omega)]
        exact congrArg x (Fin.ext (by dsimp; omega))
      · have hev : (emb u).1 = w + (u.1 - 1) / 2 := by simp [emb, h0, hm]
        have hu_lt : (u.1 - 1) / 2 < w := by have := u.isLt; omega
        rw [dif_neg hm, padZero_val_lt _ _ (by omega)]
        dsimp only [Aux_w54_arith.addInPlaceFn]; rw [dif_neg (by omega)]
        exact congrArg (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) (Fin.ext (by dsimp; omega))
  · intro u hu
    exfalso; apply hu
    have hlt := u.isLt
    by_cases huw : u.1 = w + w
    · exact ⟨0, Fin.ext (by simp [emb, huw])⟩
    · by_cases hw : u.1 < w
      · exact ⟨⟨1 + 2 * u.1, by omega⟩, Fin.ext (by simp [emb])⟩
      · exact ⟨⟨1 + 2 * (u.1 - w) + 1, by omega⟩, Fin.ext (by simp [emb]; omega)⟩
