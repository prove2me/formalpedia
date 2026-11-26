-- Prove2me | solution 1 for Aux_w54_arith.ctrlConstXorCircuit_implements
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:13.011609+00:00
-- url     : https://prove2.me/submissions/7486b832-2759-450d-a11e-ea727c2ce49a

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
section
set_option autoImplicit false

/-! Reused accepted arithmetic proof by Robin Kothari, submission 0ac99132-8635-4775-91de-dd0ad0e55353.
Apache-2.0. This local dependency is not a new contribution.
Helper definitions are exposed to verify their realization over gatesRev. -/

namespace Aux_w54_arith

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router




























/-! ### Part 2: Zero-Ancilla Register Primitives -/


































































private lemma act_ctrlConstPrefixCircuit_ket (w c k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w)) :
    act (ctrlConstPrefixCircuit w c k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then if h : 1 ≤ u.1 ∧ u.1 < 1 + k then xor (z u) (c.testBit (u.1 - 1)) else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [ctrlConstPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega)]
  | succ k ih =>
    dsimp only [ctrlConstPrefixCircuit]
    cases hc : c.testBit k
    · rw [if_neg (by simp), ih (by omega)]
      congr 1; funext u
      cases hz0 : z ⟨0, by omega⟩
      · rfl
      · simp only [↓reduceIte]
        by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + k
        · rw [dif_pos hu, dif_pos (by omega)]
        · rw [dif_neg hu]
          by_cases heq : u.1 = 1 + k
          · rw [dif_pos (by omega), show u.1 - 1 = k by omega, hc, Bool.xor_false]
          · rw [dif_neg (by omega)]
    · rw [if_pos (by simp), LayeredCircuit.seq_unitary, act_mul, ih (by omega),
        act_cnotGate_ket]
      congr 1; funext u
      let c0 : Fin (1 + w) := ⟨0, by omega⟩
      let tgt : Fin (1 + w) := ⟨1 + k, by omega⟩
      have hc0_v : c0.1 = 0 := rfl
      have htgt_v : tgt.1 = 1 + k := rfl
      have hzc : z c0 = z ⟨0, by omega⟩ := rfl
      by_cases hz0 : z ⟨0, by omega⟩ = true
      · have h0_lt : ¬ (1 ≤ c0.1 ∧ c0.1 < 1 + k) := by omega
        have hzc_out : (if z ⟨0, by omega⟩ = true then
            if h : 1 ≤ c0.1 ∧ c0.1 < 1 + k then xor (z c0) (c.testBit (c0.1 - 1)) else z c0
          else z c0) = true := by
          rw [if_pos hz0, dif_neg h0_lt, hzc, hz0]
        rw [hzc_out]
        by_cases hut : u = tgt
        · subst hut
          have hnt : ¬ (1 ≤ tgt.1 ∧ tgt.1 < 1 + k) := by omega
          have hnew : 1 ≤ tgt.1 ∧ tgt.1 < 1 + (k + 1) := by omega
          rw [Function.update_self, if_pos hz0, if_pos hz0, dif_neg hnt, dif_pos hnew,
            show tgt.1 - 1 = k by omega, hc]
        · rw [Function.update_of_ne hut, if_pos hz0, if_pos hz0]
          by_cases hu : 1 ≤ u.1 ∧ u.1 < 1 + k
          · rw [dif_pos hu, dif_pos (by omega)]
          · rw [dif_neg hu, dif_neg (by intro h; apply hut; apply Fin.ext; omega)]
      · have hzc_out : (if z ⟨0, by omega⟩ = true then
            if h : 1 ≤ c0.1 ∧ c0.1 < 1 + k then xor (z c0) (c.testBit (c0.1 - 1)) else z c0
          else z c0) = false := by
          rw [if_neg hz0, hzc]
          cases hz_c : z ⟨0, by omega⟩
          · rfl
          · exact absurd hz_c hz0
        rw [hzc_out, Bool.xor_false, Function.update_eq_self, if_neg hz0, if_neg hz0]









/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/

















































































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
theorem solution (w c : ℕ) :
    (Aux_w54_arith.ctrlConstXorCircuit w c).ImplementsOnClean (permMat (Aux_w54_arith.ctrlConstXorFn w c)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [Aux_w54_arith.ctrlConstXorCircuit]
  have h0 : padZero (1 + w) 0 x = x := by
    funext u; simp
  have h0' : padZero (1 + w) 0 (Aux_w54_arith.ctrlConstXorFn w c x) = Aux_w54_arith.ctrlConstXorFn w c x := by
    funext u; simp
  rw [h0, h0']
  have hact := act_ctrlConstPrefixCircuit_ket w c w le_rfl x
  change act (Aux_w54_arith.ctrlConstPrefixCircuit w c w le_rfl).unitary (ket x) = ket (Aux_w54_arith.ctrlConstXorFn w c x)
  rw [hact]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [Aux_w54_arith.ctrlConstXorFn]; rw [if_pos hx, if_pos hx]
    by_cases h1 : 1 ≤ u.1
    · rw [dif_pos ⟨h1, hu⟩, dif_pos h1]
      simp [natToBitsLSB]
    · rw [dif_neg (by omega), dif_neg h1]
  · dsimp only [Aux_w54_arith.ctrlConstXorFn]; rw [if_neg hx, if_neg hx]
