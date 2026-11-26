-- Prove2me | solution 1 for Aux_w54_arith.cswapRegCircuit_implements
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:12.219728+00:00
-- url     : https://prove2.me/submissions/a0a74585-cbda-42bc-a8a9-33f1d0c4a78b

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









































private lemma act_cswapPrefixCircuit_ket (w k : ℕ) (hk : k ≤ w) (z : Qubits (1 + w + w)) :
    act (cswapPrefixCircuit w k hk).unitary (ket z) =
      ket (fun u =>
        if z ⟨0, by omega⟩ then
          if h1 : 1 ≤ u.1 ∧ u.1 < 1 + k then z ⟨u.1 + w, by omega⟩
          else if h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k then z ⟨u.1 - w, by omega⟩
          else z u
        else z u) := by
  induction k with
  | zero =>
    simp only [cswapPrefixCircuit, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    cases hz : z ⟨0, by omega⟩
    · rfl
    · simp only [↓reduceIte]; rw [dif_neg (by omega), dif_neg (by omega)]
  | succ k ih =>
    dsimp only [cswapPrefixCircuit]
    rw [LayeredCircuit.seq_unitary, act_mul, ih (by omega), act_cswapOn_ket]
    congr 1; funext u
    let c : Fin (1 + w + w) := ⟨0, by omega⟩
    let a : Fin (1 + w + w) := ⟨1 + k, by omega⟩
    let b : Fin (1 + w + w) := ⟨1 + w + k, by omega⟩
    have hzc : z c = z ⟨0, by omega⟩ := rfl
    by_cases hz0 : z ⟨0, by omega⟩ = true
    · have hca_n : ¬ (1 ≤ c.1 ∧ c.1 < 1 + k) := by dsimp [c]; omega
      have hcb_n : ¬ (1 + w ≤ c.1 ∧ c.1 < 1 + w + k) := by dsimp [c]; omega
      have ha1_n : ¬ (1 ≤ a.1 ∧ a.1 < 1 + k) := by dsimp [a]; omega
      have ha2_n : ¬ (1 + w ≤ a.1 ∧ a.1 < 1 + w + k) := by dsimp [a]; omega
      have hb1_n : ¬ (1 ≤ b.1 ∧ b.1 < 1 + k) := by dsimp [b]; omega
      have hb2_n : ¬ (1 + w ≤ b.1 ∧ b.1 < 1 + w + k) := by dsimp [b]; omega
      have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h1 : 1 ≤ c.1 ∧ c.1 < 1 + k then z ⟨c.1 + w, by omega⟩
          else if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then z ⟨c.1 - w, by omega⟩
          else z c else z c) = true := by
        rw [if_pos hz0, dif_neg hca_n, dif_neg hcb_n, hzc, hz0]
      rw [if_pos hzc_out]; simp only [hz0, ↓reduceIte]
      by_cases hua : u = a
      · subst hua
        have ha_new : 1 ≤ a.1 ∧ a.1 < 1 + (k + 1) := by dsimp [a]; omega
        rw [if_pos rfl, dif_neg hb1_n, dif_neg hb2_n, dif_pos ha_new]
        exact congrArg z (Fin.ext (by dsimp [a]; omega))
      · rw [if_neg hua]
        by_cases hub : u = b
        · subst hub
          have hb_n1 : ¬ (1 ≤ b.1 ∧ b.1 < 1 + (k + 1)) := by dsimp [b]; omega
          have hb_n2 : 1 + w ≤ b.1 ∧ b.1 < 1 + w + (k + 1) := by dsimp [b]; omega
          rw [if_pos rfl, dif_neg ha1_n, dif_neg ha2_n, dif_neg hb_n1, dif_pos hb_n2]
          exact congrArg z (Fin.ext (by dsimp [a, b]; omega))
        · rw [if_neg hub]
          by_cases h1 : 1 ≤ u.1 ∧ u.1 < 1 + k
          · have h1' : 1 ≤ u.1 ∧ u.1 < 1 + (k + 1) := by omega
            rw [dif_pos h1, dif_pos h1']
          · have h1' : ¬ (1 ≤ u.1 ∧ u.1 < 1 + (k + 1)) := by
              intro h; apply hua; apply Fin.ext; dsimp [a]; omega
            rw [dif_neg h1, dif_neg h1']
            by_cases h2 : 1 + w ≤ u.1 ∧ u.1 < 1 + w + k
            · have h2' : 1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1) := by omega
              rw [dif_pos h2, dif_pos h2']
            · have h2' : ¬ (1 + w ≤ u.1 ∧ u.1 < 1 + w + (k + 1)) := by
                intro h; apply hub; apply Fin.ext; dsimp [b]; omega
              rw [dif_neg h2, dif_neg h2']
    · have hzc_out : (if z ⟨0, by omega⟩ = true then
          if h1 : 1 ≤ c.1 ∧ c.1 < 1 + k then z ⟨c.1 + w, by omega⟩
          else if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then z ⟨c.1 - w, by omega⟩
          else z c else z c) = false := by
        rw [if_neg hz0, hzc]
        cases hz_c : z ⟨0, by omega⟩
        · rfl
        · exact absurd hz_c hz0
      have hzc_out_ne : ¬ ((if z ⟨0, by omega⟩ = true then
          if h1 : 1 ≤ c.1 ∧ c.1 < 1 + k then z ⟨c.1 + w, by omega⟩
          else if h2 : 1 + w ≤ c.1 ∧ c.1 < 1 + w + k then z ⟨c.1 - w, by omega⟩
          else z c else z c) = true) := by rw [hzc_out]; decide
      rw [if_neg hzc_out_ne, if_neg hz0, if_neg hz0]


































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
theorem solution (w : ℕ) :
    (Aux_w54_arith.cswapRegCircuit w).ImplementsOnClean (permMat (cswapRegFn w)) := by
  apply implementsOnClean_of_act_perm
  intro x
  dsimp only [Aux_w54_arith.cswapRegCircuit]
  have h0 : padZero (1 + w + w) 0 x = x := by
    funext u; simp
  have h0' : padZero (1 + w + w) 0 (cswapRegFn w x) = cswapRegFn w x := by
    funext u; simp
  rw [h0, h0', act_cswapPrefixCircuit_ket]
  congr 1; funext u
  have hu := u.isLt
  by_cases hx : x ⟨0, by omega⟩ = true
  · dsimp only [cswapRegFn]
    rw [if_pos hx, if_pos hx]
    by_cases h1 : 1 ≤ u.1 ∧ u.1 < 1 + w
    · rw [dif_pos h1, dif_pos h1]
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : 1 + w ≤ u.1
      · rw [dif_pos h2, dif_pos ⟨h2, hu⟩]
      · rw [dif_neg h2, dif_neg (by omega)]
  · dsimp only [cswapRegFn]; rw [if_neg hx, if_neg hx]
