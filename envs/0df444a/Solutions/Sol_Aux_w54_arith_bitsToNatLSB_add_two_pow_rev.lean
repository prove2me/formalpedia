-- Prove2me | solution 1 for Aux_w54_arith.bitsToNatLSB_add_two_pow_rev
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:07.42688+00:00
-- url     : https://prove2.me/submissions/7c0e1a0e-3fdd-4ed3-8334-aa1ea6735a34

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
import Mathlib
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router
theorem solution (w : ℕ) (x : Qubits w) :
    bitsToNatLSB (fun i => !x i) + bitsToNatLSB x = 2 ^ w - 1 := by
  induction w with
  | zero => simp [bitsToNatLSB]
  | succ w ih =>
    simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
    have hih := ih (fun i => x i.succ)
    have h1 : (∑ i : Fin w, if !x i.succ then 2 ^ (i.1 + 1) else 0) =
        2 * ∑ i : Fin w, if !x i.succ then 2 ^ i.1 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [pow_succ']
    have h2 : (∑ i : Fin w, if x i.succ then 2 ^ (i.1 + 1) else 0) =
        2 * ∑ i : Fin w, if x i.succ then 2 ^ i.1 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [pow_succ']
    dsimp only [bitsToNatLSB] at hih
    rw [h1, h2]
    have hp : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have hb : (if !x 0 then 1 else 0) + (if x 0 then 1 else 0) = 1 := by
      cases x 0 <;> rfl
    rw [pow_succ']
    omega
