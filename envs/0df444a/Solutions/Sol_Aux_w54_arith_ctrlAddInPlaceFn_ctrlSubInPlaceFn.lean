-- Prove2me | solution 1 for Aux_w54_arith.ctrlAddInPlaceFn_ctrlSubInPlaceFn
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:49.526506+00:00
-- url     : https://prove2.me/submissions/7609a003-f9db-4318-a6e9-d03ccf2d1ad2

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
import Theorems.Thm_Aux_w54_arith_addInPlaceFn_subInPlaceFn
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router
theorem solution (w : ℕ) (x : Qubits (1 + w + w)) :
    Aux_w54_arith.ctrlAddInPlaceFn w (Aux_w54_arith.ctrlSubInPlaceFn w x) = x ∧
      Aux_w54_arith.ctrlSubInPlaceFn w (Aux_w54_arith.ctrlAddInPlaceFn w x) = x := by
  by_cases hx : x ⟨0, by omega⟩ = true
  · let x' : Qubits (w + w) := fun i => x ⟨1 + i.1, by omega⟩
    have hinv := Aux_w54_arith.addInPlaceFn_subInPlaceFn w x'
    have hsub_ctrl : Aux_w54_arith.ctrlSubInPlaceFn w x ⟨0, by omega⟩ = true := by
      dsimp only [Aux_w54_arith.ctrlSubInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have hadd_ctrl : Aux_w54_arith.ctrlAddInPlaceFn w x ⟨0, by omega⟩ = true := by
      dsimp only [Aux_w54_arith.ctrlAddInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have ha_s : (fun i : Fin w => Aux_w54_arith.ctrlSubInPlaceFn w x ⟨1 + i.1, by omega⟩) =
        fun i : Fin w => Aux_w54_arith.subInPlaceFn w x' ⟨i.1, by omega⟩ := by
      funext i; dsimp only [Aux_w54_arith.ctrlSubInPlaceFn, Aux_w54_arith.subInPlaceFn, x']
      rw [if_pos hx, dif_neg (by omega), dif_pos i.isLt]
    have hb_s : (fun i : Fin w => Aux_w54_arith.ctrlSubInPlaceFn w x ⟨1 + w + i.1, by omega⟩) =
        fun i : Fin w => Aux_w54_arith.subInPlaceFn w x' ⟨w + i.1, by omega⟩ := by
      funext i; dsimp only [Aux_w54_arith.ctrlSubInPlaceFn, Aux_w54_arith.subInPlaceFn, x']
      rw [if_pos hx, dif_pos (by omega), dif_neg (by omega)]
      congr 1
      · congr 2; congr 1; funext j; exact congrArg x (Fin.ext (by dsimp only; omega))
      · exact Fin.ext (by dsimp only; omega)
    have ha_a : (fun i : Fin w => Aux_w54_arith.ctrlAddInPlaceFn w x ⟨1 + i.1, by omega⟩) =
        fun i : Fin w => Aux_w54_arith.addInPlaceFn w x' ⟨i.1, by omega⟩ := by
      funext i; dsimp only [Aux_w54_arith.ctrlAddInPlaceFn, Aux_w54_arith.addInPlaceFn, x']
      rw [if_pos hx, dif_neg (by omega), dif_pos i.isLt]
    have hb_a : (fun i : Fin w => Aux_w54_arith.ctrlAddInPlaceFn w x ⟨1 + w + i.1, by omega⟩) =
        fun i : Fin w => Aux_w54_arith.addInPlaceFn w x' ⟨w + i.1, by omega⟩ := by
      funext i; dsimp only [Aux_w54_arith.ctrlAddInPlaceFn, Aux_w54_arith.addInPlaceFn, x']
      rw [if_pos hx, dif_pos (by omega), dif_neg (by omega)]
      congr 1
      · congr 2; funext j; exact congrArg x (Fin.ext (by dsimp only; omega))
      · exact Fin.ext (by dsimp only; omega)
    constructor
    · funext u
      by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [Aux_w54_arith.ctrlAddInPlaceFn]; rw [if_pos hsub_ctrl, dif_neg (by omega), hsub_ctrl, hx]
      · by_cases h1w : 1 + w ≤ u.1
        · have hu_lt : u.1 - (1 + w) < w := by have := u.isLt; omega
          have h1 := congrFun hinv.1 ⟨w + (u.1 - (1 + w)), by omega⟩
          dsimp only [Aux_w54_arith.ctrlAddInPlaceFn]; rw [if_pos hsub_ctrl, dif_pos h1w]
          have hadd_rw : natToBitsLSB w
              (bitsToNatLSB (fun i : Fin w => Aux_w54_arith.ctrlSubInPlaceFn w x ⟨1 + i.1, by omega⟩) +
                bitsToNatLSB (fun i : Fin w => Aux_w54_arith.ctrlSubInPlaceFn w x ⟨1 + w + i.1, by omega⟩))
              ⟨u.1 - (1 + w), hu_lt⟩ =
              Aux_w54_arith.addInPlaceFn w (Aux_w54_arith.subInPlaceFn w x') ⟨w + (u.1 - (1 + w)), by omega⟩ := by
            rw [ha_s, hb_s]
            dsimp only [Aux_w54_arith.addInPlaceFn]
            rw [dif_neg (by omega)]
            exact congrArg _ (Fin.ext (by dsimp only; omega))
          rw [hadd_rw, h1]; exact congrArg x (Fin.ext (by dsimp only [x']; omega))
        · dsimp only [Aux_w54_arith.ctrlAddInPlaceFn]; rw [if_pos hsub_ctrl, dif_neg h1w]
          have hu_eq : (⟨1 + (u.1 - 1), by omega⟩ : Fin (1 + w + w)) = u :=
            Fin.ext (by dsimp only; omega)
          rw [← hu_eq]
          refine (congrFun ha_s ⟨u.1 - 1, by omega⟩).trans ?_
          dsimp only [Aux_w54_arith.subInPlaceFn, x']; rw [dif_pos (by omega)]
    · funext u
      by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [Aux_w54_arith.ctrlSubInPlaceFn]; rw [if_pos hadd_ctrl, dif_neg (by omega), hadd_ctrl, hx]
      · by_cases h1w : 1 + w ≤ u.1
        · have hu_lt : u.1 - (1 + w) < w := by have := u.isLt; omega
          have h2 := congrFun hinv.2 ⟨w + (u.1 - (1 + w)), by omega⟩
          dsimp only [Aux_w54_arith.ctrlSubInPlaceFn]; rw [if_pos hadd_ctrl, dif_pos h1w]
          have hsub_rw : natToBitsLSB w
              (2 ^ w + bitsToNatLSB (fun i : Fin w => Aux_w54_arith.ctrlAddInPlaceFn w x ⟨1 + w + i.1, by omega⟩) -
                bitsToNatLSB (fun i : Fin w => Aux_w54_arith.ctrlAddInPlaceFn w x ⟨1 + i.1, by omega⟩))
              ⟨u.1 - (1 + w), hu_lt⟩ =
              Aux_w54_arith.subInPlaceFn w (Aux_w54_arith.addInPlaceFn w x') ⟨w + (u.1 - (1 + w)), by omega⟩ := by
            rw [ha_a, hb_a]
            dsimp only [Aux_w54_arith.subInPlaceFn]
            rw [dif_neg (by omega)]
            exact congrArg _ (Fin.ext (by dsimp only; omega))
          rw [hsub_rw, h2]; exact congrArg x (Fin.ext (by dsimp only [x']; omega))
        · dsimp only [Aux_w54_arith.ctrlSubInPlaceFn]; rw [if_pos hadd_ctrl, dif_neg h1w]
          have hu_eq : (⟨1 + (u.1 - 1), by omega⟩ : Fin (1 + w + w)) = u :=
            Fin.ext (by dsimp only; omega)
          rw [← hu_eq]
          refine (congrFun ha_a ⟨u.1 - 1, by omega⟩).trans ?_
          dsimp only [Aux_w54_arith.addInPlaceFn, x']; rw [dif_pos (by omega)]
  · have hsub_eq : Aux_w54_arith.ctrlSubInPlaceFn w x = x := by funext u; dsimp only [Aux_w54_arith.ctrlSubInPlaceFn]; rw [if_neg hx]
    have hadd_eq : Aux_w54_arith.ctrlAddInPlaceFn w x = x := by funext u; dsimp only [Aux_w54_arith.ctrlAddInPlaceFn]; rw [if_neg hx]
    simp only [hsub_eq, hadd_eq, and_self]
