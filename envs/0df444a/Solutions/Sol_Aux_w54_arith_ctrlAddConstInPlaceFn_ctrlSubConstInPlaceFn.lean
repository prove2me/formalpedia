-- Prove2me | solution 1 for Aux_w54_arith.ctrlAddConstInPlaceFn_ctrlSubConstInPlaceFn
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:52.322053+00:00
-- url     : https://prove2.me/submissions/8e715894-e7be-471c-a5f8-214c3ab4eef2

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
set_option autoImplicit false
namespace Aux_w54_arith
end Aux_w54_arith
open Aux_w54_arith
open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement
open QuantumLTF.Membership.Supplement.LcgSym54 Thm49Primitives Thm410Router
theorem solution (w c : ℕ) (x : Qubits (1 + w)) :
    Aux_w54_arith.ctrlAddConstInPlaceFn w c (Aux_w54_arith.ctrlSubConstInPlaceFn w c x) = x ∧
      Aux_w54_arith.ctrlSubConstInPlaceFn w c (Aux_w54_arith.ctrlAddConstInPlaceFn w c x) = x := by
  by_cases hx : x ⟨0, by omega⟩ = true
  · let b : Qubits w := fun i => x ⟨1 + i.1, by omega⟩
    have hcm : c % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have hb_lt := bitsToNatLSB_lt w b
    have hntb_eq : ∀ u : ℕ, natToBitsLSB w (u % 2 ^ w) = natToBitsLSB w u := fun u => by
      funext i; simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
    have hsub_ctrl : Aux_w54_arith.ctrlSubConstInPlaceFn w c x ⟨0, by omega⟩ = true := by
      dsimp only [Aux_w54_arith.ctrlSubConstInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have hadd_ctrl : Aux_w54_arith.ctrlAddConstInPlaceFn w c x ⟨0, by omega⟩ = true := by
      dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn]; rw [if_pos hx, dif_neg (by omega)]; exact hx
    have hb_s : (fun i : Fin w => Aux_w54_arith.ctrlSubConstInPlaceFn w c x ⟨1 + i.1, by omega⟩) =
        natToBitsLSB w (2 ^ w + bitsToNatLSB b - c % 2 ^ w) := by
      funext i; dsimp only [Aux_w54_arith.ctrlSubConstInPlaceFn]; rw [if_pos hx, dif_pos (by omega)]
      exact congrArg _ (Fin.ext (by dsimp only; omega))
    have hb_a : (fun i : Fin w => Aux_w54_arith.ctrlAddConstInPlaceFn w c x ⟨1 + i.1, by omega⟩) =
        natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b) := by
      funext i; dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn]; rw [if_pos hx, dif_pos (by omega)]
      exact congrArg _ (Fin.ext (by dsimp only; omega))
    have hadd_m : ∀ u v : ℕ, (u + v % 2 ^ w) % 2 ^ w = (u + v) % 2 ^ w := fun u v => by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hmod1 : (c % 2 ^ w + (2 ^ w + bitsToNatLSB b - c % 2 ^ w) % 2 ^ w) % 2 ^ w = bitsToNatLSB b := by
      rw [hadd_m, show c % 2 ^ w + (2 ^ w + bitsToNatLSB b - c % 2 ^ w) = 2 ^ w + bitsToNatLSB b by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
    have hmod2 : (2 ^ w + (c % 2 ^ w + bitsToNatLSB b) % 2 ^ w - c % 2 ^ w) % 2 ^ w = bitsToNatLSB b := by
      by_cases hsum : c % 2 ^ w + bitsToNatLSB b < 2 ^ w
      · rw [Nat.mod_eq_of_lt hsum, show 2 ^ w + (c % 2 ^ w + bitsToNatLSB b) - c % 2 ^ w =
          2 ^ w + bitsToNatLSB b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
      · have hmeq : (c % 2 ^ w + bitsToNatLSB b) % 2 ^ w = c % 2 ^ w + bitsToNatLSB b - 2 ^ w := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hmeq, show 2 ^ w + (c % 2 ^ w + bitsToNatLSB b - 2 ^ w) - c % 2 ^ w = bitsToNatLSB b by omega,
          Nat.mod_eq_of_lt hb_lt]
    constructor
    · funext u; by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn]; rw [if_pos hsub_ctrl, dif_neg (by omega), hsub_ctrl, hx]
      · dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn]; rw [if_pos hsub_ctrl, dif_pos (by omega), hb_s]
        have h1 : bitsToNatLSB (natToBitsLSB w (2 ^ w + bitsToNatLSB b - c % 2 ^ w)) =
            (2 ^ w + bitsToNatLSB b - c % 2 ^ w) % 2 ^ w := by
          rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
        rw [h1, ← hntb_eq, hmod1, natToBitsLSB_bitsToNatLSB]
        exact congrArg x (Fin.ext (by dsimp only [b]; omega))
    · funext u; by_cases hu0 : u.1 = 0
      · have hu_eq : u = ⟨0, by omega⟩ := Fin.ext hu0
        rw [hu_eq]; dsimp only [Aux_w54_arith.ctrlSubConstInPlaceFn]; rw [if_pos hadd_ctrl, dif_neg (by omega), hadd_ctrl, hx]
      · dsimp only [Aux_w54_arith.ctrlSubConstInPlaceFn]; rw [if_pos hadd_ctrl, dif_pos (by omega), hb_a]
        have h1 : bitsToNatLSB (natToBitsLSB w (c % 2 ^ w + bitsToNatLSB b)) =
            (c % 2 ^ w + bitsToNatLSB b) % 2 ^ w := by
          rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
        rw [h1, ← hntb_eq, hmod2, natToBitsLSB_bitsToNatLSB]
        exact congrArg x (Fin.ext (by dsimp only [b]; omega))
  · have hsub_eq : Aux_w54_arith.ctrlSubConstInPlaceFn w c x = x := by
      funext u; dsimp only [Aux_w54_arith.ctrlSubConstInPlaceFn]; rw [if_neg hx]
    have hadd_eq : Aux_w54_arith.ctrlAddConstInPlaceFn w c x = x := by
      funext u; dsimp only [Aux_w54_arith.ctrlAddConstInPlaceFn]; rw [if_neg hx]
    simp only [hsub_eq, hadd_eq, and_self]
