-- Prove2me | solution 1 for Aux_w54_arith.addInPlaceFn_subInPlaceFn
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:45:54.499093+00:00
-- url     : https://prove2.me/submissions/7ca77045-9d0f-4f28-8064-649683fe01a5

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
theorem solution (w : ℕ) (x : Qubits (w + w)) :
    Aux_w54_arith.addInPlaceFn w (Aux_w54_arith.subInPlaceFn w x) = x ∧ Aux_w54_arith.subInPlaceFn w (Aux_w54_arith.addInPlaceFn w x) = x := by
  let a : Qubits w := fun i => x ⟨i.1, by omega⟩
  let b : Qubits w := fun i => x ⟨w + i.1, by omega⟩
  have ha_lt := bitsToNatLSB_lt w a
  have hb_lt := bitsToNatLSB_lt w b
  have ha_s : (fun i : Fin w => Aux_w54_arith.subInPlaceFn w x ⟨i.1, by omega⟩) = a := by
    funext i; simp [Aux_w54_arith.subInPlaceFn, a, i.isLt]
  have hb_s : (fun i : Fin w => Aux_w54_arith.subInPlaceFn w x ⟨w + i.1, by omega⟩) =
      natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) := by
    funext i; simp [Aux_w54_arith.subInPlaceFn, a, b, show ¬ w + i.1 < w by omega]
  have ha_a : (fun i : Fin w => Aux_w54_arith.addInPlaceFn w x ⟨i.1, by omega⟩) = a := by
    funext i; simp [Aux_w54_arith.addInPlaceFn, a, i.isLt]
  have hb_a : (fun i : Fin w => Aux_w54_arith.addInPlaceFn w x ⟨w + i.1, by omega⟩) =
      natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b) := by
    funext i; simp [Aux_w54_arith.addInPlaceFn, a, b, show ¬ w + i.1 < w by omega]
  have hmod1 : (bitsToNatLSB a + (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) % 2 ^ w) % 2 ^ w =
      bitsToNatLSB b := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
      show bitsToNatLSB a + (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) = 2 ^ w + bitsToNatLSB b by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
  have hmod2 : (2 ^ w + (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w - bitsToNatLSB a) % 2 ^ w =
      bitsToNatLSB b := by
    by_cases hsum : bitsToNatLSB a + bitsToNatLSB b < 2 ^ w
    · rw [Nat.mod_eq_of_lt hsum, show 2 ^ w + (bitsToNatLSB a + bitsToNatLSB b) - bitsToNatLSB a =
        2 ^ w + bitsToNatLSB b by omega, Nat.add_mod_left, Nat.mod_eq_of_lt hb_lt]
    · have hmod_eq : (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w =
          bitsToNatLSB a + bitsToNatLSB b - 2 ^ w := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hmod_eq, show 2 ^ w + (bitsToNatLSB a + bitsToNatLSB b - 2 ^ w) - bitsToNatLSB a =
        bitsToNatLSB b by omega, Nat.mod_eq_of_lt hb_lt]
  have hntb_eq : ∀ u : ℕ, natToBitsLSB w (u % 2 ^ w) = natToBitsLSB w u := fun u => by
    funext i; simp [natToBitsLSB, Nat.testBit_mod_two_pow, i.isLt]
  constructor
  · funext i; by_cases hi : i.1 < w
    · simp [Aux_w54_arith.addInPlaceFn, Aux_w54_arith.subInPlaceFn, hi]
    · simp only [Aux_w54_arith.addInPlaceFn, hi, ↓reduceDIte, ha_s, hb_s]
      have h1 : bitsToNatLSB (natToBitsLSB w (2 ^ w + bitsToNatLSB b - bitsToNatLSB a)) =
          (2 ^ w + bitsToNatLSB b - bitsToNatLSB a) % 2 ^ w := by
        rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
      rw [h1, ← hntb_eq, hmod1, natToBitsLSB_bitsToNatLSB]
      have hie : b ⟨i.1 - w, by omega⟩ = x i := by
        dsimp only [b]; exact congrArg x (Fin.ext (by dsimp; omega))
      exact hie
  · funext i; by_cases hi : i.1 < w
    · simp [Aux_w54_arith.subInPlaceFn, Aux_w54_arith.addInPlaceFn, hi]
    · simp only [Aux_w54_arith.subInPlaceFn, hi, ↓reduceDIte, ha_a, hb_a]
      have h1 : bitsToNatLSB (natToBitsLSB w (bitsToNatLSB a + bitsToNatLSB b)) =
          (bitsToNatLSB a + bitsToNatLSB b) % 2 ^ w := by
        rw [← hntb_eq, bitsToNatLSB_natToBitsLSB (Nat.mod_lt _ (Nat.two_pow_pos w))]
      rw [h1, ← hntb_eq, hmod2, natToBitsLSB_bitsToNatLSB]
      have hie : b ⟨i.1 - w, by omega⟩ = x i := by
        dsimp only [b]; exact congrArg x (Fin.ext (by dsimp; omega))
      exact hie
