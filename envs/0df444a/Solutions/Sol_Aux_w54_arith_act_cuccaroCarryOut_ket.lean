-- Prove2me | solution 1 for Aux_w54_arith.act_cuccaroCarryOut_ket
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:14.853127+00:00
-- url     : https://prove2.me/submissions/b3f0dd47-5a97-4133-913d-6e40c994de4d

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












































































/-! ### Part 3: Equality, Constant Comparison & Particle Encoding -/
































/-! ### Part 4: Recursive Cuccaro In-Place Adder & Unsigned Comparator -/









private lemma act_cuccaroMAJ_ket {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) (z : Qubits m) :
    act (cuccaroMAJ c b a hcb hca hba).unitary (ket z) =
      ket (fun w =>
        if w = c then xor (z c) (z a)
        else if w = b then xor (z b) (z a)
        else if w = a then xor (z a) ((xor (z c) (z a)) && (xor (z b) (z a)))
        else z w) := by
  simp only [cuccaroMAJ, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1; funext w
  by_cases hwc : w = c
  · subst hwc
    simp only [Function.update_self, Function.update_of_ne hca, Function.update_of_ne hcb,
      Function.update_of_ne hca.symm, Function.update_of_ne hcb.symm,
      Function.update_of_ne hba.symm, ↓reduceIte]
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hba, Function.update_of_ne hba.symm,
        Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
        Function.update_of_ne hca.symm, if_neg hwc, ↓reduceIte]
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hca.symm,
          Function.update_of_ne hba.symm,
          Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
          if_neg hwc, if_neg hwb, ↓reduceIte]
      · rw [Function.update_of_ne hwa, Function.update_of_ne hwc, Function.update_of_ne hwb,
          if_neg hwc, if_neg hwb, if_neg hwa]



private lemma bool_maj_carry (va vb vc : Bool) :
    xor va ((xor vc va) && (xor vb va)) =
      decide (2 ≤ (if va then 1 else 0) + (if vb then 1 else 0) + (if vc then 1 else 0)) := by
  cases va <;> cases vb <;> cases vc <;> decide





































@[simp] private lemma cuccaroCarryShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w + 1)) :
    (cuccaroCarryShiftEmb w i).1 =
      if i.1 = 0 then 1 else if i.1 = 1 + 2 * w then 1 + 2 * (w + 1) else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1) + 1))
    else if i.1 = 1 + 2 * w then ⟨1 + 2 * (w + 1), _⟩ else ⟨i.1 + 2, _⟩).1 = _
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
theorem solution (w : ℕ) (cin tgt : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w + 1) := fun u =>
      if h0 : u.1 = 0 then cin
      else if ht : u.1 = 1 + 2 * w then tgt
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let carryBit := decide (2 ^ w ≤ bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0))
    let out : Qubits (1 + 2 * w + 1) := Function.update init ⟨1 + 2 * w, by omega⟩ (xor tgt carryBit)
    act (Aux_w54_arith.cuccaroCarryOut w).unitary (ket init) = ket out := by
  induction w generalizing cin with
  | zero =>
    intro init carryBit out
    simp only [Aux_w54_arith.cuccaroCarryOut, act_cnotGate_ket]
    congr 1; funext u
    have h0 : init ⟨0, by omega⟩ = cin := by dsimp [init]
    have h1 : init ⟨1, by omega⟩ = tgt := by
      dsimp only [init]; rw [dif_neg (by omega), dif_pos rfl]
    have hc : carryBit = cin := by
      dsimp only [carryBit]; simp only [bitsToNatLSB, Finset.univ_eq_empty, Finset.sum_empty,
        pow_zero, zero_add]
      cases cin <;> simp
    have h1_eq : (⟨1 + 2 * 0, by omega⟩ : Fin (1 + 2 * 0 + 1)) = ⟨1, by omega⟩ := rfl
    dsimp only [out]; rw [h1_eq]
    by_cases hu : u = ⟨1, by omega⟩
    · subst hu; rw [Function.update_self, Function.update_self, h0, h1, hc]
    · rw [Function.update_of_ne hu, Function.update_of_ne hu]
  | succ w ih =>
    intro init carryBit out
    dsimp only [Aux_w54_arith.cuccaroCarryOut]
    simp only [LayeredCircuit.seq_unitary, act_mul]
    let c0 : Fin (1 + 2 * (w + 1) + 1) := ⟨0, by omega⟩
    let a0 : Fin (1 + 2 * (w + 1) + 1) := ⟨1, by omega⟩
    let b0 : Fin (1 + 2 * (w + 1) + 1) := ⟨2, by omega⟩
    let tW : Fin (1 + 2 * (w + 1) + 1) := ⟨1 + 2 * (w + 1), by omega⟩
    have hc0_v : c0.1 = 0 := rfl
    have ha0_v : a0.1 = 1 := rfl
    have hb0_v : b0.1 = 2 := rfl
    have htW_v : tW.1 = 1 + 2 * (w + 1) := rfl
    let maj0 := Aux_w54_arith.cuccaroMAJ c0 b0 a0 (Fin.ne_of_val_ne (by omega))
      (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
    have hc_init : init c0 = cin := by dsimp [init, c0]
    have ha_init : init a0 = a 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
      exact congrArg a (Fin.ext (by dsimp; omega))
    have hb_init : init b0 = b 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
      exact congrArg b (Fin.ext (by dsimp; omega))
    let a' : Qubits w := fun i => a i.succ
    let b' : Qubits w := fun i => b i.succ
    let cin' := decide (2 ≤ (if a 0 then 1 else 0) + (if b 0 then 1 else 0) + (if cin then 1 else 0))
    let z1 : Qubits (1 + 2 * (w + 1) + 1) := fun u =>
      if u = c0 then xor cin (a 0)
      else if u = b0 then xor (b 0) (a 0)
      else if u = a0 then cin'
      else init u
    have hmaj : act maj0.unitary (ket init) = ket z1 := by
      dsimp only [maj0]; rw [act_cuccaroMAJ_ket]; congr 1; funext u
      rw [hc_init, ha_init, hb_init]
      by_cases huc : u = c0
      · simp [z1, huc]
      · by_cases hub : u = b0
        · simp [z1, hub]
        · by_cases hua : u = a0
          · simp [z1, hua, cin', bool_maj_carry]
          · simp [z1, huc, hub, hua]
    have hcarry_eq : carryBit =
        decide (2 ^ w ≤ bitsToNatLSB a' + bitsToNatLSB b' + (if cin' then 1 else 0)) := by
      have ha_s : bitsToNatLSB a = 2 * bitsToNatLSB a' + (if a 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if a i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if a' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [a']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      have hb_s : bitsToNatLSB b = 2 * bitsToNatLSB b' + (if b 0 then 1 else 0) := by
        simp only [bitsToNatLSB, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero]
        have hs : (∑ i : Fin w, if b i.succ then 2 ^ (i.1 + 1) else 0) =
            2 * ∑ i : Fin w, if b' i then 2 ^ i.1 else 0 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [b']; split_ifs <;> simp [pow_succ']
        rw [hs]; omega
      dsimp only [carryBit]
      rw [ha_s, hb_s, pow_succ', Bool.eq_iff_iff]
      simp only [decide_eq_true_eq]
      cases hax : a 0 <;> cases hbx : b 0 <;> cases hcx : cin <;> simp [cin', hax, hbx, hcx] <;> omega
    let emb := Aux_w54_arith.cuccaroCarryShiftEmb w
    have hih := ih cin' a' b'
    dsimp only at hih
    have hz1_comp : z1 ∘ emb = fun u : Fin (1 + 2 * w + 1) =>
        if h0 : u.1 = 0 then cin'
        else if ht : u.1 = 1 + 2 * w then tgt
        else if hm : (u.1 - 1) % 2 = 0 then a' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
        else b' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
      funext u
      dsimp only [Function.comp_apply]
      by_cases hu0 : u.1 = 0
      · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
        rw [he, dif_pos hu0]
        dsimp only [z1]
        rw [if_neg (Fin.ne_of_val_ne (by omega)),
          if_neg (Fin.ne_of_val_ne (by omega)), if_pos rfl]
      · rw [dif_neg hu0]
        by_cases hut : u.1 = 1 + 2 * w
        · have he : emb u = tW := Fin.ext (by simp [emb, tW, hut])
          rw [he, dif_pos hut]
          dsimp only [z1]
          rw [if_neg (Fin.ne_of_val_ne (by omega)),
            if_neg (Fin.ne_of_val_ne (by omega)),
            if_neg (Fin.ne_of_val_ne (by omega))]
          dsimp only [init]; rw [dif_neg (by omega), dif_pos (by omega)]
        · rw [dif_neg hut]
          have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0, hut]
          have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
          have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
          have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
          dsimp only [z1]; rw [if_neg hnc, if_neg hnb, if_neg hna]
          dsimp only [init, a', b']
          rw [dif_neg (by omega), dif_neg (by omega)]
          have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
          have hdiv : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
          by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
          · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
          · exact absurd (hmod.mp hp1) hp2
          · exact absurd (hmod.mpr hp2) hp1
          · rw [dif_neg hp1, dif_neg hp2]; exact congrArg b (Fin.ext (by dsimp [Fin.succ]; omega))
    let z2 := Function.update z1 tW (xor tgt carryBit)
    have hmid : act ((Aux_w54_arith.cuccaroCarryOut w).mapWires emb).unitary (ket z1) = ket z2 := by
      refine act_mapWires_ket (Aux_w54_arith.cuccaroCarryOut w) emb z1 _ (by rw [hz1_comp]; exact hih) z2 ?_ ?_
      · funext u
        dsimp only [Function.comp_apply]
        by_cases hu0 : u.1 = 0
        · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
          have hne : a0 ≠ tW := Fin.ne_of_val_ne (by omega)
          have hne' : u ≠ ⟨1 + 2 * w, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
          rw [he]; dsimp only [z2]; rw [Function.update_of_ne hne, Function.update_of_ne hne']
          rw [← he]
          exact congrFun hz1_comp u
        · by_cases hut : u.1 = 1 + 2 * w
          · have he : emb u = tW := Fin.ext (by simp [emb, tW, hut])
            have hu_eq : u = ⟨1 + 2 * w, by omega⟩ := Fin.ext hut
            rw [he, hu_eq]; dsimp only [z2]; rw [Function.update_self, Function.update_self, hcarry_eq]
          · have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0, hut]
            have hne1 : emb u ≠ tW := Fin.ne_of_val_ne (by omega)
            have hne2 : u ≠ ⟨1 + 2 * w, by omega⟩ := Fin.ne_of_val_ne (by dsimp; omega)
            dsimp only [z2]; rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
            exact congrFun hz1_comp u
      · intro u hu
        have hne_t : u ≠ tW := fun heq => hu ⟨⟨1 + 2 * w, by omega⟩, by
          apply Fin.ext; simp [emb, heq, tW]⟩
        dsimp only [z2]; rw [Function.update_of_ne hne_t]
    have hmaj_uses : maj0.UsesOnly {c0, b0, a0} := by
      refine LayeredCircuit.seq_usesOnly
        ((cnotGate_usesOnly a0 b0 (Fin.ne_of_val_ne (by omega))).mono
          (by intro x hx; simp at hx ⊢; tauto))
        (LayeredCircuit.seq_usesOnly ?_ (toffoliOn_usesOnly c0 b0 a0
          (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))
          (Fin.ne_of_val_ne (by omega))))
      exact (cnotGate_usesOnly a0 c0 (Fin.ne_of_val_ne (by omega))).mono
        (by intro x hx; simp at hx ⊢; tauto)
    have hnot_tW : tW ∉ ({c0, b0, a0} : Finset (Fin (1 + 2 * (w + 1) + 1))) := by
      intro hmem; simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h | h <;> have hv := congrArg Fin.val h <;> omega
    have hupd_adj := act_ket_update_of_not_mem maj0 hmaj_uses tW hnot_tW hmaj (xor tgt carryBit)
    have hadj_z2 : act maj0.adj.unitary (ket z2) = ket out := by
      have hz2_eq : z2 = Function.update z1 tW (xor tgt carryBit) := rfl
      rw [hz2_eq, ← hupd_adj, ← act_mul, LayeredCircuit.adj_unitary,
        Matrix.mem_unitaryGroup_iff'.mp maj0.unitary_mem_unitaryGroup, act_one]
    rw [hmaj, hmid, hadj_z2]
