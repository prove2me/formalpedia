-- Prove2me | solution 1 for Aux_w54_arith.act_cuccaroCore_ket
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:43:15.790885+00:00
-- url     : https://prove2.me/submissions/4e7b453b-568f-4958-9c16-1cad3a272af0

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

private lemma act_cuccaroUMA_ket {m : ℕ} (c b a : Fin m)
    (hcb : c ≠ b) (hca : c ≠ a) (hba : b ≠ a) (z : Qubits m) :
    act (cuccaroUMA c b a hcb hca hba).unitary (ket z) =
      ket (fun w =>
        let a1 := xor (z a) (z c && z b)
        let c1 := xor (z c) a1
        if w = c then c1
        else if w = b then xor (z b) c1
        else if w = a then a1
        else z w) := by
  simp only [cuccaroUMA, LayeredCircuit.seq_unitary, act_mul, act_cnotGate_ket, act_toffoliOn_ket]
  congr 1; funext w
  by_cases hwc : w = c
  · subst hwc
    simp only [Function.update_self, Function.update_of_ne hcb, Function.update_of_ne hcb.symm,
      Function.update_of_ne hca, Function.update_of_ne hba, ↓reduceIte]
  · by_cases hwb : w = b
    · subst hwb
      simp only [Function.update_self, Function.update_of_ne hba,
        Function.update_of_ne hcb.symm,
        Function.update_of_ne hca, if_neg hwc, ↓reduceIte]
    · by_cases hwa : w = a
      · subst hwa
        simp only [Function.update_self, Function.update_of_ne hwc, Function.update_of_ne hwb,
          Function.update_of_ne hca,
          Function.update_of_ne hba,
          Function.update_of_ne hcb.symm,
          if_neg hwc, if_neg hwb, ↓reduceIte]
      · rw [Function.update_of_ne hwb, Function.update_of_ne hwc, Function.update_of_ne hwa,
          if_neg hwc, if_neg hwb, if_neg hwa]

private lemma bool_maj_carry (va vb vc : Bool) :
    xor va ((xor vc va) && (xor vb va)) =
      decide (2 ≤ (if va then 1 else 0) + (if vb then 1 else 0) + (if vc then 1 else 0)) := by
  cases va <;> cases vb <;> cases vc <;> decide





@[simp] private lemma cuccaroShiftEmb_val (w : ℕ) (i : Fin (1 + 2 * w)) :
    (cuccaroShiftEmb w i).1 = if i.1 = 0 then 1 else i.1 + 2 := by
  change (if i.1 = 0 then (⟨1, _⟩ : Fin (1 + 2 * (w + 1))) else ⟨i.1 + 2, _⟩).1 = _
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
theorem solution (w : ℕ) (cin : Bool) (a b : Qubits w) :
    let init : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else b ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    let sNat := bitsToNatLSB a + bitsToNatLSB b + (if cin then 1 else 0)
    let sout := natToBitsLSB w sNat
    let out : Qubits (1 + 2 * w) := fun u =>
      if h0 : u.1 = 0 then cin
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
    act (Aux_w54_arith.cuccaroCore w).unitary (ket init) = ket out := by
  induction w generalizing cin with
  | zero =>
    intro init sNat sout out
    simp only [Aux_w54_arith.cuccaroCore, LayeredCircuit.id_unitary, act_one]
    congr 1; funext u
    simp [init, out]
  | succ w ih =>
    intro init sNat sout out
    dsimp only [Aux_w54_arith.cuccaroCore]
    simp only [LayeredCircuit.seq_unitary, act_mul]
    let c0 : Fin (1 + 2 * (w + 1)) := ⟨0, by omega⟩
    let a0 : Fin (1 + 2 * (w + 1)) := ⟨1, by omega⟩
    let b0 : Fin (1 + 2 * (w + 1)) := ⟨2, by omega⟩
    have hc0_v : c0.1 = 0 := rfl
    have ha0_v : a0.1 = 1 := rfl
    have hb0_v : b0.1 = 2 := rfl
    have hc_init : init c0 = cin := by dsimp [init, c0]
    have ha_init : init a0 = a 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_pos (by omega)]
      exact congrArg a (Fin.ext (by dsimp; omega))
    have hb_init : init b0 = b 0 := by
      dsimp only [init]; rw [dif_neg (by omega), dif_neg (by omega)]
      exact congrArg b (Fin.ext (by dsimp; omega))
    let a' : Qubits w := fun i => a i.succ
    let b' : Qubits w := fun i => b i.succ
    let cin' := decide (2 ≤ (if a 0 then 1 else 0) + (if b 0 then 1 else 0) + (if cin then 1 else 0))
    let z1 : Qubits (1 + 2 * (w + 1)) := fun u =>
      if u = c0 then xor cin (a 0)
      else if u = b0 then xor (b 0) (a 0)
      else if u = a0 then cin'
      else init u
    have hmaj : act (Aux_w54_arith.cuccaroMAJ c0 b0 a0 (Fin.ne_of_val_ne (by omega))
        (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega))).unitary (ket init) =
        ket z1 := by
      rw [act_cuccaroMAJ_ket]
      congr 1; funext u
      rw [hc_init, ha_init, hb_init]
      by_cases huc : u = c0
      · simp [z1, huc]
      · by_cases hub : u = b0
        · simp [z1, hub]
        · by_cases hua : u = a0
          · simp [z1, hua, cin', bool_maj_carry]
          · simp [z1, huc, hub, hua]
    have hih := ih cin' a' b'
    dsimp only at hih
    let emb := Aux_w54_arith.cuccaroShiftEmb w
    have hz1_comp : z1 ∘ emb = fun u : Fin (1 + 2 * w) =>
        if h0 : u.1 = 0 then cin'
        else if hm : (u.1 - 1) % 2 = 0 then a' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
        else b' ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ := by
      funext u
      dsimp only [Function.comp_apply]
      by_cases hu0 : u.1 = 0
      · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
        rw [he, dif_pos hu0]
        dsimp only [z1]
        have h1 : a0 ≠ c0 := Fin.ne_of_val_ne (by omega)
        have h2 : a0 ≠ b0 := Fin.ne_of_val_ne (by omega)
        rw [if_neg h1, if_neg h2, if_pos rfl]
      · rw [dif_neg hu0]
        have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0]
        have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
        have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
        have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
        dsimp only [z1]; rw [if_neg hnc, if_neg hnb, if_neg hna]
        dsimp only [init, a', b']
        rw [dif_neg (by omega)]
        have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
        have hdiv : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
        by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
        · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
        · exact absurd (hmod.mp hp1) hp2
        · exact absurd (hmod.mpr hp2) hp1
        · rw [dif_neg hp1, dif_neg hp2]; exact congrArg b (Fin.ext (by dsimp [Fin.succ]; omega))
    let sNat' := bitsToNatLSB a' + bitsToNatLSB b' + (if cin' then 1 else 0)
    let sout' := natToBitsLSB w sNat'
    let z2 : Qubits (1 + 2 * (w + 1)) := fun u =>
      if hc : u = c0 then xor cin (a 0)
      else if hb : u = b0 then xor (b 0) (a 0)
      else if ha : u = a0 then cin'
      else if hm : (u.1 - 1) % 2 = 0 then a ⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩
      else sout' ⟨(u.1 - 1) / 2 - 1, by
        have hu3 : 3 ≤ u.1 := by
          by_contra hlt
          have : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 := by omega
          rcases this with h | h | h
          · exact hc (Fin.ext h)
          · exact ha (Fin.ext h)
          · exact hb (Fin.ext h)
        have := u.isLt; omega⟩
    have hmid : act ((Aux_w54_arith.cuccaroCore w).mapWires emb).unitary (ket z1) = ket z2 := by
      refine act_mapWires_ket (Aux_w54_arith.cuccaroCore w) emb z1 _ (by rw [hz1_comp]; exact hih) z2 ?_ ?_
      · funext u
        dsimp only [Function.comp_apply]
        by_cases hu0 : u.1 = 0
        · have he : emb u = a0 := Fin.ext (by simp [emb, a0, hu0])
          rw [he, dif_pos hu0]
          dsimp only [z2]
          rw [dif_neg (Fin.ne_of_val_ne (by omega)),
            dif_neg (Fin.ne_of_val_ne (by omega)), dif_pos rfl]
        · rw [dif_neg hu0]
          have hev : (emb u).1 = u.1 + 2 := by simp [emb, hu0]
          have hnc : emb u ≠ c0 := Fin.ne_of_val_ne (by omega)
          have hnb : emb u ≠ b0 := Fin.ne_of_val_ne (by omega)
          have hna : emb u ≠ a0 := Fin.ne_of_val_ne (by omega)
          dsimp only [z2]; rw [dif_neg hnc, dif_neg hnb, dif_neg hna]
          have hmod : ((emb u).1 - 1) % 2 = 0 ↔ (u.1 - 1) % 2 = 0 := by omega
          have hdiv1 : ((emb u).1 - 1) / 2 = (u.1 - 1) / 2 + 1 := by omega
          have hdiv2 : ((emb u).1 - 1) / 2 - 1 = (u.1 - 1) / 2 := by omega
          by_cases hp1 : ((emb u).1 - 1) % 2 = 0 <;> by_cases hp2 : (u.1 - 1) % 2 = 0
          · rw [dif_pos hp1, dif_pos hp2]; exact congrArg a (Fin.ext (by dsimp [Fin.succ]; omega))
          · exact absurd (hmod.mp hp1) hp2
          · exact absurd (hmod.mpr hp2) hp1
          · rw [dif_neg hp1, dif_neg hp2]; exact congrArg sout' (Fin.ext (by dsimp; omega))
      · intro u hu
        have hu_le2 : u.1 = 0 ∨ u.1 = 2 := by
          by_contra h
          have hne0 : u.1 ≠ 0 := fun h0 => h (Or.inl h0)
          have hne2 : u.1 ≠ 2 := fun h2 => h (Or.inr h2)
          by_cases hu1 : u.1 = 1
          · exact hu ⟨0, Fin.ext (by simp [emb, hu1])⟩
          · exact hu ⟨⟨u.1 - 2, by have := u.isLt; omega⟩,
              Fin.ext (by simp [emb, show u.1 - 2 ≠ 0 by omega]; omega)⟩
        rcases hu_le2 with h0 | h2
        · have huc : u = c0 := Fin.ext h0
          rw [huc]; simp [z1, z2]
        · have hub : u = b0 := Fin.ext h2
          rw [hub]; simp [z1, z2]
    have hsNat_eq : sNat = 2 * sNat' + (if xor (xor (a 0) (b 0)) cin then 1 else 0) := by
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
      dsimp only [sNat, sNat']
      rw [ha_s, hb_s]
      cases hax : a 0 <;> cases hbx : b 0 <;> cases hcx : cin <;> simp [cin', hax, hbx, hcx] <;> omega
    have hsout0 : sout 0 = xor (xor (a 0) (b 0)) cin := by
      simp only [sout, natToBitsLSB, Fin.val_zero, Nat.testBit_zero]
      rw [hsNat_eq]
      cases xor (xor (a 0) (b 0)) cin <;> simp
    have hsout_succ : ∀ i : Fin w, sout i.succ = sout' i := fun i => by
      simp only [sout, sout', natToBitsLSB, Fin.val_succ]
      rw [hsNat_eq, Nat.testBit_succ]
      have hdiv2 : (2 * sNat' + (if xor (xor (a 0) (b 0)) cin then 1 else 0)) / 2 = sNat' := by
        split_ifs <;> omega
      rw [hdiv2]
    rw [hmaj, hmid, act_cuccaroUMA_ket]
    congr 1; funext u
    have hbc : b0 ≠ c0 := Fin.ne_of_val_ne (by omega)
    have hac : a0 ≠ c0 := Fin.ne_of_val_ne (by omega)
    have hab : a0 ≠ b0 := Fin.ne_of_val_ne (by omega)
    have hz2_c : z2 c0 = xor cin (a 0) := by simp [z2]
    have hz2_b : z2 b0 = xor (b 0) (a 0) := by simp [z2, hbc]
    have hz2_a : z2 a0 = cin' := by simp [z2, hac, hab]
    have hcin' : cin' = xor (a 0) (xor cin (a 0) && xor (b 0) (a 0)) := (bool_maj_carry (a 0) (b 0) cin).symm
    have huma_a : xor (z2 a0) (z2 c0 && z2 b0) = a 0 := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    have huma_c : xor (z2 c0) (xor (z2 a0) (z2 c0 && z2 b0)) = cin := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    have huma_b : xor (z2 b0) (xor (z2 c0) (xor (z2 a0) (z2 c0 && z2 b0))) =
        xor (xor (a 0) (b 0)) cin := by
      rw [hz2_a, hz2_c, hz2_b, hcin']
      cases a 0 <;> cases b 0 <;> cases cin <;> rfl
    by_cases huc : u = c0
    · subst huc; rw [if_pos rfl, huma_c]; dsimp [out, c0]
    · rw [if_neg huc]
      by_cases hub : u = b0
      · subst hub; rw [if_pos rfl, huma_b]
        dsimp only [out]; rw [dif_neg (by omega), dif_neg (by omega)]
        have hb0_idx : (⟨(b0.1 - 1) / 2, by have := b0.isLt; omega⟩ : Fin (w + 1)) = 0 :=
          Fin.ext (by dsimp; omega)
        rw [hb0_idx, hsout0]
      · rw [if_neg hub]
        by_cases hua : u = a0
        · subst hua; rw [if_pos rfl, huma_a]
          dsimp only [out]; rw [dif_neg (by omega), dif_pos (by omega)]
          exact congrArg a (Fin.ext (by dsimp; omega))
        · rw [if_neg hua]
          have hge3 : 3 ≤ u.1 := by
            by_contra h; have h1 : u.1 = 0 ∨ u.1 = 1 ∨ u.1 = 2 := by omega
            rcases h1 with h | h | h
            · exact huc (Fin.ext h)
            · exact hua (Fin.ext h)
            · exact hub (Fin.ext h)
          have hu0 : u.1 ≠ 0 := by omega
          dsimp only [z2, out]
          rw [dif_neg huc, dif_neg hub, dif_neg hua, dif_neg hu0]
          by_cases hm : (u.1 - 1) % 2 = 0
          · rw [dif_pos hm, dif_pos hm]
          · rw [dif_neg hm, dif_neg hm]
            have hidx_eq : (⟨(u.1 - 1) / 2, by have := u.isLt; omega⟩ : Fin (w + 1)) =
                Fin.succ ⟨(u.1 - 1) / 2 - 1, by have := u.isLt; omega⟩ := by
              apply Fin.ext; dsimp [Fin.succ]; omega
            rw [hidx_eq, hsout_succ]
