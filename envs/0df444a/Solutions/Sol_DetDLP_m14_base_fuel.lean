-- Prove2me | solution 1 for DetDLP.m14_base_fuel
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T08:16:07.092948+00:00
-- url     : https://prove2.me/submissions/4b6a8201-8579-46aa-81a7-4048a3c9bce1

import Definitions.Def_DetDLP_D4SoloPlanDefs

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace DetDLP.M14BaseFuelInternal

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

noncomputable section







private theorem coeff_polynomial_eq (bs : List Bool) (i : ℕ) :
    (DetDLP_M13A_IrredHermite.polynomial ℤ bs).coeff i =
      if h : i < bs.length then ((bs.reverse[i]'(by simpa using h)).toNat : ℤ) else 0 := by
  induction bs generalizing i with
  | nil => simp [DetDLP_M13A_IrredHermite.polynomial]
  | cons b bs ih =>
    rw [DetDLP_M13A_IrredHermite.polynomial, coeff_add, coeff_C_mul_X_pow, ih i]
    by_cases hlt : i < bs.length
    · have hlt' : i < (b :: bs).length := Nat.lt_succ_of_lt hlt
      rw [dif_pos hlt, dif_pos hlt']
      split_ifs with he
      · omega
      · rw [zero_add]; congr 1
        simp only [List.reverse_cons]
        rw [List.getElem_append_left (by simp [hlt])]
    · by_cases heq : i = bs.length
      · subst heq
        have hlt' : bs.length < (b :: bs).length := Nat.lt_succ_self _
        rw [dif_neg hlt, dif_pos hlt']
        split_ifs with he
        · rw [add_zero]; congr 1
          simp only [List.reverse_cons]
          rw [List.getElem_append_right (by simp)]
          simp
        · exact False.elim (by omega)
      · have hnot : ¬(i < (b :: bs).length) := by simp; omega
        have hne1 : i ≠ bs.length := heq
        have hne2 : bs.length ≠ i := Ne.symm heq
        rw [dif_neg hlt, dif_neg hnot]
        simp [hne1]

theorem findIrredPoly_eq_cons {κ : ℕ} (hκ : 0 < κ) :
    ∃ ys : List Bool, ys.length = κ ∧ DetDLP_M13A_IrredHermite.findIrredPoly κ = true :: ys := by
  have hm := (DetDLP.m13a_irred_poly_machine.2.1 κ hκ).2.1
  have hne : DetDLP_M13A_IrredHermite.findIrredPoly κ ≠ [] := by
    intro he
    rw [he, DetDLP_M13A_IrredHermite.polynomial] at hm
    simp at hm
    omega
  unfold DetDLP_M13A_IrredHermite.findIrredPoly DetDLP_M13A_IrredHermite.search at hne ⊢
  generalize hopt :
    (((DetDLP_M13A_IrredHermite.candidates (List.range κ) (List.range (2 ^ κ))).map (true :: ·)).find?
      (DetDLP_M13A_IrredHermite.passes (List.range κ) (List.range (2 ^ κ)))) = opt
  cases opt with
  | none => rw [hopt] at hne; exact False.elim (hne rfl)
  | some val =>
    have hmem := List.mem_of_find?_eq_some hopt
    simp only [List.mem_map, DetDLP_M13A_IrredHermite.candidates, DetDLP_M13A_IrredHermite.word] at hmem
    obtain ⟨ys, ⟨mask, _, rfl⟩, rfl⟩ := hmem
    exact ⟨_, by simp, rfl⟩

theorem soloPoly_monic {S : ℕ} (hL : 1 ≤ D3Stopped.level S) : (soloPoly S).Monic :=
  (DetDLP.m13a_irred_poly_machine.2.1 _ (Nat.mul_pos (by decide) hL)).1

theorem soloPoly_natDegree {S : ℕ} (hL : 1 ≤ D3Stopped.level S) :
    (soloPoly S).natDegree = 4 * Nat.clog 2 S :=
  (DetDLP.m13a_irred_poly_machine.2.1 _ (Nat.mul_pos (by decide) hL)).2.1

theorem soloPoly_coeff_01 (S i : ℕ) : (soloPoly S).coeff i = 0 ∨ (soloPoly S).coeff i = 1 := by
  unfold soloPoly
  rw [coeff_polynomial_eq]
  split_ifs with h
  · cases ((DetDLP_M13A_IrredHermite.findIrredPoly (4 * D3Stopped.level S)).reverse[i]'(by simpa using h)) <;> simp
  · simp

theorem soloPoly_ringOK {S : ℕ} (hL : 1 ≤ D3Stopped.level S) : RingOK (soloPoly S) :=
  ⟨by rw [soloPoly_natDegree hL]; exact Nat.mul_pos (by decide) hL,
   (DetDLP.m13a_irred_poly_machine.2.1 _ (Nat.mul_pos (by decide) hL)).2.2,
   fun i _ => soloPoly_coeff_01 S i⟩

theorem polynomialBits_findIrredPoly {κ : ℕ} (hκ : 0 < κ) :
    ((DetDLP_M13A_IrredHermite.findIrredPoly κ).reverse).take κ =
      polynomialBits (DetDLP_M13A_IrredHermite.polynomial ℤ (DetDLP_M13A_IrredHermite.findIrredPoly κ)) := by
  obtain ⟨ys, hlen, hcons⟩ := findIrredPoly_eq_cons hκ
  have hdeg : (DetDLP_M13A_IrredHermite.polynomial ℤ (true :: ys)).natDegree = κ := by
    rw [← hcons]
    exact (DetDLP.m13a_irred_poly_machine.2.1 κ hκ).2.1
  rw [hcons]
  unfold polynomialBits
  apply List.ext_getElem
  · simp [hlen, hdeg]
  · intro i hi₁ hi₂
    have hi_ys : i < ys.length := by
      simp only [List.length_take, List.reverse_cons, List.length_append, List.length_reverse,
        List.length_singleton, hlen] at hi₁
      omega
    have hi_full : i < (true :: ys).length := by simp [hlen]; omega
    simp only [List.getElem_take, List.getElem_ofFn]
    rw [coeff_polynomial_eq (true :: ys) i, dif_pos hi_full]
    simp only [List.reverse_cons]
    rw [List.getElem_append_left (by simpa using hi_ys)]
    cases ys.reverse[i]'(by simpa using hi_ys) <;> rfl

theorem input_field_0 {C c : ℕ} (x : Input C c) :
    D4Slice.field 0 (D4Plan.input x) = x.desc := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_1 {C c : ℕ} (x : Input C c) :
    D4Slice.field 1 (D4Plan.input x) = x.G.encode := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_2 {C c : ℕ} (x : Input C c) :
    D4Slice.field 2 (D4Plan.input x) = countWord x.b := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_3 {C c : ℕ} (x : Input C c) :
    D4Slice.field 3 (D4Plan.input x) = countWord x.m := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_4 {C c : ℕ} (x : Input C c) :
    D4Slice.field 4 (D4Plan.input x) = countWord x.k := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_5 {C c : ℕ} (x : Input C c) :
    D4Slice.field 5 (D4Plan.input x) = countWord x.S := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_6 {C c : ℕ} (x : Input C c) :
    D4Slice.field 6 (D4Plan.input x) = countWord x.p := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_7 {C c : ℕ} (x : Input C c) :
    D4Slice.field 7 (D4Plan.input x) = countWord x.l := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

theorem input_field_8 {C c : ℕ} (x : Input C c) :
    D4Slice.field 8 (D4Plan.input x) = List.ofFn (fun v : Fin x.G.nV => decide (v ∈ x.spec.lookupVerts)) := by
  simp [D4Plan.input, encodeTerminalBTNInstance, D4Slice.field]

private theorem filter_id_replicate_true (n : ℕ) :
    ((List.replicate n true).filter id).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.filter_cons]
    simp

private theorem filter_id_replicate_false (n : ℕ) :
    ((List.replicate n false).filter id).length = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.filter_cons]
    simp

private theorem pow2Level4_eq (S : ℕ) :
    pow2Level4 S = 2 ^ (4 * D3Stopped.level S) := by
  unfold pow2Level4
  dsimp only [letFun]
  calc (2 ^ D3Stopped.level S * 2 ^ D3Stopped.level S) *
        (2 ^ D3Stopped.level S * 2 ^ D3Stopped.level S)
      = (2 ^ D3Stopped.level S) ^ 4 := by ring
    _ = 2 ^ (D3Stopped.level S * 4) := (pow_mul 2 (D3Stopped.level S) 4).symm
    _ = 2 ^ (4 * D3Stopped.level S) := by rw [mul_comm]

theorem fBitsRaw_eq_polynomialBits {C c : ℕ} (x : Input C c) (hL : 1 ≤ D3Stopped.level x.S) (A : ℕ)
    (h4L : 4 * D3Stopped.level x.S ≤ (polyUnits A (D4Plan.input x)).length)
    (hpow : pow2Level4 x.S ≤ (polyUnits A (D4Plan.input x)).length) :
    fBitsRaw A (D4Plan.input x) = polynomialBits (soloPoly x.S) := by
  have hmod : modInput A (D4Plan.input x) =
      List.replicate (4 * D3Stopped.level x.S) true ++ List.replicate (pow2Level4 x.S) false := by
    unfold modInput
    dsimp only [letFun]
    rw [input_field_5, num_countWord,
      unaryFuelRep_eq _ _ true h4L, unaryFuelRep_eq _ _ false hpow]
  have hflt : ((modInput A (D4Plan.input x)).filter id).length = 4 * D3Stopped.level x.S := by
    rw [hmod, List.filter_append, List.length_append,
      filter_id_replicate_true, filter_id_replicate_false, Nat.add_zero]
  have hlen : 2 ^ (4 * D3Stopped.level x.S) ≤ (modInput A (D4Plan.input x)).length := by
    rw [hmod, List.length_append, List.length_replicate, List.length_replicate, ← pow2Level4_eq]
    exact Nat.le_add_left _ _
  unfold fBitsRaw
  dsimp only [letFun]
  rw [hflt]
  have hirr := DetDLP.m13a_irred_poly_machine.2.2 (modInput A (D4Plan.input x))
  rw [hflt] at hirr
  rw [hirr hlen]
  exact polynomialBits_findIrredPoly (Nat.mul_pos (by decide) hL)

private theorem frame_len_ge (w : List Bool) : w.length ≤ (Encoding.frame w).length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    change w.length + 1 ≤ ((Encoding.frame w).length + 1) + 1
    omega

theorem encodeList_mem_len_le {w : List Bool} {xs : List (List Bool)} (hw : w ∈ xs) :
    w.length ≤ (Encoding.encodeList id xs).length := by
  induction xs with
  | nil => cases hw
  | cons u xs ih =>
    rcases List.mem_cons.mp hw with rfl | hmem
    · change w.length ≤ (true :: (Encoding.frame w ++ Encoding.encodeList id xs)).length
      simp only [List.length_cons, List.length_append]
      have := frame_len_ge w
      omega
    · change w.length ≤ (true :: (Encoding.frame u ++ Encoding.encodeList id xs)).length
      simp only [List.length_cons, List.length_append]
      exact (ih hmem).trans (by omega)

theorem input_nV_le_length {C c : ℕ} (x : Input C c) :
    x.G.nV ≤ (D4Plan.input x).length := by
  have hmem : List.ofFn (fun v : Fin x.G.nV => decide (v ∈ x.spec.lookupVerts)) ∈
      [x.desc, x.G.encode, countWord x.b, countWord x.m, countWord x.k,
       countWord x.S, countWord x.p, countWord x.l,
       List.ofFn (fun v : Fin x.G.nV => decide (v ∈ x.spec.lookupVerts))] := by
    simp
  have hlen := encodeList_mem_len_le hmem
  simpa [D4Plan.input, encodeTerminalBTNInstance] using hlen

theorem input_four_m_k_le {C c : ℕ} (x : Input C c) :
    4 * x.m * x.k ≤ (D4Plan.input x).length := by
  have h1 : x.spec.termSubdivVerts.card ≤ x.G.nV := by
    simpa using Finset.card_le_univ x.spec.termSubdivVerts
  rw [x.spec.card_termSubdiv] at h1
  exact h1.trans (input_nV_le_length x)









theorem clog2_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  cases n with
  | zero => simp
  | succ n =>
    apply Nat.clog_le_of_le_pow
    simpa using (Nat.lt_pow_self (by decide : 1 < 2) (n := n + 1)).le

theorem pow2_clog2_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ Nat.clog 2 n ≤ 2 * n := by
  by_cases h1 : n = 1
  · subst h1; simp
  · have hn2 : 1 < n := by omega
    have hc : 0 < Nat.clog 2 n := Nat.clog_pos (by decide) hn2
    have hlt : 2 ^ (Nat.clog 2 n - 1) < n := by
      by_contra h
      have hle : n ≤ 2 ^ (Nat.clog 2 n - 1) := Nat.le_of_not_lt h
      have := Nat.clog_le_of_le_pow hle
      omega
    have hp : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      conv_lhs => rw [show Nat.clog 2 n = Nat.clog 2 n - 1 + 1 from by omega, pow_succ']
    omega

theorem pow32_clog32_le {n : ℕ} (hn : 2 ≤ n) : 32 ^ Nat.clog 32 n ≤ 32 * n := by
  have hc : 0 < Nat.clog 32 n := Nat.clog_pos (by decide) (by omega)
  have hlt : 32 ^ (Nat.clog 32 n - 1) < n := by
    by_contra h
    have hle : n ≤ 32 ^ (Nat.clog 32 n - 1) := Nat.le_of_not_lt h
    have := Nat.clog_le_of_le_pow hle
    omega
  have hp : 32 ^ Nat.clog 32 n = 32 * 32 ^ (Nat.clog 32 n - 1) := by
    conv_lhs => rw [show Nat.clog 32 n = Nat.clog 32 n - 1 + 1 from by omega, pow_succ']
  omega

theorem pow64_clog32_le {n : ℕ} (hn : 2 ≤ n) : 64 ^ Nat.clog 32 n ≤ (32 * n) ^ 2 := by
  have h32 := pow32_clog32_le hn
  have h2 : 2 ^ Nat.clog 32 n ≤ 32 ^ Nat.clog 32 n := Nat.pow_le_pow_left (by decide) _
  have h64 : 64 ^ Nat.clog 32 n = 2 ^ Nat.clog 32 n * 32 ^ Nat.clog 32 n := by
    rw [← mul_pow]; norm_num
  rw [h64, sq]
  exact Nat.mul_le_mul (h2.trans h32) h32

theorem fuel_bounds {C c : ℕ} (x : Input C c) (K_loc : ℕ) (w : Wd)
    (hw : (D4Plan.input x).length ≤ w.length) :
    let F := (polyUnits (A_fuel C K_loc) w).length
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    4 * x.m * x.k ≤ F ∧
    4 * D3Stopped.level x.S ≤ F ∧
    pow2Level4 x.S ≤ F ∧
    (∀ d, 64 ^ D3Stopped.shift x.S d ≤ F) ∧
    guard + x.p ≤ F ∧
    D4UnrollBudget.budget x.S D (8 * K_loc) ≤ F ∧
    x.l * (4 * D3Stopped.level x.S) ≤ F ∧
    (∀ v₀ : Fin x.G.nV, x.G.deg v₀ ≤ F) := by
  intro F D guard
  let W := w.length + 1
  let B₀ := A_fuel C K_loc + 1
  have hW1 : 1 ≤ W := Nat.succ_pos _
  have hB₀_val : B₀ = 256 * (C + 1) * (K_loc + 1) + 1 := rfl
  have hck_pos : 1 ≤ (C + 1) * (K_loc + 1) := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hB₀_mul_ge : ∀ m ≤ 256, m * ((C + 1) * (K_loc + 1)) ≤ B₀ := by
    intro m hm
    calc m * ((C + 1) * (K_loc + 1)) ≤ 256 * ((C + 1) * (K_loc + 1)) := Nat.mul_le_mul_right _ hm
      _ = 256 * (C + 1) * (K_loc + 1) := (Nat.mul_assoc 256 (C + 1) (K_loc + 1)).symm
      _ ≤ B₀ := by rw [hB₀_val]; omega
  have hB₀_const : ∀ m ≤ 256, m ≤ B₀ := fun m hm =>
    (Nat.le_mul_of_pos_right m hck_pos).trans (hB₀_mul_ge m hm)
  have hB₀_pos : 0 < B₀ := by rw [hB₀_val]; exact Nat.succ_pos _
  have hB₀_ge2 : 2 ≤ B₀ := hB₀_const 2 (by decide)
  have hF : F = B₀ ^ 16 * W ^ 16 := by
    simp only [F, W, B₀, polyUnits_length, mul_pow]
  have hpow_le : ∀ a₁ b₁ e : ℕ, e ≤ 16 →
      a₁ ≤ B₀ ^ 16 → b₁ ≤ W ^ e → a₁ * b₁ ≤ F := by
    intro a₁ b₁ e he ha hb
    rw [hF]
    exact Nat.mul_le_mul ha (hb.trans (Nat.pow_le_pow_right hW1 he))
  have hB16_ge : ∀ a e : ℕ, a ≤ B₀ → e ≤ 16 → a ^ e ≤ B₀ ^ 16 := fun a e ha he =>
    (Nat.pow_le_pow_left ha e).trans (Nat.pow_le_pow_right hB₀_pos he)
  have hCK_le : C + 1 ≤ (C + 1) * (K_loc + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hKC_le : K_loc + 1 ≤ (C + 1) * (K_loc + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have h2C_B : 2 * (C + 1) ≤ B₀ :=
    (Nat.mul_le_mul_left 2 hCK_le).trans (hB₀_mul_ge 2 (by decide))
  have hC_B : C + 1 ≤ B₀ := (by omega : C + 1 ≤ 2 * (C + 1)).trans h2C_B
  have hmk : 4 * x.m * x.k ≤ W := (input_four_m_k_le x).trans (by omega)
  have hm_le : x.m ≤ W :=
    (calc x.m = 1 * x.m * 1 := by ring
      _ ≤ 4 * x.m * x.k := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide)) x.hk).trans hmk
  have hxb : x.b ≤ (C + 1) * W := by
    calc x.b ≤ C * (4 * x.m * x.k) := x.lower
      _ ≤ (C + 1) * W := Nat.mul_le_mul (Nat.le_succ C) hmk
  have hS : x.S ≤ (C + 1) ^ 2 * W ^ 2 := by
    calc x.S ≤ C * x.m * x.b := x.hS
      _ ≤ (C + 1) * W * ((C + 1) * W) := Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ C) hm_le) hxb
      _ = (C + 1) ^ 2 * W ^ 2 := by ring
  have hS_pos : 1 ≤ x.S := x.hp.trans x.pS
  have h2L : 2 ^ D3Stopped.level x.S ≤ 2 * x.S := by
    unfold D3Stopped.level; exact pow2_clog2_le hS_pos
  have h2S : 2 * x.S ≤ (2 * (C + 1)) ^ 2 * W ^ 2 := by
    calc 2 * x.S ≤ 2 * ((C + 1) ^ 2 * W ^ 2) := Nat.mul_le_mul_left 2 hS
      _ ≤ 4 * ((C + 1) ^ 2 * W ^ 2) := Nat.mul_le_mul_right _ (by decide)
      _ = (2 * (C + 1)) ^ 2 * W ^ 2 := by ring
  have h4m_ge : 2 ≤ 4 * x.m := by have := x.hm; omega
  have h64D : 64 ^ D ≤ B₀ ^ 2 * W ^ 2 := by
    have h1d : 64 ^ D ≤ (32 * (4 * x.m)) ^ 2 := pow64_clog32_le h4m_ge
    have h2d : 32 * (4 * x.m) ≤ B₀ * W := by
      have : 128 ≤ B₀ := hB₀_const 128 (by decide)
      calc 32 * (4 * x.m) = 128 * x.m := by ring
        _ ≤ B₀ * W := Nat.mul_le_mul this hm_le
    exact h1d.trans (by rw [← mul_pow]; exact Nat.pow_le_pow_left h2d 2)
  have h2D : 2 ^ D ≤ B₀ ^ 2 * W ^ 2 :=
    (Nat.pow_le_pow_left (by decide : 2 ≤ 64) D).trans h64D
  have h2L_M : 2 ^ D3Stopped.level x.S ≤ (2 * (C + 1)) ^ 2 * W ^ 2 := h2L.trans h2S
  have hA_le : localAllowance x.S D ≤ B₀ ^ 9 * W ^ 6 := by
    unfold localAllowance
    have hsh1 : D3Stopped.shift x.S D + 1 ≤ 2 * x.S := by
      have := (D4SoloStep.shift_le_level_solo x.S D).trans (clog2_le_self x.S)
      dsimp only [D3Stopped.level] at *
      omega
    have h2sh : 2 ^ D3Stopped.shift x.S D ≤ (2 * (C + 1)) ^ 2 * W ^ 2 :=
      (Nat.pow_le_pow_right (by decide) (D4SoloStep.shift_le_level_solo x.S D)).trans h2L_M
    have hS1 : x.S + 1 ≤ 2 * x.S := by omega
    have h40 : 40 ≤ B₀ ^ 3 := by
      have : 40 ≤ B₀ := hB₀_const 40 (by decide)
      exact this.trans (by
        calc B₀ = B₀ ^ 1 := (pow_one B₀).symm
          _ ≤ B₀ ^ 3 := Nat.pow_le_pow_right hB₀_pos (by decide))
    have hcoeff : 40 * (2 * (C + 1)) ^ 6 ≤ B₀ ^ 9 := by
      calc 40 * (2 * (C + 1)) ^ 6 ≤ B₀ ^ 3 * B₀ ^ 6 := Nat.mul_le_mul h40 (Nat.pow_le_pow_left h2C_B 6)
        _ = B₀ ^ 9 := by ring
    calc 40 * (x.S + 1) * (D3Stopped.shift x.S D + 1) * 2 ^ D3Stopped.shift x.S D
        ≤ 40 * ((2 * (C + 1)) ^ 2 * W ^ 2) * ((2 * (C + 1)) ^ 2 * W ^ 2) *
            ((2 * (C + 1)) ^ 2 * W ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 40 (hS1.trans h2S)) (hsh1.trans h2S)) h2sh
      _ = (40 * (2 * (C + 1)) ^ 6) * W ^ 6 := by ring
      _ ≤ B₀ ^ 9 * W ^ 6 := Nat.mul_le_mul_right _ hcoeff
  have hguard_le : guard ≤ B₀ ^ 11 * W ^ 8 := by
    unfold guard totalGuard
    calc localAllowance x.S D * 64 ^ D ≤ (B₀ ^ 9 * W ^ 6) * (B₀ ^ 2 * W ^ 2) := Nat.mul_le_mul hA_le h64D
      _ = B₀ ^ 11 * W ^ 8 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hmk.trans (by
      simpa using hpow_le 1 W 1 (by decide) (Nat.one_le_pow 16 B₀ hB₀_pos) (by simp))
  · have h4L : 4 * D3Stopped.level x.S ≤ (2 * (C + 1)) ^ 2 * W ^ 2 := by
      have := clog2_le_self x.S
      dsimp only [D3Stopped.level] at *
      calc 4 * Nat.clog 2 x.S ≤ 4 * x.S := Nat.mul_le_mul_left 4 this
        _ ≤ 4 * ((C + 1) ^ 2 * W ^ 2) := Nat.mul_le_mul_left 4 hS
        _ = (2 * (C + 1)) ^ 2 * W ^ 2 := by ring
    exact h4L.trans (hpow_le _ _ 2 (by decide) (hB16_ge _ 2 h2C_B (by decide)) le_rfl)
  · unfold pow2Level4
    have h4 : (2 ^ D3Stopped.level x.S * 2 ^ D3Stopped.level x.S) *
        (2 ^ D3Stopped.level x.S * 2 ^ D3Stopped.level x.S) ≤
        ((2 * (C + 1)) ^ 2 * W ^ 2) ^ 4 := by
      calc (2 ^ D3Stopped.level x.S * 2 ^ D3Stopped.level x.S) *
            (2 ^ D3Stopped.level x.S * 2 ^ D3Stopped.level x.S)
          = (2 ^ D3Stopped.level x.S) ^ 4 := by ring
        _ ≤ ((2 * (C + 1)) ^ 2 * W ^ 2) ^ 4 := Nat.pow_le_pow_left h2L_M 4
    have h4eq : ((2 * (C + 1)) ^ 2 * W ^ 2) ^ 4 = (2 * (C + 1)) ^ 8 * W ^ 8 := by ring
    rw [h4eq] at h4
    exact h4.trans (hpow_le _ _ 8 (by decide) (hB16_ge _ 8 h2C_B (by decide)) le_rfl)
  · intro d
    have h64sh : 64 ^ D3Stopped.shift x.S d ≤ (2 ^ D3Stopped.level x.S) ^ 6 := by
      have h64_2 : 64 ^ D3Stopped.shift x.S d = (2 ^ D3Stopped.shift x.S d) ^ 6 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h64_2]
      exact Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) (D4SoloStep.shift_le_level_solo x.S d)) 6
    have h6 : (2 ^ D3Stopped.level x.S) ^ 6 ≤ (2 * (C + 1)) ^ 12 * W ^ 12 := by
      calc (2 ^ D3Stopped.level x.S) ^ 6 ≤ ((2 * (C + 1)) ^ 2 * W ^ 2) ^ 6 := Nat.pow_le_pow_left h2L_M 6
        _ = (2 * (C + 1)) ^ 12 * W ^ 12 := by ring
    exact (h64sh.trans h6).trans (hpow_le _ _ 12 (by decide) (hB16_ge _ 12 h2C_B (by decide)) le_rfl)
  · have hgp : guard + x.p ≤ (B₀ ^ 11 + (C + 1) ^ 2) * W ^ 8 := by
      have hpW : x.p ≤ (C + 1) ^ 2 * W ^ 8 := by
        calc x.p ≤ x.S := x.pS
          _ ≤ (C + 1) ^ 2 * W ^ 2 := hS
          _ ≤ (C + 1) ^ 2 * W ^ 8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW1 (by decide))
      calc guard + x.p ≤ B₀ ^ 11 * W ^ 8 + (C + 1) ^ 2 * W ^ 8 := Nat.add_le_add hguard_le hpW
        _ = (B₀ ^ 11 + (C + 1) ^ 2) * W ^ 8 := by ring
    have hC_11 : B₀ ^ 11 + (C + 1) ^ 2 ≤ B₀ ^ 16 := by
      have hB_ge1 : 1 ≤ B₀ := hB₀_pos
      have h12 : (C + 1) ^ 2 ≤ B₀ ^ 2 := Nat.pow_le_pow_left hC_B 2
      have hB2 : B₀ ^ 2 ≤ B₀ ^ 11 := Nat.pow_le_pow_right hB_ge1 (by decide)
      have hB16 : 2 * B₀ ^ 11 ≤ B₀ ^ 16 := by
        have hB5 : 2 ≤ B₀ ^ 5 := by
          calc 2 ≤ B₀ := hB₀_ge2
            _ = B₀ ^ 1 := (pow_one B₀).symm
            _ ≤ B₀ ^ 5 := Nat.pow_le_pow_right hB_ge1 (by decide)
        calc 2 * B₀ ^ 11 ≤ B₀ ^ 5 * B₀ ^ 11 := Nat.mul_le_mul_right _ hB5
          _ = B₀ ^ 16 := by ring
      omega
    exact hgp.trans (hpow_le _ _ 8 (by decide) hC_11 le_rfl)
  · unfold D4UnrollBudget.budget
    have h1 : 8 * (D3Stopped.level x.S + 1) * 64 ^ D ≤ 8 * ((2 * (C + 1)) ^ 2 * W ^ 2) * (B₀ ^ 2 * W ^ 2) := by
      have hL1 : D3Stopped.level x.S + 1 ≤ 2 * x.S := by
        have := clog2_le_self x.S; dsimp only [D3Stopped.level]; omega
      exact Nat.mul_le_mul (Nat.mul_le_mul_left 8 (hL1.trans h2S)) h64D
    have h2 : (2 * (8 * K_loc) * (2 ^ D - 1) * x.S) / max 1 (D3Stopped.width x.S D).sqrt ≤
        16 * (K_loc + 1) * (B₀ ^ 2 * W ^ 2) * ((C + 1) ^ 2 * W ^ 2) := by
      refine (Nat.div_le_self _ _).trans ?_
      have h2D' : 2 ^ D - 1 ≤ B₀ ^ 2 * W ^ 2 := (Nat.sub_le _ _).trans h2D
      have hK_le : 2 * (8 * K_loc) ≤ 16 * (K_loc + 1) := by omega
      exact Nat.mul_le_mul (Nat.mul_le_mul hK_le h2D') hS
    have hsum : 8 * (D3Stopped.level x.S + 1) * 64 ^ D +
        (2 * (8 * K_loc) * (2 ^ D - 1) * x.S) / max 1 (D3Stopped.width x.S D).sqrt ≤
        (8 * (2 * (C + 1)) ^ 2 * B₀ ^ 2 + 16 * (K_loc + 1) * B₀ ^ 2 * (C + 1) ^ 2) * W ^ 4 := by
      calc 8 * (D3Stopped.level x.S + 1) * 64 ^ D +
            (2 * (8 * K_loc) * (2 ^ D - 1) * x.S) / max 1 (D3Stopped.width x.S D).sqrt
          ≤ 8 * ((2 * (C + 1)) ^ 2 * W ^ 2) * (B₀ ^ 2 * W ^ 2) +
              16 * (K_loc + 1) * (B₀ ^ 2 * W ^ 2) * ((C + 1) ^ 2 * W ^ 2) := Nat.add_le_add h1 h2
        _ = (8 * (2 * (C + 1)) ^ 2 * B₀ ^ 2 + 16 * (K_loc + 1) * B₀ ^ 2 * (C + 1) ^ 2) * W ^ 4 := by ring
    have hB_bd : 8 * (2 * (C + 1)) ^ 2 * B₀ ^ 2 + 16 * (K_loc + 1) * B₀ ^ 2 * (C + 1) ^ 2 ≤ B₀ ^ 16 := by
      have h1a : 8 * (2 * (C + 1)) ^ 2 * B₀ ^ 2 ≤ B₀ * B₀ ^ 2 * B₀ ^ 2 := by
        have h8 : 8 ≤ B₀ := hB₀_const 8 (by decide)
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul h8 (Nat.pow_le_pow_left h2C_B 2))
      have h2a : 16 * (K_loc + 1) * B₀ ^ 2 * (C + 1) ^ 2 ≤ B₀ * B₀ ^ 2 * B₀ ^ 2 := by
        have h16K : 16 * (K_loc + 1) ≤ B₀ :=
          (Nat.mul_le_mul_left 16 hKC_le).trans (hB₀_mul_ge 16 (by decide))
        have hC2 : (C + 1) ^ 2 ≤ B₀ ^ 2 := Nat.pow_le_pow_left hC_B 2
        exact Nat.mul_le_mul (Nat.mul_le_mul h16K (le_refl _)) hC2
      have hB11 : 2 ≤ B₀ ^ 11 := by
        calc 2 ≤ B₀ := hB₀_ge2
          _ = B₀ ^ 1 := (pow_one B₀).symm
          _ ≤ B₀ ^ 11 := Nat.pow_le_pow_right hB₀_pos (by decide)
      calc 8 * (2 * (C + 1)) ^ 2 * B₀ ^ 2 + 16 * (K_loc + 1) * B₀ ^ 2 * (C + 1) ^ 2
          ≤ B₀ * B₀ ^ 2 * B₀ ^ 2 + B₀ * B₀ ^ 2 * B₀ ^ 2 := Nat.add_le_add h1a h2a
        _ = 2 * B₀ ^ 5 := by ring
        _ ≤ B₀ ^ 11 * B₀ ^ 5 := Nat.mul_le_mul_right _ hB11
        _ = B₀ ^ 16 := by ring
    exact hsum.trans (hpow_le _ _ 4 (by decide) hB_bd le_rfl)
  · have hl_le : x.l * (4 * D3Stopped.level x.S) ≤ (4 * (C + 1) ^ 3) * W ^ 3 := by
      have hlm : x.l ≤ (C + 1) * W := x.lm.trans (Nat.mul_le_mul (Nat.le_succ C) hm_le)
      have hL : 4 * D3Stopped.level x.S ≤ 4 * (C + 1) ^ 2 * W ^ 2 := by
        calc 4 * D3Stopped.level x.S ≤ 4 * x.S := Nat.mul_le_mul_left 4 (clog2_le_self x.S)
          _ ≤ 4 * ((C + 1) ^ 2 * W ^ 2) := Nat.mul_le_mul_left 4 hS
          _ = 4 * (C + 1) ^ 2 * W ^ 2 := by ring
      calc x.l * (4 * D3Stopped.level x.S) ≤ ((C + 1) * W) * (4 * (C + 1) ^ 2 * W ^ 2) := Nat.mul_le_mul hlm hL
        _ = (4 * (C + 1) ^ 3) * W ^ 3 := by ring
    have h4C3 : 4 * (C + 1) ^ 3 ≤ B₀ ^ 16 := by
      have h4 : 4 ≤ B₀ := hB₀_const 4 (by decide)
      have hB4 : 4 * (C + 1) ^ 3 ≤ B₀ * B₀ ^ 3 :=
        Nat.mul_le_mul h4 (Nat.pow_le_pow_left hC_B 3)
      exact hB4.trans (by
        calc B₀ * B₀ ^ 3 = B₀ ^ 4 := by ring
          _ ≤ B₀ ^ 16 := Nat.pow_le_pow_right hB₀_pos (by decide))
    exact hl_le.trans (hpow_le _ _ 3 (by decide) h4C3 le_rfl)
  · intro v₀
    have hdeg_le : x.G.deg v₀ ≤ 3 * x.S := by
      have h1 : x.G.deg v₀ ≤ x.G.nE := by
        unfold BipartiteMultigraph.deg BipartiteMultigraph.ports
        exact (List.length_filter_le _ _).trans (by simp)
      exact h1.trans (DetDLP.m14a_separator_edge_budget x.spec).2
    have h3S : 3 * x.S ≤ (3 * (C + 1) ^ 2) * W ^ 2 :=
      (Nat.mul_le_mul_left 3 hS).trans_eq (by ring)
    have h3 : 3 ≤ B₀ := hB₀_const 3 (by decide)
    have h3C2 : 3 * (C + 1) ^ 2 ≤ B₀ ^ 16 := by
      calc 3 * (C + 1) ^ 2 ≤ B₀ * B₀ ^ 2 := Nat.mul_le_mul h3 (Nat.pow_le_pow_left hC_B 2)
        _ = B₀ ^ 3 := by ring
        _ ≤ B₀ ^ 16 := Nat.pow_le_pow_right hB₀_pos (by decide)
    exact hdeg_le.trans (h3S.trans (hpow_le _ _ 2 (by decide) h3C2 le_rfl))



end
end DetDLP.M14BaseFuelInternal

open Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloPlanDefs
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∀ {S : ℕ}, 1 ≤ D3Stopped.level S →
      (soloPoly S).Monic ∧ (soloPoly S).natDegree = 4 * Nat.clog 2 S ∧ RingOK (soloPoly S)) ∧
    (∀ (S i : ℕ), (soloPoly S).coeff i = 0 ∨ (soloPoly S).coeff i = 1) ∧
    (∀ {C c : ℕ} (x : Input C c),
      D4Slice.field 0 (D4Plan.input x) = x.desc ∧
      D4Slice.field 1 (D4Plan.input x) = x.G.encode ∧
      D4Slice.field 2 (D4Plan.input x) = countWord x.b ∧
      D4Slice.field 3 (D4Plan.input x) = countWord x.m ∧
      D4Slice.field 4 (D4Plan.input x) = countWord x.k ∧
      D4Slice.field 5 (D4Plan.input x) = countWord x.S ∧
      D4Slice.field 6 (D4Plan.input x) = countWord x.p ∧
      D4Slice.field 7 (D4Plan.input x) = countWord x.l ∧
      D4Slice.field 8 (D4Plan.input x) = List.ofFn (fun v : Fin x.G.nV => decide (v ∈ x.spec.lookupVerts))) ∧
    (∀ {C c : ℕ} (x : Input C c), 1 ≤ D3Stopped.level x.S → ∀ (A : ℕ),
      4 * D3Stopped.level x.S ≤ (polyUnits A (D4Plan.input x)).length →
      pow2Level4 x.S ≤ (polyUnits A (D4Plan.input x)).length →
      fBitsRaw A (D4Plan.input x) = polynomialBits (soloPoly x.S)) ∧
    (∀ {w : List Bool} {xs : List (List Bool)}, w ∈ xs → w.length ≤ (Encoding.encodeList id xs).length) ∧
    (∀ n : ℕ, Nat.clog 2 n ≤ n) ∧
    (∀ {n : ℕ}, 1 ≤ n → 2 ^ Nat.clog 2 n ≤ 2 * n) ∧
    (∀ {n : ℕ}, 2 ≤ n → 64 ^ Nat.clog 32 n ≤ (32 * n) ^ 2) ∧
    (∀ {C c : ℕ} (x : Input C c) (K_loc : ℕ) (w : Wd),
      (D4Plan.input x).length ≤ w.length →
      let F := (polyUnits (A_fuel C K_loc) w).length
      let D := Nat.clog 32 (4 * x.m)
      let guard := totalGuard x.S D
      4 * x.m * x.k ≤ F ∧
      4 * D3Stopped.level x.S ≤ F ∧
      pow2Level4 x.S ≤ F ∧
      (∀ d, 64 ^ D3Stopped.shift x.S d ≤ F) ∧
      guard + x.p ≤ F ∧
      D4UnrollBudget.budget x.S D (8 * K_loc) ≤ F ∧
      x.l * (4 * D3Stopped.level x.S) ≤ F ∧
      (∀ v₀ : Fin x.G.nV, x.G.deg v₀ ≤ F)) :=
  ⟨fun hL => ⟨DetDLP.M14BaseFuelInternal.soloPoly_monic hL,
      DetDLP.M14BaseFuelInternal.soloPoly_natDegree hL,
      DetDLP.M14BaseFuelInternal.soloPoly_ringOK hL⟩,
   DetDLP.M14BaseFuelInternal.soloPoly_coeff_01,
   fun x => ⟨DetDLP.M14BaseFuelInternal.input_field_0 x,
      DetDLP.M14BaseFuelInternal.input_field_1 x,
      DetDLP.M14BaseFuelInternal.input_field_2 x,
      DetDLP.M14BaseFuelInternal.input_field_3 x,
      DetDLP.M14BaseFuelInternal.input_field_4 x,
      DetDLP.M14BaseFuelInternal.input_field_5 x,
      DetDLP.M14BaseFuelInternal.input_field_6 x,
      DetDLP.M14BaseFuelInternal.input_field_7 x,
      DetDLP.M14BaseFuelInternal.input_field_8 x⟩,
   fun x hL A h4L hpow => DetDLP.M14BaseFuelInternal.fBitsRaw_eq_polynomialBits x hL A h4L hpow,
   fun hw => DetDLP.M14BaseFuelInternal.encodeList_mem_len_le hw,
   DetDLP.M14BaseFuelInternal.clog2_le_self,
   fun hn => DetDLP.M14BaseFuelInternal.pow2_clog2_le hn,
   fun hn => DetDLP.M14BaseFuelInternal.pow64_clog32_le hn,
   fun x K_loc w hw => DetDLP.M14BaseFuelInternal.fuel_bounds x K_loc w hw⟩
