-- Prove2me | solution 1 for CircuitLowerBound.stClauseCirc
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:04:00.701439+00:00
-- url     : https://prove2.me/submissions/016c659b-14cf-4d54-ad42-d28da6f32c56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_ofWord_lt
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_add
import Theorems.Thm_Groundwork_Unary_mul
import Theorems.Thm_Groundwork_Unary_poly
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork CircuitLowerBound.Blocks CircuitLowerBound.Clause

attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.any
attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.contains
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.decide_mem
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.div_pow
attribute [local fun_prop] Groundwork.PolyT.dropWhile
attribute [local fun_prop] Groundwork.PolyT.elem
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.idxOf
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] Groundwork.PolyT.mul
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.pow_const
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.product
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sprod
attribute [local fun_prop] Groundwork.PolyT.sum
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.takeWhile
attribute [local fun_prop] Groundwork.PolyT.testBit
attribute [local fun_prop] Groundwork.Unary.poly
attribute [local fun_prop] P2M_Groundwork_PolyT_chunks__bc5b8682856d
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_inl__78f4b62d65a1
attribute [local fun_prop] P2M_Groundwork_PolyT_inr__53ca1f30b2d3
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219
attribute [local fun_prop] P2M_Groundwork_PolyT_log2__935ea318e2e8
attribute [local fun_prop] P2M_Groundwork_PolyT_ofWord__0eb069943014
attribute [local fun_prop] P2M_Groundwork_PolyT_size__c8c8eb1b342f
attribute [local fun_prop] P2M_Groundwork_PolyT_some__e6a32bd6af45

/- Supporting proofs from the cited upstream `Circ/Blocks.lean`. -/

namespace CircuitLowerBound.Blocks
open ENP Groundwork

theorem gval_zero (v : ℕ → Bool) (i j : ℕ) : gval v (opZero, i, j) = false := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opZero, hi, hj]

theorem gval_one (v : ℕ → Bool) (i j : ℕ) : gval v (opOne, i, j) = true := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opOne, hi, hj]

theorem gval_and (v : ℕ → Bool) (i j : ℕ) : gval v (opAnd, i, j) = (v i && v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opAnd, hi, hj]

theorem gval_or (v : ℕ → Bool) (i j : ℕ) : gval v (opOr, i, j) = (v i || v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opOr, hi, hj]

theorem gval_xor (v : ℕ → Bool) (i j : ℕ) : gval v (opXor, i, j) = (v i ^^ v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opXor, hi, hj]

theorem gval_fst (v : ℕ → Bool) (i j : ℕ) : gval v (opFst, i, j) = v i := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opFst, hi, hj]

theorem gval_andN (v : ℕ → Bool) (i j : ℕ) : gval v (opAndN, i, j) = (v i && !v j) := by
  cases hi : v i <;> cases hj : v j <;> simp [gval, GateD.toGate, opAndN, hi, hj]


theorem obeys_append (v : ℕ → Bool) (n : ℕ) (C D : List GateD) : Obeys v n (C ++ D) ↔ Obeys v n C ∧ Obeys v (n + C.length) D := by
  induction C generalizing n with
  | nil => simp [Obeys]
  | cons g C ih =>
    simp only [List.cons_append, Obeys, ih, List.length_cons, and_assoc]
    rw [show n + 1 + C.length = n + (C.length + 1) by omega]

theorem wfa_append (n : ℕ) (C D : List GateD) : WFa n (C ++ D) ↔ WFa n C ∧ WFa (n + C.length) D := by
  induction C generalizing n with
  | nil => simp [WFa]
  | cons g C ih =>
    simp only [List.cons_append, WFa, ih, List.length_cons, and_assoc]
    rw [show n + 1 + C.length = n + (C.length + 1) by omega]

theorem length_flatMap_const {α : Type} {k : ℕ} (f : ℕ → List α) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    ((List.range w).flatMap f).length = k * w := by
  induction w with
  | zero => simp
  | succ w ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hf]; ring

theorem obeys_flatMap (v : ℕ → Bool) (n : ℕ) {k : ℕ} (f : ℕ → List GateD) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    Obeys v n ((List.range w).flatMap f) ↔ ∀ i < w, Obeys v (n + k * i) (f i) := by
  induction w with
  | zero => simp [Obeys]
  | succ w ih =>
    rw [List.range_succ, List.flatMap_append, obeys_append, ih, length_flatMap_const f hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h w (by omega)⟩

theorem wfa_flatMap (n : ℕ) {k : ℕ} (f : ℕ → List GateD) (hf : ∀ i, (f i).length = k) (w : ℕ) :
    WFa n ((List.range w).flatMap f) ↔ ∀ i < w, WFa (n + k * i) (f i) := by
  induction w with
  | zero => simp [WFa]
  | succ w ih =>
    rw [List.range_succ, List.flatMap_append, wfa_append, ih, length_flatMap_const f hf]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h w (by omega)⟩

theorem map_eq_flatMap {α : Type} (g : ℕ → α) (w : ℕ) : (List.range w).map g = (List.range w).flatMap fun i => [g i] := by
  induction w with
  | zero => rfl
  | succ w ih => rw [List.range_succ, List.map_append, List.flatMap_append, ih]; rfl

theorem obeys_map (v : ℕ → Bool) (n : ℕ) (g : ℕ → GateD) (w : ℕ) : Obeys v n ((List.range w).map g) ↔ ∀ i < w, v (n + i) = gval v (g i) := by
  rw [map_eq_flatMap, obeys_flatMap v n (k := 1) _ (fun _ => rfl)]
  simp [Obeys]

theorem wfa_map (n : ℕ) (g : ℕ → GateD) (w : ℕ) : WFa n ((List.range w).map g) ↔ ∀ i < w, (g i).2.1 < n + i ∧ (g i).2.2 < n + i := by
  rw [map_eq_flatMap, wfa_flatMap n (k := 1) _ (fun _ => rfl)]
  simp [WFa]

theorem wf_of_wfa {n : ℕ} {C : List GateD} (h : WFa n C) : WF n C := by
  induction C generalizing n with
  | nil => intro t ht; simp at ht
  | cons g C ih =>
    intro t ht
    cases t with
    | zero => simpa using h.1
    | succ t =>
      have := ih h.2 t (by simpa using ht)
      simp only [List.getElem_cons_succ]
      omega

/-! ### The wires of a circuit -/

theorem wires_cons (x : List Bool) (G : Gate) (C : Circuit) : wires x (G :: C) = wires (x ++ [G.op (x.getD G.in₁ false) (x.getD G.in₂ false)]) C := rfl

theorem prefix_wires (x : List Bool) (C : Circuit) : x <+: wires x C := by
  induction C generalizing x with
  | nil => exact List.prefix_rfl
  | cons G C ih => rw [wires_cons]; exact (List.prefix_append _ _).trans (ih _)

theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) : l₂.getD i false = l₁.getD i false := by
  obtain ⟨r, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

/-- The input wires carry the input. -/
theorem wires_input (x : List Bool) (C : Circuit) {i : ℕ} (hi : i < x.length) : (wires x C).getD i false = x.getD i false :=
  getD_of_prefix (prefix_wires x C) hi

/-- The values of the wires of a circuit on an input obey the circuit. -/
theorem obeys_wires (x : List Bool) (C : List GateD) (h : WFa x.length C) : Obeys (fun i => (wires x (toC C)).getD i false) x.length C := by
  induction C generalizing x with
  | nil => trivial
  | cons g C ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e : wires x (toC (g :: C)) = wires (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (toC C) := rfl
    have hl : (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]).length = x.length + 1 := by simp
    have hp := prefix_wires (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (toC C)
    have ih' := ih (x ++ [g.toGate.op (x.getD g.2.1 false) (x.getD g.2.2 false)]) (by rw [hl]; exact h3)
    rw [hl] at ih'
    refine ⟨?_, by rw [e]; exact ih'⟩
    simp only [gval]
    rw [e, getD_of_prefix hp (by omega), getD_of_prefix hp (by omega), getD_of_prefix hp (by omega), List.getD_append _ _ _ _ h1,
      List.getD_append _ _ _ _ h2, List.getD_append_right _ _ _ _ le_rfl]
    simp

/-! ### Chains -/


theorem prevW_succ (off init i : ℕ) : prevW off init (i + 1) = off + i := by simp [prevW]

theorem prevW_lt {off init i : ℕ} (h : init < off) : prevW off init i < off + i := by
  unfold prevW; split_ifs <;> omega

/-- A chain of gates «the wire before, and p i». -/
theorem chain_all (v : ℕ → Bool) (off init len : ℕ) (p : ℕ → Bool) (h : ∀ i < len, v (off + i) = (v (prevW off init i) && p i)) :
    ∀ m ≤ len, v (prevW off init m) = (v init && decide (∀ i < m, p i = true)) := by
  intro m
  induction m with
  | zero => intro _; simp [prevW]
  | succ m ih =>
    intro hm
    rw [prevW_succ, h m hm, ih (by omega), Bool.and_assoc]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h m (by omega)⟩

/-- A chain of gates «the wire before, or p i». -/
theorem chain_any (v : ℕ → Bool) (off init len : ℕ) (p : ℕ → Bool) (h : ∀ i < len, v (off + i) = (v (prevW off init i) || p i)) :
    ∀ m ≤ len, v (prevW off init m) = (v init || decide (∃ i < m, p i = true)) := by
  intro m
  induction m with
  | zero => intro _; simp [prevW]
  | succ m ih =>
    intro hm
    rw [prevW_succ, h m hm, ih (by omega), Bool.or_assoc]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨i, hi, h1⟩ | h2)
      · exact ⟨i, by omega, h1⟩
      · exact ⟨m, by omega, h2⟩
    · rintro ⟨i, hi, h1⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact .inl ⟨i, h, h1⟩
      · exact .inr h1

/-! ### Numbers in binary -/

theorem ofWord_append (l₁ l₂ : List Bool) : ofWord (l₁ ++ l₂) = ofWord l₁ + 2 ^ l₁.length * ofWord l₂ := by
  induction l₁ with
  | nil => simp [ofWord]
  | cons b l ih => simp only [List.cons_append, ofWord, ih, List.length_cons, pow_succ]; ring

theorem num_zero (b : ℕ → Bool) : num b 0 = 0 := rfl

theorem num_succ (b : ℕ → Bool) (w : ℕ) : num b (w + 1) = num b w + 2 ^ w * (b w).toNat := by
  rw [num, List.range_succ, List.map_append, ofWord_append]
  simp [num, ofWord]

theorem num_lt (b : ℕ → Bool) (w : ℕ) : num b w < 2 ^ w := by
  have := ofWord_lt ((List.range w).map b)
  simpa [num] using this

theorem num_congr {b c : ℕ → Bool} {w : ℕ} (h : ∀ i < w, b i = c i) : num b w = num c w := by
  unfold num
  exact congrArg ofWord (List.map_congr_left fun i hi => h i (List.mem_range.1 hi))

theorem num_testBit (x w : ℕ) : num x.testBit w = x % 2 ^ w := by
  induction w with
  | zero => simp [num_zero, Nat.mod_one]
  | succ w ih =>
    rw [num_succ, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ w) with h | h <;> simp [h]

theorem num_false (w : ℕ) : num (fun _ => false) w = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => rw [num_succ, ih]; simp

theorem getD_toWord {n j k : ℕ} (hk : k < n) : (toWord n j).getD k false = j.testBit k := by
  induction n generalizing j k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [toWord, List.getD_cons_zero, Nat.testBit_zero]
    | succ k =>
      simp only [toWord, List.getD_cons_succ]
      rw [ih (by omega), Nat.testBit_succ]

/-- A chain of half adders: s i = a i ⊕ c i, c (i+1) = a i ∧ c i. -/
theorem half_adder (a s c : ℕ → Bool) (w : ℕ) (hs : ∀ i < w, s i = (a i ^^ c i)) (hc : ∀ i < w, c (i + 1) = (a i && c i)) :
    ∀ m ≤ w, num s m + 2 ^ m * (c m).toNat = num a m + (c 0).toNat := by
  intro m
  induction m with
  | zero => intro _; simp [num_zero]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [num_succ, num_succ, hs m hm, hc m hm, pow_succ]
    generalize 2 ^ m = p at h1 ⊢
    generalize c m = cm at h1 ⊢
    cases a m <;> cases cm <;> simp at h1 ⊢ <;> omega

/-- A chain of full adders: s i = a i ⊕ d i ⊕ c i, c (i+1) = (a i ∧ d i) ∨ ((a i ⊕ d i) ∧ c i). -/
theorem full_adder (a d s c : ℕ → Bool) (w : ℕ) (hs : ∀ i < w, s i = ((a i ^^ d i) ^^ c i))
    (hc : ∀ i < w, c (i + 1) = ((a i && d i) || ((a i ^^ d i) && c i))) :
    ∀ m ≤ w, num s m + 2 ^ m * (c m).toNat = num a m + num d m + (c 0).toNat := by
  intro m
  induction m with
  | zero => intro _; simp [num_zero]
  | succ m ih =>
    intro hm
    have h1 := ih (by omega)
    rw [num_succ, num_succ, num_succ, hs m hm, hc m hm, pow_succ]
    generalize 2 ^ m = p at h1 ⊢
    generalize c m = cm at h1 ⊢
    cases a m <;> cases d m <;> cases cm <;> simp at h1 ⊢ <;> omega


end CircuitLowerBound.Blocks

/- Supporting proofs from the cited upstream `Circ/Clause.lean`. -/

namespace CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem length_selG (n bq bt rb R : ℕ) : (selG n bq bt rb R).length = rb * R :=
  length_flatMap_const _ (fun _ => by simp [selChain]) R

theorem length_fldG (n rb kbm nf : ℕ) (tb : List TCl) : (fldG n rb kbm nf tb).length = tb.length * (3 * nf) :=
  length_flatMap_const _ (fun _ => by simp [fldChain]) _

theorem length_timeG (bq bt a m0 m1 : ℕ) : (timeG bq bt a m0 m1).length = 3 * bt + 4 := by
  simp only [timeG, List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt, List.length_cons, List.length_nil]
  omega

theorem length_posG (z bq P b p0 p1 : ℕ) (dW : ℕ → ℕ) : (posG z bq P b p0 p1 dW).length = 7 * (bq + 1) + 1 := by
  simp only [posG, List.length_append, length_flatMap_const (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1), List.length_cons, List.length_nil]
  omega

theorem length_litG (n bq bt rb R kbm Dq P ι : ℕ) : (litG n bq bt rb R kbm Dq P ι).length = szL bq bt := by
  rw [litG, List.length_append, length_timeG, length_posG, szL]
  omega

theorem length_gatesC (n bq bt rb kbm Dq P : ℕ) (tb : List TCl) :
    (gatesC n bq bt rb kbm Dq P tb).length = 2 + rb * tb.length + tb.length * (3 * (5 + kbm + Dq)) + szL bq bt * 3 := by
  simp only [gatesC, List.length_append, length_selG, length_fldG, length_flatMap_const _ (length_litG n bq bt rb tb.length kbm Dq P) 3,
    List.length_cons, List.length_nil]

theorem length_outsL {bq bt kbm L : ℕ} (hL : bq + bt + 2 + kbm ≤ L) (n rb R Dq ι : ℕ) : (outsL n bq bt rb R kbm Dq L ι).length = L + 1 := by
  simp only [outsL, List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
  omega

/-! ### A gate whose function is chosen by a bit that is known when the circuit is written -/

theorem gval_ite (v : ℕ → Bool) (c : Bool) (o₁ o₂ : B4) (i j : ℕ) :
    gval v ((if c then o₁ else o₂), i, j) = if c then gval v (o₁, i, j) else gval v (o₂, i, j) := by
  cases c <;> rfl

/-- A number modulo 4 from its two lowest bits. -/
theorem mod_four (md : ℕ) : md % 4 = (md.testBit 0).toNat + 2 * (md.testBit 1).toNat := by
  have h0 : md.testBit 0 = decide (md % 2 = 1) := Nat.testBit_zero md
  have h1 : md.testBit 1 = decide (md / 2 % 2 = 1) := by rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.testBit_succ, Nat.testBit_zero]
  rw [h0, h1]
  rcases Nat.mod_two_eq_zero_or_one md with a | a <;> rcases Nat.mod_two_eq_zero_or_one (md / 2) with b | b <;> simp [a, b] <;> omega

/-! ### The time -/

theorem timeG_eqs {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) :
    v a = (v m0 ^^ v m1) ∧ v (a + 1) = (v m1 && !v m0) ∧ v (a + 2) = (v m0 && v m1) ∧
    (∀ i < bt, v (a + 3 + 3 * i) = (v a && v (bq + i)) ∧ v (a + 3 + 3 * i + 1) = (v (a + 3 + 3 * i) ^^ v (cinT a i)) ∧
      v (a + 3 + 3 * i + 2) = (v (a + 3 + 3 * i) && v (cinT a i))) ∧
    v (a + 3 + 3 * bt) = (v (cinT a bt) || v (a + 2)) := by
  rw [timeG, obeys_append, obeys_append, obeys_flatMap v _ (k := 3) (timeBit bq a) (fun _ => rfl) bt] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl : a + ([(opXor, m0, m1), (opAndN, m1, m0), (opAnd, m0, m1)] ++ (List.range bt).flatMap (timeBit bq a)).length = a + 3 + 3 * bt := by
    rw [List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [hl] at h3
  simp only [Obeys, gval_xor, gval_andN, gval_and, gval_or, and_true] at h1 h3
  refine ⟨h1.1, h1.2.1, h1.2.2, fun i hi => ?_, h3⟩
  have h4 := h2 i hi
  simp only [timeBit, Obeys, gval_xor, gval_and, and_true, List.length_cons, List.length_nil] at h4
  exact ⟨h4.1, h4.2.1, h4.2.2⟩

/-- The output wires for the time carry the time of the literal. -/
theorem time_val {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) {md t : ℕ} (hm0 : v m0 = md.testBit 0)
    (hm1 : v m1 = md.testBit 1) (ht : ∀ i < bt, v (bq + i) = t.testBit i) (htl : t < 2 ^ bt) :
    num (fun i => v (a + 3 + 3 * i + 1)) bt + 2 ^ bt * (v (a + 3 + 3 * bt)).toNat = tval bt t md := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := timeG_eqs h
  have hadd := half_adder (fun i => v (a + 3 + 3 * i)) (fun i => v (a + 3 + 3 * i + 1)) (fun i => v (cinT a i)) bt
    (fun i hi => (e3 i hi).2.1) (fun i hi => by
      have : cinT a (i + 1) = a + 3 + 3 * i + 2 := by simp [cinT]
      simp only [this]
      exact (e3 i hi).2.2) bt le_rfl
  have hc0 : cinT a 0 = a + 1 := by simp [cinT]
  simp only [hc0] at hadd
  have hA : num (fun i => v (a + 3 + 3 * i)) bt = if v a then t else 0 := by
    cases hu : v a
    · rw [num_congr (c := fun _ => false) fun i hi => by simp [(e3 i hi).1, hu], num_false]; rfl
    · rw [num_congr (c := t.testBit) fun i hi => by simp [(e3 i hi).1, hu, ht i hi], num_testBit, Nat.mod_eq_of_lt htl]; rfl
  rw [hA, e0, e1, hm0, hm1] at hadd
  rw [e4, e2, hm0, hm1]
  have h4 := mod_four md
  have hp : 0 < 2 ^ bt := by positivity
  unfold tval
  generalize num (fun i => v (a + 3 + 3 * i + 1)) bt = S at hadd ⊢
  generalize v (cinT a bt) = cb at hadd ⊢
  generalize 2 ^ bt = p at hadd hp ⊢
  generalize md.testBit 0 = b0 at h4 hadd ⊢
  generalize md.testBit 1 = b1 at h4 hadd ⊢
  generalize md % 4 = m4 at h4 ⊢
  subst h4
  cases b0 <;> cases b1 <;> cases cb <;> simp at hadd ⊢ <;> omega

/-! ### The position -/

theorem posG_eqs {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) :
    v b = (v p0 && !v p1) ∧ ∀ i < bq + 1,
      v (b + 1 + 7 * i) = (v b && v (if i < bq then i else z)) ∧
      v (b + 1 + 7 * i + 1) = (if P.testBit i then (v (b + 1 + 7 * i) || v p1) else v (b + 1 + 7 * i)) ∧
      v (b + 1 + 7 * i + 2) = (v (b + 1 + 7 * i + 1) ^^ v (dW i)) ∧
      v (b + 1 + 7 * i + 3) = (v (b + 1 + 7 * i + 2) ^^ v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 4) = (v (b + 1 + 7 * i + 1) && v (dW i)) ∧
      v (b + 1 + 7 * i + 5) = (v (b + 1 + 7 * i + 2) && v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 6) = (v (b + 1 + 7 * i + 4) || v (b + 1 + 7 * i + 5)) := by
  rw [posG, obeys_append, obeys_flatMap v _ (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1)] at h
  obtain ⟨h1, h2⟩ := h
  simp only [Obeys, gval_andN, and_true] at h1
  refine ⟨h1, fun i hi => ?_⟩
  have h4 := h2 i hi
  simp only [posBit, Obeys, gval_xor, gval_and, gval_or, gval_ite, gval_fst, and_true, List.length_cons, List.length_nil] at h4
  exact ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, h4.2.2.2.2.1, h4.2.2.2.2.2.1, h4.2.2.2.2.2.2⟩

/-- The output wires for the position carry the position of the literal. -/
theorem pos_val {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) {md q dq : ℕ} (hz : v z = false)
    (hp0 : v p0 = md.testBit 0) (hp1 : v p1 = md.testBit 1) (hq : ∀ i < bq, v i = q.testBit i) (hql : q < 2 ^ bq)
    (hd : ∀ i < bq + 1, v (dW i) = dq.testBit i) :
    num (fun i => v (b + 1 + 7 * i + 3)) (bq + 1) = (qval P q md + dq) % 2 ^ (bq + 1) := by
  obtain ⟨e0, e⟩ := posG_eqs h
  have hadd := full_adder (fun i => v (b + 1 + 7 * i + 1)) (fun i => v (dW i)) (fun i => v (b + 1 + 7 * i + 3)) (fun i => v (cinQ z b i)) (bq + 1)
    (fun i hi => by
      obtain ⟨-, -, e2, e3, -⟩ := e i hi
      simp only [e3, e2])
    (fun i hi => by
      obtain ⟨-, -, e2, -, e4, e5, e6⟩ := e i hi
      have : cinQ z b (i + 1) = b + 1 + 7 * i + 6 := by simp [cinQ]
      simp only [this, e6, e4, e5, e2]) (bq + 1) le_rfl
  have hc0 : cinQ z b 0 = z := by simp [cinQ]
  simp only [hc0, hz] at hadd
  have hD : num (fun i => v (dW i)) (bq + 1) = dq % 2 ^ (bq + 1) := by rw [num_congr hd, num_testBit]
  have hqb : ∀ i < bq + 1, v (if i < bq then i else z) = q.testBit i := by
    intro i _
    split_ifs with hi
    · exact hq i hi
    · rw [hz]
      exact (Nat.testBit_eq_false_of_lt (hql.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm
  have hB : num (fun i => v (b + 1 + 7 * i + 1)) (bq + 1) = qval P q md % 2 ^ (bq + 1) := by
    have h4 := mod_four md
    have hb : ∀ i < bq + 1, v (b + 1 + 7 * i + 1) = (((md.testBit 0 && !md.testBit 1) && q.testBit i) || (P.testBit i && md.testBit 1)) := by
      intro i hi
      obtain ⟨e1, e2, -⟩ := e i hi
      rw [e2, e1, e0, hp0, hp1, hqb i hi]
      cases P.testBit i <;> simp
    rw [num_congr hb]
    unfold qval
    generalize md.testBit 0 = b0 at h4 ⊢
    generalize md.testBit 1 = b1 at h4 ⊢
    generalize md % 4 = m4 at h4 ⊢
    subst h4
    cases b0 <;> cases b1 <;> simp [num_false, num_testBit]
  rw [hD, hB] at hadd
  have hlt := num_lt (fun i => v (b + 1 + 7 * i + 3)) (bq + 1)
  rw [Nat.add_mod, ← Nat.add_zero (qval P q md % 2 ^ (bq + 1) + dq % 2 ^ (bq + 1))]
  have h0 : (false : Bool).toNat = 0 := rfl
  rw [h0] at hadd
  rw [← hadd, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-! ### The place in the table -/

/-- The wire «r = k». -/
theorem sel_val {v : ℕ → Bool} {n bq bt rb R : ℕ} (h : Obeys v (n + 2) (selG n bq bt rb R)) (hO : v (n + 1) = true) {r : ℕ}
    (hr : ∀ i < rb, v (bq + bt + i) = r.testBit i) (hrl : r < 2 ^ rb) {k : ℕ} (hk : k < R) (hkl : k < 2 ^ rb) : v (Ew n rb k) = decide (r = k) := by
  rw [selG, obeys_flatMap v _ (k := rb) (selChain n bq bt rb) (fun _ => by simp [selChain]) R] at h
  have h1 := h k hk
  rw [selChain, obeys_map] at h1
  have h2 := chain_all v (n + 2 + rb * k) (n + 1) rb (fun i => decide (r.testBit i = k.testBit i)) (fun i hi => by
    rw [h1 i hi, selGate, gval_ite, gval_and, gval_andN, hr i hi]
    cases k.testBit i <;> cases r.testBit i <;> simp) rb le_rfl
  rw [Ew, h2, hO, Bool.true_and]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · intro h3
    have := num_congr (b := r.testBit) (c := k.testBit) (w := rb) h3
    rwa [num_testBit, num_testBit, Nat.mod_eq_of_lt hrl, Nat.mod_eq_of_lt hkl] at this
  · rintro rfl i _
    rfl

theorem litI_zeroCl (ι : ℕ) : litI zeroCl ι = (0, 0, 0, 0, false) := by
  unfold litI zeroCl
  split_ifs <;> rfl

theorem fbit_zero (kbm ι f : ℕ) : fbit kbm (litI zeroCl ι) f = false := by
  rw [litI_zeroCl]
  unfold fbit
  split_ifs <;> simp

/-- The wire of a bit of what the table says at the place r. -/
theorem fld_val {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {a : ℕ} (ha : a < 3 * nf) :
    v (prevW (n + 2 + rb * tb.length + tb.length * a) n tb.length) = fbit kbm (litI (tb.getD r zeroCl) (a / nf)) (a % nf) := by
  rw [fldG, obeys_flatMap v _ (k := tb.length) (fldChain n rb kbm nf tb) (fun _ => by simp [fldChain]) (3 * nf)] at h
  have h1 := h a ha
  rw [fldChain, obeys_map] at h1
  have h2 := chain_any v (n + 2 + rb * tb.length + tb.length * a) n tb.length
    (fun k => fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) && decide (r = k)) (fun k hk => by
    rw [h1 k hk, fldGate, gval_ite, gval_or, gval_fst, hE k hk]
    cases fbit kbm (litI (tb.getD k zeroCl) (a / nf)) (a % nf) <;> simp) tb.length le_rfl
  rw [h2, hZ, Bool.false_or]
  by_cases hr : r < tb.length
  · rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨k, -, h3, rfl⟩
      exact h3
    · intro h3
      exact ⟨r, hr, h3, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega), fbit_zero]
    simp only [decide_eq_false_iff_not, Bool.and_eq_true, decide_eq_true_eq, not_exists, not_and]
    intro k hk _ hrk
    omega

/-- The wire of bit f of literal ι. -/
theorem Fw_val {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {ι f : ℕ} (hι : ι < 3) (hf : f < nf) :
    v (Fw n rb tb.length nf ι f) = fbit kbm (litI (tb.getD r zeroCl) ι) f := by
  have ha : ι * nf + f < 3 * nf := by nlinarith
  have h1 := fld_val h hZ hE ha
  have e1 : (ι * nf + f) / nf = ι := by rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hf, Nat.add_zero]
  have e2 : (ι * nf + f) % nf = f := by rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hf]
  rw [e1, e2] at h1
  exact h1

/-! ### Every gate reads earlier wires -/

theorem wfa_timeG {bq bt a m0 m1 : ℕ} (h0 : m0 < a) (h1 : m1 < a) (hin : bq + bt ≤ a) : WFa a (timeG bq bt a m0 m1) := by
  rw [timeG, wfa_append, wfa_append, wfa_flatMap _ (k := 3) (timeBit bq a) (fun _ => rfl) bt]
  refine ⟨⟨?_, fun i hi => ?_⟩, ?_⟩
  · simp only [WFa, and_true]
    and_intros <;> omega
  · simp only [timeBit, WFa, cinT, and_true, List.length_cons, List.length_nil]
    split_ifs <;> and_intros <;> omega
  · rw [List.length_append, length_flatMap_const (k := 3) (timeBit bq a) (fun _ => rfl) bt]
    simp only [WFa, cinT, and_true, List.length_cons, List.length_nil]
    split_ifs <;> and_intros <;> omega

theorem wfa_posG {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h0 : p0 < b) (h1 : p1 < b) (hz : z < b) (hin : bq ≤ b) (hd : ∀ i, dW i < b) :
    WFa b (posG z bq P b p0 p1 dW) := by
  rw [posG, wfa_append, wfa_flatMap _ (k := 7) (posBit z bq P b p1 dW) (fun _ => rfl) (bq + 1)]
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [WFa, and_true]
    and_intros <;> omega
  · have := hd i
    simp only [posBit, WFa, cinQ, and_true, List.length_cons, List.length_nil]
    split_ifs <;> and_intros <;> omega

theorem wfa_selG {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R : ℕ) : WFa (n + 2) (selG n bq bt rb R) := by
  rw [selG, wfa_flatMap _ (k := rb) (selChain n bq bt rb) (fun _ => by simp [selChain]) R]
  intro k _
  rw [selChain, wfa_map]
  intro i hi
  exact ⟨prevW_lt (by omega), by simp only [selGate]; omega⟩

theorem Ew_lt (n rb : ℕ) {R k : ℕ} (hk : k < R) : Ew n rb k < n + 2 + rb * R := by
  have h1 : Ew n rb k < n + 2 + rb * k + rb := prevW_lt (by omega)
  have h2 : rb * (k + 1) ≤ rb * R := Nat.mul_le_mul_left _ hk
  rw [Nat.mul_succ] at h2
  omega

theorem wfa_fldG (n rb kbm nf : ℕ) (tb : List TCl) : WFa (n + 2 + rb * tb.length) (fldG n rb kbm nf tb) := by
  rw [fldG, wfa_flatMap _ (k := tb.length) (fldChain n rb kbm nf tb) (fun _ => by simp [fldChain]) (3 * nf)]
  intro a _
  rw [fldChain, wfa_map]
  intro k hk
  have := Ew_lt n rb hk
  exact ⟨prevW_lt (by omega), by simp only [fldGate]; omega⟩

theorem Fw_lt (n rb R : ℕ) {nf ι f : ℕ} (hι : ι < 3) (hf : f < nf) : Fw n rb R nf ι f < n + 2 + rb * R + R * (3 * nf) := by
  have h1 : Fw n rb R nf ι f < n + 2 + rb * R + R * (ι * nf + f) + R := prevW_lt (by omega)
  have h2 : R * (ι * nf + f + 1) ≤ R * (3 * nf) := Nat.mul_le_mul_left _ (by nlinarith)
  rw [Nat.mul_succ] at h2
  omega

theorem offA_ge (n bq bt rb R nf ι : ℕ) : n + 2 + rb * R + R * (3 * nf) ≤ offA n bq bt rb R nf ι := Nat.le_add_right _ _

theorem dWire_lt (n rb R kbm Dq : ℕ) {ι : ℕ} (hι : ι < 3) (i : ℕ) : dWire n rb R kbm Dq ι i < n + 2 + rb * R + R * (3 * (5 + kbm + Dq)) := by
  unfold dWire
  split_ifs with h
  · exact Fw_lt n rb R hι (by omega)
  · omega

theorem wfa_litG {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R kbm Dq P : ℕ) {ι : ℕ} (hι : ι < 3) :
    WFa (offA n bq bt rb R (5 + kbm + Dq) ι) (litG n bq bt rb R kbm Dq P ι) := by
  have hg := offA_ge n bq bt rb R (5 + kbm + Dq) ι
  have f0 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 0) hι (by omega)
  have f1 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 1) hι (by omega)
  have f2 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 2) hι (by omega)
  have f3 := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 3) hι (by omega)
  rw [litG, wfa_append, length_timeG]
  refine ⟨wfa_timeG (by omega) (by omega) (by omega), ?_⟩
  rw [show offA n bq bt rb R (5 + kbm + Dq) ι + (3 * bt + 4) = offA n bq bt rb R (5 + kbm + Dq) ι + 4 + 3 * bt by omega]
  exact wfa_posG (by omega) (by omega) (by omega) (by omega) fun i => by have := dWire_lt n rb R kbm Dq hι i; omega

theorem wfa_gatesC {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (h1 : 1 ≤ n) (kbm Dq P : ℕ) (tb : List TCl) : WFa n (gatesC n bq bt rb kbm Dq P tb) := by
  rw [gatesC, wfa_append, wfa_append, wfa_append, wfa_flatMap _ (k := szL bq bt) _ (length_litG n bq bt rb tb.length kbm Dq P) 3]
  refine ⟨⟨⟨?_, wfa_selG hn _⟩, ?_⟩, fun ι hι => ?_⟩
  · simp only [WFa, and_true]
    and_intros <;> omega
  · have e : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length).length = n + 2 + rb * tb.length := by
      rw [List.length_append, length_selG]
      simp only [List.length_cons, List.length_nil]
      omega
    rw [e]
    exact wfa_fldG n rb kbm _ tb
  · have e : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb).length + szL bq bt * ι =
        offA n bq bt rb tb.length (5 + kbm + Dq) ι := by
      rw [List.length_append, List.length_append, length_selG, length_fldG, offA]
      simp only [List.length_cons, List.length_nil]
      omega
    rw [e]
    exact wfa_litG hn _ kbm Dq P hι

/-- The output wires are wires of the circuit. -/
theorem outsL_lt (n bq bt rb R kbm Dq L : ℕ) {ι : ℕ} (hι : ι < 3) :
    ∀ w ∈ outsL n bq bt rb R kbm Dq L ι, w < n + (2 + rb * R + R * (3 * (5 + kbm + Dq)) + szL bq bt * 3) := by
  have h1 : offA n bq bt rb R (5 + kbm + Dq) ι + szL bq bt ≤ n + 2 + rb * R + R * (3 * (5 + kbm + Dq)) + szL bq bt * 3 := by
    have : szL bq bt * (ι + 1) ≤ szL bq bt * 3 := Nat.mul_le_mul_left _ hι
    rw [Nat.mul_succ] at this
    unfold offA
    omega
  intro w hw
  simp only [outsL, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hw
  unfold szL at h1 ⊢
  rcases hw with ((((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | rfl) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | rfl
  · omega
  · omega
  · omega
  · have := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 5 + i) hι (by omega)
    omega
  · omega
  · have := Fw_lt n rb R (nf := 5 + kbm + Dq) (f := 4) hι (by omega)
    omega

/-! ### What the output wires carry -/

theorem fbit_kind {kbm i : ℕ} (l : TLit) (h : i < kbm) : fbit kbm l (5 + i) = l.1.testBit i := by
  unfold fbit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  omega

theorem fbit_dq (kbm i : ℕ) (l : TLit) : fbit kbm l (5 + kbm + i) = l.2.2.2.1.testBit i := by
  unfold fbit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/-- The values of the output wires of literal ι, for the clause number j. -/
theorem core_val {n bq bt rb kbm Dq L P : ℕ} {tb : List TCl} (hn : n = rb + bt + bq) (hbt : 1 ≤ bt) (hR : tb.length < 2 ^ rb) (hL : bq + bt + 2 + kbm ≤ L)
    (hD : ∀ k ι i, Dq ≤ i → i < bq + 1 → (litI (tb.getD k zeroCl) ι).2.2.2.1.testBit i = false) {j : ℕ} (hj : j < 2 ^ n) {ι : ℕ} (hι : ι < 3)
    (v : ℕ → Bool) (hv : v = fun i => (wires (toWord n j) (toC (gatesC n bq bt rb kbm Dq P tb))).getD i false)
    (l : TLit) (hl : l = litI (tb.getD (j / 2 ^ (bt + bq)) zeroCl) ι) :
    ofWord (((outsL n bq bt rb tb.length kbm Dq L ι).take L).map v) =
      ((l.1 % 2 ^ kbm) * 2 ^ (bt + 1) + tval bt (j / 2 ^ bq % 2 ^ bt) l.2.1) * 2 ^ (bq + 1) + (qval P (j % 2 ^ bq) l.2.2.1 + l.2.2.2.1) % 2 ^ (bq + 1) ∧
    v ((outsL n bq bt rb tb.length kbm Dq L ι).getD L 0) = l.2.2.2.2 := by
  have hx : (toWord n j).length = n := length_toWord n j
  have hwf : WFa n (gatesC n bq bt rb kbm Dq P tb) := wfa_gatesC (by omega) (by omega) kbm Dq P tb
  have hob : Obeys v n (gatesC n bq bt rb kbm Dq P tb) := by
    have := obeys_wires (toWord n j) (gatesC n bq bt rb kbm Dq P tb) (by rw [hx]; exact hwf)
    rw [hx] at this
    rw [hv]
    exact this
  have hin : ∀ k < n, v k = j.testBit k := by
    intro k hk
    rw [hv]
    simp only
    rw [wires_input _ _ (by rw [hx]; exact hk), getD_toWord hk]
  rw [gatesC, obeys_append, obeys_append, obeys_append, obeys_flatMap v _ (k := szL bq bt) _ (length_litG n bq bt rb tb.length kbm Dq P) 3] at hob
  obtain ⟨⟨⟨hc, hsel⟩, hfld⟩, hlit⟩ := hob
  have e1 : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length).length = n + 2 + rb * tb.length := by
    rw [List.length_append, length_selG]
    simp only [List.length_cons, List.length_nil]
    omega
  have e2 : n + ([(opZero, 0, 0), (opOne, 0, 0)] ++ selG n bq bt rb tb.length ++ fldG n rb kbm (5 + kbm + Dq) tb).length + szL bq bt * ι =
      offA n bq bt rb tb.length (5 + kbm + Dq) ι := by
    rw [List.length_append, List.length_append, length_selG, length_fldG, offA]
    simp only [List.length_cons, List.length_nil]
    omega
  rw [e1] at hfld
  have hlit' := hlit ι hι
  rw [e2, litG, obeys_append, length_timeG,
    show offA n bq bt rb tb.length (5 + kbm + Dq) ι + (3 * bt + 4) = offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt by omega] at hlit'
  obtain ⟨htime, hpos⟩ := hlit'
  simp only [Obeys, gval_zero, gval_one, and_true] at hc
  obtain ⟨hZ, hO⟩ := hc
  -- the three parts of j
  have hrl : j / 2 ^ (bt + bq) < 2 ^ rb := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← Nat.add_assoc, ← hn]
    exact hj
  have hrb : ∀ i < rb, v (bq + bt + i) = (j / 2 ^ (bt + bq)).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_div_two_pow, Nat.add_comm bq bt, Nat.add_comm i]
  have htb : ∀ i < bt, v (bq + i) = (j / 2 ^ bq % 2 ^ bt).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm i]
    simp [hi]
  have hqb : ∀ i < bq, v i = (j % 2 ^ bq).testBit i := by
    intro i hi
    rw [hin _ (by omega), Nat.testBit_mod_two_pow]
    simp [hi]
  have hE : ∀ k < tb.length, v (Ew n rb k) = decide (j / 2 ^ (bt + bq) = k) := fun k hk => sel_val hsel hO hrb hrl hk (hk.trans hR)
  have hF : ∀ f < 5 + kbm + Dq, v (Fw n rb tb.length (5 + kbm + Dq) ι f) = fbit kbm l f := fun f hf => by
    rw [hl]
    exact Fw_val hfld hZ hE hι hf
  have hT := time_val htime (md := l.2.1) (t := j / 2 ^ bq % 2 ^ bt) (by rw [hF 0 (by omega)]; rfl) (by rw [hF 1 (by omega)]; rfl) htb
    (Nat.mod_lt _ (by positivity))
  have hP := pos_val hpos (md := l.2.2.1) (q := j % 2 ^ bq) (dq := l.2.2.2.1) hZ (by rw [hF 2 (by omega)]; rfl) (by rw [hF 3 (by omega)]; rfl) hqb
    (Nat.mod_lt _ (by positivity)) (fun i hi => by
      unfold dWire
      split_ifs with h
      · rw [hF _ (by omega), fbit_dq]
      · rw [hZ, hl, hD _ _ i (by omega) hi])
  have hK : num (fun i => v (Fw n rb tb.length (5 + kbm + Dq) ι (5 + i))) kbm = l.1 % 2 ^ kbm := by
    rw [num_congr (c := l.1.testBit) fun i hi => by rw [hF _ (by omega), fbit_kind l hi], num_testBit]
  have hZs : num (fun _ => v n) (L - (bq + bt + 2 + kbm)) = 0 := by
    rw [hZ]
    exact num_false _
  unfold outsL
  constructor
  · rw [List.take_left' (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega)]
    simp only [List.map_append, List.map_map, ofWord_append, List.length_append, List.length_map, List.length_range, List.map_cons, List.map_nil,
      List.length_cons, List.length_nil]
    change num (fun i => v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3)) (bq + 1) +
      2 ^ (bq + 1) * num (fun i => v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * i + 1)) bt +
      2 ^ (bq + 1 + bt) * ofWord [v (offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * bt)] +
      2 ^ (bq + 1 + bt + (0 + 1)) * num (fun i => v (Fw n rb tb.length (5 + kbm + Dq) ι (5 + i))) kbm +
      2 ^ (bq + 1 + bt + (0 + 1) + kbm) * num (fun _ => v n) (L - (bq + bt + 2 + kbm)) = _
    rw [hP, hK, hZs, ← hT]
    simp only [ofWord]
    ring
  · rw [List.getD_append_right _ _ _ _ (by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega)]
    have e : L - ((((List.range (bq + 1)).map fun i => offA n bq bt rb tb.length (5 + kbm + Dq) ι + 4 + 3 * bt + 1 + 7 * i + 3) ++
        ((List.range bt).map fun i => offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * i + 1) ++ [offA n bq bt rb tb.length (5 + kbm + Dq) ι + 3 + 3 * bt] ++
        ((List.range kbm).map fun i => Fw n rb tb.length (5 + kbm + Dq) ι (5 + i)) ++ ((List.range (L - (bq + bt + 2 + kbm))).map fun _ => n)).length) = 0 := by
      simp only [List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil]
      omega
    rw [e, List.getD_cons_zero, hF 4 (by omega)]
    rfl

/-! ### The circuit is written in polynomial time -/

section poly

variable {α : Type} [Enc α]

@[fun_prop] theorem prevW_polyT {off init i : α → ℕ} (h1 : PolyT off) (h2 : PolyT init) (h3 : PolyT i) :
    PolyT fun x => prevW (off x) (init x) (i x) := by unfold prevW; fun_prop

@[fun_prop] theorem litI_polyT {c : α → TCl} {ι : α → ℕ} (h1 : PolyT c) (h2 : PolyT ι) : PolyT fun x => litI (c x) (ι x) := by unfold litI; fun_prop

@[fun_prop] theorem fbit_polyT {kbm f : α → ℕ} {l : α → TLit} (h1 : PolyT kbm) (h2 : PolyT l) (h3 : PolyT f) :
    PolyT fun x => fbit (kbm x) (l x) (f x) := by unfold fbit; fun_prop

@[fun_prop] theorem Ew_polyT {n rb k : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT k) : PolyT fun x => Ew (n x) (rb x) (k x) := by
  unfold Ew; fun_prop

@[fun_prop] theorem selGate_polyT {n bq bt rb k i : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : PolyT rb) (h5 : PolyT k) (h6 : PolyT i) :
    PolyT fun x => selGate (n x) (bq x) (bt x) (rb x) (k x) (i x) := by unfold selGate; fun_prop

theorem selChain_polyT {n bq bt rb k : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : Unary rb) (h5 : PolyT k) :
    PolyT fun x => selChain (n x) (bq x) (bt x) (rb x) (k x) :=
  PolyT.map (f := fun x i => selGate (n x) (bq x) (bt x) (rb x) (k x) i) (by have := h4.poly; fun_prop) (PolyT.range h4)

theorem selG_polyT {n bq bt rb R : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : Unary rb) (h5 : Unary R) :
    PolyT fun x => selG (n x) (bq x) (bt x) (rb x) (R x) :=
  PolyT.flatMap (f := fun x k => selChain (n x) (bq x) (bt x) (rb x) k)
    (selChain_polyT (by fun_prop) (by fun_prop) (by fun_prop) (h4.comp (h := Prod.fst) (by fun_prop)) (by fun_prop)) (PolyT.range h5)

@[fun_prop] theorem Fw_polyT {n rb R nf ι f : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT R) (h4 : PolyT nf) (h5 : PolyT ι) (h6 : PolyT f) :
    PolyT fun x => Fw (n x) (rb x) (R x) (nf x) (ι x) (f x) := by unfold Fw; fun_prop

@[fun_prop] theorem fldGate_polyT {n rb kbm nf a k : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : PolyT nf)
    (h5 : PolyT tb) (h6 : PolyT a) (h7 : PolyT k) : PolyT fun x => fldGate (n x) (rb x) (kbm x) (nf x) (tb x) (a x) (k x) := by
  unfold fldGate; fun_prop

theorem fldChain_polyT {n rb kbm nf a : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : PolyT nf)
    (h5 : PolyT tb) (h6 : PolyT a) : PolyT fun x => fldChain (n x) (rb x) (kbm x) (nf x) (tb x) (a x) :=
  PolyT.map (f := fun x k => fldGate (n x) (rb x) (kbm x) (nf x) (tb x) (a x) k) (by fun_prop) (PolyT.range (Unary.of_length h5))

theorem fldG_polyT {n rb kbm nf : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : Unary nf) (h5 : PolyT tb) :
    PolyT fun x => fldG (n x) (rb x) (kbm x) (nf x) (tb x) :=
  PolyT.flatMap (f := fun x a => fldChain (n x) (rb x) (kbm x) (nf x) (tb x) a)
    (fldChain_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by have := h4.poly; fun_prop) (by fun_prop) (by fun_prop))
    (PolyT.range ((Unary.const 3).mul h4))

@[fun_prop] theorem cinT_polyT {a i : α → ℕ} (h1 : PolyT a) (h2 : PolyT i) : PolyT fun x => cinT (a x) (i x) := by unfold cinT; fun_prop

@[fun_prop] theorem cinQ_polyT {z b i : α → ℕ} (h1 : PolyT z) (h2 : PolyT b) (h3 : PolyT i) : PolyT fun x => cinQ (z x) (b x) (i x) := by
  unfold cinQ; fun_prop

@[fun_prop] theorem timeBit_polyT {bq a i : α → ℕ} (h1 : PolyT bq) (h2 : PolyT a) (h3 : PolyT i) : PolyT fun x => timeBit (bq x) (a x) (i x) := by
  unfold timeBit; fun_prop

theorem timeG_polyT {bq bt a m0 m1 : α → ℕ} (h1 : PolyT bq) (h2 : Unary bt) (h3 : PolyT a) (h4 : PolyT m0) (h5 : PolyT m1) :
    PolyT fun x => timeG (bq x) (bt x) (a x) (m0 x) (m1 x) := by
  have h6 : PolyT fun x => (List.range (bt x)).flatMap (timeBit (bq x) (a x)) :=
    PolyT.flatMap (f := fun x i => timeBit (bq x) (a x) i) (by fun_prop) (PolyT.range h2)
  have := h2.poly
  unfold timeG
  fun_prop

@[fun_prop] theorem dWire_polyT {n rb R kbm Dq ι i : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT R) (h4 : PolyT kbm) (h5 : PolyT Dq) (h6 : PolyT ι)
    (h7 : PolyT i) : PolyT fun x => dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x) (i x) := by unfold dWire; fun_prop

theorem posBit_polyT {n bq P b p1 rb R kbm Dq ι i : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT P) (h4 : PolyT b) (h5 : PolyT p1) (h6 : PolyT rb)
    (h7 : PolyT R) (h8 : PolyT kbm) (h9 : PolyT Dq) (h10 : PolyT ι) (h11 : PolyT i) :
    PolyT fun x => posBit (n x) (bq x) (P x) (b x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x)) (i x) := by
  unfold posBit; fun_prop

theorem posG_polyT {n bq P b p0 p1 rb R kbm Dq ι : α → ℕ} (h1 : PolyT n) (h2 : Unary bq) (h3 : PolyT P) (h4 : PolyT b) (h0 : PolyT p0) (h5 : PolyT p1)
    (h6 : PolyT rb) (h7 : PolyT R) (h8 : PolyT kbm) (h9 : PolyT Dq) (h10 : PolyT ι) :
    PolyT fun x => posG (n x) (bq x) (P x) (b x) (p0 x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x)) := by
  have hq := h2.poly
  have h12 : PolyT fun x => (List.range (bq x + 1)).flatMap (posBit (n x) (bq x) (P x) (b x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x))) :=
    PolyT.flatMap (f := fun x i => posBit (n x) (bq x) (P x) (b x) (p1 x) (dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x)) i)
      (posBit_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop)) (PolyT.range (h2.add (Unary.const 1)))
  unfold posG
  fun_prop

@[fun_prop] theorem szL_polyT {bq bt : α → ℕ} (h1 : PolyT bq) (h2 : PolyT bt) : PolyT fun x => szL (bq x) (bt x) := by unfold szL; fun_prop

@[fun_prop] theorem offA_polyT {n bq bt rb R nf ι : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : PolyT nf)
    (h7 : PolyT ι) : PolyT fun x => offA (n x) (bq x) (bt x) (rb x) (R x) (nf x) (ι x) := by unfold offA; fun_prop

theorem litG_polyT {n bq bt rb R kbm Dq P ι : α → ℕ} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : PolyT kbm)
    (h7 : PolyT Dq) (h8 : PolyT P) (h9 : PolyT ι) : PolyT fun x => litG (n x) (bq x) (bt x) (rb x) (R x) (kbm x) (Dq x) (P x) (ι x) := by
  have hq := h2.poly
  have ht := h3.poly
  exact PolyT.append (timeG_polyT hq h3 (by fun_prop) (by fun_prop) (by fun_prop))
    (posG_polyT h1 h2 h8 (by fun_prop) (by fun_prop) (by fun_prop) h4 h5 h6 h7 h9)

theorem gatesC_polyT {n bq bt rb kbm Dq P : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : Unary rb) (h6 : Unary kbm)
    (h7 : Unary Dq) (h8 : PolyT P) (h9 : PolyT tb) : PolyT fun x => gatesC (n x) (bq x) (bt x) (rb x) (kbm x) (Dq x) (P x) (tb x) := by
  have hq := h2.poly
  have ht := h3.poly
  have hr := h4.poly
  have hk := h6.poly
  have hd := h7.poly
  have g1 : PolyT fun x => selG (n x) (bq x) (bt x) (rb x) (tb x).length := selG_polyT h1 hq ht h4 (Unary.of_length h9)
  have g2 : PolyT fun x => fldG (n x) (rb x) (kbm x) (5 + kbm x + Dq x) (tb x) := fldG_polyT h1 hr hk (((Unary.const 5).add h6).add h7) h9
  have g3 : PolyT fun x => (List.range 3).flatMap (litG (n x) (bq x) (bt x) (rb x) (tb x).length (kbm x) (Dq x) (P x)) :=
    PolyT.flatMap (f := fun x ι => litG (n x) (bq x) (bt x) (rb x) (tb x).length (kbm x) (Dq x) (P x) ι)
      (litG_polyT (by fun_prop) (h2.comp (h := Prod.fst) (by fun_prop)) (h3.comp (h := Prod.fst) (by fun_prop)) (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (by fun_prop) (by fun_prop)) (PolyT.const _)
  unfold gatesC
  fun_prop

theorem outs_aux1 {a bt w : α → ℕ} (h1 : PolyT a) (h2 : PolyT bt) (h3 : Unary w) :
    PolyT fun x => (List.range (w x)).map fun i => a x + 4 + 3 * bt x + 1 + 7 * i + 3 :=
  PolyT.map (f := fun x i => a x + 4 + 3 * bt x + 1 + 7 * i + 3) (by fun_prop) (PolyT.range h3)

theorem outs_aux2 {a w : α → ℕ} (h1 : PolyT a) (h3 : Unary w) : PolyT fun x => (List.range (w x)).map fun i => a x + 3 + 3 * i + 1 :=
  PolyT.map (f := fun x i => a x + 3 + 3 * i + 1) (by fun_prop) (PolyT.range h3)

theorem outs_aux3 {a bt : α → ℕ} (h1 : PolyT a) (h2 : PolyT bt) : PolyT fun x => [a x + 3 + 3 * bt x] := by fun_prop

theorem outsL_polyT {n bq bt rb R kbm Dq L ι : α → ℕ} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : Unary kbm)
    (h7 : PolyT Dq) (h8 : Unary L) (h9 : PolyT ι) : PolyT fun x => outsL (n x) (bq x) (bt x) (rb x) (R x) (kbm x) (Dq x) (L x) (ι x) := by
  have hq := h2.poly
  have ht := h3.poly
  have hk := h6.poly
  have hl := h8.poly
  have ha : PolyT fun x => offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) := by fun_prop
  have r1 : PolyT fun x => (List.range (bq x + 1)).map fun i => offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) + 4 + 3 * bt x + 1 + 7 * i + 3 :=
    outs_aux1 ha ht (h2.add (Unary.const 1))
  have r2 : PolyT fun x => (List.range (bt x)).map fun i => offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) + 3 + 3 * i + 1 := outs_aux2 ha h3
  have r3 : PolyT fun x => (List.range (kbm x)).map fun i => Fw (n x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) (5 + i) :=
    PolyT.map (f := fun x i => Fw (n x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) (5 + i)) (by fun_prop) (PolyT.range h6)
  have r4 : PolyT fun x => (List.range (L x - (bq x + bt x + 2 + kbm x))).map fun _ => n x :=
    PolyT.map (f := fun x _ => n x) (by fun_prop) (PolyT.range (Unary.of_le h8 (by fun_prop) fun x => Nat.sub_le _ _))
  have r5 : PolyT fun x => [offA (n x) (bq x) (bt x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) + 3 + 3 * bt x] := outs_aux3 ha ht
  have r6 : PolyT fun x => [Fw (n x) (rb x) (R x) (5 + kbm x + Dq x) (ι x) 4] := by fun_prop
  exact PolyT.append (PolyT.append (PolyT.append (PolyT.append (PolyT.append r1 r2) r5) r3) r4) r6

theorem coreB_polyT {n bq bt rb kbm Dq L P : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : Unary bq) (h3 : Unary bt) (h4 : Unary rb) (h6 : Unary kbm)
    (h7 : Unary Dq) (h5 : Unary L) (h8 : PolyT P) (h9 : PolyT tb) :
    PolyT fun x => coreB (n x) (bq x) (bt x) (rb x) (kbm x) (Dq x) (L x) (P x) (tb x) := by
  have hr := h4.poly
  have hd := h7.poly
  exact PolyT.prodMk (gatesC_polyT h1 h2 h3 h4 h6 h7 h8 h9)
    (PolyT.flatMap (f := fun x ι => outsL (n x) (bq x) (bt x) (rb x) (tb x).length (kbm x) (Dq x) (L x) ι)
      (outsL_polyT (by fun_prop) (h2.comp (h := Prod.fst) (by fun_prop)) (h3.comp (h := Prod.fst) (by fun_prop)) (by fun_prop) (by fun_prop)
        (h6.comp (h := Prod.fst) (by fun_prop)) (by fun_prop) (h5.comp (h := Prod.fst) (by fun_prop)) (by fun_prop)) (PolyT.const _))

@[fun_prop] theorem kb_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => kb (e x) := by unfold kb; fun_prop

@[fun_prop] theorem lam_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => lam (e x) := by unfold lam; fun_prop

@[fun_prop] theorem tab_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => tab (e x) := by unfold tab; fun_prop

@[fun_prop] theorem bt_polyT {e : α → MCode} {L : α → ℕ} (h : PolyT e) (hL : PolyT L) : PolyT fun x => bt (e x) (L x) := by unfold bt; fun_prop

@[fun_prop] theorem bq_polyT {e : α → MCode} {L : α → ℕ} (h : PolyT e) (hL : PolyT L) : PolyT fun x => bq (e x) (L x) := by unfold bq; fun_prop

theorem size_aux {f : α → ℕ} (h : PolyT f) : PolyT fun x => Nat.size (f x) := by fun_prop

@[fun_prop] theorem rb_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => rb (e x) := size_aux (f := fun x => (tab (e x)).length) (by fun_prop)

@[fun_prop] theorem nb_polyT {e : α → MCode} {L : α → ℕ} (h : PolyT e) (hL : PolyT L) : PolyT fun x => nb (e x) (L x) := by unfold nb; fun_prop

@[fun_prop] theorem dSum_polyT {tb : α → List TCl} (h : PolyT tb) : PolyT fun x => dSum (tb x) := by unfold dSum; fun_prop

theorem B_polyT : PolyT B := by
  have hL : Unary fun x : MCode × List Unit × ℕ => x.2.1.length := Unary.of_length (by fun_prop)
  have hl := hL.poly
  have hbq : Unary fun x : MCode × List Unit × ℕ => min (bq x.1 x.2.1.length) x.2.1.length := Unary.of_le hL (by fun_prop) fun x => min_le_right _ _
  have hbt : Unary fun x : MCode × List Unit × ℕ => bt x.1 x.2.1.length :=
    Unary.of_le hL (by fun_prop) fun x => by
      unfold bt
      exact (Nat.div_le_self _ _).trans (by omega)
  have hrb : Unary fun x : MCode × List Unit × ℕ => rb x.1 :=
    Unary.of_le (Unary.of_length (w := fun x : MCode × List Unit × ℕ => tab x.1) (by fun_prop)) (by fun_prop) fun x => Nat.size_le.2 Nat.lt_two_pow_self
  have hkb : Unary fun x : MCode × List Unit × ℕ => min (kb x.1) x.2.1.length := Unary.of_le hL (by fun_prop) fun x => min_le_right _ _
  have hs : PolyT fun x : MCode × List Unit × ℕ => Nat.size (dSum (tab x.1)) := size_aux (by fun_prop)
  have hq := hbq.poly
  have hDq : Unary fun x : MCode × List Unit × ℕ => min (Nat.size (dSum (tab x.1))) (min (bq x.1 x.2.1.length) x.2.1.length + 1) :=
    Unary.of_le (hbq.add (Unary.const 1)) (by fun_prop) fun x => min_le_right _ _
  exact coreB_polyT (by fun_prop) hbq hbt hrb hkb hDq hL (by fun_prop) (by fun_prop)

end poly

/-! ### The statement -/

theorem pick3 (f : ℕ → List ℕ) {k : ℕ} (hf : ∀ i, (f i).length = k) {i : ℕ} (hi : i < 3) :
    ∃ rest, ((List.range 3).flatMap f).drop (i * k) = f i ++ rest := by
  have e : (List.range 3).flatMap f = f 0 ++ (f 1 ++ (f 2 ++ [])) := rfl
  rw [e]
  interval_cases i
  · exact ⟨f 1 ++ (f 2 ++ []), by simp⟩
  · exact ⟨_, by rw [Nat.one_mul]; exact List.drop_left' (hf 0)⟩
  · refine ⟨[], ?_⟩
    rw [← List.append_assoc]
    exact List.drop_left' (by rw [List.length_append, hf 0, hf 1]; omega)

theorem le_sum_map {α : Type} (f : α → ℕ) (l : List α) {c : α} (hc : c ∈ l) : f c ≤ (l.map f).sum := by
  induction l with
  | nil => simp at hc
  | cons d l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hc with rfl | h
    · omega
    · have := ih h
      omega

/-- No number that the table adds to a position is larger than `dSum`. -/
theorem dq_le_dSum (tb : List TCl) (k ι : ℕ) : (litI (tb.getD k zeroCl) ι).2.2.2.1 ≤ dSum tb := by
  by_cases hk : k < tb.length
  · rw [List.getD_eq_getElem _ _ hk]
    refine le_trans ?_ (le_sum_map (fun c : TCl => c.1.2.2.2.1 + c.2.1.2.2.2.1 + c.2.2.2.2.2.1) tb (List.getElem_mem hk))
    unfold litI
    split_ifs <;> omega
  · rw [List.getD_eq_default _ _ (by omega), litI_zeroCl]
    exact Nat.zero_le _


end CircuitLowerBound.Clause

open CircuitLowerBound
open ENP Groundwork CircuitLowerBound.Blocks CircuitLowerBound.Clause

theorem solution : StClauseCirc := by
  refine ⟨36, fun e => 2 + rb e * (tab e).length + (tab e).length * (3 * (5 + kb e + Nat.size (dSum (tab e)))), B, B_polyT, fun e L P hF => ?_⟩
  obtain ⟨h1, h2⟩ := hF
  have hbt2 : 2 * bt e L ≤ L - kb e - lam e - 2 := by unfold bt; omega
  have hbt1 : 1 ≤ bt e L := by
    by_contra h
    have h0 : bt e L = 0 := by omega
    rw [h0] at h2
    simp at h2
  have hbq : bq e L = bt e L + lam e := rfl
  have hn : nb e L = rb e + bt e L + bq e L := rfl
  have hL' : bq e L + bt e L + 2 + kb e ≤ L := by omega
  have hR : (tab e).length < 2 ^ rb e := Nat.lt_size_self _
  have hB : B (e, List.replicate L (), P) =
      coreB (nb e L) (bq e L) (bt e L) (rb e) (kb e) (min (Nat.size (dSum (tab e))) (bq e L + 1)) L P (tab e) := by
    simp only [B, List.length_replicate]
    rw [min_eq_left (by omega : bq e L ≤ L), min_eq_left (by omega : kb e ≤ L)]
  rw [hB]
  simp only [coreB]
  obtain ⟨Dq, hDq⟩ : ∃ Dq, Dq = min (Nat.size (dSum (tab e))) (bq e L + 1) := ⟨_, rfl⟩
  rw [← hDq]
  have hD : ∀ k ι i, Dq ≤ i → i < bq e L + 1 → (litI ((tab e).getD k zeroCl) ι).2.2.2.1.testBit i = false := by
    intro k ι i hi1 hi2
    have hs : Nat.size (dSum (tab e)) ≤ i := by omega
    exact Nat.testBit_eq_false_of_lt (lt_of_le_of_lt (dq_le_dSum (tab e) k ι) ((Nat.lt_size_self _).trans_le (Nat.pow_le_pow_right (by norm_num) hs)))
  have hlen := length_gatesC (nb e L) (bq e L) (bt e L) (rb e) (kb e) Dq P (tab e)
  have hol := length_outsL hL' (nb e L) (rb e) (tab e).length Dq
  refine ⟨wf_of_wfa (wfa_gatesC (by omega) (by omega) _ _ _ _), ?_, ?_, ?_, ?_⟩
  · rw [hlen]
    have g1 : (tab e).length * (3 * (5 + kb e + Dq)) ≤ (tab e).length * (3 * (5 + kb e + Nat.size (dSum (tab e)))) :=
      Nat.mul_le_mul_left _ (by omega)
    unfold szL
    omega
  · rw [length_flatMap_const _ hol 3]
    omega
  · intro w hw
    obtain ⟨ι, hι, hw⟩ := List.mem_flatMap.1 hw
    rw [hlen]
    exact outsL_lt _ _ _ _ _ _ _ _ (List.mem_range.1 hι) w hw
  · intro j hj i hi
    obtain ⟨rest, hr⟩ := pick3 (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L) hol hi
    obtain ⟨c1, c2⟩ := core_val hn hbt1 hR hL' hD hj hi _ rfl _ rfl (P := P)
    have hg : ((List.range 3).flatMap (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L)).getD (i * (L + 1) + L) 0 =
        (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L i).getD L 0 := by
      have e1 : ((List.range 3).flatMap (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L)).getD (i * (L + 1) + L) 0 =
          (((List.range 3).flatMap (outsL (nb e L) (bq e L) (bt e L) (rb e) (tab e).length (kb e) Dq L)).drop (i * (L + 1))).getD L 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
      rw [e1, hr, List.getD_append _ _ _ _ (by rw [hol]; omega)]
    rw [hr, List.take_append_of_le_length (by rw [hol]; omega), hg]
    have hcl : (clauseAt e L P j).getD i (0, false) =
        litAt e L P (j / 2 ^ bq e L % 2 ^ bt e L) (j % 2 ^ bq e L) (litI ((tab e).getD (j / 2 ^ (bt e L + bq e L)) zeroCl) i) := by
      interval_cases i <;> rfl
    rw [hcl, litAt, vidx]
    exact Prod.ext c1 c2
