-- Prove2me | solution 2 for DetDLP.scalar_contraction_local_prep_program_v3
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:31:03.581642+00:00
-- url     : https://prove2.me/submissions/01f6ab7a-d35a-46d8-9b0a-a8e14e087436

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.BitProgram hiding Trace
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Single vertex, no edges: the contraction is the unique vertex polynomial. -/
abbrev oneVertex : BipartiteMultigraph where
  nV := 1
  nE := 0
  endpoints := fun e => Fin.elim0 e
  side := fun _ => false
  bipartite := fun e => Fin.elim0 e

def Aconst (c : ℕ) (_v : Fin oneVertex.nV) (_t : Fin (oneVertex.deg _v) → Bool)
    (_i : Fin 1) : ℕ :=
  c

private lemma trace_unique {r s l : ℕ} {p : Program r s l} {n : ℕ}
    {a b c : Cfg r s l}
    (h₁ : Trace (step p) n a b) (h₂ : Trace (step p) n a c) : b = c := by
  induction h₁ generalizing c with
  | refl =>
    cases h₂
    rfl
  | cons hstep hrest ih =>
    cases h₂ with
    | cons hstep' hrest' =>
      injection hstep.symm.trans hstep' with hb
      exact ih (hb ▸ hrest')

private lemma trace_prefix {r s l : ℕ} {p : Program r s l} :
    ∀ {n m : ℕ} {a c : Cfg r s l},
      n ≤ m → Trace (step p) m a c →
        ∃ d, Trace (step p) n a d ∧ Trace (step p) (m - n) d c := by
  intro n m a c hnm h
  induction h generalizing n with
  | refl x =>
    have hn : n = 0 := Nat.le_zero.mp hnm
    subst hn
    exact ⟨x, Trace.refl x, by simpa using (Trace.refl x : Trace (step p) 0 x x)⟩
  | @cons k x y z hstep hrest ih =>
    cases n with
    | zero =>
      exact ⟨x, Trace.refl x, by simpa using (Trace.cons hstep hrest)⟩
    | succ n =>
      obtain ⟨d, hd₁, hd₂⟩ := ih (Nat.le_of_succ_le_succ hnm)
      exact ⟨d, Trace.cons hstep hd₁, by simpa [Nat.succ_sub_succ] using hd₂⟩

private lemma halt_trace_le {r s l : ℕ} {p : Program r s l}
    {n m : ℕ} {a b c : Cfg r s l}
    (hnm : n ≤ m) (hb : b.pc = none) (_hc : c.pc = none)
    (h₁ : Trace (step p) n a b) (h₂ : Trace (step p) m a c) : n = m ∧ b = c := by
  obtain ⟨d, hd₁, hd₂⟩ := trace_prefix hnm h₂
  have hd : d = b := trace_unique hd₁ h₁
  cases hgap : m - n with
  | zero =>
    have hm : m = n := le_antisymm (Nat.sub_eq_zero_iff_le.mp hgap) hnm
    subst hm
    have htail : Trace (step p) 0 d c := by simpa [hgap] using hd₂
    cases htail
    subst hd
    exact ⟨rfl, rfl⟩
  | succ t =>
    have htail : Trace (step p) (Nat.succ t) d c := by simpa [hgap] using hd₂
    cases htail with
    | cons hstep _ =>
      have hpc : d.pc = none := by simpa [hd] using hb
      have hnone : step p d = none := by simp [step, hpc]
      rw [hnone] at hstep
      cases hstep

private lemma halt_trace_unique {r s l : ℕ} {p : Program r s l}
    {n m : ℕ} {a b c : Cfg r s l}
    (hb : b.pc = none) (hc : c.pc = none)
    (h₁ : Trace (step p) n a b) (h₂ : Trace (step p) m a c) : n = m ∧ b = c := by
  rcases Nat.le_total n m with hnm | hmn
  · exact halt_trace_le hnm hb hc h₁ h₂
  · have ⟨heq, hcfg⟩ := halt_trace_le hmn hc hb h₂ h₁
    exact ⟨heq.symm, hcfg.symm⟩

lemma contract_one (c : ℕ) :
    BTNContract oneVertex (fun v t =>
        ∑ i : Fin 1, Polynomial.monomial i.val (Aconst c v t i : ℤ)) =
      Polynomial.monomial 0 (c : ℤ) := by
  classical
  simp only [BTNContract]
  rw [Finset.univ_unique, Finset.sum_singleton, Finset.univ_unique, Finset.prod_singleton]
  simp [Aconst, Fin.sum_univ_one]

lemma coeff_contract_one (c : ℕ) :
    (BTNContract oneVertex (fun v t =>
        ∑ i : Fin 1, Polynomial.monomial i.val (Aconst c v t i : ℤ))).coeff 0 =
      (c : ℤ) := by
  rw [contract_one]
  simp [Polynomial.coeff_monomial]

lemma zmod_val_small (c : ℕ) (hc : c < 2) :
    (((c : ℤ) : ZMod (2 ^ 1)).val) = c := by
  have h2 : 2 ^ 1 = 2 := by decide
  simp only [h2, Int.cast_natCast, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hc

lemma coeffList_one (c : ℕ) (hc : c < 2) :
    List.ofFn (fun i : Fin 1 =>
      ((BTNContract oneVertex (fun v t =>
          ∑ j : Fin 1, Polynomial.monomial j.val (Aconst c v t j : ℤ))).coeff i.val :
        ZMod (2 ^ 1)).val) = [c] := by
  have hcoeff : ∀ i : Fin 1,
      ((BTNContract oneVertex (fun v t =>
          ∑ j : Fin 1, Polynomial.monomial j.val (Aconst c v t j : ℤ))).coeff i.val :
        ZMod (2 ^ 1)).val = c := by
    intro i
    have hi : i.val = 0 := by simpa using congrArg Fin.val (Subsingleton.elim i 0)
    rw [hi, coeff_contract_one, zmod_val_small c hc]
  have hfun : (fun i : Fin 1 =>
      ((BTNContract oneVertex (fun v t =>
          ∑ j : Fin 1, Polynomial.monomial j.val (Aconst c v t j : ℤ))).coeff i.val :
        ZMod (2 ^ 1)).val) = fun _ => c := by
    funext i
    exact hcoeff i
  rw [hfun]
  have hcast : List.ofFn (fun _ : Fin 1 => c) =
      List.ofFn (fun i : Fin (0 + 1) => c) := rfl
  rw [hcast, List.ofFn_succ, List.ofFn_zero]

def ofBits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBits bs

lemma ofBits_bits : ∀ n : ℕ, ofBits n.bits = n := by
  intro n
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits, Nat.zero_bits]
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb, ofBits, ih, Nat.bit_val, Nat.add_comm]

lemma bits_injective {m n : ℕ} (h : m.bits = n.bits) : m = n := by
  simpa [ofBits_bits] using congrArg ofBits h

lemma encode_zero :
    encodeNatListBin [0] = [true, true, false, false, false] := by
  decide

lemma encode_one :
    encodeNatListBin [1] = [true, true, true, false, false] := by
  have hc : countWord 1 = [true] := by
    simp [countWord, Nat.one_bits]
  unfold encodeNatListBin
  rw [show Encoding.encodeList countWord [1] =
      true :: (Encoding.frame (countWord 1) ++ Encoding.encodeList countWord []) by
    rfl]
  simp [hc, Encoding.encodeList, Encoding.frame, List.foldr_cons, List.foldr_nil]

lemma fold_zero :
    (encodeNatListBin [0]).foldr (fun b z => b.toNat + 2 * z) 1 = 35 := by
  rw [encode_zero]
  decide

lemma fold_one :
    (encodeNatListBin [1]).foldr (fun b z => b.toNat + 2 * z) 1 = 39 := by
  rw [encode_one]
  decide

noncomputable def wordOf (c : ℕ) : ℕ :=
  let Z := BTNContract oneVertex (fun v t =>
    ∑ i : Fin 1, Polynomial.monomial i.val (Aconst c v t i : ℤ))
  let w := encodeNatListBin (List.ofFn fun i : Fin 1 =>
    ((Z.coeff i.val : ZMod (2 ^ 1)).val))
  w.foldr (fun b z => b.toNat + 2 * z) 1

lemma wordOf_eq (c : ℕ) (hc : c < 2) :
    wordOf c = (encodeNatListBin [c]).foldr (fun b z => b.toNat + 2 * z) 1 := by
  simp only [wordOf]
  rw [coeffList_one c hc]

lemma wordOf_zero : wordOf 0 = 35 := by
  rw [wordOf_eq 0 (by decide), fold_zero]

lemma wordOf_one : wordOf 1 = 39 := by
  rw [wordOf_eq 1 (by decide), fold_one]

lemma wordOf_ne : wordOf 0 ≠ wordOf 1 := by
  simp [wordOf_zero, wordOf_one]

lemma pack_context {s : ℕ} (hs : 0 < s)
    (nums : Fin 20 → List Bool) (context : Fin s → List Bool)
    (i : Fin (20 + s)) (hi : i.val = 20) :
    Fin.addCases (m := 20) (n := s) nums context i = context ⟨0, hs⟩ := by
  have hidx : i = Fin.natAdd 20 ⟨0, hs⟩ := by
    apply Fin.ext
    simp [Fin.natAdd, hi]
  simpa [hidx] using
    (Fin.addCases_right (motive := fun _ => List Bool)
      (left := nums) (right := context) ⟨0, hs⟩)

/--
`prep_program_v3` asks one machine, started from `encodeBTNInstance`
(which does not contain the coefficient tensor), to halt with `word.bits`
for every tensor. The one-vertex instances with constant coefficients `0` and `1`
share a start state and halt with distinct context bits.
-/
theorem solution :
    ¬ (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
        ∀ {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se),
          it ≠ iv → ot ≠ ov →
          ∃ (s lp : ℕ) (hs : 0 < s) (prep : BitProgram.Program 8 (20 + s) lp),
            ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
              (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
              2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
              1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
              (∀ v t i, A v t i < 2 ^ P) →
              let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
                Polynomial.monomial i.val (A v t i : ℤ))
              let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
                ((Z.coeff i.val : ZMod (2 ^ P)).val))
              let word := w.foldr (fun b z => b.toNat + 2 * z) 1
              let B := word + 1
              let q := B + 1
              let context : Fin s → List Bool := fun i => if i.val = 0 then word.bits else []
              let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
                let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
                Fin.addCases (m := 20) (n := s)
                  (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits))
                  context
              let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
              let reg : Fin 8 → Bool := fun _ => true
              ∃ (prepSteps cap0 U : ℕ),
                (∀ i, (context i).length ≤ U) ∧
                BitProgram.Trace prep prepSteps start ⟨none, reg, pack 0 0 1 0 0 0⟩ ∧
                  (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
                    ∀ i, (c.stacks i).length ≤ cap0)) := by
  intro h
  let Q : BitProgram.Program 3 3 1 :=
    { inputStack := 0, outputStack := 1, entry := 0, code := fun _ => .halt }
  obtain ⟨s, lp, hs, prep, hprep⟩ :=
    h 1 1 (by decide) (by decide) (se := 3) (le := 1) Q
      (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 3) (by decide) (by decide)
  have hne : oneVertex.nE ≤ 1 * 2 := Nat.zero_le _
  have hv : oneVertex.nV ≤ (2 : ℕ) ^ 1 := by decide
  have ha0 : ∀ v t i, Aconst 0 v t i < 2 ^ 1 := by
    intro _ _ _; simp [Aconst]
  have ha1 : ∀ v t i, Aconst 1 v t i < 2 ^ 1 := by
    intro _ _ _; simp [Aconst]
  obtain ⟨n0, _, _, _, htr0, _⟩ :=
    hprep 2 1 1 1 [] oneVertex (Aconst 0)
      (by decide) (by decide) hne hv (by decide) (by decide) (by decide) (by decide) ha0
  obtain ⟨n1, _, _, _, htr1, _⟩ :=
    hprep 2 1 1 1 [] oneVertex (Aconst 1)
      (by decide) (by decide) hne hv (by decide) (by decide) (by decide) (by decide) ha1
  set start := initial prep (encodeBTNInstance ([] : List Bool) oneVertex 2 1 1)
  let reg : Fin 8 → Bool := fun _ => true
  let ctx (c : ℕ) : Fin s → List Bool := fun i => if i.val = 0 then (wordOf c).bits else []
  let packOf (c : ℕ) : Fin (20 + s) → List Bool :=
    let word := wordOf c
    let B := word + 1
    let q := B + 1
    let v : Fin 12 → ℕ := ![q, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    Fin.addCases (m := 20) (n := s)
      (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) (ctx c)
  have htr0' : Trace (step prep) n0 start ⟨none, reg, packOf 0⟩ := by
    simpa [start, reg, packOf, ctx, wordOf, Aconst] using htr0
  have htr1' : Trace (step prep) n1 start ⟨none, reg, packOf 1⟩ := by
    simpa [start, reg, packOf, ctx, wordOf, Aconst] using htr1
  have ⟨_, hcfg⟩ := halt_trace_unique rfl rfl htr0' htr1'
  have hbits : (wordOf 0).bits ≠ (wordOf 1).bits :=
    fun h => wordOf_ne (bits_injective h)
  let i20 : Fin (20 + s) := ⟨20, by omega⟩
  have hi20 : i20.val = 20 := rfl
  have hstack0 : packOf 0 i20 = (wordOf 0).bits := by
    simpa [packOf, ctx, i20] using
      pack_context hs
        (let word := wordOf 0
          let B := word + 1
          let q := B + 1
          let v : Fin 12 → ℕ := ![q, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
          Fin.addCases (m := 8) (n := 12) (fun _ => ([] : List Bool)) (fun j => (v j).bits))
        (ctx 0) i20 hi20
  have hstack1 : packOf 1 i20 = (wordOf 1).bits := by
    simpa [packOf, ctx, i20] using
      pack_context hs
        (let word := wordOf 1
          let B := word + 1
          let q := B + 1
          let v : Fin 12 → ℕ := ![q, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
          Fin.addCases (m := 8) (n := 12) (fun _ => ([] : List Bool)) (fun j => (v j).bits))
        (ctx 1) i20 hi20
  have heq := congrFun (congrArg Cfg.stacks hcfg) i20
  have : packOf 0 i20 = packOf 1 i20 := by
    simpa [packOf] using heq
  rw [hstack0, hstack1] at this
  exact hbits this
