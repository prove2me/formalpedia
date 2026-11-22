-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T09:43:16.47717+00:00
-- url     : https://prove2.me/submissions/1a8618fa-627e-4ee1-a55c-b0915e5d6cc2

import Mathlib
import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_LTL
import Definitions.Def_DistLTLSynth_Char_Automata
import Definitions.Def_DistLTLSynth_Char_ComponentTree
import Definitions.Def_DistLTLSynth_Char_SynthesisEngine

set_option autoImplicit false

namespace DistLTLSynth.Char.Thm34LTLBlockAux

open DistLTLSynth.Char

/-! ### Section 1: Automaton Codes, Primrec Combinators, Bitmasks, and Alphabet Bijections -/

/-- Abstract executable NBW-to-DPA determinizer hypothesis. -/
structure NBWDeterminizer : Type where
  detNBW : ℕ → NBWCode → GenDPACode
  hPrim : Primrec₂ detNBW
  hCorr : ∀ (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)),
    (toGenDPA αSize (detNBW αSize b)).Accepts w ↔ NBWAccepts αSize b w

lemma getD_eq_getElem {α : Type} (l : List α) (d : α) (i : ℕ) (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

lemma getD_of_ge {α : Type} (l : List α) (d : α) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma getD_map_range_mul (Q αLen : ℕ) (f : ℕ → ℕ) (q a : ℕ)
    (hq : q < Q) (ha : a < αLen) :
    ((List.range (Q * αLen)).map f).getD (q * αLen + a) 0 = f (q * αLen + a) := by
  have hidx : q * αLen + a < Q * αLen := by
    have h1 : q + 1 ≤ Q := hq
    calc q * αLen + a < q * αLen + αLen := Nat.add_lt_add_left ha _
      _ = (q + 1) * αLen := by rw [Nat.succ_mul]
      _ ≤ Q * αLen := Nat.mul_le_mul_right αLen h1
  rw [getD_eq_getElem _ _ _ (by simp [hidx])]
  simp

lemma mul_add_div_alpha (αLen q a : ℕ) (ha : a < αLen) :
    (q * αLen + a) / αLen = q := by
  have hpos : 0 < αLen := Nat.zero_lt_of_lt ha
  rw [Nat.mul_comm q αLen, Nat.add_comm, Nat.add_mul_div_left _ _ hpos,
      Nat.div_eq_of_lt ha, zero_add]

lemma mul_add_mod_alpha (αLen q a : ℕ) (ha : a < αLen) :
    (q * αLen + a) % αLen = a := by
  rw [Nat.mul_comm q αLen, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha]

def commGraphEquivFin3 : CommGraph ≃ Fin 3 where
  toFun
    | .oneToTwo => ⟨0, by decide⟩
    | .both => ⟨1, by decide⟩
    | .twoToOne => ⟨2, by decide⟩
  invFun
    | ⟨0, _⟩ => .oneToTwo
    | ⟨1, _⟩ => .both
    | _ => .twoToOne
  left_inv g := by cases g <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance instPrimcodableCommGraph : Primcodable CommGraph :=
  Primcodable.ofEquiv (Fin 3) commGraphEquivFin3

def graphOfNat : ℕ → CommGraph
  | 0 => .oneToTwo
  | 1 => .both
  | _ => .twoToOne

lemma graphOfNat_idx (g : CommGraph) : graphOfNat g.idx = g := by
  cases g <;> rfl

lemma idx_graphOfNat (k : ℕ) (hk : k < 3) : (graphOfNat k).idx = k := by
  interval_cases k <;> rfl

@[simp] lemma commGraphEquivFin3_symm_eq (i : Fin 3) :
    commGraphEquivFin3.symm i = graphOfNat i.val := by
  fin_cases i <;> rfl

lemma primrec_commGraphIdx : Primrec CommGraph.idx := by
  have h : Primrec (fun g : CommGraph => (commGraphEquivFin3 g).val) :=
    Primrec.fin_val.comp Primrec.of_equiv
  exact h.of_eq fun g => by cases g <;> rfl

lemma primrec_graphOfNat : Primrec graphOfNat := by
  have h : Primrec (fun n : ℕ =>
      if n = 0 then CommGraph.oneToTwo else if n = 1 then CommGraph.both else CommGraph.twoToOne) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const CommGraph.oneToTwo)
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const CommGraph.both)
        (Primrec.const CommGraph.twoToOne))
  exact h.of_eq fun n => by
    rcases n with _ | _ | n <;> rfl

lemma primrec_list_getD {α : Type} [Primcodable α] :
    Primrec (fun p : List α × ℕ × α => p.1.getD p.2.1 p.2.2) := by
  have h : Primrec (fun p : List α × ℕ × α => (p.1[p.2.1]?).getD p.2.2) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun p => by simp [List.getD_eq_getElem?_getD]

lemma primrec_bool_and : Primrec₂ and :=
  (Primrec.cond Primrec.fst Primrec.snd (Primrec.const false)).of_eq fun p => by
    cases p.1 <;> rfl

lemma primrec_bool_or : Primrec₂ or :=
  (Primrec.cond Primrec.fst (Primrec.const true) Primrec.snd).of_eq fun p => by
    cases p.1 <;> rfl

lemma primrec_list_all {X α : Type} [Primcodable X] [Primcodable α]
    {L : X → List α} {P : X → α → Bool}
    (hL : Primrec L) (hP : Primrec (fun p : X × α => P p.1 p.2)) :
    Primrec (fun x => (L x).all (P x)) := by
  have hm : Primrec (fun x => (L x).map (P x)) := Primrec.list_map hL hP.to₂
  have hf : Primrec (fun bs : List Bool => bs.foldr and true) :=
    (Primrec.list_foldr Primrec.id (Primrec.const true)
      (primrec_bool_and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)
  exact (hf.comp hm).of_eq fun x => by
    induction (L x) with
    | nil => rfl
    | cons a tl ih => simp [List.all_cons, ih]

lemma primrec_list_any {X α : Type} [Primcodable X] [Primcodable α]
    {L : X → List α} {P : X → α → Bool}
    (hL : Primrec L) (hP : Primrec (fun p : X × α => P p.1 p.2)) :
    Primrec (fun x => (L x).any (P x)) := by
  have hm : Primrec (fun x => (L x).map (P x)) := Primrec.list_map hL hP.to₂
  have hf : Primrec (fun bs : List Bool => bs.foldr or false) :=
    (Primrec.list_foldr Primrec.id (Primrec.const false)
      (primrec_bool_or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)
  exact (hf.comp hm).of_eq fun x => by
    induction (L x) with
    | nil => rfl
    | cons a tl ih => simp [List.any_cons, ih]

lemma primrec_nat_pair : Primrec₂ Nat.pair :=
  Primrec.encode.of_eq fun _ => rfl

lemma primrec_range_map {X β : Type} [Primcodable X] [Primcodable β]
    (N : X → ℕ) (F : X → ℕ → β)
    {N' : X → ℕ} {F' : X × ℕ → β}
    (hN : Primrec N') (hN_eq : ∀ x, N' x = N x)
    (hF : Primrec F') (hF_eq : ∀ x i, F' (x, i) = F x i) :
    Primrec (fun x => (List.range (N x)).map (F x)) := by
  have hL : Primrec (fun x => List.range (N x)) :=
    (Primrec.list_range.comp hN).of_eq fun x => congrArg List.range (hN_eq x)
  have hF2 : Primrec (fun p : X × ℕ => F p.1 p.2) :=
    hF.of_eq fun p => hF_eq p.1 p.2
  exact (Primrec.list_map hL hF2.to₂).of_eq fun _ => rfl

lemma primrec_any_clean {X α : Type} [Primcodable X] [Primcodable α]
    (L : X → List α) (P : X → α → Bool)
    {L' : X → List α} {P' : X × α → Bool}
    (hL : Primrec L') (hL_eq : ∀ x, L' x = L x)
    (hP : Primrec P') (hP_eq : ∀ x a, P' (x, a) = P x a) :
    Primrec (fun x => (L x).any (P x)) :=
  primrec_list_any (L := L) (P := P) (hL.of_eq hL_eq) (hP.of_eq fun p => hP_eq p.1 p.2)

def powNat (b e : ℕ) : ℕ :=
  (List.range e).foldl (fun acc _ => acc * b) 1

lemma powNat_eq (b e : ℕ) : powNat b e = b ^ e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    simp only [powNat, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← powNat, ih, pow_succ]

lemma primrec_powNat : Primrec₂ powNat :=
  Primrec.list_foldl (Primrec.list_range.comp Primrec.snd) (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)).to₂

/-- Pack a list of booleans into a natural number bitmask (`bs[0]` is bit `0`). -/
def packBits : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * packBits bs

lemma primrec_packBits : Primrec packBits := by
  have hf := Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp
      (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂
  exact hf.of_eq fun bs => by
    dsimp only [id]
    induction bs with
    | nil => rfl
    | cons b tl ih => cases b <;> simp [packBits, ← ih]

lemma testBit_packBits (bs : List Bool) (j : ℕ) :
    (packBits bs).testBit j = bs.getD j false := by
  induction bs generalizing j with
  | nil => simp [packBits]
  | cons b tl ih =>
    rcases j with _ | k
    · rw [packBits, Nat.testBit_zero]
      cases b <;> simp
    · rw [packBits, Nat.testBit_succ]
      have hdiv : ((if b then 1 else 0) + 2 * packBits tl) / 2 = packBits tl := by
        (cases b <;> simp); omega
      rw [hdiv, ih k]
      simp [List.getD_eq_getElem?_getD]

lemma packBits_lt_two_pow (bs : List Bool) : packBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [packBits]
  | cons b tl ih =>
    have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> decide
    simp only [packBits, List.length_cons, pow_succ]
    omega

def listToMask (N : ℕ) (pred : ℕ → Bool) : ℕ :=
  packBits ((List.range N).map pred)

lemma testBit_listToMask (N : ℕ) (pred : ℕ → Bool) (j : ℕ) :
    (listToMask N pred).testBit j = (decide (j < N) && pred j) := by
  unfold listToMask
  rw [testBit_packBits]
  by_cases hj : j < N
  · rw [getD_eq_getElem _ _ j (by simp [hj])]
    simp [hj]
  · rw [getD_of_ge _ _ j (by simp; omega)]
    simp [hj]

lemma primrec_listToMask {X : Type} [Primcodable X]
    {N : X → ℕ} {pred : X → ℕ → Bool}
    (hN : Primrec N) (hP : Primrec (fun p : X × ℕ => pred p.1 p.2)) :
    Primrec (fun x => listToMask (N x) (pred x)) :=
  primrec_packBits.comp (Primrec.list_map (Primrec.list_range.comp hN) hP.to₂)

lemma primrec_mask_clean {X : Type} [Primcodable X]
    (N : X → ℕ) (pred : X → ℕ → Bool)
    {N' : X → ℕ} {P' : X × ℕ → Bool}
    (hN : Primrec N') (hN_eq : ∀ x, N' x = N x)
    (hP : Primrec P') (hP_eq : ∀ x i, P' (x, i) = pred x i) :
    Primrec (fun x => listToMask (N x) (pred x)) :=
  (primrec_packBits.comp (primrec_range_map N pred hN hN_eq hP hP_eq)).of_eq fun _ => rfl

lemma primrec_testBit : Primrec₂ Nat.testBit := by
  have h : Primrec₂ (fun x i => decide ((x / powNat 2 i) % 2 = 1)) :=
    (Primrec.eq.comp
      (Primrec.nat_mod.comp
        (Primrec.nat_div.comp Primrec.fst (primrec_powNat.comp (Primrec.const 2) Primrec.snd))
        (Primrec.const 2))
      (Primrec.const 1)).decide
  exact h.of_eq fun x i => by
    rw [powNat_eq, Nat.testBit_eq_decide_div_mod_eq]

/-! #### Explicit mixed-radix round and block alphabet bijections -/

def prodFinEquiv {m n : ℕ} (_hm : 0 < m) (hn : 0 < n) : Fin m × Fin n ≃ Fin (m * n) where
  toFun p := ⟨p.1.val * n + p.2.val, by
    have h1 : p.1.val + 1 ≤ m := p.1.isLt
    calc p.1.val * n + p.2.val
        < p.1.val * n + n := Nat.add_lt_add_left p.2.isLt _
      _ = (p.1.val + 1) * n := by rw [Nat.succ_mul]
      _ ≤ m * n := Nat.mul_le_mul_right n h1⟩
  invFun k :=
    (⟨k.val / n, Nat.div_lt_of_lt_mul (k.isLt.trans_eq (Nat.mul_comm m n))⟩,
     ⟨k.val % n, Nat.mod_lt _ hn⟩)
  left_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp only
    · rw [Nat.mul_comm p.1.val n, Nat.add_comm, Nat.add_mul_div_left _ _ hn,
          Nat.div_eq_of_lt p.2.isLt, zero_add]
    · rw [Nat.mul_comm p.1.val n, Nat.add_comm, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt p.2.isLt]
  right_inv k := by
    apply Fin.ext; dsimp only
    have h := Nat.div_add_mod k.val n
    linarith

/-- One round letter over instance `I`'s alphabets. -/
abbrev RoundLetter (I : Instance) : Type := Signal I.X1 I.X2 × (I.Y1 × I.Y2)

/-- Cardinality `(k1 + 1)(k2 + 1) · 3 · (m1 + 1)(m2 + 1) ≥ 1` of `RoundLetter I`. -/
def roundSize (I : Instance) : ℕ :=
  (I.k1 + 1) * ((I.k2 + 1) * (3 * ((I.m1 + 1) * (I.m2 + 1))))

lemma roundSize_pos (I : Instance) : 0 < roundSize I := by
  unfold roundSize; positivity

/-- `roundAlphaMinusOne I + 1 = roundSize I`. -/
def roundAlphaMinusOne (I : Instance) : ℕ := roundSize I - 1

lemma roundAlphaMinusOne_succ (I : Instance) :
    roundAlphaMinusOne I + 1 = roundSize I :=
  Nat.sub_add_cancel (roundSize_pos I)

lemma primrec_k1 : Primrec Instance.k1 := Primrec.fst.comp Primrec.of_equiv
lemma primrec_k2 : Primrec Instance.k2 := Primrec.fst.comp (Primrec.snd.comp Primrec.of_equiv)
lemma primrec_m1 : Primrec Instance.m1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv))
lemma primrec_m2 : Primrec Instance.m2 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)))
lemma primrec_tokens : Primrec Instance.tokens :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.of_equiv)))

lemma primrec_roundSize : Primrec roundSize :=
  Primrec.nat_mul.comp (Primrec.succ.comp primrec_k1)
    (Primrec.nat_mul.comp (Primrec.succ.comp primrec_k2)
      (Primrec.nat_mul.comp (Primrec.const 3)
        (Primrec.nat_mul.comp (Primrec.succ.comp primrec_m1) (Primrec.succ.comp primrec_m2))))

lemma primrec_roundAlphaMinusOne : Primrec roundAlphaMinusOne :=
  Primrec.nat_sub.comp primrec_roundSize (Primrec.const 1)

/-- Explicit bijection `RoundLetter I ≃ Fin (roundAlphaMinusOne I + 1)`. -/
def roundLetterEquiv (I : Instance) : RoundLetter I ≃ Fin (roundAlphaMinusOne I + 1) :=
  let eOut : (I.Y1 × I.Y2) ≃ Fin ((I.m1 + 1) * (I.m2 + 1)) :=
    prodFinEquiv (Nat.succ_pos _) (Nat.succ_pos _)
  let eGOut : (CommGraph × (I.Y1 × I.Y2)) ≃ Fin (3 * ((I.m1 + 1) * (I.m2 + 1))) :=
    (Equiv.prodCongr commGraphEquivFin3 eOut).trans (prodFinEquiv (by decide) (by positivity))
  let eX2 : (I.X2 × CommGraph × (I.Y1 × I.Y2)) ≃
      Fin ((I.k2 + 1) * (3 * ((I.m1 + 1) * (I.m2 + 1)))) :=
    (Equiv.prodCongr (Equiv.refl _) eGOut).trans
      (prodFinEquiv (Nat.succ_pos _) (by positivity))
  let eFlat : RoundLetter I ≃ (I.X1 × I.X2 × CommGraph × (I.Y1 × I.Y2)) :=
    { toFun := fun r => (r.1.1, r.1.2.1, r.1.2.2, r.2)
      invFun := fun t => ((t.1, t.2.1, t.2.2.1), t.2.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  eFlat.trans (((Equiv.prodCongr (Equiv.refl _) eX2).trans
    (prodFinEquiv (Nat.succ_pos _) (by positivity))).trans
      (finCongr (show I.k1.succ * ((I.k2 + 1) * (3 * ((I.m1 + 1) * (I.m2 + 1)))) =
        roundAlphaMinusOne I + 1 from (roundAlphaMinusOne_succ I).symm)))

@[simp] private lemma val_finCongr {m n : ℕ} (h : m = n) (x : Fin m) :
    (finCongr h x).val = x.val := by
  cases h; rfl

@[simp] private lemma val_finCongr_symm {m n : ℕ} (h : m = n) (x : Fin n) :
    ((finCongr h).symm x).val = x.val := by
  cases h; rfl

/-- Primitive-recursive extraction `(x1, x2, g, y1, y2)` from a round letter code `a : ℕ`. -/
def decodeRoundFields (I : Instance) (a : ℕ) : ℕ × ℕ × CommGraph × ℕ × ℕ :=
  let sOut := (I.m1 + 1) * (I.m2 + 1)
  let sG := 3 * sOut
  let sX2 := (I.k2 + 1) * sG
  let x1 := (a / sX2) % (I.k1 + 1)
  let r1 := a % sX2
  let x2 := r1 / sG
  let r2 := r1 % sG
  let g := graphOfNat (r2 / sOut)
  let r3 := r2 % sOut
  let y1 := r3 / (I.m2 + 1)
  let y2 := r3 % (I.m2 + 1)
  (x1, x2, g, y1, y2)

lemma decodeRoundFields_spec (I : Instance) (a : Fin (roundAlphaMinusOne I + 1)) :
    let r := (roundLetterEquiv I).symm a
    decodeRoundFields I a.val =
      (r.1.1.val, r.1.2.1.val, r.1.2.2, r.2.1.val, r.2.2.val) := by
  dsimp only
  have ha : a.val < roundSize I := a.isLt.trans_eq (roundAlphaMinusOne_succ I)
  unfold roundSize at ha
  have hx1_lt : a.val / ((I.k2 + 1) * (3 * ((I.m1 + 1) * (I.m2 + 1)))) < I.k1 + 1 :=
    Nat.div_lt_of_lt_mul (ha.trans_eq (Nat.mul_comm _ _))
  simp only [roundLetterEquiv, decodeRoundFields, Equiv.symm_trans_apply, prodFinEquiv,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_symm,
    Equiv.refl_apply, Equiv.coe_fn_symm_mk, commGraphEquivFin3_symm_eq]
  rw [Nat.mod_eq_of_lt hx1_lt, val_finCongr_symm]

lemma primrec_decodeRoundFields : Primrec₂ decodeRoundFields := by
  have hsOut : Primrec (fun p : Instance × ℕ => (p.1.m1 + 1) * (p.1.m2 + 1)) :=
    Primrec.nat_mul.comp (Primrec.succ.comp (primrec_m1.comp Primrec.fst))
      (Primrec.succ.comp (primrec_m2.comp Primrec.fst))
  have hsG : Primrec (fun p : Instance × ℕ => 3 * ((p.1.m1 + 1) * (p.1.m2 + 1))) :=
    Primrec.nat_mul.comp (Primrec.const 3) hsOut
  have hsX2 : Primrec (fun p : Instance × ℕ =>
      (p.1.k2 + 1) * (3 * ((p.1.m1 + 1) * (p.1.m2 + 1)))) :=
    Primrec.nat_mul.comp (Primrec.succ.comp (primrec_k2.comp Primrec.fst)) hsG
  have hr1 : Primrec (fun p : Instance × ℕ =>
      p.2 % ((p.1.k2 + 1) * (3 * ((p.1.m1 + 1) * (p.1.m2 + 1))))) :=
    Primrec.nat_mod.comp Primrec.snd hsX2
  have hr2 : Primrec (fun p : Instance × ℕ =>
      (p.2 % ((p.1.k2 + 1) * (3 * ((p.1.m1 + 1) * (p.1.m2 + 1))))) %
        (3 * ((p.1.m1 + 1) * (p.1.m2 + 1)))) :=
    Primrec.nat_mod.comp hr1 hsG
  have hr3 : Primrec (fun p : Instance × ℕ =>
      (((p.2 % ((p.1.k2 + 1) * (3 * ((p.1.m1 + 1) * (p.1.m2 + 1))))) %
        (3 * ((p.1.m1 + 1) * (p.1.m2 + 1)))) % ((p.1.m1 + 1) * (p.1.m2 + 1)))) :=
    Primrec.nat_mod.comp hr2 hsOut
  have hx1 := Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd hsX2)
    (Primrec.succ.comp (primrec_k1.comp Primrec.fst))
  have hx2 := Primrec.nat_div.comp hr1 hsG
  have hg := primrec_graphOfNat.comp (Primrec.nat_div.comp hr2 hsOut)
  have hy1 := Primrec.nat_div.comp hr3 (Primrec.succ.comp (primrec_m2.comp Primrec.fst))
  have hy2 := Primrec.nat_mod.comp hr3 (Primrec.succ.comp (primrec_m2.comp Primrec.fst))
  exact (hx1.pair (hx2.pair (hg.pair (hy1.pair hy2)))).of_eq fun _ => rfl

/-- Base-`M` encoding of `Fin d → Fin M` into `Fin (M ^ d)`. -/
def encodeDigits (M : ℕ) : ∀ {d : ℕ}, (Fin d → Fin M) → ℕ
  | 0, _ => 0
  | d + 1, f => (f ⟨0, Nat.succ_pos d⟩).val + M * encodeDigits M (fun i : Fin d => f i.succ)

def decodeDigitNat (M code i : ℕ) : ℕ :=
  (code / powNat M i) % M

lemma primrec_decodeDigitNat : Primrec (fun t : ℕ × ℕ × ℕ => decodeDigitNat t.1 t.2.1 t.2.2) :=
  Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
      (primrec_powNat.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
    Primrec.fst

lemma encodeDigits_lt {M : ℕ} (hM : 0 < M) : ∀ {d : ℕ} (f : Fin d → Fin M),
    encodeDigits M f < M ^ d
  | 0, _ => by simp [encodeDigits]
  | d + 1, f => by
    simp only [encodeDigits, pow_succ]
    have ih : encodeDigits M (fun i : Fin d => f i.succ) + 1 ≤ M ^ d := encodeDigits_lt hM _
    have h0 := (f ⟨0, Nat.succ_pos d⟩).isLt
    calc (f ⟨0, Nat.succ_pos d⟩).val + M * encodeDigits M (fun i : Fin d => f i.succ)
        < M + M * encodeDigits M (fun i : Fin d => f i.succ) := Nat.add_lt_add_right h0 _
      _ = M * (encodeDigits M (fun i : Fin d => f i.succ) + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      _ ≤ M * M ^ d := Nat.mul_le_mul_left M ih
      _ = M ^ d * M := Nat.mul_comm _ _

lemma decodeDigitNat_encodeDigits {M : ℕ} (hM : 0 < M) :
    ∀ {d : ℕ} (f : Fin d → Fin M) (i : Fin d),
      decodeDigitNat M (encodeDigits M f) i.val = (f i).val
  | 0, _, i => Fin.elim0 i
  | d + 1, f, i => by
    unfold decodeDigitNat
    rw [powNat_eq]
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.val_zero, pow_zero, Nat.div_one, encodeDigits]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (f ⟨0, Nat.succ_pos d⟩).isLt]
      rfl
    · intro j
      simp only [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, encodeDigits]
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt (f ⟨0, Nat.succ_pos d⟩).isLt, zero_add]
      have ih := decodeDigitNat_encodeDigits hM (fun k : Fin d => f k.succ) j
      unfold decodeDigitNat at ih
      rwa [powNat_eq] at ih

lemma encodeDigits_decodeDigitNat {M : ℕ} (hM : 0 < M) :
    ∀ {d : ℕ} (code : ℕ), code < M ^ d →
      encodeDigits M (fun i : Fin d => ⟨decodeDigitNat M code i.val, Nat.mod_lt _ hM⟩) = code
  | 0, code, hc => by simp at hc; simp [encodeDigits, hc]
  | d + 1, code, hc => by
    simp only [encodeDigits]
    have h0 : decodeDigitNat M code 0 = code % M := by simp [decodeDigitNat, powNat]
    have hsucc : ∀ i : Fin d, decodeDigitNat M code i.succ.val = decodeDigitNat M (code / M) i.val := by
      intro i
      simp only [decodeDigitNat, powNat_eq, Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul]
    have hfn : (fun i : Fin d => (⟨decodeDigitNat M code i.succ.val, Nat.mod_lt _ hM⟩ : Fin M)) =
        (fun i : Fin d => ⟨decodeDigitNat M (code / M) i.val, Nat.mod_lt _ hM⟩) := by
      funext i; exact Fin.ext (hsucc i)
    have hdiv_lt : code / M < M ^ d :=
      Nat.div_lt_of_lt_mul (by rwa [← pow_succ'])
    rw [h0, hfn, encodeDigits_decodeDigitNat hM (code / M) hdiv_lt]
    exact Nat.mod_add_div code M

def finFunEquiv {M : ℕ} (hM : 0 < M) (D : ℕ) : (Fin D → Fin M) ≃ Fin (M ^ D) where
  toFun f := ⟨encodeDigits M f, encodeDigits_lt hM f⟩
  invFun c i := ⟨decodeDigitNat M c.val i.val, Nat.mod_lt _ hM⟩
  left_inv f := by funext i; exact Fin.ext (decodeDigitNat_encodeDigits hM f i)
  right_inv c := Fin.ext (encodeDigits_decodeDigitNat hM c.val c.isLt)

@[simp] lemma finFunEquiv_apply_val {M : ℕ} (hM : 0 < M) (D : ℕ) (f : Fin D → Fin M) :
    (finFunEquiv hM D f).val = encodeDigits M f := rfl

/-- Cardinality `(roundSize I) ^ D ≥ 1` of the `D`-block alphabet. -/
def blockSize (I : Instance) (D : ℕ) : ℕ := powNat (roundSize I) D

lemma blockSize_eq (I : Instance) (D : ℕ) : blockSize I D = (roundSize I) ^ D :=
  powNat_eq (roundSize I) D

lemma blockSize_pos (I : Instance) (D : ℕ) : 0 < blockSize I D := by
  rw [blockSize_eq]; exact pow_pos (roundSize_pos I) D

/-- `blockAlphaMinusOne I D + 1 = blockSize I D`. -/
def blockAlphaMinusOne (I : Instance) (D : ℕ) : ℕ := blockSize I D - 1

lemma blockAlphaMinusOne_succ (I : Instance) (D : ℕ) :
    blockAlphaMinusOne I D + 1 = (roundSize I) ^ D :=
  (Nat.sub_add_cancel (blockSize_pos I D)).trans (blockSize_eq I D)

lemma primrec_blockSize : Primrec₂ blockSize :=
  primrec_powNat.comp (primrec_roundSize.comp Primrec.fst) Primrec.snd

lemma primrec_blockAlphaMinusOne : Primrec₂ blockAlphaMinusOne :=
  Primrec.nat_sub.comp primrec_blockSize (Primrec.const 1)

/-- Explicit bijection `(Fin D → RoundLetter I) ≃ Fin (blockAlphaMinusOne I D + 1)`. -/
def blockLetterEquiv (I : Instance) (D : ℕ) :
    (Fin D → RoundLetter I) ≃ Fin (blockAlphaMinusOne I D + 1) :=
  (Equiv.arrowCongr (Equiv.refl (Fin D))
    ((roundLetterEquiv I).trans (finCongr (roundAlphaMinusOne_succ I)))).trans
    ((finFunEquiv (roundSize_pos I) D).trans (finCongr (blockAlphaMinusOne_succ I D).symm))

lemma decodeDigitNat_blockLetterEquiv (I : Instance) (D : ℕ)
    (blk : Fin D → RoundLetter I) (t : Fin D) :
    decodeDigitNat (roundSize I) (blockLetterEquiv I D blk).val t.val =
      (roundLetterEquiv I (blk t)).val := by
  simp only [blockLetterEquiv, Equiv.trans_apply, val_finCongr, finFunEquiv_apply_val]
  rw [decodeDigitNat_encodeDigits (roundSize_pos I)]
  simp only [Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, Equiv.refl_apply,
    Equiv.trans_apply, val_finCongr]

/-- Pull back a `GenDPACode` over `Fin (blockAlphaMinusOne I D + 1)` to a `DPA` over
`Fin D → RoundLetter I`. -/
def blockDPAOf (I : Instance) (D : ℕ) (blockCode : GenDPACode) :
    DPA (Fin (blockCode.1 + 1)) (Fin D → RoundLetter I) where
  init := (toGenDPA (blockAlphaMinusOne I D) blockCode).init
  step q blk := (toGenDPA (blockAlphaMinusOne I D) blockCode).step q (blockLetterEquiv I D blk)
  prio := (toGenDPA (blockAlphaMinusOne I D) blockCode).prio

lemma blockDPAOf_run (I : Instance) (D : ℕ) (blockCode : GenDPACode)
    (W : ℕ → Fin D → RoundLetter I) (n : ℕ) :
    (blockDPAOf I D blockCode).run W n =
      (toGenDPA (blockAlphaMinusOne I D) blockCode).run (fun k => blockLetterEquiv I D (W k)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [DPA.run]
    rw [ih]
    rfl

lemma blockDPAOf_accepts_iff (I : Instance) (D : ℕ) (blockCode : GenDPACode)
    (W : ℕ → Fin D → RoundLetter I) :
    (blockDPAOf I D blockCode).Accepts W ↔
      (toGenDPA (blockAlphaMinusOne I D) blockCode).Accepts (fun k => blockLetterEquiv I D (W k)) := by
  unfold DPA.Accepts
  simp only [blockDPAOf_run]
  rfl

/-! ### Section 2: `instFormulaOf`, Prefix-Polish Stack Parser, `Primcodable Formula`, and `evalPrefix` -/

lemma sat_tt {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    (Formula.tt : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.tt, Formula.Sat]; exact em _

lemma sat_ff {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) :
    ¬ (Formula.ff : Formula X1 X2 Y1 Y2).Sat e := by
  simp only [Formula.ff, Formula.Sat]; exact not_not_intro (sat_tt e)

@[simp] lemma shift_zero {α : Type} (e : ℕ → α) : shift e 0 = e := rfl

lemma shift_valExec {a b c d : ℕ} (e : ℕ → Signal (Fin a) (Fin b) × (Fin c × Fin d)) (r : ℕ) :
    shift (valExec e) r = valExec (shift e r) := rfl

lemma shift_shift {α : Type} (e : ℕ → α) (a b : ℕ) :
    shift (shift e a) b = shift e (a + b) := by
  funext n; simp only [shift]; congr 1; omega

theorem sat_instFormulaOf (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ)
    (e : ℕ → RoundLetter I) :
    (instFormulaOf I φ).Sat e ↔ φ.Sat (valExec e) := by
  induction φ generalizing e with
  | inp1 x =>
    simp only [instFormulaOf]
    by_cases h : x < I.k1 + 1
    · rw [dif_pos h]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg h]
      exact ⟨fun hf => False.elim (sat_ff e hf),
        fun hv => False.elim (h (hv ▸ (e 0).1.1.isLt))⟩
  | inp2 x =>
    simp only [instFormulaOf]
    by_cases h : x < I.k2 + 1
    · rw [dif_pos h]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg h]
      exact ⟨fun hf => False.elim (sat_ff e hf),
        fun hv => False.elim (h (hv ▸ (e 0).1.2.1.isLt))⟩
  | out1 y =>
    simp only [instFormulaOf]
    by_cases h : y < I.m1 + 1
    · rw [dif_pos h]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg h]
      exact ⟨fun hf => False.elim (sat_ff e hf),
        fun hv => False.elim (h (hv ▸ (e 0).2.1.isLt))⟩
  | out2 y =>
    simp only [instFormulaOf]
    by_cases h : y < I.m2 + 1
    · rw [dif_pos h]; simp [Formula.Sat, valExec, Fin.ext_iff]
    · rw [dif_neg h]
      exact ⟨fun hf => False.elim (sat_ff e hf),
        fun hv => False.elim (h (hv ▸ (e 0).2.2.isLt))⟩
  | graph g => rfl
  | next φ ih => simp only [instFormulaOf, Formula.Sat, shift_valExec, ih]
  | eventually φ ih => simp only [instFormulaOf, Formula.Sat, shift_valExec, ih]
  | always φ ih => simp only [instFormulaOf, Formula.Sat, shift_valExec, ih]
  | untl φ ψ ih1 ih2 => simp only [instFormulaOf, Formula.Sat, shift_valExec, ih1, ih2]
  | weakUntil ψ φ ih1 ih2 => simp only [instFormulaOf, Formula.Sat, shift_valExec, ih1, ih2]
  | neg φ ih => simp only [instFormulaOf, Formula.Sat, ih]
  | or φ ψ ih1 ih2 => simp only [instFormulaOf, Formula.Sat, ih1, ih2]
  | and φ ψ ih1 ih2 => simp only [instFormulaOf, Formula.Sat, ih1, ih2]
  | imp φ ψ ih1 ih2 => simp only [instFormulaOf, Formula.Sat, ih1, ih2]
  | iff φ ψ ih1 ih2 => simp only [instFormulaOf, Formula.Sat, ih1, ih2]

/-- Canonical prefix-Polish serializer `Formula ℕ ℕ ℕ ℕ → List Token`. -/
def encFormula : Formula ℕ ℕ ℕ ℕ → List Token
  | .inp1 x => [(0, 1, x)]
  | .inp2 x => [(0, 2, x)]
  | .out1 y => [(1, 1, y)]
  | .out2 y => [(1, 2, y)]
  | .graph .oneToTwo => [(2, 0, 0)]
  | .graph .both => [(2, 1, 0)]
  | .graph .twoToOne => [(2, 2, 0)]
  | .next φ => (3, 0, 0) :: encFormula φ
  | .eventually φ => (4, 0, 0) :: encFormula φ
  | .always φ => (5, 0, 0) :: encFormula φ
  | .untl φ ψ => (6, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .weakUntil ψ φ => (7, 0, 0) :: (encFormula ψ ++ encFormula φ)
  | .neg φ => (8, 0, 0) :: encFormula φ
  | .or φ ψ => (9, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .and φ ψ => (10, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .imp φ ψ => (11, 0, 0) :: (encFormula φ ++ encFormula ψ)
  | .iff φ ψ => (12, 0, 0) :: (encFormula φ ++ encFormula ψ)

lemma parseAux_enc (φ : Formula ℕ ℕ ℕ ℕ) :
    ∀ (rest : List Token) (m : ℕ), (encFormula φ).length ≤ m →
      parseAux m (encFormula φ ++ rest) = some (φ, rest) := by
  induction φ with
  | inp1 x => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | inp2 x => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | out1 y => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | out2 y => intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl
  | graph g =>
    intro rest m hm
    cases g <;> (obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩; rfl)
  | next φ ih =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | eventually φ ih =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | always φ ih =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | neg φ ih =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp [encFormula, parseAux, ih rest k (by simp [encFormula] at hm; omega)]
  | untl φ ψ ih1 ih2 =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | weakUntil ψ φ ih1 ih2 =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula φ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | or φ ψ ih1 ih2 =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | and φ ψ ih1 ih2 =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | imp φ ψ ih1 ih2 =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]
  | iff φ ψ ih1 ih2 =>
    intro rest m hm; obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp [encFormula] at hm; omega⟩
    simp only [encFormula, List.cons_append, List.append_assoc, parseAux]
    rw [ih1 (encFormula ψ ++ rest) k (by simp [encFormula] at hm; omega)]; dsimp only
    rw [ih2 rest k (by simp [encFormula] at hm; omega)]

lemma parse_encFormula (φ : Formula ℕ ℕ ℕ ℕ) : parse (encFormula φ) = some φ := by
  unfold parse
  have h := parseAux_enc φ [] (encFormula φ).length le_rfl
  rw [List.append_nil] at h
  rw [h]

lemma encFormula_injective : Function.Injective encFormula := fun φ ψ h =>
  Option.some.inj ((parse_encFormula φ).symm.trans (by rw [h, parse_encFormula]))

instance instDecidableEqFormulaNat : DecidableEq (Formula ℕ ℕ ℕ ℕ) :=
  fun φ ψ => decidable_of_iff (encFormula φ = encFormula ψ) encFormula_injective.eq_iff

/-- Right-to-left stack step normalizing any valid prefix-Polish token stream. -/
def stackStep (t : Token) (acc : Option (List (List Token))) : Option (List (List Token)) :=
  match acc with
  | none => none
  | some stk =>
    if t.1 = 0 then
      if t.2.1 = 1 then some ([(0, 1, t.2.2)] :: stk)
      else if t.2.1 = 2 then some ([(0, 2, t.2.2)] :: stk)
      else none
    else if t.1 = 1 then
      if t.2.1 = 1 then some ([(1, 1, t.2.2)] :: stk)
      else if t.2.1 = 2 then some ([(1, 2, t.2.2)] :: stk)
      else none
    else if t.1 = 2 then
      if t.2.1 = 0 then some ([(2, 0, 0)] :: stk)
      else if t.2.1 = 1 then some ([(2, 1, 0)] :: stk)
      else if t.2.1 = 2 then some ([(2, 2, 0)] :: stk)
      else none
    else if t.1 = 3 ∨ t.1 = 4 ∨ t.1 = 5 ∨ t.1 = 8 then
      match stk with
      | c1 :: rest => some (((t.1, 0, 0) :: c1) :: rest)
      | [] => none
    else if t.1 = 6 ∨ t.1 = 7 ∨ t.1 = 9 ∨ t.1 = 10 ∨ t.1 = 11 ∨ t.1 = 12 then
      match stk with
      | c1 :: c2 :: rest => some (((t.1, 0, 0) :: (c1 ++ c2)) :: rest)
      | _ => none
    else none

def normTokens (ts : List Token) : Option (List Token) :=
  match ts.foldr stackStep (some []) with
  | some [c] => some c
  | _ => none

lemma primrec_stackStep : Primrec₂ stackStep := by
  have hUnPred : PrimrecPred (fun p : Token × List (List Token) =>
      p.1.1 = 3 ∨ p.1.1 = 4 ∨ p.1.1 = 5 ∨ p.1.1 = 8) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 3)).or
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 4)).or
        ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 5)).or
          (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 8))))
  have hBinPred : PrimrecPred (fun p : Token × List (List Token) =>
      p.1.1 = 6 ∨ p.1.1 = 7 ∨ p.1.1 = 9 ∨ p.1.1 = 10 ∨ p.1.1 = 11 ∨ p.1.1 = 12) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 6)).or
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 7)).or
        ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 9)).or
          ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 10)).or
            ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 11)).or
              (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 12))))))
  have hTagTok : Primrec (fun p : Token × List (List Token) => (p.1.1, (0 : ℕ), (0 : ℕ))) :=
    (Primrec.fst.comp Primrec.fst).pair (Primrec.const (0, 0))
  have hUnBody : Primrec (fun p : Token × List (List Token) =>
      match p.2 with
      | c1 :: rest => some (((p.1.1, 0, 0) :: c1) :: rest)
      | [] => none) :=
    (Primrec.list_casesOn Primrec.snd (Primrec.const none)
      (Primrec.option_some.comp
        (Primrec.list_cons.comp
          (Primrec.list_cons.comp (hTagTok.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd))).to₂).of_eq fun p => by cases p.2 <;> rfl
  have hBinBody : Primrec (fun p : Token × List (List Token) =>
      match p.2 with
      | c1 :: c2 :: rest => some (((p.1.1, 0, 0) :: (c1 ++ c2)) :: rest)
      | _ => none) :=
    (Primrec.list_casesOn Primrec.snd (Primrec.const none)
      (Primrec.list_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const none)
        (Primrec.option_some.comp
          (Primrec.list_cons.comp
            (Primrec.list_cons.comp
              (hTagTok.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.list_append.comp
                (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
                (Primrec.fst.comp Primrec.snd)))
            (Primrec.snd.comp Primrec.snd))).to₂).to₂).of_eq fun p => by
      rcases p.2 with _ | ⟨c1, _ | ⟨c2, rest⟩⟩ <;> rfl
  have hMkAtom : ∀ tag a : ℕ, Primrec (fun p : Token × List (List Token) =>
      some ([(tag, a, p.1.2.2)] :: p.2)) := fun tag a =>
    Primrec.option_some.comp
      (Primrec.list_cons.comp
        (Primrec.list_cons.comp
          ((Primrec.const tag).pair ((Primrec.const a).pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
          (Primrec.const []))
        Primrec.snd)
  have hMkGraph : ∀ a : ℕ, Primrec (fun p : Token × List (List Token) =>
      some ([(2, a, 0)] :: p.2)) := fun a =>
    Primrec.option_some.comp
      (Primrec.list_cons.comp (Primrec.const [(2, a, 0)]) Primrec.snd)
  have ht1 : Primrec (fun p : Token × List (List Token) => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have ht21 : Primrec (fun p : Token × List (List Token) => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hSome : Primrec (fun p : Token × List (List Token) => stackStep p.1 (some p.2)) :=
    (Primrec.ite (Primrec.eq.comp ht1 (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 1)) (hMkAtom 0 1)
        (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 2)) (hMkAtom 0 2) (Primrec.const none)))
      (Primrec.ite (Primrec.eq.comp ht1 (Primrec.const 1))
        (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 1)) (hMkAtom 1 1)
          (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 2)) (hMkAtom 1 2) (Primrec.const none)))
        (Primrec.ite (Primrec.eq.comp ht1 (Primrec.const 2))
          (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 0)) (hMkGraph 0)
            (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 1)) (hMkGraph 1)
              (Primrec.ite (Primrec.eq.comp ht21 (Primrec.const 2)) (hMkGraph 2) (Primrec.const none))))
          (Primrec.ite hUnPred hUnBody (Primrec.ite hBinPred hBinBody (Primrec.const none)))))).of_eq
      fun _ => rfl
  exact (Primrec.option_casesOn Primrec.snd (Primrec.const none)
    (hSome.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂).of_eq fun p => by
    cases p.2 <;> rfl

lemma primrec_normTokens : Primrec normTokens := by
  have hfold : Primrec (fun ts : List Token => ts.foldr stackStep (some [])) :=
    (Primrec.list_foldr Primrec.id (Primrec.const (some []))
      (primrec_stackStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      fun _ => rfl
  have hpost : Primrec (fun o : Option (List (List Token)) =>
      match o with | some [c] => some c | _ => none) :=
    (Primrec.option_casesOn Primrec.id (Primrec.const none)
      (Primrec.list_casesOn Primrec.snd (Primrec.const none)
        (Primrec.list_casesOn (Primrec.snd.comp Primrec.snd)
          (Primrec.option_some.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.const none).to₂).to₂).to₂).of_eq fun o => by
      rcases o with _ | ⟨_ | ⟨c, _ | _⟩⟩ <;> rfl
  exact hpost.comp hfold

private def GoodSlice (u : List Token) (φ : Formula ℕ ℕ ℕ ℕ) : Prop :=
  ∀ (rest : List Token) (m : ℕ), u.length ≤ m → parseAux m (u ++ rest) = some (φ, rest)

private lemma parseAux_implies_stackStep (m : ℕ) :
    ∀ (ts : List Token) (φ : Formula ℕ ℕ ℕ ℕ) (r : List Token),
      parseAux m ts = some (φ, r) →
        ∃ u : List Token, ts = u ++ r ∧
          ∀ stk, u.foldr stackStep (some stk) = some (encFormula φ :: stk) := by
  induction m with
  | zero => intro ts φ r h; simp [parseAux] at h
  | succ m ih =>
    intro ts φ r h
    rcases ts with _ | ⟨⟨tag, a, b⟩, ts'⟩
    · simp [parseAux] at h
    · simp only [parseAux] at h
      have hUn : ∀ (mk : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ),
          (htag : tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 8) →
          (henc : ∀ α, encFormula (mk α) = (tag, 0, 0) :: encFormula α) →
          (match parseAux m ts' with | some (α, r') => some (mk α, r') | none => none) = some (φ, r) →
          ∃ u, (tag, a, b) :: ts' = u ++ r ∧
            ∀ stk, u.foldr stackStep (some stk) = some (encFormula φ :: stk) := by
        intro mk htag henc hm
        cases hp : parseAux m ts' with
        | none => simp [hp] at hm
        | some pr =>
          rcases pr with ⟨α, r'⟩
          simp only [hp, Option.some.injEq, Prod.mk.injEq] at hm
          rcases hm with ⟨hφ, hr⟩
          rw [hr] at hp
          obtain ⟨u1, rfl, hu1⟩ := ih ts' α r hp
          refine ⟨(tag, a, b) :: u1, rfl, fun stk => ?_⟩
          rw [← hφ]
          simp only [List.foldr_cons, hu1 stk]
          rcases htag with rfl | rfl | rfl | rfl <;> simp [stackStep, henc]
      have hBin : ∀ (mk : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ),
          (htag : tag = 6 ∨ tag = 7 ∨ tag = 9 ∨ tag = 10 ∨ tag = 11 ∨ tag = 12) →
          (henc : ∀ α β, encFormula (mk α β) = (tag, 0, 0) :: (encFormula α ++ encFormula β)) →
          (match parseAux m ts' with
            | some (α, r1) => match parseAux m r1 with | some (β, r2) => some (mk α β, r2) | none => none
            | none => none) = some (φ, r) →
          ∃ u, (tag, a, b) :: ts' = u ++ r ∧
            ∀ stk, u.foldr stackStep (some stk) = some (encFormula φ :: stk) := by
        intro mk htag henc hm
        cases hp1 : parseAux m ts' with
        | none => simp [hp1] at hm
        | some pr1 =>
          rcases pr1 with ⟨α, r1⟩
          simp only [hp1] at hm
          cases hp2 : parseAux m r1 with
          | none => simp [hp2] at hm
          | some pr2 =>
            rcases pr2 with ⟨β, r2⟩
            simp only [hp2, Option.some.injEq, Prod.mk.injEq] at hm
            rcases hm with ⟨hφ, hr⟩
            rw [hr] at hp2
            obtain ⟨u1, rfl, hu1⟩ := ih ts' α r1 hp1
            obtain ⟨u2, rfl, hu2⟩ := ih r1 β r hp2
            refine ⟨(tag, a, b) :: (u1 ++ u2), by simp [List.append_assoc], fun stk => ?_⟩
            rw [← hφ]
            simp only [List.foldr_cons, List.foldr_append, hu2 stk, hu1]
            rcases htag with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [stackStep, henc]
      rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag
      · rcases a with _ | _ | _ | a <;> simp at h
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(0, 1, b)], rfl, fun _ => rfl⟩
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(0, 2, b)], rfl, fun _ => rfl⟩
      · rcases a with _ | _ | _ | a <;> simp at h
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(1, 1, b)], rfl, fun _ => rfl⟩
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(1, 2, b)], rfl, fun _ => rfl⟩
      · rcases a with _ | _ | _ | a <;> simp at h
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(2, 0, b)], rfl, fun _ => rfl⟩
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(2, 1, b)], rfl, fun _ => rfl⟩
        · rcases h with ⟨hφ, hr⟩; rw [← hφ, ← hr]; exact ⟨[(2, 2, b)], rfl, fun _ => rfl⟩
      · exact hUn .next (Or.inl rfl) (fun _ => rfl) h
      · exact hUn .eventually (Or.inr (Or.inl rfl)) (fun _ => rfl) h
      · exact hUn .always (Or.inr (Or.inr (Or.inl rfl))) (fun _ => rfl) h
      · exact hBin .untl (Or.inl rfl) (fun _ _ => rfl) h
      · exact hBin .weakUntil (Or.inr (Or.inl rfl)) (fun _ _ => rfl) h
      · exact hUn .neg (Or.inr (Or.inr (Or.inr rfl))) (fun _ => rfl) h
      · exact hBin .or (Or.inr (Or.inr (Or.inl rfl))) (fun _ _ => rfl) h
      · exact hBin .and (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (fun _ _ => rfl) h
      · exact hBin .imp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (fun _ _ => rfl) h
      · exact hBin .iff (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (fun _ _ => rfl) h
      · simp at h

private lemma stackStep_single_implies_goodSlice (t : Token) (stk' stk : List (List Token))
    (hstep : stackStep t (some stk') = some stk)
    (us' : List (List Token)) (fs' : List (Formula ℕ ℕ ℕ ℕ))
    (hstk' : stk' = fs'.map encFormula)
    (hgood' : List.Forall₂ GoodSlice us' fs') :
    ∃ (us : List (List Token)) (fs : List (Formula ℕ ℕ ℕ ℕ)),
      stk = fs.map encFormula ∧ us.flatten = t :: us'.flatten ∧ List.Forall₂ GoodSlice us fs := by
  rcases t with ⟨tag, a, b⟩
  have hAtom : ∀ (φ : Formula ℕ ℕ ℕ ℕ),
      stk = encFormula φ :: stk' →
      (∀ rest k, parseAux (k + 1) ((tag, a, b) :: rest) = some (φ, rest)) →
      ∃ us fs, stk = fs.map encFormula ∧ us.flatten = (tag, a, b) :: us'.flatten ∧
        List.Forall₂ GoodSlice us fs := by
    intro φ hstk hpa
    refine ⟨[(tag, a, b)] :: us', φ :: fs', by rw [hstk, hstk']; rfl, rfl,
      List.Forall₂.cons ?_ hgood'⟩
    intro rest m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp at hm; omega⟩
    exact hpa rest k
  have hUn : ∀ (mk : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ),
      (match stk' with | c1 :: rest => some (((tag, 0, 0) :: c1) :: rest) | [] => none) = some stk →
      (∀ α, encFormula (mk α) = (tag, 0, 0) :: encFormula α) →
      (∀ rest k, parseAux (k + 1) ((tag, a, b) :: rest) =
        match parseAux k rest with | some (α, r) => some (mk α, r) | none => none) →
      ∃ us fs, stk = fs.map encFormula ∧ us.flatten = (tag, a, b) :: us'.flatten ∧
        List.Forall₂ GoodSlice us fs := by
    intro mk hm henc hpa
    rcases fs' with _ | ⟨α, fs_r⟩
    · simp [hstk'] at hm
    · rcases us' with _ | ⟨u1, us_r⟩
      · cases hgood'
      · cases hgood' with
        | cons hg1 hg_rest =>
          simp only [hstk', List.map_cons, Option.some.injEq] at hm
          refine ⟨((tag, a, b) :: u1) :: us_r, mk α :: fs_r,
            by rw [← hm, List.map_cons, henc],
            by simp [List.flatten], List.Forall₂.cons ?_ hg_rest⟩
          intro rest m hm_len
          obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp at hm_len; omega⟩
          rw [List.cons_append, hpa, hg1 rest k (by simp at hm_len; omega)]
  have hBin : ∀ (mk : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ),
      (match stk' with | c1 :: c2 :: rest => some (((tag, 0, 0) :: (c1 ++ c2)) :: rest) | _ => none) = some stk →
      (∀ α β, encFormula (mk α β) = (tag, 0, 0) :: (encFormula α ++ encFormula β)) →
      (∀ rest k, parseAux (k + 1) ((tag, a, b) :: rest) =
        match parseAux k rest with
        | some (α, r) => match parseAux k r with | some (β, r') => some (mk α β, r') | none => none
        | none => none) →
      ∃ us fs, stk = fs.map encFormula ∧ us.flatten = (tag, a, b) :: us'.flatten ∧
        List.Forall₂ GoodSlice us fs := by
    intro mk hm henc hpa
    rcases fs' with _ | ⟨α, _ | ⟨β, fs_r⟩⟩
    · simp [hstk'] at hm
    · simp [hstk'] at hm
    · rcases us' with _ | ⟨u1, _ | ⟨u2, us_r⟩⟩
      · cases hgood'
      · cases hgood' with | cons _ h2 => cases h2
      · cases hgood' with
        | cons hg1 h2 =>
          cases h2 with
          | cons hg2 hg_rest =>
            simp only [hstk', List.map_cons, Option.some.injEq] at hm
            refine ⟨((tag, a, b) :: (u1 ++ u2)) :: us_r, mk α β :: fs_r,
              by rw [← hm, List.map_cons, henc],
              by simp [List.flatten, List.append_assoc], List.Forall₂.cons ?_ hg_rest⟩
            intro rest m hm_len
            obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by simp at hm_len; omega⟩
            have hk1 : u1.length ≤ k := by simp at hm_len; omega
            have hk2 : u2.length ≤ k := by simp at hm_len; omega
            rw [List.cons_append, List.append_assoc, hpa, hg1 (u2 ++ rest) k hk1]; dsimp only
            rw [hg2 rest k hk2]
  rcases tag with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag
  · rcases a with _ | _ | _ | a <;> simp [stackStep] at hstep
    · exact hAtom (.inp1 b) hstep.symm (fun _ _ => rfl)
    · exact hAtom (.inp2 b) hstep.symm (fun _ _ => rfl)
  · rcases a with _ | _ | _ | a <;> simp [stackStep] at hstep
    · exact hAtom (.out1 b) hstep.symm (fun _ _ => rfl)
    · exact hAtom (.out2 b) hstep.symm (fun _ _ => rfl)
  · rcases a with _ | _ | _ | a <;> simp [stackStep] at hstep
    · exact hAtom (.graph .oneToTwo) hstep.symm (fun _ _ => rfl)
    · exact hAtom (.graph .both) hstep.symm (fun _ _ => rfl)
    · exact hAtom (.graph .twoToOne) hstep.symm (fun _ _ => rfl)
  · exact hUn .next (by simpa [stackStep] using hstep) (fun _ => rfl) (fun _ _ => rfl)
  · exact hUn .eventually (by simpa [stackStep] using hstep) (fun _ => rfl) (fun _ _ => rfl)
  · exact hUn .always (by simpa [stackStep] using hstep) (fun _ => rfl) (fun _ _ => rfl)
  · exact hBin .untl (by simpa [stackStep] using hstep) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact hBin .weakUntil (by simpa [stackStep] using hstep) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact hUn .neg (by simpa [stackStep] using hstep) (fun _ => rfl) (fun _ _ => rfl)
  · exact hBin .or (by simpa [stackStep] using hstep) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact hBin .and (by simpa [stackStep] using hstep) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact hBin .imp (by simpa [stackStep] using hstep) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact hBin .iff (by simpa [stackStep] using hstep) (fun _ _ => rfl) (fun _ _ => rfl)
  · simp [stackStep] at hstep

private lemma foldr_stackStep_goodSlices (ts : List Token) :
    ∀ (stk : List (List Token)), ts.foldr stackStep (some []) = some stk →
      ∃ (us : List (List Token)) (fs : List (Formula ℕ ℕ ℕ ℕ)),
        stk = fs.map encFormula ∧ us.flatten = ts ∧ List.Forall₂ GoodSlice us fs := by
  induction ts with
  | nil =>
    intro stk h
    simp only [List.foldr_nil, Option.some.injEq] at h
    exact ⟨[], [], h.symm, rfl, List.Forall₂.nil⟩
  | cons t tl ih =>
    intro stk h
    simp only [List.foldr_cons] at h
    cases htl : tl.foldr stackStep (some []) with
    | none => rw [htl] at h; simp [stackStep] at h
    | some stk' =>
      rw [htl] at h
      obtain ⟨us', fs', hstk', hflat', hgood'⟩ := ih stk' htl
      obtain ⟨us, fs, hstk, hflat, hgood⟩ :=
        stackStep_single_implies_goodSlice t stk' stk h us' fs' hstk' hgood'
      exact ⟨us, fs, hstk, by rwa [hflat'] at hflat, hgood⟩

lemma normTokens_eq_parse_map (ts : List Token) :
    normTokens ts = (parse ts).map encFormula := by
  unfold normTokens
  cases hp : parse ts with
  | some φ =>
    unfold parse at hp
    cases hpa : parseAux ts.length ts with
    | none => simp [hpa] at hp
    | some pr =>
      rcases pr with ⟨ψ, rem⟩
      rw [hpa] at hp
      rcases rem with _ | _
      · simp only [Option.some.injEq] at hp; subst hp
        obtain ⟨u, hu_eq, hu_fold⟩ := parseAux_implies_stackStep ts.length ts ψ [] hpa
        rw [List.append_nil] at hu_eq; subst hu_eq
        rw [hu_fold []]
        rfl
      · simp at hp
  | none =>
    simp only [Option.map_none]
    cases hf : ts.foldr stackStep (some []) with
    | none => rfl
    | some stk =>
      rcases stk with _ | ⟨c, _ | ⟨c2, rest⟩⟩
      · rfl
      · obtain ⟨us, fs, hstk, hflat, hgood⟩ := foldr_stackStep_goodSlices ts [c] hf
        rcases fs with _ | ⟨φ1, _ | _⟩
        · simp at hstk
        · rcases us with _ | ⟨u1, _ | _⟩
          · cases hgood
          · cases hgood with
            | cons hg1 _ =>
              simp at hflat
              subst hflat
              have hp_some : parse u1 = some φ1 := by
                unfold parse
                have h1 := hg1 [] u1.length le_rfl
                simp at h1
                rw [h1]
              rw [hp_some] at hp; simp at hp
          · cases hgood with | cons _ h2 => cases h2
        · simp at hstk
      · rfl

instance instEncodableFormulaNat : Encodable (Formula ℕ ℕ ℕ ℕ) :=
  Encodable.ofLeftInjection encFormula parse parse_encFormula

private lemma encode_option_formula_eq (o : Option (Formula ℕ ℕ ℕ ℕ)) :
    Encodable.encode o = Encodable.encode (o.map encFormula) := by
  cases o <;> rfl

instance instPrimcodableFormulaNat : Primcodable (Formula ℕ ℕ ℕ ℕ) where
  prim := by
    have h : Primrec (fun n : ℕ =>
        Encodable.encode ((Encodable.decode (α := List Token) n).bind normTokens)) :=
      Primrec.encode.comp
        (Primrec.option_bind Primrec.decode (primrec_normTokens.comp Primrec.snd).to₂)
    have h' : Primrec (fun n : ℕ =>
        Encodable.encode (Encodable.decode (α := Formula ℕ ℕ ℕ ℕ) n)) := by
      refine h.of_eq fun n => ?_
      change _ = Encodable.encode ((Encodable.decode (α := List Token) n).bind parse)
      rw [encode_option_formula_eq]
      cases Encodable.decode (α := List Token) n with
      | none => rfl
      | some ts => simp [normTokens_eq_parse_map]
    exact Primrec.nat_iff.mp h'

lemma primrec_encFormula : Primrec encFormula := by
  have h : Primrec (fun φ : Formula ℕ ℕ ℕ ℕ => Encodable.encode (encFormula φ)) :=
    Primrec.encode.of_eq fun _ => rfl
  exact Primrec.encode_iff.mp h

theorem primrec_parse : Primrec parse := by
  have h : Primrec (fun ts : List Token => Encodable.encode (parse ts)) :=
    (Primrec.encode.comp primrec_normTokens).of_eq fun ts =>
      (congrArg Encodable.encode (normTokens_eq_parse_map ts)).trans
        (encode_option_formula_eq (parse ts)).symm
  exact Primrec.encode_iff.mp h

lemma primrec_formula_inp1 : Primrec (Formula.inp1 : ℕ → Formula ℕ ℕ ℕ ℕ) := by
  have h : Primrec (fun x : ℕ => Encodable.encode (Formula.inp1 x : Formula ℕ ℕ ℕ ℕ)) :=
    (Primrec.encode.comp
      (Primrec.list_cons.comp
        ((Primrec.const 0).pair ((Primrec.const 1).pair Primrec.id))
        (Primrec.const []))).of_eq fun _ => rfl
  exact Primrec.encode_iff.mp h

lemma primrec_formula_inp2 : Primrec (Formula.inp2 : ℕ → Formula ℕ ℕ ℕ ℕ) := by
  have h : Primrec (fun x : ℕ => Encodable.encode (Formula.inp2 x : Formula ℕ ℕ ℕ ℕ)) :=
    (Primrec.encode.comp
      (Primrec.list_cons.comp
        ((Primrec.const 0).pair ((Primrec.const 2).pair Primrec.id))
        (Primrec.const []))).of_eq fun _ => rfl
  exact Primrec.encode_iff.mp h

lemma primrec_formula_out1 : Primrec (Formula.out1 : ℕ → Formula ℕ ℕ ℕ ℕ) := by
  have h : Primrec (fun y : ℕ => Encodable.encode (Formula.out1 y : Formula ℕ ℕ ℕ ℕ)) :=
    (Primrec.encode.comp
      (Primrec.list_cons.comp
        ((Primrec.const 1).pair ((Primrec.const 1).pair Primrec.id))
        (Primrec.const []))).of_eq fun _ => rfl
  exact Primrec.encode_iff.mp h

lemma primrec_formula_out2 : Primrec (Formula.out2 : ℕ → Formula ℕ ℕ ℕ ℕ) := by
  have h : Primrec (fun y : ℕ => Encodable.encode (Formula.out2 y : Formula ℕ ℕ ℕ ℕ)) :=
    (Primrec.encode.comp
      (Primrec.list_cons.comp
        ((Primrec.const 1).pair ((Primrec.const 2).pair Primrec.id))
        (Primrec.const []))).of_eq fun _ => rfl
  exact Primrec.encode_iff.mp h

lemma primrec_formula_graph : Primrec (Formula.graph : CommGraph → Formula ℕ ℕ ℕ ℕ) := by
  have h : Primrec (fun g : CommGraph => Encodable.encode (Formula.graph g : Formula ℕ ℕ ℕ ℕ)) :=
    (Primrec.encode.comp
      (Primrec.list_cons.comp
        ((Primrec.const 2).pair (primrec_commGraphIdx.pair (Primrec.const 0)))
        (Primrec.const []))).of_eq fun g => by cases g <;> rfl
  exact Primrec.encode_iff.mp h

private lemma primrec_formula_un (tag : ℕ) (mk : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ)
    (henc : ∀ α, encFormula (mk α) = (tag, 0, 0) :: encFormula α) : Primrec mk := by
  have h : Primrec (fun α : Formula ℕ ℕ ℕ ℕ => Encodable.encode (mk α)) :=
    (Primrec.encode.comp (Primrec.list_cons.comp (Primrec.const (tag, 0, 0)) primrec_encFormula)).of_eq
      fun α => congrArg Encodable.encode (henc α).symm
  exact Primrec.encode_iff.mp h

private lemma primrec_formula_bin (tag : ℕ) (mk : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ)
    (henc : ∀ α β, encFormula (mk α β) = (tag, 0, 0) :: (encFormula α ++ encFormula β)) : Primrec₂ mk := by
  have h : Primrec (fun p : Formula ℕ ℕ ℕ ℕ × Formula ℕ ℕ ℕ ℕ => Encodable.encode (mk p.1 p.2)) :=
    (Primrec.encode.comp
      (Primrec.list_cons.comp (Primrec.const (tag, 0, 0))
        (Primrec.list_append.comp (primrec_encFormula.comp Primrec.fst)
          (primrec_encFormula.comp Primrec.snd)))).of_eq
      fun p => congrArg Encodable.encode (henc p.1 p.2).symm
  exact Primrec.encode_iff.mp h

lemma primrec_formula_next : Primrec (Formula.next : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_un 3 .next (fun _ => rfl)
lemma primrec_formula_eventually : Primrec (Formula.eventually : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_un 4 .eventually (fun _ => rfl)
lemma primrec_formula_always : Primrec (Formula.always : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_un 5 .always (fun _ => rfl)
lemma primrec_formula_neg : Primrec (Formula.neg : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_un 8 .neg (fun _ => rfl)
lemma primrec_formula_untl : Primrec₂ (Formula.untl : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_bin 6 .untl (fun _ _ => rfl)
lemma primrec_formula_weakUntil : Primrec₂ (Formula.weakUntil : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_bin 7 .weakUntil (fun _ _ => rfl)
lemma primrec_formula_or : Primrec₂ (Formula.or : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_bin 9 .or (fun _ _ => rfl)
lemma primrec_formula_and : Primrec₂ (Formula.and : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_bin 10 .and (fun _ _ => rfl)
lemma primrec_formula_imp : Primrec₂ (Formula.imp : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_bin 11 .imp (fun _ _ => rfl)
lemma primrec_formula_iff : Primrec₂ (Formula.iff : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ) :=
  primrec_formula_bin 12 .iff (fun _ _ => rfl)

/-- Generic structural fold over `Formula ℕ ℕ ℕ ℕ` evaluated via right-to-left stack fold on
`encFormula φ`. -/
def evalPrefixStep {R : Type} (onAtom : ℕ → ℕ → ℕ → R) (onUn : ℕ → R → R) (onBin : ℕ → R → R → R)
    (t : Token) (stk : List R) : List R :=
  if t.1 ≤ 2 then onAtom t.1 t.2.1 t.2.2 :: stk
  else if t.1 = 3 ∨ t.1 = 4 ∨ t.1 = 5 ∨ t.1 = 8 then
    match stk with
    | r1 :: rest => onUn t.1 r1 :: rest
    | [] => []
  else
    match stk with
    | r1 :: r2 :: rest => onBin t.1 r1 r2 :: rest
    | _ => []

def evalFormulaFold {R : Type} (dflt : R) (onAtom : ℕ → ℕ → ℕ → R)
    (onUn : ℕ → R → R) (onBin : ℕ → R → R → R) : Formula ℕ ℕ ℕ ℕ → R
  | .inp1 x => onAtom 0 1 x
  | .inp2 x => onAtom 0 2 x
  | .out1 y => onAtom 1 1 y
  | .out2 y => onAtom 1 2 y
  | .graph .oneToTwo => onAtom 2 0 0
  | .graph .both => onAtom 2 1 0
  | .graph .twoToOne => onAtom 2 2 0
  | .next α => onUn 3 (evalFormulaFold dflt onAtom onUn onBin α)
  | .eventually α => onUn 4 (evalFormulaFold dflt onAtom onUn onBin α)
  | .always α => onUn 5 (evalFormulaFold dflt onAtom onUn onBin α)
  | .neg α => onUn 8 (evalFormulaFold dflt onAtom onUn onBin α)
  | .untl α β => onBin 6 (evalFormulaFold dflt onAtom onUn onBin α) (evalFormulaFold dflt onAtom onUn onBin β)
  | .weakUntil ψ φ => onBin 7 (evalFormulaFold dflt onAtom onUn onBin ψ) (evalFormulaFold dflt onAtom onUn onBin φ)
  | .or α β => onBin 9 (evalFormulaFold dflt onAtom onUn onBin α) (evalFormulaFold dflt onAtom onUn onBin β)
  | .and α β => onBin 10 (evalFormulaFold dflt onAtom onUn onBin α) (evalFormulaFold dflt onAtom onUn onBin β)
  | .imp α β => onBin 11 (evalFormulaFold dflt onAtom onUn onBin α) (evalFormulaFold dflt onAtom onUn onBin β)
  | .iff α β => onBin 12 (evalFormulaFold dflt onAtom onUn onBin α) (evalFormulaFold dflt onAtom onUn onBin β)

lemma foldr_evalPrefixStep {R : Type} (dflt : R) (onAtom : ℕ → ℕ → ℕ → R)
    (onUn : ℕ → R → R) (onBin : ℕ → R → R → R) (φ : Formula ℕ ℕ ℕ ℕ) :
    ∀ stk : List R,
      (encFormula φ).foldr (evalPrefixStep onAtom onUn onBin) stk =
        evalFormulaFold dflt onAtom onUn onBin φ :: stk := by
  induction φ with
  | inp1 x => intro stk; rfl
  | inp2 x => intro stk; rfl
  | out1 y => intro stk; rfl
  | out2 y => intro stk; rfl
  | graph g => intro stk; cases g <;> rfl
  | next α ih => intro stk; simp [encFormula, ih stk, evalPrefixStep, evalFormulaFold]
  | eventually α ih => intro stk; simp [encFormula, ih stk, evalPrefixStep, evalFormulaFold]
  | always α ih => intro stk; simp [encFormula, ih stk, evalPrefixStep, evalFormulaFold]
  | neg α ih => intro stk; simp [encFormula, ih stk, evalPrefixStep, evalFormulaFold]
  | untl α β ih1 ih2 =>
    intro stk; simp [encFormula, List.foldr_append, ih2 stk, ih1, evalPrefixStep, evalFormulaFold]
  | weakUntil ψ φ ih1 ih2 =>
    intro stk; simp [encFormula, List.foldr_append, ih2 stk, ih1, evalPrefixStep, evalFormulaFold]
  | or α β ih1 ih2 =>
    intro stk; simp [encFormula, List.foldr_append, ih2 stk, ih1, evalPrefixStep, evalFormulaFold]
  | and α β ih1 ih2 =>
    intro stk; simp [encFormula, List.foldr_append, ih2 stk, ih1, evalPrefixStep, evalFormulaFold]
  | imp α β ih1 ih2 =>
    intro stk; simp [encFormula, List.foldr_append, ih2 stk, ih1, evalPrefixStep, evalFormulaFold]
  | iff α β ih1 ih2 =>
    intro stk; simp [encFormula, List.foldr_append, ih2 stk, ih1, evalPrefixStep, evalFormulaFold]

lemma primrec_evalFormulaFold {R : Type} [Primcodable R] (dflt : R)
    {onAtom : ℕ → ℕ → ℕ → R} {onUn : ℕ → R → R} {onBin : ℕ → R → R → R}
    (hAtom : Primrec (fun t : Token => onAtom t.1 t.2.1 t.2.2))
    (hUn : Primrec₂ onUn)
    (hBin : Primrec (fun p : ℕ × R × R => onBin p.1 p.2.1 p.2.2)) :
    Primrec (evalFormulaFold dflt onAtom onUn onBin) := by
  have hUnPred : PrimrecPred (fun p : Token × List R =>
      p.1.1 = 3 ∨ p.1.1 = 4 ∨ p.1.1 = 5 ∨ p.1.1 = 8) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 3)).or
      ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 4)).or
        ((Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 5)).or
          (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 8))))
  have hUnCase : Primrec (fun p : Token × List R =>
      match p.2 with | r1 :: rest => onUn p.1.1 r1 :: rest | [] => []) :=
    (Primrec.list_casesOn Primrec.snd (Primrec.const [])
      (Primrec.list_cons.comp
        (hUn.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun p => by cases p.2 <;> rfl
  have hBinCase : Primrec (fun p : Token × List R =>
      match p.2 with | r1 :: r2 :: rest => onBin p.1.1 r1 r2 :: rest | _ => []) :=
    (Primrec.list_casesOn Primrec.snd (Primrec.const [])
      (Primrec.list_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const [])
        (Primrec.list_cons.comp
          (hBin.comp
            ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
              ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd))))
          (Primrec.snd.comp Primrec.snd)).to₂).to₂).of_eq fun p => by
      rcases p.2 with _ | ⟨r1, _ | ⟨r2, rest⟩⟩ <;> rfl
  have hStep : Primrec₂ (evalPrefixStep onAtom onUn onBin) :=
    (Primrec.ite (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 2))
      (Primrec.list_cons.comp (hAtom.comp Primrec.fst) Primrec.snd)
      (Primrec.ite hUnPred hUnCase hBinCase)).of_eq fun _ => rfl
  have hFold := Primrec.option_getD.comp
    (Primrec.list_head?.comp
      (Primrec.list_foldr primrec_encFormula (Primrec.const [])
        (hStep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂))
    (Primrec.const dflt)
  exact hFold.of_eq fun φ => by
    dsimp only
    rw [foldr_evalPrefixStep dflt onAtom onUn onBin φ []]
    rfl

/-! #### Desugaring `F`, `G`, `W` into `U` and `¬`, Subformula Closure, and 1-Level Classifier -/

private abbrev ttNat : Formula ℕ ℕ ℕ ℕ := Formula.tt

def desugar : Formula ℕ ℕ ℕ ℕ → Formula ℕ ℕ ℕ ℕ
  | .inp1 x => .inp1 x
  | .inp2 x => .inp2 x
  | .out1 y => .out1 y
  | .out2 y => .out2 y
  | .graph g => .graph g
  | .next α => .next (desugar α)
  | .eventually α => .untl ttNat (desugar α)
  | .always α => .neg (.untl ttNat (.neg (desugar α)))
  | .untl α β => .untl (desugar α) (desugar β)
  | .weakUntil ψ φ =>
      .or (.neg (.untl ttNat (.neg (desugar ψ)))) (.untl (desugar ψ) (desugar φ))
  | .neg α => .neg (desugar α)
  | .or α β => .or (desugar α) (desugar β)
  | .and α β => .and (desugar α) (desugar β)
  | .imp α β => .imp (desugar α) (desugar β)
  | .iff α β => .iff (desugar α) (desugar β)

lemma sat_desugar (φ : Formula ℕ ℕ ℕ ℕ) (e : ℕ → Signal ℕ ℕ × (ℕ × ℕ)) :
    (desugar φ).Sat e ↔ φ.Sat e := by
  induction φ generalizing e with
  | inp1 _ | inp2 _ | out1 _ | out2 _ | graph _ => rfl
  | next α ih => simp [desugar, Formula.Sat, ih]
  | eventually α ih =>
    simp only [desugar, Formula.Sat, ih]
    exact ⟨fun ⟨r, hr, _⟩ => ⟨r, hr⟩, fun ⟨r, hr⟩ => ⟨r, hr, fun r' _ => sat_tt _⟩⟩
  | always α ih =>
    simp only [desugar, Formula.Sat, ih]
    constructor
    · intro h r
      by_contra hnr
      exact h ⟨r, hnr, fun r' _ => sat_tt _⟩
    · rintro hall ⟨r, hnr, _⟩
      exact hnr (hall r)
  | untl α β ih1 ih2 => simp [desugar, Formula.Sat, ih1, ih2]
  | weakUntil ψ φ ih1 ih2 =>
    simp only [desugar, Formula.Sat, ih1, ih2]
    refine or_congr ?_ Iff.rfl
    constructor
    · intro h r
      by_contra hnr
      exact h ⟨r, hnr, fun r' _ => sat_tt _⟩
    · rintro hall ⟨r, hnr, _⟩
      exact hnr (hall r)
  | neg α ih => simp [desugar, Formula.Sat, ih]
  | or α β ih1 ih2 => simp [desugar, Formula.Sat, ih1, ih2]
  | and α β ih1 ih2 => simp [desugar, Formula.Sat, ih1, ih2]
  | imp α β ih1 ih2 => simp [desugar, Formula.Sat, ih1, ih2]
  | iff α β ih1 ih2 => simp [desugar, Formula.Sat, ih1, ih2]

def NoDerived : Formula ℕ ℕ ℕ ℕ → Prop
  | .inp1 _ | .inp2 _ | .out1 _ | .out2 _ | .graph _ => True
  | .next α | .neg α => NoDerived α
  | .untl α β | .or α β | .and α β | .imp α β | .iff α β => NoDerived α ∧ NoDerived β
  | .eventually _ | .always _ | .weakUntil _ _ => False

lemma noDerived_desugar (φ : Formula ℕ ℕ ℕ ℕ) : NoDerived (desugar φ) := by
  have htt : NoDerived ttNat := ⟨trivial, trivial⟩
  induction φ <;> simp_all [desugar, NoDerived]

lemma primrec_desugar : Primrec desugar := by
  let onAtom (tag a b : ℕ) : Formula ℕ ℕ ℕ ℕ :=
    if tag = 0 then (if a = 1 then .inp1 b else .inp2 b)
    else if tag = 1 then (if a = 1 then .out1 b else .out2 b)
    else .graph (graphOfNat a)
  let onUn (tag : ℕ) (r : Formula ℕ ℕ ℕ ℕ) : Formula ℕ ℕ ℕ ℕ :=
    if tag = 3 then .next r
    else if tag = 4 then .untl ttNat r
    else if tag = 5 then .neg (.untl ttNat (.neg r))
    else .neg r
  let onBin (tag : ℕ) (r1 r2 : Formula ℕ ℕ ℕ ℕ) : Formula ℕ ℕ ℕ ℕ :=
    if tag = 6 then .untl r1 r2
    else if tag = 7 then .or (.neg (.untl ttNat (.neg r1))) (.untl r1 r2)
    else if tag = 9 then .or r1 r2
    else if tag = 10 then .and r1 r2
    else if tag = 11 then .imp r1 r2
    else .iff r1 r2
  have hAtom : Primrec (fun t : Token => onAtom t.1 t.2.1 t.2.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
        (primrec_formula_inp1.comp (Primrec.snd.comp Primrec.snd))
        (primrec_formula_inp2.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
          (primrec_formula_out1.comp (Primrec.snd.comp Primrec.snd))
          (primrec_formula_out2.comp (Primrec.snd.comp Primrec.snd)))
        (primrec_formula_graph.comp (primrec_graphOfNat.comp (Primrec.fst.comp Primrec.snd))))
  have hUn : Primrec₂ onUn :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
      (primrec_formula_next.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4))
        (primrec_formula_untl.comp (Primrec.const ttNat) Primrec.snd)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
          (primrec_formula_neg.comp
            (primrec_formula_untl.comp (Primrec.const ttNat)
              (primrec_formula_neg.comp Primrec.snd)))
          (primrec_formula_neg.comp Primrec.snd)))
  have hBin : Primrec (fun p : ℕ × Formula ℕ ℕ ℕ ℕ × Formula ℕ ℕ ℕ ℕ => onBin p.1 p.2.1 p.2.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6))
      (primrec_formula_untl.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7))
        (primrec_formula_or.comp
          (primrec_formula_neg.comp (primrec_formula_untl.comp (Primrec.const ttNat)
            (primrec_formula_neg.comp (Primrec.fst.comp Primrec.snd))))
          (primrec_formula_untl.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 9))
          (primrec_formula_or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 10))
            (primrec_formula_and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 11))
              (primrec_formula_imp.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
              (primrec_formula_iff.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))))))
  refine (primrec_evalFormulaFold ttNat hAtom hUn hBin).of_eq fun φ => ?_
  induction φ with
  | graph g => cases g <;> rfl
  | _ => simp_all [evalFormulaFold, desugar, onAtom, onUn, onBin]

def subformulas : Formula ℕ ℕ ℕ ℕ → List (Formula ℕ ℕ ℕ ℕ)
  | .inp1 x => [.inp1 x]
  | .inp2 x => [.inp2 x]
  | .out1 y => [.out1 y]
  | .out2 y => [.out2 y]
  | .graph g => [.graph g]
  | .next α => .next α :: subformulas α
  | .eventually α => .eventually α :: subformulas α
  | .always α => .always α :: subformulas α
  | .neg α => .neg α :: subformulas α
  | .untl α β => .untl α β :: (subformulas α ++ subformulas β)
  | .weakUntil ψ φ => .weakUntil ψ φ :: (subformulas ψ ++ subformulas φ)
  | .or α β => .or α β :: (subformulas α ++ subformulas β)
  | .and α β => .and α β :: (subformulas α ++ subformulas β)
  | .imp α β => .imp α β :: (subformulas α ++ subformulas β)
  | .iff α β => .iff α β :: (subformulas α ++ subformulas β)

lemma subformulas_headD (φ : Formula ℕ ℕ ℕ ℕ) : (subformulas φ).headD ttNat = φ := by
  cases φ <;> rfl

lemma self_mem_subformulas (φ : Formula ℕ ℕ ℕ ℕ) : φ ∈ subformulas φ := by
  cases φ <;> simp [subformulas]

lemma subformulas_trans {φ ψ χ : Formula ℕ ℕ ℕ ℕ}
    (h1 : χ ∈ subformulas ψ) (h2 : ψ ∈ subformulas φ) : χ ∈ subformulas φ := by
  induction φ with
  | inp1 _ | inp2 _ | out1 _ | out2 _ | graph _ =>
    simp [subformulas] at h2; subst h2; exact h1
  | next α ih | eventually α ih | always α ih | neg α ih =>
    simp only [subformulas, List.mem_cons] at h2 ⊢
    rcases h2 with rfl | h2
    · simpa [subformulas] using h1
    · exact Or.inr (ih h2)
  | untl α β ih1 ih2 | weakUntil α β ih1 ih2 | or α β ih1 ih2 | and α β ih1 ih2
  | imp α β ih1 ih2 | iff α β ih1 ih2 =>
    simp only [subformulas, List.mem_cons, List.mem_append] at h2 ⊢
    rcases h2 with rfl | h2 | h2
    · simpa [subformulas] using h1
    · exact Or.inr (Or.inl (ih1 h2))
    · exact Or.inr (Or.inr (ih2 h2))

lemma noDerived_of_mem_subformulas {φ χ : Formula ℕ ℕ ℕ ℕ}
    (hnd : NoDerived φ) (hmem : χ ∈ subformulas φ) : NoDerived χ := by
  induction φ with
  | inp1 _ | inp2 _ | out1 _ | out2 _ | graph _ =>
    simp [subformulas] at hmem; subst hmem; exact hnd
  | eventually _ | always _ | weakUntil _ _ => cases hnd
  | next α ih | neg α ih =>
    simp only [subformulas, List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact hnd
    · exact ih hnd hmem
  | untl α β ih1 ih2 | or α β ih1 ih2 | and α β ih1 ih2 | imp α β ih1 ih2 | iff α β ih1 ih2 =>
    simp only [subformulas, List.mem_cons, List.mem_append] at hmem
    rcases hmem with rfl | hmem | hmem
    · exact hnd
    · exact ih1 hnd.1 hmem
    · exact ih2 hnd.2 hmem

lemma primrec_subformulas : Primrec subformulas := by
  let onAtom (tag a b : ℕ) : List (Formula ℕ ℕ ℕ ℕ) :=
    if tag = 0 then (if a = 1 then [.inp1 b] else [.inp2 b])
    else if tag = 1 then (if a = 1 then [.out1 b] else [.out2 b])
    else [.graph (graphOfNat a)]
  let headF (l : List (Formula ℕ ℕ ℕ ℕ)) : Formula ℕ ℕ ℕ ℕ := l.headD ttNat
  let onUn (tag : ℕ) (r : List (Formula ℕ ℕ ℕ ℕ)) : List (Formula ℕ ℕ ℕ ℕ) :=
    let α := headF r
    let p := if tag = 3 then .next α else if tag = 4 then .eventually α
      else if tag = 5 then .always α else .neg α
    p :: r
  let onBin (tag : ℕ) (r1 r2 : List (Formula ℕ ℕ ℕ ℕ)) : List (Formula ℕ ℕ ℕ ℕ) :=
    let α := headF r1
    let β := headF r2
    let p := if tag = 6 then .untl α β else if tag = 7 then .weakUntil α β
      else if tag = 9 then .or α β else if tag = 10 then .and α β
      else if tag = 11 then .imp α β else .iff α β
    p :: (r1 ++ r2)
  have hHead : Primrec headF :=
    (Primrec.option_getD.comp Primrec.list_head? (Primrec.const ttNat)).of_eq
      fun l => by cases l <;> rfl
  have hSing : ∀ {X : Type} [Primcodable X] {f : X → Formula ℕ ℕ ℕ ℕ}, Primrec f →
      Primrec (fun x => [f x]) := fun hf =>
    Primrec.list_cons.comp hf (Primrec.const [])
  have hAtom : Primrec (fun t : Token => onAtom t.1 t.2.1 t.2.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
        (hSing (primrec_formula_inp1.comp (Primrec.snd.comp Primrec.snd)))
        (hSing (primrec_formula_inp2.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
          (hSing (primrec_formula_out1.comp (Primrec.snd.comp Primrec.snd)))
          (hSing (primrec_formula_out2.comp (Primrec.snd.comp Primrec.snd))))
        (hSing (primrec_formula_graph.comp (primrec_graphOfNat.comp (Primrec.fst.comp Primrec.snd)))))
  have hUn : Primrec₂ onUn := by
    have hα : Primrec (fun p : ℕ × List (Formula ℕ ℕ ℕ ℕ) => headF p.2) := hHead.comp Primrec.snd
    exact Primrec.list_cons.comp
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3)) (primrec_formula_next.comp hα)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4)) (primrec_formula_eventually.comp hα)
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5)) (primrec_formula_always.comp hα)
            (primrec_formula_neg.comp hα))))
      Primrec.snd
  have hBin : Primrec (fun p : ℕ × List (Formula ℕ ℕ ℕ ℕ) × List (Formula ℕ ℕ ℕ ℕ) =>
      onBin p.1 p.2.1 p.2.2) := by
    have hα : Primrec (fun p : ℕ × List (Formula ℕ ℕ ℕ ℕ) × List (Formula ℕ ℕ ℕ ℕ) => headF p.2.1) :=
      hHead.comp (Primrec.fst.comp Primrec.snd)
    have hβ : Primrec (fun p : ℕ × List (Formula ℕ ℕ ℕ ℕ) × List (Formula ℕ ℕ ℕ ℕ) => headF p.2.2) :=
      hHead.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.list_cons.comp
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6)) (primrec_formula_untl.comp hα hβ)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7)) (primrec_formula_weakUntil.comp hα hβ)
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 9)) (primrec_formula_or.comp hα hβ)
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 10)) (primrec_formula_and.comp hα hβ)
              (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 11)) (primrec_formula_imp.comp hα hβ)
                (primrec_formula_iff.comp hα hβ))))))
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  refine (primrec_evalFormulaFold [] hAtom hUn hBin).of_eq fun φ => ?_
  induction φ with
  | graph g => cases g <;> rfl
  | next α ih | eventually α ih | always α ih | neg α ih =>
    simp only [evalFormulaFold, subformulas, ih, onUn, headF, subformulas_headD]
    simp
  | untl α β ih1 ih2 | weakUntil α β ih1 ih2 | or α β ih1 ih2 | and α β ih1 ih2
  | imp α β ih1 ih2 | iff α β ih1 ih2 =>
    simp only [evalFormulaFold, subformulas, ih1, ih2, onBin, headF, subformulas_headD]
    simp
  | _ => rfl

def dedupList {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldr (fun x ys => if x ∈ ys then ys else x :: ys) []

lemma mem_dedupList {α : Type} [DecidableEq α] (xs : List α) (a : α) :
    a ∈ dedupList xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [dedupList]
  | cons x xs ih =>
    change a ∈ (if x ∈ dedupList xs then dedupList xs else x :: dedupList xs) ↔ a ∈ x :: xs
    split_ifs with h
    · have hx := (ih x).mp h
      simp only [ih, List.mem_cons]
      exact ⟨Or.inr, fun hc => hc.elim (fun he => he ▸ hx) id⟩
    · simp only [List.mem_cons, ih]

lemma nodup_dedupList {α : Type} [DecidableEq α] (xs : List α) : (dedupList xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    change (if x ∈ dedupList xs then dedupList xs else x :: dedupList xs).Nodup
    split_ifs with h
    · exact ih
    · exact List.nodup_cons.mpr ⟨h, ih⟩

lemma primrec_dedupList {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec (dedupList (α := α)) := by
  have hm : PrimrecRel (fun (ys : List α) (x : α) => x ∈ ys) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (hm.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂).of_eq
    fun _ => rfl

/-- One-level constructor inspection `(kind, atomArg, child1, child2)` of `Formula ℕ ℕ ℕ ℕ`. -/
def classifyFormula : Formula ℕ ℕ ℕ ℕ → ℕ × ℕ × Formula ℕ ℕ ℕ ℕ × Formula ℕ ℕ ℕ ℕ
  | .inp1 x => (0, x, ttNat, ttNat)
  | .inp2 x => (1, x, ttNat, ttNat)
  | .out1 y => (2, y, ttNat, ttNat)
  | .out2 y => (3, y, ttNat, ttNat)
  | .graph g => (4, g.idx, ttNat, ttNat)
  | .next α => (5, 0, α, ttNat)
  | .eventually α => (6, 0, α, ttNat)
  | .always α => (7, 0, α, ttNat)
  | .untl α β => (8, 0, α, β)
  | .weakUntil ψ φ => (9, 0, ψ, φ)
  | .neg α => (10, 0, α, ttNat)
  | .or α β => (11, 0, α, β)
  | .and α β => (12, 0, α, β)
  | .imp α β => (13, 0, α, β)
  | .iff α β => (14, 0, α, β)

lemma primrec_classifyFormula : Primrec classifyFormula := by
  let Cls := Formula ℕ ℕ ℕ ℕ × (ℕ × ℕ × Formula ℕ ℕ ℕ ℕ × Formula ℕ ℕ ℕ ℕ)
  let onAtom (tag a b : ℕ) : Cls :=
    if tag = 0 then
      if a = 1 then (.inp1 b, (0, b, ttNat, ttNat)) else (.inp2 b, (1, b, ttNat, ttNat))
    else if tag = 1 then
      if a = 1 then (.out1 b, (2, b, ttNat, ttNat)) else (.out2 b, (3, b, ttNat, ttNat))
    else (.graph (graphOfNat a), (4, (graphOfNat a).idx, ttNat, ttNat))
  let onUn (tag : ℕ) (r : Cls) : Cls :=
    if tag = 3 then (.next r.1, (5, 0, r.1, ttNat))
    else if tag = 4 then (.eventually r.1, (6, 0, r.1, ttNat))
    else if tag = 5 then (.always r.1, (7, 0, r.1, ttNat))
    else (.neg r.1, (10, 0, r.1, ttNat))
  let onBin (tag : ℕ) (r1 r2 : Cls) : Cls :=
    if tag = 6 then (.untl r1.1 r2.1, (8, 0, r1.1, r2.1))
    else if tag = 7 then (.weakUntil r1.1 r2.1, (9, 0, r1.1, r2.1))
    else if tag = 9 then (.or r1.1 r2.1, (11, 0, r1.1, r2.1))
    else if tag = 10 then (.and r1.1 r2.1, (12, 0, r1.1, r2.1))
    else if tag = 11 then (.imp r1.1 r2.1, (13, 0, r1.1, r2.1))
    else (.iff r1.1 r2.1, (14, 0, r1.1, r2.1))
  have hAtom : Primrec (fun t : Token => onAtom t.1 t.2.1 t.2.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
        ((primrec_formula_inp1.comp (Primrec.snd.comp Primrec.snd)).pair
          ((Primrec.const 0).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (ttNat, ttNat)))))
        ((primrec_formula_inp2.comp (Primrec.snd.comp Primrec.snd)).pair
          ((Primrec.const 1).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (ttNat, ttNat))))))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
          ((primrec_formula_out1.comp (Primrec.snd.comp Primrec.snd)).pair
            ((Primrec.const 2).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (ttNat, ttNat)))))
          ((primrec_formula_out2.comp (Primrec.snd.comp Primrec.snd)).pair
            ((Primrec.const 3).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const (ttNat, ttNat))))))
        ((primrec_formula_graph.comp (primrec_graphOfNat.comp (Primrec.fst.comp Primrec.snd))).pair
          ((Primrec.const 4).pair
            ((primrec_commGraphIdx.comp (primrec_graphOfNat.comp (Primrec.fst.comp Primrec.snd))).pair
              (Primrec.const (ttNat, ttNat))))))
  have hUn : Primrec₂ onUn := by
    have hα : Primrec (fun p : ℕ × Cls => p.2.1) := Primrec.fst.comp Primrec.snd
    exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
      ((primrec_formula_next.comp hα).pair ((Primrec.const 5).pair ((Primrec.const 0).pair (hα.pair (Primrec.const ttNat)))))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4))
        ((primrec_formula_eventually.comp hα).pair ((Primrec.const 6).pair ((Primrec.const 0).pair (hα.pair (Primrec.const ttNat)))))
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
          ((primrec_formula_always.comp hα).pair ((Primrec.const 7).pair ((Primrec.const 0).pair (hα.pair (Primrec.const ttNat)))))
          ((primrec_formula_neg.comp hα).pair ((Primrec.const 10).pair ((Primrec.const 0).pair (hα.pair (Primrec.const ttNat)))))))
  have hBin : Primrec (fun p : ℕ × Cls × Cls => onBin p.1 p.2.1 p.2.2) := by
    have hα : Primrec (fun p : ℕ × Cls × Cls => p.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have hβ : Primrec (fun p : ℕ × Cls × Cls => p.2.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6))
      ((primrec_formula_untl.comp hα hβ).pair ((Primrec.const 8).pair ((Primrec.const 0).pair (hα.pair hβ))))
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7))
        ((primrec_formula_weakUntil.comp hα hβ).pair ((Primrec.const 9).pair ((Primrec.const 0).pair (hα.pair hβ))))
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 9))
          ((primrec_formula_or.comp hα hβ).pair ((Primrec.const 11).pair ((Primrec.const 0).pair (hα.pair hβ))))
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 10))
            ((primrec_formula_and.comp hα hβ).pair ((Primrec.const 12).pair ((Primrec.const 0).pair (hα.pair hβ))))
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 11))
              ((primrec_formula_imp.comp hα hβ).pair ((Primrec.const 13).pair ((Primrec.const 0).pair (hα.pair hβ))))
              ((primrec_formula_iff.comp hα hβ).pair ((Primrec.const 14).pair ((Primrec.const 0).pair (hα.pair hβ))))))))
  have hPair := primrec_evalFormulaFold (ttNat, (0, 0, ttNat, ttNat)) hAtom hUn hBin
  refine (Primrec.snd.comp hPair).of_eq fun φ => ?_
  suffices evalFormulaFold (ttNat, (0, 0, ttNat, ttNat)) onAtom onUn onBin φ = (φ, classifyFormula φ) by
    rw [this]
  induction φ with
  | graph g => cases g <;> rfl
  | _ => simp_all [evalFormulaFold, classifyFormula, onAtom, onUn, onBin]

/-! ### Section 3: Executable Vardi–Wolper Compiler (`ltlToNBW`) -/

def holds (S : List (Formula ℕ ℕ ℕ ℕ)) (m : ℕ) (χ : Formula ℕ ℕ ℕ ℕ) : Bool :=
  m.testBit (S.idxOf χ)

lemma primrec_list_idxOf {α : Type} [Primcodable α] [DecidableEq α] :
    Primrec₂ (List.idxOf (α := α)) := by
  have h : Primrec₂ (fun (a : α) (l : List α) =>
      l.foldr (fun b acc => if b = a then 0 else acc + 1) 0) :=
    Primrec.list_foldr (Primrec.snd : Primrec fun p : α × List α => p.2) (Primrec.const 0)
      (Primrec.ite
        (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.const 0)
        (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun a l => by
    induction l with
    | nil => rfl
    | cons b tl ih =>
      rw [List.idxOf_cons]
      by_cases hba : b = a
      · subst hba; simp
      · have h1 : (b == a) = false := beq_eq_false_iff_ne.mpr hba
        simp [hba, h1, ih]

lemma primrec_holds :
    Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × Formula ℕ ℕ ℕ ℕ =>
      holds p.1 p.2.1 p.2.2) :=
  primrec_testBit.comp (Primrec.fst.comp Primrec.snd)
    (primrec_list_idxOf.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)

def localConsistentAt (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ)
    (χ : Formula ℕ ℕ ℕ ℕ) : Bool :=
  let b := holds S m χ
  let rf := decodeRoundFields I a
  let c := classifyFormula χ
  let k := c.1
  let arg := c.2.1
  let α := c.2.2.1
  let β := c.2.2.2
  if k = 0 then b == decide (rf.1 = arg)
  else if k = 1 then b == decide (rf.2.1 = arg)
  else if k = 2 then b == decide (rf.2.2.2.1 = arg)
  else if k = 3 then b == decide (rf.2.2.2.2 = arg)
  else if k = 4 then b == decide (rf.2.2.1.idx = arg)
  else if k = 10 then b == !(holds S m α)
  else if k = 11 then b == (holds S m α || holds S m β)
  else if k = 12 then b == (holds S m α && holds S m β)
  else if k = 13 then b == (!(holds S m α) || holds S m β)
  else if k = 14 then b == (holds S m α == holds S m β)
  else true

@[simp] private lemma localConsistentAt_inp1 (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a x : ℕ) :
    localConsistentAt I S m a (.inp1 x) = (holds S m (.inp1 x) == decide ((decodeRoundFields I a).1 = x)) := rfl
@[simp] private lemma localConsistentAt_inp2 (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a x : ℕ) :
    localConsistentAt I S m a (.inp2 x) = (holds S m (.inp2 x) == decide ((decodeRoundFields I a).2.1 = x)) := rfl
@[simp] private lemma localConsistentAt_out1 (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a y : ℕ) :
    localConsistentAt I S m a (.out1 y) = (holds S m (.out1 y) == decide ((decodeRoundFields I a).2.2.2.1 = y)) := rfl
@[simp] private lemma localConsistentAt_out2 (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a y : ℕ) :
    localConsistentAt I S m a (.out2 y) = (holds S m (.out2 y) == decide ((decodeRoundFields I a).2.2.2.2 = y)) := rfl
@[simp] private lemma localConsistentAt_graph (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (g : CommGraph) :
    localConsistentAt I S m a (.graph g) = (holds S m (.graph g) == decide ((decodeRoundFields I a).2.2.1.idx = g.idx)) := rfl
@[simp] private lemma localConsistentAt_neg (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.neg α) = (holds S m (.neg α) == !(holds S m α)) := rfl
@[simp] private lemma localConsistentAt_or (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α β : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.or α β) = (holds S m (.or α β) == (holds S m α || holds S m β)) := rfl
@[simp] private lemma localConsistentAt_and (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α β : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.and α β) = (holds S m (.and α β) == (holds S m α && holds S m β)) := rfl
@[simp] private lemma localConsistentAt_imp (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α β : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.imp α β) = (holds S m (.imp α β) == (!(holds S m α) || holds S m β)) := rfl
@[simp] private lemma localConsistentAt_iff (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α β : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.iff α β) = (holds S m (.iff α β) == (holds S m α == holds S m β)) := rfl
@[simp] private lemma localConsistentAt_next (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.next α) = true := rfl
@[simp] private lemma localConsistentAt_eventually (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.eventually α) = true := rfl
@[simp] private lemma localConsistentAt_always (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.always α) = true := rfl
@[simp] private lemma localConsistentAt_untl (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (α β : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.untl α β) = true := rfl
@[simp] private lemma localConsistentAt_weakUntil (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) (ψ φ : Formula ℕ ℕ ℕ ℕ) :
    localConsistentAt I S m a (.weakUntil ψ φ) = true := rfl

def localConsistent (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (m a : ℕ) : Bool :=
  S.all (localConsistentAt I S m a)

def stepConsistentAt (S : List (Formula ℕ ℕ ℕ ℕ)) (m m' : ℕ) (χ : Formula ℕ ℕ ℕ ℕ) : Bool :=
  let b := holds S m χ
  let c := classifyFormula χ
  let k := c.1
  let α := c.2.2.1
  let β := c.2.2.2
  if k = 5 then b == holds S m' α
  else if k = 8 then b == (holds S m β || (holds S m α && holds S m' χ))
  else true

@[simp] private lemma stepConsistentAt_next (S : List (Formula ℕ ℕ ℕ ℕ)) (m m' : ℕ) (α : Formula ℕ ℕ ℕ ℕ) :
    stepConsistentAt S m m' (.next α) = (holds S m (.next α) == holds S m' α) := rfl
@[simp] private lemma stepConsistentAt_untl (S : List (Formula ℕ ℕ ℕ ℕ)) (m m' : ℕ) (α β : Formula ℕ ℕ ℕ ℕ) :
    stepConsistentAt S m m' (.untl α β) =
      (holds S m (.untl α β) == (holds S m β || (holds S m α && holds S m' (.untl α β)))) := rfl

def stepConsistent (S : List (Formula ℕ ℕ ℕ ℕ)) (m m' : ℕ) : Bool :=
  S.all (stepConsistentAt S m m')

def oblSat (S : List (Formula ℕ ℕ ℕ ℕ)) (m k : ℕ) : Bool :=
  if k < S.length then
    let χ := S.getD k ttNat
    let c := classifyFormula χ
    if c.1 = 8 then !(m.testBit k) || holds S m c.2.2.2 else true
  else true

def nextCounter (S : List (Formula ℕ ℕ ℕ ℕ)) (m k : ℕ) : ℕ :=
  if oblSat S m k then (k + 1) % (S.length + 1) else k

def ltlInitMask (S : List (Formula ℕ ℕ ℕ ℕ)) (ψ : Formula ℕ ℕ ℕ ℕ) : ℕ :=
  let K := S.length + 1
  let Q := powNat 2 S.length * K
  listToMask Q (fun q => decide (q % K = S.length) && holds S (q / K) ψ)

def ltlAccMask (S : List (Formula ℕ ℕ ℕ ℕ)) : ℕ :=
  let K := S.length + 1
  let Q := powNat 2 S.length * K
  listToMask Q (fun q => decide (q % K = S.length))

def ltlTransEntry (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ)) (idx : ℕ) : ℕ :=
  let K := S.length + 1
  let Q := powNat 2 S.length * K
  let αLen := roundSize I
  let q := idx / αLen
  let a := idx % αLen
  let m := q / K
  let k := q % K
  if localConsistent I S m a = true then
    let k' := nextCounter S m k
    listToMask Q (fun q' => decide (q' % K = k') && stepConsistent S m (q' / K))
  else 0

/-- Executable Vardi–Wolper compiler `ltlToNBW I φ : NBWCode` over `Fin (roundAlphaMinusOne I + 1)`.
States are `q = m * (|S| + 1) + k` for `m < 2^|S|` and `k < |S| + 1`, where `S` is the deduplicated
subformula list of `desugar φ`. -/
def ltlToNBW (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ) : NBWCode :=
  let ψ := desugar φ
  let S := dedupList (subformulas ψ)
  let Q := powNat 2 S.length * (S.length + 1)
  let αLen := roundSize I
  (Q - 1, ltlInitMask S ψ, (List.range (Q * αLen)).map (ltlTransEntry I S), ltlAccMask S)

lemma primrec_localConsistent :
    Primrec (fun p : Instance × List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ =>
      localConsistent p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  apply primrec_list_all (Primrec.fst.comp Primrec.snd)
  let Ctx := (Instance × List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ) × Formula ℕ ℕ ℕ ℕ
  have hI : Primrec (fun x : Ctx => x.1.1) := Primrec.fst.comp Primrec.fst
  have hS : Primrec (fun x : Ctx => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hm : Primrec (fun x : Ctx => x.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have ha : Primrec (fun x : Ctx => x.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hχ : Primrec (fun x : Ctx => x.2) := Primrec.snd
  have hrf := primrec_decodeRoundFields.comp hI ha
  have hc := primrec_classifyFormula.comp hχ
  have hk := Primrec.fst.comp hc
  have harg := Primrec.fst.comp (Primrec.snd.comp hc)
  have hα := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hβ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hb := primrec_holds.comp (hS.pair (hm.pair hχ))
  have hbα := primrec_holds.comp (hS.pair (hm.pair hα))
  have hbβ := primrec_holds.comp (hS.pair (hm.pair hβ))
  exact (Primrec.ite (Primrec.eq.comp hk (Primrec.const 0))
    (Primrec.beq.comp hb (Primrec.eq.comp (Primrec.fst.comp hrf) harg).decide)
    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 1))
      (Primrec.beq.comp hb (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp hrf)) harg).decide)
      (Primrec.ite (Primrec.eq.comp hk (Primrec.const 2))
        (Primrec.beq.comp hb (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrf)))) harg).decide)
        (Primrec.ite (Primrec.eq.comp hk (Primrec.const 3))
          (Primrec.beq.comp hb (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrf)))) harg).decide)
          (Primrec.ite (Primrec.eq.comp hk (Primrec.const 4))
            (Primrec.beq.comp hb (Primrec.eq.comp (primrec_commGraphIdx.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hrf)))) harg).decide)
            (Primrec.ite (Primrec.eq.comp hk (Primrec.const 10))
              (Primrec.beq.comp hb (Primrec.not.comp hbα))
              (Primrec.ite (Primrec.eq.comp hk (Primrec.const 11))
                (Primrec.beq.comp hb (primrec_bool_or.comp hbα hbβ))
                (Primrec.ite (Primrec.eq.comp hk (Primrec.const 12))
                  (Primrec.beq.comp hb (primrec_bool_and.comp hbα hbβ))
                  (Primrec.ite (Primrec.eq.comp hk (Primrec.const 13))
                    (Primrec.beq.comp hb (primrec_bool_or.comp (Primrec.not.comp hbα) hbβ))
                    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 14))
                      (Primrec.beq.comp hb (Primrec.beq.comp hbα hbβ))
                      (Primrec.const true))))))))))).of_eq fun _ => rfl

lemma primrec_stepConsistent :
    Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ =>
      stepConsistent p.1 p.2.1 p.2.2) := by
  apply primrec_list_all Primrec.fst
  let Ctx := (List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ) × Formula ℕ ℕ ℕ ℕ
  have hS : Primrec (fun x : Ctx => x.1.1) := Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun x : Ctx => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hm' : Primrec (fun x : Ctx => x.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hχ : Primrec (fun x : Ctx => x.2) := Primrec.snd
  have hc := primrec_classifyFormula.comp hχ
  have hk := Primrec.fst.comp hc
  have hα := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hβ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hb := primrec_holds.comp (hS.pair (hm.pair hχ))
  have hm'α := primrec_holds.comp (hS.pair (hm'.pair hα))
  have hmβ := primrec_holds.comp (hS.pair (hm.pair hβ))
  have hmα := primrec_holds.comp (hS.pair (hm.pair hα))
  have hm'χ := primrec_holds.comp (hS.pair (hm'.pair hχ))
  exact (Primrec.ite (Primrec.eq.comp hk (Primrec.const 5))
    (Primrec.beq.comp hb hm'α)
    (Primrec.ite (Primrec.eq.comp hk (Primrec.const 8))
      (Primrec.beq.comp hb (primrec_bool_or.comp hmβ (primrec_bool_and.comp hmα hm'χ)))
      (Primrec.const true))).of_eq fun _ => rfl

lemma primrec_oblSat :
    Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => oblSat p.1 p.2.1 p.2.2) := by
  have hS : Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => p.1) := Primrec.fst
  have hm : Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hχ := primrec_list_getD.comp (hS.pair (hk.pair (Primrec.const ttNat)))
  have hc := primrec_classifyFormula.comp hχ
  have hβ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  exact (Primrec.ite (Primrec.nat_lt.comp hk (Primrec.list_length.comp hS))
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hc) (Primrec.const 8))
      (primrec_bool_or.comp (Primrec.not.comp (primrec_testBit.comp hm hk))
        (primrec_holds.comp (hS.pair (hm.pair hβ))))
      (Primrec.const true))
    (Primrec.const true)).of_eq fun _ => rfl

lemma primrec_nextCounter :
    Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => nextCounter p.1 p.2.1 p.2.2) := by
  have hS : Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => p.1) := Primrec.fst
  have hk : Primrec (fun p : List (Formula ℕ ℕ ℕ ℕ) × ℕ × ℕ => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.ite (Primrec.eq.comp primrec_oblSat (Primrec.const true))
    (Primrec.nat_mod.comp (Primrec.succ.comp hk) (Primrec.succ.comp (Primrec.list_length.comp hS)))
    hk).of_eq fun _ => rfl

private lemma primrec_ltlInitMask : Primrec₂ ltlInitMask := by
  let Inp := List (Formula ℕ ℕ ℕ ℕ) × Formula ℕ ℕ ℕ ℕ
  have hLen : Primrec (fun p : Inp => p.1.length) := Primrec.list_length.comp Primrec.fst
  have hK : Primrec (fun p : Inp => p.1.length + 1) := Primrec.succ.comp hLen
  have hQ : Primrec (fun p : Inp => powNat 2 p.1.length * (p.1.length + 1)) :=
    Primrec.nat_mul.comp (primrec_powNat.comp (Primrec.const 2) hLen) hK
  exact (primrec_listToMask hQ
    (primrec_bool_and.comp
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (hK.comp Primrec.fst))
        (hLen.comp Primrec.fst)).decide
      (primrec_holds.comp
        ((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.nat_div.comp Primrec.snd (hK.comp Primrec.fst)).pair
            (Primrec.snd.comp Primrec.fst)))))).of_eq fun _ => rfl

private lemma primrec_ltlAccMask : Primrec ltlAccMask := by
  have hLen : Primrec (fun S : List (Formula ℕ ℕ ℕ ℕ) => S.length) := Primrec.list_length
  have hK : Primrec (fun S : List (Formula ℕ ℕ ℕ ℕ) => S.length + 1) := Primrec.succ.comp hLen
  have hQ : Primrec (fun S : List (Formula ℕ ℕ ℕ ℕ) => powNat 2 S.length * (S.length + 1)) :=
    Primrec.nat_mul.comp (primrec_powNat.comp (Primrec.const 2) hLen) hK
  exact (primrec_listToMask hQ
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (hK.comp Primrec.fst))
      (hLen.comp Primrec.fst)).decide).of_eq fun _ => rfl

private def ltlTransMask (S : List (Formula ℕ ℕ ℕ ℕ)) (mk' : ℕ) : ℕ :=
  let K := S.length + 1
  let Q := powNat 2 S.length * K
  let m := mk'.unpair.1
  let k' := mk'.unpair.2
  listToMask Q (fun q' => decide (q' % K = k') && stepConsistent S m (q' / K))

private lemma primrec_ltlTransMask : Primrec₂ ltlTransMask := by
  let Inp := List (Formula ℕ ℕ ℕ ℕ) × ℕ
  have hLen : Primrec (fun p : Inp => p.1.length) := Primrec.list_length.comp Primrec.fst
  have hK : Primrec (fun p : Inp => p.1.length + 1) :=
    Primrec.nat_add.comp hLen (Primrec.const 1)
  have hQ : Primrec (fun p : Inp => powNat 2 p.1.length * (p.1.length + 1)) :=
    Primrec.nat_mul.comp (primrec_powNat.comp (Primrec.const 2) hLen) hK
  have hm : Primrec (fun p : Inp => p.2.unpair.1) := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hk' : Primrec (fun p : Inp => p.2.unpair.2) := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hPred := primrec_bool_and.comp
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (hK.comp Primrec.fst))
      (hk'.comp Primrec.fst)).decide
    (primrec_stepConsistent.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((hm.comp Primrec.fst).pair
          (Primrec.nat_div.comp Primrec.snd (hK.comp Primrec.fst)))))
  exact primrec_mask_clean
    (fun p : Inp => powNat 2 p.1.length * (p.1.length + 1))
    (fun (p : Inp) q' =>
      decide (q' % (p.1.length + 1) = p.2.unpair.2) &&
        stepConsistent p.1 p.2.unpair.1 (q' / (p.1.length + 1)))
    hQ (fun _ => rfl) hPred (fun _ _ => rfl)

private lemma primrec_ltlTransEntry :
    Primrec (fun p : (Instance × List (Formula ℕ ℕ ℕ ℕ)) × ℕ =>
      ltlTransEntry p.1.1 p.1.2 p.2) := by
  let Ctx := (Instance × List (Formula ℕ ℕ ℕ ℕ)) × ℕ
  have hI : Primrec (fun x : Ctx => x.1.1) := Primrec.fst.comp Primrec.fst
  have hS : Primrec (fun x : Ctx => x.1.2) := Primrec.snd.comp Primrec.fst
  have hidx : Primrec (fun x : Ctx => x.2) := Primrec.snd
  have hK := Primrec.nat_add.comp (Primrec.list_length.comp hS) (Primrec.const 1)
  have hαLen := primrec_roundSize.comp hI
  have hq := Primrec.nat_div.comp hidx hαLen
  have ha := Primrec.nat_mod.comp hidx hαLen
  have hm := Primrec.nat_div.comp hq hK
  have hk := Primrec.nat_mod.comp hq hK
  have hk' := primrec_nextCounter.comp (hS.pair (hm.pair hk))
  have hlc := primrec_localConsistent.comp (hI.pair (hS.pair (hm.pair ha)))
  have hMask := primrec_ltlTransMask.comp hS (primrec_nat_pair.comp hm hk')
  exact (Primrec.ite (Primrec.eq.comp hlc (Primrec.const true)) hMask (Primrec.const 0)).of_eq
    fun p => by
      dsimp only [ltlTransEntry, ltlTransMask]
      simp only [Nat.unpair_pair]

theorem primrec_ltlToNBW : Primrec₂ ltlToNBW := by
  let Inp := Instance × Formula ℕ ℕ ℕ ℕ
  have hI : Primrec (fun p : Inp => p.1) := Primrec.fst
  have hψ : Primrec (fun p : Inp => desugar p.2) := primrec_desugar.comp Primrec.snd
  have hS : Primrec (fun p : Inp => dedupList (subformulas (desugar p.2))) :=
    primrec_dedupList.comp (primrec_subformulas.comp hψ)
  have hLen := Primrec.list_length.comp hS
  have hQ := Primrec.nat_mul.comp (primrec_powNat.comp (Primrec.const 2) hLen)
    (Primrec.nat_add.comp hLen (Primrec.const 1))
  have hαLen := primrec_roundSize.comp hI
  have hEntry := primrec_ltlTransEntry.comp
    (((hI.comp Primrec.fst).pair (hS.comp Primrec.fst)).pair Primrec.snd)
  have hTrans := primrec_range_map
    (fun p : Inp =>
      let S := dedupList (subformulas (desugar p.2))
      (powNat 2 S.length * (S.length + 1)) * roundSize p.1)
    (fun p idx => ltlTransEntry p.1 (dedupList (subformulas (desugar p.2))) idx)
    (Primrec.nat_mul.comp hQ hαLen) (fun _ => rfl)
    hEntry (fun _ _ => rfl)
  exact ((Primrec.nat_sub.comp hQ (Primrec.const 1)).pair
    ((primrec_ltlInitMask.comp hS hψ).pair (hTrans.pair (primrec_ltlAccMask.comp hS)))).of_eq
    fun _ => rfl

/-- Convenience wrapper compiling directly from `I : Instance` via `parse I.tokens`. -/
def ltlToNBWInst (I : Instance) : NBWCode :=
  match parse I.tokens with
  | some φ => ltlToNBW I φ
  | none => (0, 0, [0], 0)

theorem primrec_ltlToNBWInst : Primrec ltlToNBWInst :=
  (Primrec.option_casesOn (primrec_parse.comp primrec_tokens)
    (Primrec.const (0, 0, [0], 0))
    (primrec_ltlToNBW.comp Primrec.fst Primrec.snd).to₂).of_eq fun I => by
    unfold ltlToNBWInst
    cases parse I.tokens <;> rfl

/-! #### Correctness of `ltlToNBW` -/

private lemma ltlToNBW_trans_getD (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ) (q a : ℕ)
    (hq : q < powNat 2 (dedupList (subformulas (desugar φ))).length *
      ((dedupList (subformulas (desugar φ))).length + 1))
    (ha : a < roundAlphaMinusOne I + 1) :
    let S := dedupList (subformulas (desugar φ))
    let K := S.length + 1
    let Q := powNat 2 S.length * K
    (ltlToNBW I φ).2.2.1.getD (q * (roundAlphaMinusOne I + 1) + a) 0 =
      if localConsistent I S (q / K) a = true then
        listToMask Q (fun q' =>
          decide (q' % K = nextCounter S (q / K) (q % K)) && stepConsistent S (q / K) (q' / K))
      else 0 := by
  dsimp only [ltlToNBW]
  rw [roundAlphaMinusOne_succ I] at ha ⊢
  rw [getD_map_range_mul _ _ _ q a hq ha]
  unfold ltlTransEntry
  dsimp only
  rw [mul_add_div_alpha _ q a ha, mul_add_mod_alpha _ q a ha]

private lemma nextCounter_lt (S : List (Formula ℕ ℕ ℕ ℕ)) (m k : ℕ) (hk : k < S.length + 1) :
    nextCounter S m k < S.length + 1 := by
  unfold nextCounter
  split_ifs
  · exact Nat.mod_lt _ (Nat.succ_pos _)
  · exact hk

private lemma nextCounter_at_end (S : List (Formula ℕ ℕ ℕ ℕ)) (m : ℕ) :
    nextCounter S m S.length = 0 := by
  unfold nextCounter oblSat
  simp

private lemma nextCounter_lt_end (S : List (Formula ℕ ℕ ℕ ℕ)) (m k : ℕ) (hk : k < S.length) :
    nextCounter S m k = if oblSat S m k then k + 1 else k := by
  unfold nextCounter
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rfl

private lemma counter_fairness_iff (S : List (Formula ℕ ℕ ℕ ℕ)) (mseq kseq : ℕ → ℕ)
    (hk_lt : ∀ t, kseq t ≤ S.length)
    (hk_step : ∀ t, kseq (t + 1) = nextCounter S (mseq t) (kseq t)) :
    (∃ᶠ t in Filter.atTop, kseq t = S.length) ↔
      ∀ i < S.length, ∃ᶠ t in Filter.atTop, oblSat S (mseq t) i = true := by
  rw [Filter.frequently_atTop]
  constructor
  · intro hinf i hi
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨t0, ht0_ge, ht0_eq⟩ := hinf N
    have hk_t01 : kseq (t0 + 1) = 0 := by rw [hk_step t0, ht0_eq, nextCounter_at_end]
    obtain ⟨t1, ht1_ge, ht1_eq⟩ := hinf (t0 + 1)
    by_contra hno
    have hstay : ∀ d ≤ t1 - (t0 + 1), kseq (t0 + 1 + d) ≤ i := by
      intro d hd
      induction d with
      | zero => simp [hk_t01]
      | succ d ih =>
        have hprev := ih (by omega)
        have hstep := hk_step (t0 + 1 + d)
        rw [show t0 + 1 + (d + 1) = t0 + 1 + d + 1 by omega, hstep,
            nextCounter_lt_end S _ _ (by omega)]
        rcases Nat.eq_or_lt_of_le hprev with hki | hlt
        · rw [hki]
          have hfalse : oblSat S (mseq (t0 + 1 + d)) i = false := by
            cases hob : oblSat S (mseq (t0 + 1 + d)) i
            · rfl
            · exact False.elim (hno ⟨t0 + 1 + d, by omega, hob⟩)
          simp [hfalse]
        · split_ifs <;> omega
    have hle := hstay (t1 - (t0 + 1)) le_rfl
    rw [show t0 + 1 + (t1 - (t0 + 1)) = t1 by omega, ht1_eq] at hle
    omega
  · intro hall
    have hreach : ∀ d, ∀ j ≤ S.length, S.length - j ≤ d →
        ∀ t, kseq t = j → ∃ t' ≥ t, kseq t' = S.length := by
      intro d
      induction d with
      | zero =>
        intro j hj hrem t hkt
        have hj_eq : j = S.length := by omega
        exact ⟨t, le_rfl, hkt.trans hj_eq⟩
      | succ d ih =>
        intro j hj hrem t hkt
        rcases Nat.eq_or_lt_of_le hj with rfl | hj_lt
        · exact ⟨t, le_rfl, hkt⟩
        · have hfreq := hall j hj_lt
          rw [Filter.frequently_atTop] at hfreq
          obtain ⟨s, hs_ge, hs_obl⟩ := hfreq t
          by_cases hex : ∃ u, t ≤ u ∧ u ≤ s ∧ kseq u = S.length
          · obtain ⟨u, htu, _, hku⟩ := hex
            exact ⟨u, htu, hku⟩
          · have hlt_all : ∀ u, t ≤ u → u ≤ s → kseq u < S.length := by
              intro u htu hus
              have hle := hk_lt u
              have hne : kseq u ≠ S.length := fun he => hex ⟨u, htu, hus, he⟩
              omega
            have hmono : ∀ n ≤ s - t, j ≤ kseq (t + n) := by
              intro n hn
              induction n with
              | zero => simp [hkt]
              | succ n ihn =>
                have hprev := ihn (by omega)
                have hlt_u := hlt_all (t + n) (by omega) (by omega)
                rw [show t + (n + 1) = t + n + 1 by omega, hk_step (t + n),
                    nextCounter_lt_end S _ _ hlt_u]
                split_ifs <;> omega
            have hks_ge : j ≤ kseq s := by
              simpa [show t + (s - t) = s by omega] using hmono (s - t) le_rfl
            have hks_lt : kseq s < S.length := hlt_all s hs_ge le_rfl
            rcases Nat.eq_or_lt_of_le hks_ge with hks_eq | hks_gt
            · have hnext : kseq (s + 1) = j + 1 := by
                rw [hk_step s, ← hks_eq, nextCounter_lt_end S _ _ (by omega), if_pos hs_obl]
              obtain ⟨t', ht'_ge, ht'_eq⟩ := ih (j + 1) (by omega) (by omega) (s + 1) hnext
              exact ⟨t', by omega, ht'_eq⟩
            · obtain ⟨t', ht'_ge, ht'_eq⟩ :=
                ih (kseq s) (by omega) (by omega) s rfl
              exact ⟨t', by omega, ht'_eq⟩
    intro N
    exact hreach S.length (kseq N) (hk_lt N) (by omega) N rfl

private lemma vw_truth_lemma (I : Instance) (S : List (Formula ℕ ℕ ℕ ℕ))
    (hclosed : ∀ φ ∈ S, ∀ χ ∈ subformulas φ, χ ∈ S)
    (hnd : ∀ φ ∈ S, NoDerived φ)
    (e : ℕ → RoundLetter I)
    (mseq : ℕ → ℕ)
    (hloc : ∀ t, localConsistent I S (mseq t) (roundLetterEquiv I (e t)).val = true)
    (hstep : ∀ t, stepConsistent S (mseq t) (mseq (t + 1)) = true)
    (hfair : ∀ i < S.length, ∃ᶠ t in Filter.atTop, oblSat S (mseq t) i = true) :
    ∀ χ ∈ S, ∀ t, (holds S (mseq t) χ = true ↔ χ.Sat (shift (valExec e) t)) := by
  intro χ hχ_mem
  induction χ with
  | inp1 x =>
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.inp1 x) hχ_mem
    have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
    rw [Equiv.symm_apply_apply] at hrf
    simp only [localConsistentAt_inp1, beq_iff_eq, hrf] at hl
    simp [Formula.Sat, shift, valExec, hl]
  | inp2 x =>
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.inp2 x) hχ_mem
    have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
    rw [Equiv.symm_apply_apply] at hrf
    simp only [localConsistentAt_inp2, beq_iff_eq, hrf] at hl
    simp [Formula.Sat, shift, valExec, hl]
  | out1 y =>
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.out1 y) hχ_mem
    have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
    rw [Equiv.symm_apply_apply] at hrf
    simp only [localConsistentAt_out1, beq_iff_eq, hrf] at hl
    simp [Formula.Sat, shift, valExec, hl]
  | out2 y =>
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.out2 y) hχ_mem
    have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
    rw [Equiv.symm_apply_apply] at hrf
    simp only [localConsistentAt_out2, beq_iff_eq, hrf] at hl
    simp [Formula.Sat, shift, valExec, hl]
  | graph g =>
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.graph g) hχ_mem
    have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
    rw [Equiv.symm_apply_apply] at hrf
    simp only [localConsistentAt_graph, beq_iff_eq, hrf] at hl
    have hidx_inj : ∀ g1 g2 : CommGraph, g1.idx = g2.idx ↔ g1 = g2 := by
      intro g1 g2; cases g1 <;> cases g2 <;> decide
    simp [Formula.Sat, shift, valExec, hl, hidx_inj]
  | eventually _ => exact False.elim (hnd _ hχ_mem)
  | always _ => exact False.elim (hnd _ hχ_mem)
  | weakUntil _ _ => exact False.elim (hnd _ hχ_mem)
  | neg α ih =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.neg α) hχ_mem
    simp only [localConsistentAt_neg, beq_iff_eq] at hl
    rw [hl]
    simp [Formula.Sat, ← ih hα_mem t]
  | or α β ih1 ih2 =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    have hβ_mem : β ∈ S := hclosed _ hχ_mem β (by simp [subformulas, self_mem_subformulas])
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.or α β) hχ_mem
    simp only [localConsistentAt_or, beq_iff_eq] at hl
    rw [hl, Bool.or_eq_true, ih1 hα_mem t, ih2 hβ_mem t]
    rfl
  | and α β ih1 ih2 =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    have hβ_mem : β ∈ S := hclosed _ hχ_mem β (by simp [subformulas, self_mem_subformulas])
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.and α β) hχ_mem
    simp only [localConsistentAt_and, beq_iff_eq] at hl
    rw [hl, Bool.and_eq_true, ih1 hα_mem t, ih2 hβ_mem t]
    rfl
  | imp α β ih1 ih2 =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    have hβ_mem : β ∈ S := hclosed _ hχ_mem β (by simp [subformulas, self_mem_subformulas])
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.imp α β) hχ_mem
    simp only [localConsistentAt_imp, beq_iff_eq] at hl
    rw [hl]
    cases ha : holds S (mseq t) α <;> cases hb : holds S (mseq t) β <;>
      simp [Formula.Sat, ← ih1 hα_mem t, ← ih2 hβ_mem t, ha, hb]
  | iff α β ih1 ih2 =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    have hβ_mem : β ∈ S := hclosed _ hχ_mem β (by simp [subformulas, self_mem_subformulas])
    intro t
    have hl := List.all_eq_true.mp (hloc t) (.iff α β) hχ_mem
    simp only [localConsistentAt_iff, beq_iff_eq] at hl
    rw [hl]
    cases ha : holds S (mseq t) α <;> cases hb : holds S (mseq t) β <;>
      simp [Formula.Sat, ← ih1 hα_mem t, ← ih2 hβ_mem t, ha, hb]
  | next α ih =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    intro t
    have hs := List.all_eq_true.mp (hstep t) (.next α) hχ_mem
    simp only [stepConsistentAt_next, beq_iff_eq] at hs
    rw [hs, ih hα_mem (t + 1)]
    simp only [Formula.Sat, shift_shift]
  | untl α β ih1 ih2 =>
    have hα_mem : α ∈ S := hclosed _ hχ_mem α (by simp [subformulas, self_mem_subformulas])
    have hβ_mem : β ∈ S := hclosed _ hχ_mem β (by simp [subformulas, self_mem_subformulas])
    have hstep_u : ∀ s, holds S (mseq s) (.untl α β) =
        (holds S (mseq s) β || (holds S (mseq s) α && holds S (mseq (s + 1)) (.untl α β))) := by
      intro s
      have hs := List.all_eq_true.mp (hstep s) (.untl α β) hχ_mem
      simpa only [stepConsistentAt_untl, beq_iff_eq] using hs
    intro t
    constructor
    · intro hhold
      let idx := S.idxOf (.untl α β)
      have hidx_lt : idx < S.length := List.idxOf_lt_length_of_mem hχ_mem
      have hget : S.getD idx ttNat = .untl α β := by
        rw [getD_eq_getElem _ _ idx hidx_lt]
        exact List.getElem_idxOf hidx_lt
      have hfreq := hfair idx hidx_lt
      rw [Filter.frequently_atTop] at hfreq
      obtain ⟨s, hs_ge, hobl⟩ := hfreq t
      have haux : ∀ D t0, holds S (mseq t0) (.untl α β) = true →
          oblSat S (mseq (t0 + D)) idx = true →
          (Formula.untl α β).Sat (shift (valExec e) t0) := by
        intro D
        induction D with
        | zero =>
          intro t0 hh ho
          have ho' : oblSat S (mseq t0) idx = true := ho
          unfold oblSat at ho'
          rw [if_pos hidx_lt] at ho'
          dsimp only at ho'
          rw [hget] at ho'
          change (!(mseq t0).testBit idx || holds S (mseq t0) β) = true at ho'
          have hbit : (mseq t0).testBit idx = true := hh
          rw [hbit] at ho'
          simp only [Bool.not_true, Bool.false_or] at ho'
          exact ⟨0, by rw [shift_zero]; exact (ih2 hβ_mem t0).mp ho', fun r' hr' => by omega⟩
        | succ D ihD =>
          intro t0 hh ho
          by_cases hb : holds S (mseq t0) β = true
          · exact ⟨0, by rw [shift_zero]; exact (ih2 hβ_mem t0).mp hb, fun r' hr' => by omega⟩
          · have hb_f : holds S (mseq t0) β = false := Bool.eq_false_iff.mpr hb
            have hsu := hstep_u t0
            rw [hh, hb_f, Bool.false_or] at hsu
            have hsu' : (holds S (mseq t0) α && holds S (mseq (t0 + 1)) (.untl α β)) = true :=
              hsu.symm
            rw [Bool.and_eq_true] at hsu'
            obtain ⟨ha, hnext⟩ := hsu'
            have ho' : oblSat S (mseq ((t0 + 1) + D)) idx = true := by
              rwa [show (t0 + 1) + D = t0 + (D + 1) by omega]
            obtain ⟨r, hr_β, hr_α⟩ := ihD (t0 + 1) hnext ho'
            refine ⟨r + 1, ?_, ?_⟩
            · rw [shift_shift] at hr_β ⊢
              rwa [show t0 + (r + 1) = (t0 + 1) + r by omega]
            · intro r' hr'
              rcases r' with _ | k
              · rw [shift_zero]
                exact (ih1 hα_mem t0).mp ha
              · have hk := hr_α k (by omega)
                rw [shift_shift] at hk ⊢
                rwa [show t0 + (k + 1) = (t0 + 1) + k by omega]
      exact haux (s - t) t hhold (by rwa [show t + (s - t) = s by omega])
    · rintro ⟨r, hr_β, hr_α⟩
      have hback : ∀ d t0,
          β.Sat (shift (valExec e) (t0 + d)) →
          (∀ d' < d, α.Sat (shift (valExec e) (t0 + d'))) →
          holds S (mseq t0) (.untl α β) = true := by
        intro d
        induction d with
        | zero =>
          intro t0 hβ0 _
          rw [hstep_u t0, (ih2 hβ_mem t0).mpr hβ0, Bool.true_or]
        | succ d ihd =>
          intro t0 hβd hαd
          have hα0 : holds S (mseq t0) α = true :=
            (ih1 hα_mem t0).mpr (hαd 0 (Nat.succ_pos d))
          have hnext : holds S (mseq (t0 + 1)) (.untl α β) = true :=
            ihd (t0 + 1) (by rwa [show (t0 + 1) + d = t0 + (d + 1) by omega])
              (fun d' hd' => by
                have hd1 := hαd (d' + 1) (by omega)
                rwa [show (t0 + 1) + d' = t0 + (d' + 1) by omega])
          rw [hstep_u t0, hα0, hnext, Bool.and_self, Bool.or_true]
      rw [shift_shift] at hr_β
      exact hback r t hr_β (fun d' hd' => by
        have hd1 := hr_α d' hd'
        rwa [shift_shift] at hd1)

theorem ltlToNBW_accepts_iff (I : Instance) (φ : Formula ℕ ℕ ℕ ℕ)
    (e : ℕ → RoundLetter I) :
    NBWAccepts (roundAlphaMinusOne I) (ltlToNBW I φ) (fun t => roundLetterEquiv I (e t)) ↔
      φ.Sat (valExec e) := by
  rw [← sat_desugar φ (valExec e)]
  set ψ := desugar φ
  set S := dedupList (subformulas ψ)
  set K := S.length + 1
  set M := powNat 2 S.length
  set Q := M * K
  have hψ_mem : ψ ∈ S := (mem_dedupList _ _).mpr (self_mem_subformulas ψ)
  have hclosed : ∀ f1 ∈ S, ∀ f2 ∈ subformulas f1, f2 ∈ S := by
    intro f1 hf1 f2 hf2
    exact (mem_dedupList _ _).mpr (subformulas_trans hf2 ((mem_dedupList _ _).mp hf1))
  have hnd : ∀ f1 ∈ S, NoDerived f1 := fun f1 hf1 =>
    noDerived_of_mem_subformulas (noDerived_desugar φ) ((mem_dedupList _ _).mp hf1)
  have hM_pos : 0 < M := by simp [M, powNat_eq]
  have hK_pos : 0 < K := Nat.succ_pos _
  have hQ_pos : 0 < Q := Nat.mul_pos hM_pos hK_pos
  have hQ_succ : Q - 1 + 1 = Q := Nat.sub_add_cancel hQ_pos
  constructor
  · rintro ⟨run, hinit, htrans, hacc⟩
    let qseq : ℕ → ℕ := fun t => (run t).val
    have hq_lt : ∀ t, qseq t < Q := fun t => (run t).isLt.trans_eq hQ_succ
    let mseq : ℕ → ℕ := fun t => qseq t / K
    let kseq : ℕ → ℕ := fun t => qseq t % K
    have hk_le : ∀ t, kseq t ≤ S.length := fun t =>
      Nat.lt_succ_iff.mp (Nat.mod_lt (qseq t) hK_pos)
    have hstep_props : ∀ t,
        localConsistent I S (mseq t) (roundLetterEquiv I (e t)).val = true ∧
        stepConsistent S (mseq t) (mseq (t + 1)) = true ∧
        kseq (t + 1) = nextCounter S (mseq t) (kseq t) := by
      intro t
      have ht := htrans t
      dsimp only at ht
      rw [ltlToNBW_trans_getD I φ (run t).val (roundLetterEquiv I (e t)).val
        (hq_lt t) (roundLetterEquiv I (e t)).isLt] at ht
      cases hlc : localConsistent I S (mseq t) (roundLetterEquiv I (e t)).val with
      | false =>
        change (if localConsistent I S (mseq t) (roundLetterEquiv I (e t)).val = true then _ else 0).testBit
          (qseq (t + 1)) = true at ht
        rw [hlc] at ht; simp at ht
      | true =>
        change (if localConsistent I S (mseq t) (roundLetterEquiv I (e t)).val = true then _ else 0).testBit
          (qseq (t + 1)) = true at ht
        rw [hlc, if_pos rfl, testBit_listToMask] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨rfl, ht.2.2, ht.2.1⟩
    have hk_fair : ∃ᶠ t in Filter.atTop, kseq t = S.length := by
      refine hacc.mono fun t ht => ?_
      dsimp only [ltlToNBW, ltlAccMask] at ht
      rw [testBit_listToMask] at ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ht.2
    have hfair := (counter_fairness_iff S mseq kseq hk_le (fun t => (hstep_props t).2.2)).mp hk_fair
    have htruth := vw_truth_lemma I S hclosed hnd e mseq
      (fun t => (hstep_props t).1) (fun t => (hstep_props t).2.1) hfair
    dsimp only [ltlToNBW, ltlInitMask] at hinit
    rw [testBit_listToMask] at hinit
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hinit
    have h0 := (htruth ψ hψ_mem 0).mp hinit.2.2
    rwa [shift_zero] at h0
  · intro hsat
    classical
    let mseq : ℕ → ℕ := fun t =>
      packBits ((List.range S.length).map fun i =>
        decide ((S.getD i ttNat).Sat (shift (valExec e) t)))
    have hm_lt : ∀ t, mseq t < M := fun t => by
      dsimp only [mseq, M]
      rw [powNat_eq]
      simpa using packBits_lt_two_pow ((List.range S.length).map fun i =>
        decide ((S.getD i ttNat).Sat (shift (valExec e) t)))
    have hholds_canon : ∀ t, ∀ χ ∈ S,
        holds S (mseq t) χ = decide (χ.Sat (shift (valExec e) t)) := by
      intro t χ hχ
      unfold holds
      have hidx_lt : S.idxOf χ < S.length := List.idxOf_lt_length_of_mem hχ
      dsimp only [mseq]
      rw [testBit_packBits, getD_eq_getElem _ _ _ (by simp [hidx_lt])]
      simp only [List.getElem_map, List.getElem_range]
      rw [getD_eq_getElem _ _ _ hidx_lt, List.getElem_idxOf hidx_lt]
    have hloc_canon : ∀ t, localConsistent I S (mseq t) (roundLetterEquiv I (e t)).val = true := by
      intro t
      apply List.all_eq_true.mpr
      intro χ hχ
      have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
      rw [Equiv.symm_apply_apply] at hrf
      cases χ with
      | inp1 x =>
        simp [hholds_canon t _ hχ, hrf, Formula.Sat, shift, valExec]
      | inp2 x =>
        simp [hholds_canon t _ hχ, hrf, Formula.Sat, shift, valExec]
      | out1 y =>
        simp [hholds_canon t _ hχ, hrf, Formula.Sat, shift, valExec]
      | out2 y =>
        simp [hholds_canon t _ hχ, hrf, Formula.Sat, shift, valExec]
      | graph g =>
        have hidx_inj : ∀ g1 g2 : CommGraph, g1.idx = g2.idx ↔ g1 = g2 := by
          intro g1 g2; cases g1 <;> cases g2 <;> decide
        simp [hholds_canon t _ hχ, hrf, Formula.Sat, shift, valExec, hidx_inj]
      | next _ | untl _ _ | eventually _ | always _ | weakUntil _ _ =>
        simp
      | neg α =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        by_cases ha : α.Sat (shift (valExec e) t) <;>
          simp [hholds_canon t _ hχ, hholds_canon t _ hα, Formula.Sat, ha]
      | or α β =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        have hβ := hclosed _ hχ β (by simp [subformulas, self_mem_subformulas])
        by_cases ha : α.Sat (shift (valExec e) t) <;> by_cases hb : β.Sat (shift (valExec e) t) <;>
          simp [hholds_canon t _ hχ, hholds_canon t _ hα, hholds_canon t _ hβ, Formula.Sat, ha, hb]
      | and α β =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        have hβ := hclosed _ hχ β (by simp [subformulas, self_mem_subformulas])
        by_cases ha : α.Sat (shift (valExec e) t) <;> by_cases hb : β.Sat (shift (valExec e) t) <;>
          simp [hholds_canon t _ hχ, hholds_canon t _ hα, hholds_canon t _ hβ, Formula.Sat, ha, hb]
      | imp α β =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        have hβ := hclosed _ hχ β (by simp [subformulas, self_mem_subformulas])
        by_cases ha : α.Sat (shift (valExec e) t) <;> by_cases hb : β.Sat (shift (valExec e) t) <;>
          simp [hholds_canon t _ hχ, hholds_canon t _ hα, hholds_canon t _ hβ, Formula.Sat, ha, hb]
      | iff α β =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        have hβ := hclosed _ hχ β (by simp [subformulas, self_mem_subformulas])
        by_cases ha : α.Sat (shift (valExec e) t) <;> by_cases hb : β.Sat (shift (valExec e) t) <;>
          simp [hholds_canon t _ hχ, hholds_canon t _ hα, hholds_canon t _ hβ, Formula.Sat, ha, hb]
    have hstep_canon : ∀ t, stepConsistent S (mseq t) (mseq (t + 1)) = true := by
      intro t
      apply List.all_eq_true.mpr
      intro χ hχ
      cases χ with
      | next α =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        simp only [stepConsistentAt_next, beq_iff_eq,
          hholds_canon t _ hχ, hholds_canon (t + 1) _ hα]
        congr 1
        simp only [Formula.Sat, shift_shift]
      | untl α β =>
        have hα := hclosed _ hχ α (by simp [subformulas, self_mem_subformulas])
        have hβ := hclosed _ hχ β (by simp [subformulas, self_mem_subformulas])
        simp only [stepConsistentAt_untl, beq_iff_eq,
          hholds_canon t _ hχ, hholds_canon t _ hα, hholds_canon t _ hβ, hholds_canon (t + 1) _ hχ]
        have huntl_unfold : (Formula.untl α β).Sat (shift (valExec e) t) ↔
            β.Sat (shift (valExec e) t) ∨
              (α.Sat (shift (valExec e) t) ∧ (Formula.untl α β).Sat (shift (valExec e) (t + 1))) := by
          constructor
          · rintro ⟨r, hr_β, hr_α⟩
            rcases r with _ | k
            · rw [shift_zero] at hr_β; exact Or.inl hr_β
            · refine Or.inr ⟨by have h0 := hr_α 0 (Nat.succ_pos k); rwa [shift_zero] at h0, ⟨k, ?_, ?_⟩⟩
              · rw [shift_shift] at hr_β ⊢
                rwa [show (t + 1) + k = t + (k + 1) by omega]
              · intro k' hk'
                have hk1 := hr_α (k' + 1) (by omega)
                rw [shift_shift] at hk1 ⊢
                rwa [show (t + 1) + k' = t + (k' + 1) by omega]
          · rintro (hb | ⟨ha, ⟨k, hk_β, hk_α⟩⟩)
            · exact ⟨0, by rwa [shift_zero], fun r' hr' => by omega⟩
            · refine ⟨k + 1, ?_, ?_⟩
              · rw [shift_shift] at hk_β ⊢
                rwa [show t + (k + 1) = (t + 1) + k by omega]
              · intro r' hr'
                rcases r' with _ | k'
                · rwa [shift_zero]
                · have hk1 := hk_α k' (by omega)
                  rw [shift_shift] at hk1 ⊢
                  rwa [show t + (k' + 1) = (t + 1) + k' by omega]
        by_cases hb : β.Sat (shift (valExec e) t) <;>
          by_cases ha : α.Sat (shift (valExec e) t) <;>
          by_cases hu1 : (Formula.untl α β).Sat (shift (valExec e) (t + 1)) <;>
          simp [huntl_unfold, hb, ha, hu1]
      | _ => simp [stepConsistentAt, classifyFormula]
    have hfair_canon : ∀ i < S.length, ∃ᶠ t in Filter.atTop, oblSat S (mseq t) i = true := by
      intro i hi
      rw [Filter.frequently_atTop]
      intro N
      have hget : S.getD i ttNat = S[i] := getD_eq_getElem S ttNat i hi
      cases hSi : S[i] with
      | untl α β =>
        have hβ_mem : β ∈ S := hclosed S[i] (List.getElem_mem hi) β
          (by rw [hSi]; simp [subformulas, self_mem_subformulas])
        by_cases hu : (Formula.untl α β).Sat (shift (valExec e) N)
        · obtain ⟨r, hr_β, _⟩ := hu
          refine ⟨N + r, by omega, ?_⟩
          rw [shift_shift] at hr_β
          unfold oblSat
          rw [if_pos hi]
          dsimp only
          rw [hget, hSi]
          change (!(mseq (N + r)).testBit i || holds S (mseq (N + r)) β) = true
          rw [hholds_canon (N + r) β hβ_mem, decide_eq_true hr_β, Bool.or_true]
        · refine ⟨N, le_rfl, ?_⟩
          have hbit_f : (mseq N).testBit i = false := by
            dsimp only [mseq]
            rw [testBit_packBits, getD_eq_getElem _ _ i (by simp [hi])]
            simp only [List.getElem_map, List.getElem_range]
            rw [hget, hSi]
            exact decide_eq_false hu
          unfold oblSat
          rw [if_pos hi]
          dsimp only
          rw [hget, hSi]
          change (!(mseq N).testBit i || holds S (mseq N) β) = true
          rw [hbit_f]
          rfl
      | _ =>
        refine ⟨N, le_rfl, ?_⟩
        simp [oblSat, hi, hSi, classifyFormula]
    let kseq : ℕ → ℕ := fun t => Nat.rec S.length (fun n kn => nextCounter S (mseq n) kn) t
    have hk_lt : ∀ t, kseq t < K := by
      intro t
      induction t with
      | zero => exact Nat.lt_succ_self _
      | succ t ih => exact nextCounter_lt S (mseq t) (kseq t) ih
    have hk_le : ∀ t, kseq t ≤ S.length := fun t => Nat.lt_succ_iff.mp (hk_lt t)
    have hk_inf : ∃ᶠ t in Filter.atTop, kseq t = S.length :=
      (counter_fairness_iff S mseq kseq hk_le (fun _ => rfl)).mpr hfair_canon
    have hq_lt : ∀ t, mseq t * K + kseq t < Q - 1 + 1 := by
      intro t
      rw [hQ_succ]
      have hm1 : mseq t + 1 ≤ M := hm_lt t
      have hk1 := hk_lt t
      calc mseq t * K + kseq t < mseq t * K + K := Nat.add_lt_add_left hk1 _
        _ = (mseq t + 1) * K := by rw [Nat.succ_mul]
        _ ≤ M * K := Nat.mul_le_mul_right K hm1
    let run : ℕ → Fin (Q - 1 + 1) := fun t => ⟨mseq t * K + kseq t, hq_lt t⟩
    have hdiv_run : ∀ t, (run t).val / K = mseq t := fun t => by
      dsimp only [run]
      rw [Nat.mul_comm (mseq t) K, Nat.add_comm, Nat.add_mul_div_left _ _ hK_pos,
          Nat.div_eq_of_lt (hk_lt t), zero_add]
    have hmod_run : ∀ t, (run t).val % K = kseq t := fun t => by
      dsimp only [run]
      rw [Nat.mul_comm (mseq t) K, Nat.add_comm, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (hk_lt t)]
    refine ⟨run, ?_, ?_, ?_⟩
    · dsimp only [ltlToNBW, ltlInitMask]
      rw [testBit_listToMask]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨(run 0).isLt.trans_eq hQ_succ, by rw [hmod_run 0]; rfl, ?_⟩
      rw [hdiv_run 0, hholds_canon 0 ψ hψ_mem, shift_zero]
      exact decide_eq_true hsat
    · intro t
      dsimp only
      rw [ltlToNBW_trans_getD I φ (run t).val (roundLetterEquiv I (e t)).val
        ((run t).isLt.trans_eq hQ_succ) (roundLetterEquiv I (e t)).isLt]
      rw [hdiv_run t, hmod_run t, if_pos (hloc_canon t), testBit_listToMask]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨(run (t + 1)).isLt.trans_eq hQ_succ, hmod_run (t + 1),
        by rw [hdiv_run (t + 1)]; exact hstep_canon t⟩
    · refine hk_inf.mono fun t ht => ?_
      dsimp only [ltlToNBW, ltlAccMask]
      rw [testBit_listToMask]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨(run t).isLt.trans_eq hQ_succ, by rw [hmod_run t, ht]⟩

/-! ### Section 4: Parity Dichotomy, Adversary Complement `notAdvNBW`, and `unionNBW` -/

def OddParityCond (c : ℕ → ℕ) : Prop :=
  ∃ p : ℕ, Odd p ∧ (∃ᶠ n in Filter.atTop, c n = p) ∧ ∀ᶠ n in Filter.atTop, p ≤ c n

lemma not_parityCond_and_oddParityCond (c : ℕ → ℕ) :
    ¬ (ParityCond c ∧ OddParityCond c) := by
  rintro ⟨⟨p, hp_even, hp_freq, hp_ev⟩, ⟨q, hq_odd, hq_freq, hq_ev⟩⟩
  rw [Filter.eventually_atTop] at hp_ev hq_ev
  obtain ⟨N1, hN1⟩ := hp_ev
  obtain ⟨N2, hN2⟩ := hq_ev
  rw [Filter.frequently_atTop] at hp_freq hq_freq
  obtain ⟨n1, hn1, hcn1⟩ := hq_freq N1
  obtain ⟨n2, hn2, hcn2⟩ := hp_freq N2
  have h1 := hN1 n1 hn1
  have h2 := hN2 n2 hn2
  have hpq : p = q := by omega
  subst hpq
  rcases hp_even with ⟨k, rfl⟩
  rcases hq_odd with ⟨l, hl⟩
  omega

lemma parityCond_or_oddParityCond_of_bdd (c : ℕ → ℕ) (B : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ B) :
    ParityCond c ∨ OddParityCond c := by
  classical
  have hex : ∃ p : ℕ, p ≤ B ∧ ∃ᶠ n in Filter.atTop, c n = p := by
    by_contra hall
    have hnone : ∀ p ≤ B, ∃ N : ℕ, ∀ n ≥ N, c n ≠ p := by
      intro p hp
      have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = p := fun hf => hall ⟨p, hp, hf⟩
      rw [Filter.frequently_atTop] at hnf
      by_contra hnoN
      apply hnf
      intro N
      by_contra hno_n
      exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
    let boundOf : ℕ → ℕ := fun p => if hp : p ≤ B then (hnone p hp).choose else 0
    let M := (Finset.range (B + 1)).sup boundOf
    have hcM : c M ≤ B := hbdd M
    have hleM : boundOf (c M) ≤ M :=
      Finset.le_sup (f := boundOf) (Finset.mem_range.mpr (by omega))
    have hspec : ∀ n ≥ boundOf (c M), c n ≠ c M := by
      dsimp only [boundOf]; rw [dif_pos hcM]; exact (hnone (c M) hcM).choose_spec
    exact hspec M hleM rfl
  let p := Nat.find hex
  have hp_spec : p ≤ B ∧ ∃ᶠ n in Filter.atTop, c n = p := Nat.find_spec hex
  have hp_min : ∀ q < p, ¬ (q ≤ B ∧ ∃ᶠ n in Filter.atTop, c n = q) :=
    fun q hq => Nat.find_min hex hq
  have hno_lt : ∀ q < p, ∃ N : ℕ, ∀ n ≥ N, c n ≠ q := by
    intro q hq
    have hqB : q ≤ B := le_trans (le_of_lt hq) hp_spec.1
    have hnf : ¬ ∃ᶠ n in Filter.atTop, c n = q := fun hf => hp_min q hq ⟨hqB, hf⟩
    rw [Filter.frequently_atTop] at hnf
    by_contra hnoN
    apply hnf
    intro N
    by_contra hno_n
    exact hnoN ⟨N, fun n hn hc => hno_n ⟨n, hn, hc⟩⟩
  let boundLt : ℕ → ℕ := fun q => if hq : q < p then (hno_lt q hq).choose else 0
  let N0 := (Finset.range p).sup boundLt
  have hev : ∀ᶠ n in Filter.atTop, p ≤ c n := by
    rw [Filter.eventually_atTop]
    refine ⟨N0, fun n hn => ?_⟩
    by_contra hlt
    have hcp : c n < p := by omega
    have hleN : boundLt (c n) ≤ N0 :=
      Finset.le_sup (f := boundLt) (Finset.mem_range.mpr hcp)
    have hspec : ∀ m ≥ boundLt (c n), c m ≠ c n := by
      dsimp only [boundLt]; rw [dif_pos hcp]; exact (hno_lt (c n) hcp).choose_spec
    exact hspec n (le_trans hleN hn) rfl
  rcases Nat.even_or_odd p with heven | hodd
  · exact Or.inl ⟨p, heven, hp_spec.2, hev⟩
  · exact Or.inr ⟨p, hodd, hp_spec.2, hev⟩

lemma oddParityCond_iff_not_parityCond_of_bdd (c : ℕ → ℕ) (B : ℕ)
    (hbdd : ∀ n : ℕ, c n ≤ B) :
    OddParityCond c ↔ ¬ ParityCond c := by
  constructor
  · intro ho hp; exact not_parityCond_and_oddParityCond c ⟨hp, ho⟩
  · intro hnp
    rcases parityCond_or_oddParityCond_of_bdd c B hbdd with hp | ho
    · exact False.elim (hnp hp)
    · exact ho

lemma parityCond_shift (c : ℕ → ℕ) (d : ℕ) :
    ParityCond c ↔ ParityCond (fun n => c (d + n)) := by
  unfold ParityCond
  constructor
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq (d + N)
      refine ⟨n - d, by omega, ?_⟩
      dsimp only; rwa [show d + (n - d) = n by omega]
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      exact ⟨N, fun n hn => hN (d + n) (by omega)⟩
  · rintro ⟨p, heven, hfreq, hev⟩
    refine ⟨p, heven, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N
      obtain ⟨n, hn, hp⟩ := hfreq N
      exact ⟨d + n, by omega, hp⟩
    · rw [Filter.eventually_atTop] at hev ⊢
      obtain ⟨N, hN⟩ := hev
      refine ⟨d + N, fun n hn => ?_⟩
      have h := hN (n - d) (by omega)
      dsimp only at h
      rwa [show d + (n - d) = n by omega] at h

def maxList (l : List ℕ) : ℕ := l.foldr max 0

lemma primrec_nat_max : Primrec₂ (max : ℕ → ℕ → ℕ) :=
  (Primrec.ite Primrec.nat_le Primrec.snd Primrec.fst).of_eq fun p => by
    simp [Nat.max_def]

lemma primrec_nat_min : Primrec₂ (min : ℕ → ℕ → ℕ) :=
  (Primrec.ite Primrec.nat_le Primrec.fst Primrec.snd).of_eq fun p => by
    simp [Nat.min_def]

lemma primrec_maxList : Primrec maxList :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (primrec_nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun _ => rfl

lemma getD_le_maxList (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ maxList l := by
  induction l generalizing i with
  | nil => simp [maxList]
  | cons a tl ih =>
    rcases i with _ | k
    · simp [maxList, List.getD_eq_getElem?_getD]
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, maxList, List.foldr_cons]
      rw [← List.getD_eq_getElem?_getD]
      exact le_trans (ih k) (le_max_right a (maxList tl))

def advStepNat (c : DPACode) (s : ℕ) (g : CommGraph) : ℕ :=
  (c.2.1.getD (3 * s + g.idx) 0) % (c.1 + 1)

lemma primrec_advStepNat : Primrec (fun p : DPACode × ℕ × CommGraph =>
    advStepNat p.1 p.2.1 p.2.2) :=
  Primrec.nat_mod.comp
    (primrec_list_getD.comp
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.fst.comp Primrec.snd))
          (primrec_commGraphIdx.comp (Primrec.snd.comp Primrec.snd))).pair
          (Primrec.const 0))))
    (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))

def notAdvAccMask (c : DPACode) : ℕ :=
  let P_modes := maxList c.2.2 + 2
  let Q := (c.1 + 1) * P_modes
  listToMask Q (fun q =>
    let s := q / P_modes
    let m := q % P_modes
    decide (0 < m) && decide ((m - 1) % 2 = 1) && decide (c.2.2.getD s 0 = m - 1))

def notAdvTransEntry (c : DPACode) (I : Instance) (idx : ℕ) : ℕ :=
  let P_modes := maxList c.2.2 + 2
  let Q := (c.1 + 1) * P_modes
  let αLen := roundSize I
  let q := idx / αLen
  let a := idx % αLen
  let s := q / P_modes
  let m := q % P_modes
  let g := (decodeRoundFields I a).2.2.1
  let s' := advStepNat c s g
  if m = 0 then
    listToMask Q (fun q' =>
      decide (q' / P_modes = s') &&
        (decide (q' % P_modes = 0) ||
          (decide (0 < q' % P_modes) && decide ((q' % P_modes - 1) % 2 = 1))))
  else if m - 1 ≤ c.2.2.getD s 0 ∧ (m - 1) % 2 = 1 then
    listToMask Q (fun q' => decide (q' = s' * P_modes + m))
  else 0

/-- NBW over `Fin (roundAlphaMinusOne I + 1)` recognizing `{e | graphOfExec e ∉ c.lang}` by
nondeterministically guessing the stabilization point and minimum odd priority of `c.toDPA`. -/
def notAdvNBW (c : DPACode) (I : Instance) : NBWCode :=
  let Q := (c.1 + 1) * (maxList c.2.2 + 2)
  let αLen := roundSize I
  (Q - 1, listToMask Q (fun q => decide (q = 0)),
    (List.range (Q * αLen)).map (notAdvTransEntry c I), notAdvAccMask c)

private lemma primrec_notAdvAccMask : Primrec notAdvAccMask := by
  have hP : Primrec (fun c : DPACode => maxList c.2.2 + 2) :=
    Primrec.succ.comp (Primrec.succ.comp (primrec_maxList.comp (Primrec.snd.comp Primrec.snd)))
  have hQ : Primrec (fun c : DPACode => (c.1 + 1) * (maxList c.2.2 + 2)) :=
    Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) hP
  have hs := Primrec.nat_div.comp Primrec.snd (hP.comp Primrec.fst)
  have hm := Primrec.nat_mod.comp Primrec.snd (hP.comp Primrec.fst)
  have hm1 := Primrec.nat_sub.comp hm (Primrec.const 1)
  have hprio := primrec_list_getD.comp
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair (hs.pair (Primrec.const 0)))
  exact (primrec_listToMask hQ
    (primrec_bool_and.comp
      (primrec_bool_and.comp
        (Primrec.nat_lt.comp (Primrec.const 0) hm).decide
        (Primrec.eq.comp (Primrec.nat_mod.comp hm1 (Primrec.const 2)) (Primrec.const 1)).decide)
      (Primrec.eq.comp hprio hm1).decide)).of_eq fun _ => rfl

private def notAdvMask0 (packed : ℕ) : ℕ :=
  let Q := packed.unpair.1
  let P_modes := packed.unpair.2.unpair.1
  let s' := packed.unpair.2.unpair.2
  listToMask Q (fun q' =>
    decide (q' / P_modes = s') &&
      (decide (q' % P_modes = 0) ||
        (decide (0 < q' % P_modes) && decide ((q' % P_modes - 1) % 2 = 1))))

private lemma primrec_notAdvMask0 : Primrec notAdvMask0 := by
  have hQ : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hP : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hs' : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hq'div := Primrec.nat_div.comp Primrec.snd hP
  have hq'mod := Primrec.nat_mod.comp Primrec.snd hP
  have hPred : Primrec (fun q : ℕ × ℕ =>
      decide (q.2 / q.1.unpair.2.unpair.1 = q.1.unpair.2.unpair.2) &&
        (decide (q.2 % q.1.unpair.2.unpair.1 = 0) ||
          (decide (0 < q.2 % q.1.unpair.2.unpair.1) &&
            decide ((q.2 % q.1.unpair.2.unpair.1 - 1) % 2 = 1)))) :=
    primrec_bool_and.comp
      (Primrec.eq.comp hq'div hs').decide
      (primrec_bool_or.comp
        (Primrec.eq.comp hq'mod (Primrec.const 0)).decide
        (primrec_bool_and.comp
          (Primrec.nat_lt.comp (Primrec.const 0) hq'mod).decide
          (Primrec.eq.comp
            (Primrec.nat_mod.comp (Primrec.nat_sub.comp hq'mod (Primrec.const 1)) (Primrec.const 2))
            (Primrec.const 1)).decide))
  exact (primrec_listToMask hQ hPred).of_eq fun _ => rfl

private def notAdvMaskLock (packed : ℕ) : ℕ :=
  let Q := packed.unpair.1
  let target := packed.unpair.2
  listToMask Q (fun q' => decide (q' = target))

private lemma primrec_notAdvMaskLock : Primrec notAdvMaskLock := by
  have hQ : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hPred : Primrec (fun q : ℕ × ℕ => decide (q.2 = q.1.unpair.2)) :=
    (Primrec.eq.comp Primrec.snd (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))).decide
  exact (primrec_listToMask hQ hPred).of_eq fun _ => rfl

private def zeroMask (Q : ℕ) : ℕ :=
  listToMask Q (fun q => decide (q = 0))

private lemma primrec_zeroMask : Primrec zeroMask := by
  have hPred : Primrec (fun q : ℕ × ℕ => decide (q.2 = 0)) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const 0)).decide
  exact (primrec_listToMask Primrec.id hPred).of_eq fun _ => rfl

private lemma primrec_notAdvTransEntry :
    Primrec (fun p : (DPACode × Instance) × ℕ => notAdvTransEntry p.1.1 p.1.2 p.2) := by
  let Ctx := (DPACode × Instance) × ℕ
  have hc : Primrec (fun x : Ctx => x.1.1) := Primrec.fst.comp Primrec.fst
  have hI : Primrec (fun x : Ctx => x.1.2) := Primrec.snd.comp Primrec.fst
  have hidx : Primrec (fun x : Ctx => x.2) := Primrec.snd
  have hP := Primrec.nat_add.comp
    (primrec_maxList.comp (Primrec.snd.comp (Primrec.snd.comp hc))) (Primrec.const 2)
  have hQ := Primrec.nat_mul.comp
    (Primrec.nat_add.comp (Primrec.fst.comp hc) (Primrec.const 1)) hP
  have hαLen := primrec_roundSize.comp hI
  have hq := Primrec.nat_div.comp hidx hαLen
  have ha := Primrec.nat_mod.comp hidx hαLen
  have hs := Primrec.nat_div.comp hq hP
  have hm := Primrec.nat_mod.comp hq hP
  have hg := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (primrec_decodeRoundFields.comp hI ha)))
  have hs' := primrec_advStepNat.comp (hc.pair (hs.pair hg))
  have hMask0 := primrec_notAdvMask0.comp
    (primrec_nat_pair.comp hQ (primrec_nat_pair.comp hP hs'))
  have hMaskLock := primrec_notAdvMaskLock.comp
    (primrec_nat_pair.comp hQ (Primrec.nat_add.comp (Primrec.nat_mul.comp hs' hP) hm))
  have hprio := primrec_list_getD.comp
    ((Primrec.snd.comp (Primrec.snd.comp hc)).pair (hs.pair (Primrec.const 0)))
  have hm1 := Primrec.nat_sub.comp hm (Primrec.const 1)
  have hGuard : PrimrecPred (fun x : Ctx =>
      (x.2 / roundSize x.1.2 % (maxList x.1.1.2.2 + 2) - 1 ≤
        x.1.1.2.2.getD (x.2 / roundSize x.1.2 / (maxList x.1.1.2.2 + 2)) 0) ∧
      (x.2 / roundSize x.1.2 % (maxList x.1.1.2.2 + 2) - 1) % 2 = 1) :=
    (Primrec.nat_le.comp hm1 hprio).and
      (Primrec.eq.comp (Primrec.nat_mod.comp hm1 (Primrec.const 2)) (Primrec.const 1))
  exact (Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) hMask0
    (Primrec.ite hGuard hMaskLock (Primrec.const 0))).of_eq fun p => by
      dsimp only [notAdvTransEntry, notAdvMask0, notAdvMaskLock]
      simp only [Nat.unpair_pair]

lemma primrec_notAdvNBW : Primrec₂ notAdvNBW := by
  let Inp := DPACode × Instance
  have hQ : Primrec (fun p : Inp => (p.1.1 + 1) * (maxList p.1.2.2 + 2)) :=
    Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1))
      (Primrec.nat_add.comp
        (primrec_maxList.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const 2))
  have hαLen : Primrec (fun p : Inp => roundSize p.2) := primrec_roundSize.comp Primrec.snd
  have hInit := primrec_zeroMask.comp hQ
  have hTrans := primrec_range_map
    (fun p : Inp => ((p.1.1 + 1) * (maxList p.1.2.2 + 2)) * roundSize p.2)
    (fun p idx => notAdvTransEntry p.1 p.2 idx)
    (Primrec.nat_mul.comp hQ hαLen) (fun _ => rfl)
    primrec_notAdvTransEntry (fun _ _ => rfl)
  exact ((Primrec.nat_sub.comp hQ (Primrec.const 1)).pair
    (hInit.pair (hTrans.pair (primrec_notAdvAccMask.comp Primrec.fst)))).of_eq fun _ => rfl

private lemma notAdvNBW_trans_getD (c : DPACode) (I : Instance) (q a : ℕ)
    (hq : q < (c.1 + 1) * (maxList c.2.2 + 2))
    (ha : a < roundAlphaMinusOne I + 1) :
    let P_modes := maxList c.2.2 + 2
    let Q := (c.1 + 1) * P_modes
    let s := q / P_modes
    let m := q % P_modes
    let s' := advStepNat c s (decodeRoundFields I a).2.2.1
    (notAdvNBW c I).2.2.1.getD (q * (roundAlphaMinusOne I + 1) + a) 0 =
      if m = 0 then
        listToMask Q (fun q' =>
          decide (q' / P_modes = s') &&
            (decide (q' % P_modes = 0) ||
              (decide (0 < q' % P_modes) && decide ((q' % P_modes - 1) % 2 = 1))))
      else if m - 1 ≤ c.2.2.getD s 0 ∧ (m - 1) % 2 = 1 then
        listToMask Q (fun q' => decide (q' = s' * P_modes + m))
      else 0 := by
  dsimp only [notAdvNBW]
  rw [roundAlphaMinusOne_succ I] at ha ⊢
  rw [getD_map_range_mul _ _ _ q a hq ha]
  unfold notAdvTransEntry
  dsimp only
  rw [mul_add_div_alpha _ q a ha, mul_add_mod_alpha _ q a ha]

lemma notAdvNBW_accepts_iff (c : DPACode) (I : Instance) (e : ℕ → RoundLetter I) :
    NBWAccepts (roundAlphaMinusOne I) (notAdvNBW c I) (fun t => roundLetterEquiv I (e t)) ↔
      graphOfExec e ∉ c.lang := by
  have hbdd : ∀ t, c.toDPA.prio (c.toDPA.run (graphOfExec e) t) ≤ maxList c.2.2 :=
    fun t => getD_le_maxList c.2.2 _
  change _ ↔ ¬ ParityCond (fun t => c.toDPA.prio (c.toDPA.run (graphOfExec e) t))
  rw [← oddParityCond_iff_not_parityCond_of_bdd _ (maxList c.2.2) hbdd]
  set S_adv := c.1 + 1
  set P_modes := maxList c.2.2 + 2
  set Q := S_adv * P_modes
  have hS_pos : 0 < S_adv := Nat.succ_pos _
  have hP_pos : 0 < P_modes := by omega
  have hQ_pos : 0 < Q := Nat.mul_pos hS_pos hP_pos
  have hQ_succ : Q - 1 + 1 = Q := Nat.sub_add_cancel hQ_pos
  constructor
  · rintro ⟨run, hinit, htrans, hacc⟩
    let qseq : ℕ → ℕ := fun t => (run t).val
    have hq_lt : ∀ t, qseq t < Q := fun t => (run t).isLt.trans_eq hQ_succ
    let sseq : ℕ → ℕ := fun t => qseq t / P_modes
    let mseq : ℕ → ℕ := fun t => qseq t % P_modes
    have hq0 : qseq 0 = 0 := by
      dsimp only [notAdvNBW] at hinit
      rw [testBit_listToMask] at hinit
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hinit
      exact hinit.2
    have hstep_all : ∀ t,
        sseq (t + 1) = advStepNat c (sseq t) (e t).1.2.2 ∧
        (mseq t = 0 ∨
          (0 < mseq t ∧ mseq t - 1 ≤ c.2.2.getD (sseq t) 0 ∧
            (mseq t - 1) % 2 = 1 ∧ mseq (t + 1) = mseq t)) := by
      intro t
      have ht := htrans t
      dsimp only at ht
      rw [notAdvNBW_trans_getD c I (run t).val (roundLetterEquiv I (e t)).val
        (hq_lt t) (roundLetterEquiv I (e t)).isLt] at ht
      have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
      rw [Equiv.symm_apply_apply] at hrf
      have hg_eq : (decodeRoundFields I (roundLetterEquiv I (e t)).val).2.2.1 = (e t).1.2.2 := by
        rw [hrf]
      rw [hg_eq] at ht
      by_cases hm0 : mseq t = 0
      · rw [if_pos hm0, testBit_listToMask] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨ht.2.1, Or.inl hm0⟩
      · rw [if_neg hm0] at ht
        by_cases hg_ok : mseq t - 1 ≤ c.2.2.getD (sseq t) 0 ∧ (mseq t - 1) % 2 = 1
        · rw [if_pos hg_ok, testBit_listToMask] at ht
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
          have hq_next : qseq (t + 1) = advStepNat c (sseq t) (e t).1.2.2 * P_modes + mseq t := ht.2
          have hm_lt : mseq t < P_modes := Nat.mod_lt _ hP_pos
          have hs_next : sseq (t + 1) = advStepNat c (sseq t) (e t).1.2.2 := by
            dsimp only [sseq]
            rw [hq_next, mul_add_div_alpha P_modes _ _ hm_lt]
          have hm_next : mseq (t + 1) = mseq t := by
            dsimp only [mseq]
            rw [hq_next, mul_add_mod_alpha P_modes _ _ hm_lt]
          exact ⟨hs_next, Or.inr ⟨Nat.pos_of_ne_zero hm0, hg_ok.1, hg_ok.2, hm_next⟩⟩
        · rw [if_neg hg_ok] at ht; simp at ht
    have hs_run : ∀ t, sseq t = (c.toDPA.run (graphOfExec e) t).val := by
      intro t
      induction t with
      | zero => simp [sseq, hq0, DPA.run, DPACode.toDPA]
      | succ t ih =>
        rw [(hstep_all t).1, ih]
        rfl
    have hacc_props : ∀ t,
        (notAdvNBW c I).2.2.2.testBit (qseq t) = true →
          0 < mseq t ∧ (mseq t - 1) % 2 = 1 ∧ c.2.2.getD (sseq t) 0 = mseq t - 1 := by
      intro t ht
      dsimp only [notAdvNBW, notAdvAccMask] at ht
      rw [testBit_listToMask] at ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ⟨ht.2.1.1, ht.2.1.2, ht.2.2⟩
    obtain ⟨t0, _, ht0_acc⟩ := Filter.frequently_atTop.mp hacc 0
    obtain ⟨hm0_pos, hm0_odd, _⟩ := hacc_props t0 ht0_acc
    let p := mseq t0 - 1
    have hp_odd : Odd p := Nat.odd_iff.mpr hm0_odd
    have hstay : ∀ d, mseq (t0 + d) = p + 1 ∧ p ≤ c.2.2.getD (sseq (t0 + d)) 0 := by
      intro d
      induction d with
      | zero =>
        have hm_eq : mseq t0 = p + 1 := by omega
        rcases (hstep_all t0).2 with hz | ⟨_, hle, _, _⟩
        · omega
        · exact ⟨hm_eq, hle⟩
      | succ d ih =>
        rcases (hstep_all (t0 + d)).2 with hz | ⟨_, _, _, hm_eq⟩
        · omega
        · have hm_succ : mseq (t0 + (d + 1)) = p + 1 := by
            rw [show t0 + (d + 1) = t0 + d + 1 by omega, hm_eq, ih.1]
          rcases (hstep_all (t0 + (d + 1))).2 with hz2 | ⟨_, hle2, _, _⟩
          · omega
          · exact ⟨hm_succ, by simpa [hm_succ] using hle2⟩
    refine ⟨p, hp_odd, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hacc ⊢
      intro N
      obtain ⟨t, ht_ge, ht_acc⟩ := hacc (max N t0)
      obtain ⟨_, _, hprio_eq⟩ := hacc_props t ht_acc
      have hmt : mseq t = p + 1 := by
        simpa [show t0 + (t - t0) = t by omega] using (hstay (t - t0)).1
      refine ⟨t, by omega, ?_⟩
      change c.2.2.getD (c.toDPA.run (graphOfExec e) t).val 0 = p
      rw [← hs_run t, hprio_eq, hmt, Nat.add_sub_cancel]
    · rw [Filter.eventually_atTop]
      refine ⟨t0, fun t ht => ?_⟩
      change p ≤ c.2.2.getD (c.toDPA.run (graphOfExec e) t).val 0
      rw [← hs_run t]
      simpa [show t0 + (t - t0) = t by omega] using (hstay (t - t0)).2
  · rintro ⟨p, hp_odd, hfreq, hev⟩
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T, hT⟩ := hev
    rw [Filter.frequently_atTop] at hfreq
    obtain ⟨t_wit, _, h_wit⟩ := hfreq T
    have hp_le : p ≤ maxList c.2.2 := h_wit ▸ hbdd t_wit
    have hp_mod : p % 2 = 1 := Nat.odd_iff.mp hp_odd
    let sseq : ℕ → ℕ := fun t => (c.toDPA.run (graphOfExec e) t).val
    let mseq : ℕ → ℕ := fun t => if t ≤ T then 0 else p + 1
    have hs_lt : ∀ t, sseq t < S_adv := fun t => (c.toDPA.run (graphOfExec e) t).isLt
    have hm_lt : ∀ t, mseq t < P_modes := fun t => by
      dsimp only [mseq, P_modes]; split_ifs <;> omega
    have hq_lt : ∀ t, sseq t * P_modes + mseq t < Q - 1 + 1 := fun t => by
      rw [hQ_succ]
      have hs1 : sseq t + 1 ≤ S_adv := hs_lt t
      calc sseq t * P_modes + mseq t < sseq t * P_modes + P_modes := Nat.add_lt_add_left (hm_lt t) _
        _ = (sseq t + 1) * P_modes := by rw [Nat.succ_mul]
        _ ≤ S_adv * P_modes := Nat.mul_le_mul_right P_modes hs1
    let run : ℕ → Fin (Q - 1 + 1) := fun t => ⟨sseq t * P_modes + mseq t, hq_lt t⟩
    have hdiv_run : ∀ t, (run t).val / P_modes = sseq t := fun t =>
      mul_add_div_alpha P_modes (sseq t) (mseq t) (hm_lt t)
    have hmod_run : ∀ t, (run t).val % P_modes = mseq t := fun t =>
      mul_add_mod_alpha P_modes (sseq t) (mseq t) (hm_lt t)
    refine ⟨run, ?_, ?_, ?_⟩
    · dsimp only [notAdvNBW]
      rw [testBit_listToMask]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨(run 0).isLt.trans_eq hQ_succ, by simp [run, sseq, mseq, DPA.run, DPACode.toDPA]⟩
    · intro t
      dsimp only
      rw [notAdvNBW_trans_getD c I (run t).val (roundLetterEquiv I (e t)).val
        ((run t).isLt.trans_eq hQ_succ) (roundLetterEquiv I (e t)).isLt]
      have hrf := decodeRoundFields_spec I (roundLetterEquiv I (e t))
      rw [Equiv.symm_apply_apply] at hrf
      have hg_eq : (decodeRoundFields I (roundLetterEquiv I (e t)).val).2.2.1 = (e t).1.2.2 := by
        rw [hrf]
      have hs_step : advStepNat c (sseq t) (e t).1.2.2 = sseq (t + 1) := rfl
      rw [hg_eq, hdiv_run t, hmod_run t, hs_step]
      by_cases htT : t ≤ T
      · have hm_t : mseq t = 0 := if_pos htT
        rw [hm_t, if_pos rfl, testBit_listToMask]
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨(run (t + 1)).isLt.trans_eq hQ_succ, hdiv_run (t + 1), ?_⟩
        rw [hmod_run (t + 1)]
        dsimp only [mseq]
        split_ifs
        · exact Or.inl rfl
        · exact Or.inr ⟨Nat.succ_pos p, by simpa using hp_mod⟩
      · have hm_t : mseq t = p + 1 := if_neg htT
        have hm_ne : mseq t ≠ 0 := by rw [hm_t]; exact Nat.succ_ne_zero p
        have hm_t1 : mseq (t + 1) = p + 1 := if_neg (by omega)
        have hguard : mseq t - 1 ≤ c.2.2.getD (sseq t) 0 ∧ (mseq t - 1) % 2 = 1 := by
          rw [hm_t, Nat.add_sub_cancel]
          exact ⟨hT t (by omega), hp_mod⟩
        rw [if_neg hm_ne, if_pos hguard, testBit_listToMask]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨(run (t + 1)).isLt.trans_eq hQ_succ, ?_⟩
        dsimp only [run]
        rw [hm_t1, hm_t]
    · rw [Filter.frequently_atTop]
      intro N
      obtain ⟨t, ht_ge, ht_p⟩ := hfreq (max N (T + 1))
      refine ⟨t, by omega, ?_⟩
      dsimp only [notAdvNBW, notAdvAccMask]
      rw [testBit_listToMask]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have hmt : mseq t = p + 1 := if_neg (by omega)
      refine ⟨(run t).isLt.trans_eq hQ_succ, ⟨?_, ?_⟩, ?_⟩
      · rw [hmod_run t, hmt]; exact Nat.succ_pos p
      · rw [hmod_run t, hmt, Nat.add_sub_cancel]; exact hp_mod
      · rw [hdiv_run t, hmod_run t, hmt, Nat.add_sub_cancel]; exact ht_p

def unionTransEntry (αSize : ℕ) (b1 b2 : NBWCode) (idx : ℕ) : ℕ :=
  let N1 := b1.1 + 1
  let Q := N1 + (b2.1 + 1)
  let αLen := αSize + 1
  let q := idx / αLen
  let a := idx % αLen
  if q < N1 then
    let m1 := b1.2.2.1.getD (q * αLen + a) 0
    listToMask Q (fun q' => decide (q' < N1) && m1.testBit q')
  else
    let m2 := b2.2.2.1.getD ((q - N1) * αLen + a) 0
    listToMask Q (fun q' => decide (N1 ≤ q') && m2.testBit (q' - N1))

/-- Disjoint union of two `NBWCode`s over `Fin (αSize + 1)`. -/
def unionNBW (αSize : ℕ) (b1 b2 : NBWCode) : NBWCode :=
  let N1 := b1.1 + 1
  let Q := N1 + (b2.1 + 1)
  let αLen := αSize + 1
  let initMask := listToMask Q (fun q =>
    if q < N1 then b1.2.1.testBit q else b2.2.1.testBit (q - N1))
  let accMask := listToMask Q (fun q =>
    if q < N1 then b1.2.2.2.testBit q else b2.2.2.2.testBit (q - N1))
  (b1.1 + b2.1 + 1, initMask, (List.range (Q * αLen)).map (unionTransEntry αSize b1 b2), accMask)

private def unionLeftMask (packed : ℕ) : ℕ :=
  let Q := packed.unpair.1
  let N1 := packed.unpair.2.unpair.1
  let m1 := packed.unpair.2.unpair.2
  listToMask Q (fun q' => decide (q' < N1) && m1.testBit q')

private lemma primrec_unionLeftMask : Primrec unionLeftMask := by
  have hQ : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hN1 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hm1 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hPred := primrec_bool_and.comp (Primrec.nat_lt.comp Primrec.snd hN1).decide
    (primrec_testBit.comp hm1 Primrec.snd)
  exact primrec_mask_clean
    (fun p : ℕ => p.unpair.1)
    (fun (p : ℕ) q' => decide (q' < p.unpair.2.unpair.1) && p.unpair.2.unpair.2.testBit q')
    hQ (fun _ => rfl) hPred (fun _ _ => rfl)

private def unionRightMask (packed : ℕ) : ℕ :=
  let Q := packed.unpair.1
  let N1 := packed.unpair.2.unpair.1
  let m2 := packed.unpair.2.unpair.2
  listToMask Q (fun q' => decide (N1 ≤ q') && m2.testBit (q' - N1))

private lemma primrec_unionRightMask : Primrec unionRightMask := by
  have hQ : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hN1 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hm2 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hPred := primrec_bool_and.comp (Primrec.nat_le.comp hN1 Primrec.snd).decide
    (primrec_testBit.comp hm2 (Primrec.nat_sub.comp Primrec.snd hN1))
  exact primrec_mask_clean
    (fun p : ℕ => p.unpair.1)
    (fun (p : ℕ) q' => decide (p.unpair.2.unpair.1 ≤ q') && p.unpair.2.unpair.2.testBit (q' - p.unpair.2.unpair.1))
    hQ (fun _ => rfl) hPred (fun _ _ => rfl)

private def unionCombineMask (packed : ℕ) : ℕ :=
  let Q := packed.unpair.1
  let N1 := packed.unpair.2.unpair.1
  let mask1 := packed.unpair.2.unpair.2.unpair.1
  let mask2 := packed.unpair.2.unpair.2.unpair.2
  listToMask Q (fun q => if q < N1 then mask1.testBit q else mask2.testBit (q - N1))

private lemma primrec_unionCombineMask : Primrec unionCombineMask := by
  have hQ : Primrec (fun p : ℕ => p.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hr1 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hN1 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hr1)
  have hr2 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hr1)
  have hm1 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hr2)
  have hm2 : Primrec (fun q : ℕ × ℕ => q.1.unpair.2.unpair.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hr2)
  have hPred := Primrec.ite (Primrec.nat_lt.comp Primrec.snd hN1)
    (primrec_testBit.comp hm1 Primrec.snd)
    (primrec_testBit.comp hm2 (Primrec.nat_sub.comp Primrec.snd hN1))
  exact primrec_mask_clean
    (fun p : ℕ => p.unpair.1)
    (fun (p : ℕ) q =>
      if q < p.unpair.2.unpair.1 then p.unpair.2.unpair.2.unpair.1.testBit q
      else p.unpair.2.unpair.2.unpair.2.testBit (q - p.unpair.2.unpair.1))
    hQ (fun _ => rfl) hPred (fun _ _ => rfl)

private lemma primrec_unionTransEntry :
    Primrec (fun x : (ℕ × NBWCode × NBWCode) × ℕ =>
      unionTransEntry x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  let Ctx := (ℕ × NBWCode × NBWCode) × ℕ
  have hαLen : Primrec (fun x : Ctx => x.1.1 + 1) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)
  have hb1 : Primrec (fun x : Ctx => x.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb2 : Primrec (fun x : Ctx => x.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hN1 := Primrec.nat_add.comp (Primrec.fst.comp hb1) (Primrec.const 1)
  have hN2 := Primrec.nat_add.comp (Primrec.fst.comp hb2) (Primrec.const 1)
  have hQ := Primrec.nat_add.comp hN1 hN2
  have hq := Primrec.nat_div.comp Primrec.snd hαLen
  have ha := Primrec.nat_mod.comp Primrec.snd hαLen
  have hm1 := primrec_list_getD.comp
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb1))).pair
      ((Primrec.nat_add.comp (Primrec.nat_mul.comp hq hαLen) ha).pair (Primrec.const 0)))
  have hm2 := primrec_list_getD.comp
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hb2))).pair
      ((Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.nat_sub.comp hq hN1) hαLen) ha).pair (Primrec.const 0)))
  have hLeft := primrec_unionLeftMask.comp
    (primrec_nat_pair.comp hQ (primrec_nat_pair.comp hN1 hm1))
  have hRight := primrec_unionRightMask.comp
    (primrec_nat_pair.comp hQ (primrec_nat_pair.comp hN1 hm2))
  exact (Primrec.ite (Primrec.nat_lt.comp hq hN1) hLeft hRight).of_eq fun _ => by
    dsimp only [unionTransEntry, unionLeftMask, unionRightMask]
    simp only [Nat.unpair_pair]

lemma primrec_unionNBW : Primrec (fun p : ℕ × NBWCode × NBWCode =>
    unionNBW p.1 p.2.1 p.2.2) := by
  let Inp := ℕ × NBWCode × NBWCode
  have hαLen : Primrec (fun p : Inp => p.1 + 1) :=
    Primrec.nat_add.comp Primrec.fst (Primrec.const 1)
  have hb1 : Primrec (fun p : Inp => p.2.1) := Primrec.fst.comp Primrec.snd
  have hb2 : Primrec (fun p : Inp => p.2.2) := Primrec.snd.comp Primrec.snd
  have hN1 : Primrec (fun p : Inp => p.2.1.1 + 1) :=
    Primrec.nat_add.comp (Primrec.fst.comp hb1) (Primrec.const 1)
  have hN2 : Primrec (fun p : Inp => p.2.2.1 + 1) :=
    Primrec.nat_add.comp (Primrec.fst.comp hb2) (Primrec.const 1)
  have hQ : Primrec (fun p : Inp => (p.2.1.1 + 1) + (p.2.2.1 + 1)) := Primrec.nat_add.comp hN1 hN2
  have hInit := primrec_unionCombineMask.comp
    (primrec_nat_pair.comp hQ (primrec_nat_pair.comp hN1
      (primrec_nat_pair.comp (Primrec.fst.comp (Primrec.snd.comp hb1))
        (Primrec.fst.comp (Primrec.snd.comp hb2)))))
  have hAcc := primrec_unionCombineMask.comp
    (primrec_nat_pair.comp hQ (primrec_nat_pair.comp hN1
      (primrec_nat_pair.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb1)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hb2))))))
  have hTrans := primrec_range_map
    (fun p : Inp => ((p.2.1.1 + 1) + (p.2.2.1 + 1)) * (p.1 + 1))
    (fun p idx => unionTransEntry p.1 p.2.1 p.2.2 idx)
    (Primrec.nat_mul.comp hQ hαLen) (fun _ => rfl)
    primrec_unionTransEntry (fun _ _ => rfl)
  have hn := Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.fst.comp hb1) (Primrec.fst.comp hb2)) (Primrec.const 1)
  exact (hn.pair (hInit.pair (hTrans.pair hAcc))).of_eq fun _ => by
    dsimp only [unionNBW, unionCombineMask]
    simp only [Nat.unpair_pair]

private lemma unionNBW_trans_getD (αSize : ℕ) (b1 b2 : NBWCode) (q a : ℕ)
    (hq : q < (b1.1 + 1) + (b2.1 + 1)) (ha : a < αSize + 1) :
    let N1 := b1.1 + 1
    let Q := N1 + (b2.1 + 1)
    let αLen := αSize + 1
    (unionNBW αSize b1 b2).2.2.1.getD (q * αLen + a) 0 =
      if q < N1 then
        listToMask Q (fun q' => decide (q' < N1) && (b1.2.2.1.getD (q * αLen + a) 0).testBit q')
      else
        listToMask Q (fun q' =>
          decide (N1 ≤ q') && (b2.2.2.1.getD ((q - N1) * αLen + a) 0).testBit (q' - N1)) := by
  dsimp only [unionNBW]
  rw [getD_map_range_mul _ _ _ q a hq ha]
  unfold unionTransEntry
  dsimp only
  rw [mul_add_div_alpha _ q a ha, mul_add_mod_alpha _ q a ha]

lemma unionNBW_accepts_iff (αSize : ℕ) (b1 b2 : NBWCode) (w : ℕ → Fin (αSize + 1)) :
    NBWAccepts αSize (unionNBW αSize b1 b2) w ↔
      NBWAccepts αSize b1 w ∨ NBWAccepts αSize b2 w := by
  let N1 := b1.1 + 1
  let N2 := b2.1 + 1
  let Q := N1 + N2
  let αLen := αSize + 1
  have hQ_eq : b1.1 + b2.1 + 1 + 1 = Q := by omega
  constructor
  · rintro ⟨run, hinit, htrans, hacc⟩
    have hstep_decode : ∀ t,
        if (run t).val < N1 then
          (run (t + 1)).val < N1 ∧
            (b1.2.2.1.getD ((run t).val * αLen + (w t).val) 0).testBit (run (t + 1)).val = true
        else
          N1 ≤ (run (t + 1)).val ∧
            (b2.2.2.1.getD (((run t).val - N1) * αLen + (w t).val) 0).testBit ((run (t + 1)).val - N1) = true := by
      intro t
      have ht := htrans t
      rw [unionNBW_trans_getD αSize b1 b2 (run t).val (w t).val
        ((run t).isLt.trans_eq hQ_eq) (w t).isLt] at ht
      by_cases hlt : (run t).val < N1
      · rw [if_pos hlt] at ht ⊢
        rw [testBit_listToMask] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨ht.2.1, ht.2.2⟩
      · rw [if_neg hlt] at ht ⊢
        rw [testBit_listToMask] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨ht.2.1, ht.2.2⟩
    by_cases h0 : (run 0).val < N1
    · have hall_lt : ∀ t, (run t).val < N1 := by
        intro t; induction t with
        | zero => exact h0
        | succ t ih =>
          have hs := hstep_decode t
          rw [if_pos ih] at hs; exact hs.1
      refine Or.inl ⟨fun t => ⟨(run t).val, hall_lt t⟩, ?_, ?_, ?_⟩
      · dsimp only [unionNBW] at hinit
        rw [testBit_listToMask, if_pos h0] at hinit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hinit
        exact hinit.2
      · intro t
        have hs := hstep_decode t
        rw [if_pos (hall_lt t)] at hs
        exact hs.2
      · refine hacc.mono fun t ht => ?_
        dsimp only [unionNBW] at ht
        rw [testBit_listToMask, if_pos (hall_lt t)] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ht.2
    · have hall_ge : ∀ t, N1 ≤ (run t).val := by
        intro t; induction t with
        | zero => omega
        | succ t ih =>
          have hs := hstep_decode t
          rw [if_neg (by omega)] at hs; exact hs.1
      have hsub_lt : ∀ t, (run t).val - N1 < N2 := fun t => by
        have := (run t).isLt.trans_eq hQ_eq; omega
      refine Or.inr ⟨fun t => ⟨(run t).val - N1, hsub_lt t⟩, ?_, ?_, ?_⟩
      · dsimp only [unionNBW] at hinit
        rw [testBit_listToMask, if_neg h0] at hinit
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hinit
        exact hinit.2
      · intro t
        have hs := hstep_decode t
        rw [if_neg (by have := hall_ge t; omega)] at hs
        exact hs.2
      · refine hacc.mono fun t ht => ?_
        dsimp only [unionNBW] at ht
        rw [testBit_listToMask, if_neg (by have := hall_ge t; omega)] at ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ht.2
  · rintro (⟨r1, hi1, ht1, ha1⟩ | ⟨r2, hi2, ht2, ha2⟩)
    · refine ⟨fun t => ⟨(r1 t).val, by dsimp only [unionNBW]; have := (r1 t).isLt; omega⟩, ?_, ?_, ?_⟩
      · dsimp only [unionNBW]
        rw [testBit_listToMask, if_pos (r1 0).isLt]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by have := (r1 0).isLt; omega, hi1⟩
      · intro t
        dsimp only
        rw [unionNBW_trans_getD αSize b1 b2 (r1 t).val (w t).val
          (by have := (r1 t).isLt; omega) (w t).isLt]
        rw [if_pos (r1 t).isLt, testBit_listToMask]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by have := (r1 (t + 1)).isLt; omega, (r1 (t + 1)).isLt, ht1 t⟩
      · refine ha1.mono fun t ht => ?_
        dsimp only [unionNBW]
        rw [testBit_listToMask, if_pos (r1 t).isLt]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by have := (r1 t).isLt; omega, ht⟩
    · refine ⟨fun t => ⟨N1 + (r2 t).val, by dsimp only [unionNBW, N1]; have := (r2 t).isLt; omega⟩, ?_, ?_, ?_⟩
      · dsimp only [unionNBW]
        rw [testBit_listToMask, if_neg (by omega), Nat.add_sub_cancel_left]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by have := (r2 0).isLt; omega, hi2⟩
      · intro t
        dsimp only
        rw [unionNBW_trans_getD αSize b1 b2 (N1 + (r2 t).val) (w t).val
          (by have := (r2 t).isLt; omega) (w t).isLt]
        rw [if_neg (by omega), Nat.add_sub_cancel_left, testBit_listToMask]
        simp only [N1, Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel_left]
        exact ⟨by have := (r2 (t + 1)).isLt; omega, Nat.le_add_right _ _, ht2 t⟩
      · refine ha2.mono fun t ht => ?_
        dsimp only [unionNBW]
        rw [testBit_listToMask, if_neg (by omega), Nat.add_sub_cancel_left]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by have := (r2 t).isLt; omega, ht⟩

/-! ### Section 5: Executable Adversary Liveness (`liveStateBool` and `Pref c.lang`) -/

def runFrom {S α : Type} (M : DPA S α) (s : S) (w : ℕ → α) : ℕ → S
  | 0 => s
  | n + 1 => M.step (runFrom M s w n) (w n)

lemma runFrom_shift {S α : Type} (M : DPA S α) (s : S) (w : ℕ → α) (a b : ℕ) :
    runFrom M s w (a + b) = runFrom M (runFrom M s w a) (fun n => w (a + n)) b := by
  induction b with
  | zero => simp [runFrom]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega]
    simp [runFrom, ih]

private lemma pre_succ {α : Type} (w : ℕ → α) (n : ℕ) :
    pre w (n + 1) = pre w n ++ [w n] := by
  apply List.ext_getElem
  · simp only [pre, List.length_ofFn, List.length_append, List.length_singleton]
  · intro i h1 h2
    have hlen : (pre w n).length = n := by simp only [pre, List.length_ofFn]
    simp only [pre, List.length_ofFn] at h1
    by_cases hi : i < n
    · rw [List.getElem_append_left (by rw [hlen]; exact hi)]
      simp only [pre, List.getElem_ofFn]
    · have hieq : i = n := by omega
      subst hieq
      rw [List.getElem_append_right (by rw [hlen])]
      simp only [hlen, Nat.sub_self, List.getElem_singleton]
      simp only [pre, List.getElem_ofFn]

lemma runFrom_eq_foldl_pre {S α : Type} (M : DPA S α) (s : S) (w : ℕ → α) (n : ℕ) :
    runFrom M s w n = (pre w n).foldl M.step s := by
  induction n with
  | zero => simp [runFrom, pre]
  | succ n ih =>
    rw [pre_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
    rfl

lemma run_eq_runFrom {S α : Type} (M : DPA S α) (w : ℕ → α) (n : ℕ) :
    M.run w n = runFrom M M.init w n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [DPA.run, runFrom, ih]

lemma pref_lang_iff_acceptsFrom {S α : Type} (M : DPA S α) (h : List α) :
    h ∈ Pref M.lang ↔
      ∃ suffix : ℕ → α, ParityCond (fun t => M.prio (runFrom M (h.foldl M.step M.init) suffix t)) := by
  constructor
  · rintro ⟨w, hw, hpre⟩
    refine ⟨fun t => w (h.length + t), ?_⟩
    have hq : runFrom M M.init w h.length = h.foldl M.step M.init := by
      rw [runFrom_eq_foldl_pre, hpre]
    have hshift := (parityCond_shift (fun n => M.prio (M.run w n)) h.length).mp hw
    refine (show ParityCond (fun n => M.prio (M.run w (h.length + n))) ↔ _ from ?_).mp hshift
    have heq : (fun n => M.prio (M.run w (h.length + n))) =
        (fun n => M.prio (runFrom M (h.foldl M.step M.init) (fun t => w (h.length + t)) n)) := by
      funext n
      rw [run_eq_runFrom, runFrom_shift, hq]
    rw [heq]
  · rintro ⟨suffix, hpar⟩
    let w := append h suffix
    have hpre : pre w h.length = h := by
      apply List.ext_getElem
      · simp [pre]
      · intro i hi1 hi2
        simp only [pre, List.getElem_ofFn, w, append]
        rw [dif_pos hi2]
    have htail : ∀ t, w (h.length + t) = suffix t := by
      intro t
      simp only [w, append]
      rw [dif_neg (by omega), Nat.add_sub_cancel_left]
    refine ⟨w, ?_, hpre⟩
    change ParityCond (fun n => M.prio (M.run w n))
    rw [parityCond_shift _ h.length]
    have hq : runFrom M M.init w h.length = h.foldl M.step M.init := by
      rw [runFrom_eq_foldl_pre, hpre]
    have heq : (fun n => M.prio (M.run w (h.length + n))) =
        (fun n => M.prio (runFrom M (h.foldl M.step M.init) suffix n)) := by
      funext n
      rw [run_eq_runFrom, runFrom_shift, hq]
      have hfn : (fun k => w (h.length + k)) = suffix := funext htail
      rw [hfn]
    rwa [heq]

private lemma take_append_split {α : Type} (l1 l2 : List α) :
    ∀ k : ℕ, (l1 ++ l2).take k = l1.take k ++ l2.take (k - l1.length)
  | 0 => by simp
  | k + 1 => by
    cases l1 with
    | nil => simp
    | cons hd tl => simp [Nat.succ_sub_succ_eq_sub, take_append_split tl l2 k]

private lemma take_append_take_drop {α : Type} (l : List α) :
    ∀ (b m : ℕ), l.take b ++ (l.drop b).take m = l.take (b + m)
  | 0, m => by simp
  | b + 1, m => by
    cases l with
    | nil => simp
    | cons hd tl => rw [Nat.succ_add]; simp [take_append_take_drop tl b m]

private lemma take_succ_eq {α : Type} :
    ∀ (v : List α) (k : ℕ) (hk : k < v.length), v.take (k + 1) = v.take k ++ [v[k]]
  | [], _, hk => by simp at hk
  | a :: tl, 0, _ => by simp
  | a :: tl, k + 1, hk => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
    rw [take_succ_eq tl k hk]

private lemma shorten_path_subset {N : ℕ} {α : Type} (step : Fin N → α → Fin N)
    (x : Fin N) (w : List α) :
    ∃ w' : List α,
      w'.length < N ∧
      w'.foldl step x = w.foldl step x ∧
      ∀ k ≤ w'.length, ∃ j ≤ w.length, (w'.take k).foldl step x = (w.take j).foldl step x := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ len ih =>
    subst hn
    by_cases hlt : w.length < N
    · exact ⟨w, hlt, rfl, fun k hk => ⟨k, hk, rfl⟩⟩
    · have hcard : Fintype.card (Fin N) < Fintype.card (Fin (w.length + 1)) := by
        simp; omega
      let f : Fin (w.length + 1) → Fin N := fun i => (w.take i.val).foldl step x
      obtain ⟨i, j, hij_ne, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
      have hij_ord : (i.val < j.val ∧ f i = f j) ∨ (j.val < i.val ∧ f j = f i) := by
        rcases lt_trichotomy i.val j.val with h1 | h2 | h3
        · exact Or.inl ⟨h1, hfij⟩
        · exact False.elim (hij_ne (Fin.ext h2))
        · exact Or.inr ⟨h3, hfij.symm⟩
      have hex_pair : ∃ a b : ℕ, a < b ∧ b ≤ w.length ∧
          (w.take a).foldl step x = (w.take b).foldl step x := by
        rcases hij_ord with ⟨h1, he⟩ | ⟨h1, he⟩
        · exact ⟨i.val, j.val, h1, Nat.lt_succ_iff.mp j.isLt, he⟩
        · exact ⟨j.val, i.val, h1, Nat.lt_succ_iff.mp i.isLt, he⟩
      obtain ⟨a, b, hab, hbw, heq_ab⟩ := hex_pair
      let w1 := w.take a ++ w.drop b
      have hw1_len : w1.length < w.length := by
        simp only [w1, List.length_append, List.length_take, List.length_drop]
        omega
      have hw1_end : w1.foldl step x = w.foldl step x := by
        dsimp only [w1]
        rw [List.foldl_append, heq_ab, ← List.foldl_append, List.take_append_drop]
      have hw1_vis : ∀ k ≤ w1.length, ∃ j ≤ w.length,
          (w1.take k).foldl step x = (w.take j).foldl step x := by
        intro k hk
        have hta_len : (w.take a).length = a := by simp [Nat.min_eq_left (by omega : a ≤ w.length)]
        by_cases hka : k ≤ a
        · refine ⟨k, by omega, ?_⟩
          dsimp only [w1]
          rw [take_append_split, hta_len, show k - a = 0 by omega,
              List.take_zero, List.append_nil, List.take_take, Nat.min_eq_left hka]
        · refine ⟨b + (k - a), by simp [w1, hta_len] at hk; omega, ?_⟩
          dsimp only [w1]
          rw [take_append_split, hta_len,
              List.take_of_length_le (by rw [hta_len]; omega),
              List.foldl_append, heq_ab, ← List.foldl_append,
              take_append_take_drop]
      obtain ⟨w', hw'_lt, hw'_end, hw'_vis⟩ := ih w1.length hw1_len w1 rfl
      refine ⟨w', hw'_lt, hw'_end.trans hw1_end, fun k hk => ?_⟩
      obtain ⟨k1, hk1, he1⟩ := hw'_vis k hk
      obtain ⟨j, hj, he2⟩ := hw1_vis k1 hk1
      exact ⟨j, hj, he1.trans he2⟩

def minList : List ℕ → ℕ
  | [] => 0
  | x :: xs => xs.foldr min x

lemma primrec_minList : Primrec minList := by
  have hTail : Primrec₂ (fun (x : ℕ) (xs : List ℕ) => xs.foldr min x) :=
    Primrec.list_foldr Primrec.snd Primrec.fst
      (primrec_nat_min.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_casesOn Primrec.id (Primrec.const 0)
    (hTail.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
    fun xs => by cases xs <;> rfl

private lemma foldr_min_props (x : ℕ) (bs : List ℕ) :
    (bs.foldr min x = x ∨ bs.foldr min x ∈ bs) ∧
      bs.foldr min x ≤ x ∧ ∀ y ∈ bs, bs.foldr min x ≤ y := by
  induction bs with
  | nil => exact ⟨Or.inl rfl, le_rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons b tl ih =>
    simp only [List.foldr_cons]
    refine ⟨?_, (min_le_right b _).trans ih.2.1, ?_⟩
    · rcases min_choice b (tl.foldr min x) with hm | hm
      · exact Or.inr (List.mem_cons.mpr (Or.inl hm))
      · rcases ih.1 with hx | hmem
        · exact Or.inl (hm.trans hx)
        · rw [hm]
          exact Or.inr (List.mem_cons.mpr (Or.inr hmem))
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hytl
      · exact min_le_left _ _
      · exact (min_le_right b _).trans (ih.2.2 y hytl)

lemma minList_mem_and_le (xs : List ℕ) (hne : xs ≠ []) :
    minList xs ∈ xs ∧ ∀ y ∈ xs, minList xs ≤ y := by
  rcases xs with _ | ⟨x, tl⟩
  · exact False.elim (hne rfl)
  · simp only [minList]
    obtain ⟨hm, hlex, hletl⟩ := foldr_min_props x tl
    refine ⟨?_, ?_⟩
    · rcases hm with hx | htl
      · exact List.mem_cons.mpr (Or.inl hx)
      · exact List.mem_cons.mpr (Or.inr htl)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hytl
      · exact hlex
      · exact hletl y hytl

def wordsOf {α : Type} (choices : List α) (n : ℕ) : List (List α) :=
  (List.range n).foldl
    (fun acc _ => acc.flatMap (fun u => choices.map (fun a => a :: u)))
    [[]]

lemma primrec_wordsOf {α : Type} [Primcodable α] : Primrec₂ (wordsOf (α := α)) :=
  Primrec.list_foldl
    (Primrec.list_range.comp Primrec.snd)
    (Primrec.const [[]])
    (Primrec.list_flatMap (Primrec.fst.comp Primrec.snd)
      (Primrec.list_map
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂

lemma mem_wordsOf_iff {α : Type} (choices : List α) :
    ∀ (n : ℕ) (w : List α),
      w ∈ wordsOf choices n ↔ w.length = n ∧ ∀ a ∈ w, a ∈ choices
  | 0, w => by
    cases w <;> simp [wordsOf]
  | n + 1, w => by
    rw [wordsOf, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← wordsOf]
    simp only [List.mem_flatMap, List.mem_map]
    rcases w with _ | ⟨b, tl⟩
    · simp
    · constructor
      · rintro ⟨u, hu, a, ha, heq⟩
        cases heq
        obtain ⟨hlen, hall⟩ := (mem_wordsOf_iff choices n tl).mp hu
        refine ⟨by simp [hlen], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxtl
        · exact ha
        · exact hall x hxtl
      · rintro ⟨hlen, hall⟩
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
        refine ⟨tl, (mem_wordsOf_iff choices n tl).mpr ⟨hlen, fun x hx =>
          hall x (List.mem_cons.mpr (Or.inr hx))⟩, b,
          hall b (List.mem_cons.mpr (Or.inl rfl)), rfl⟩

def allGraphs : List CommGraph := [CommGraph.oneToTwo, CommGraph.both, CommGraph.twoToOne]

lemma mem_allGraphs (g : CommGraph) : g ∈ allGraphs := by
  cases g <;> simp [allGraphs]

def advFoldNat (c : DPACode) (q : ℕ) (w : List CommGraph) : ℕ :=
  w.foldl (advStepNat c) q

lemma primrec_advFoldNat : Primrec (fun p : DPACode × ℕ × List CommGraph =>
    advFoldNat p.1 p.2.1 p.2.2) :=
  Primrec.list_foldl (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
    (primrec_advStepNat.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

def advFoldPrefix (c : DPACode) (q : ℕ) (v : List CommGraph) (k : ℕ) : ℕ :=
  (List.range k).foldl (fun q' i => advStepNat c q' (v.getD i CommGraph.oneToTwo)) q

lemma advFoldPrefix_eq_take (c : DPACode) (q : ℕ) (v : List CommGraph) (k : ℕ)
    (hk : k ≤ v.length) :
    advFoldPrefix c q v k = advFoldNat c q (v.take k) := by
  induction k with
  | zero => simp [advFoldPrefix, advFoldNat]
  | succ k ih =>
    have hk_lt : k < v.length := by omega
    have htake : v.take (k + 1) = v.take k ++ [v[k]] := take_succ_eq v k hk_lt
    simp only [advFoldPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [← advFoldPrefix, ih (by omega), htake, getD_eq_getElem v CommGraph.oneToTwo k hk_lt]
    simp only [advFoldNat, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma primrec_advFoldPrefix : Primrec (fun p : DPACode × ℕ × List CommGraph × ℕ =>
    advFoldPrefix p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Primrec.list_foldl (Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.fst.comp Primrec.snd)
    (primrec_advStepNat.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair
          (primrec_list_getD.comp
            ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
              ((Primrec.snd.comp Primrec.snd).pair (Primrec.const CommGraph.oneToTwo))))))).to₂

def cycleMinPrio (c : DPACode) (q : ℕ) (v : List CommGraph) : ℕ :=
  minList ((List.range v.length).map fun k => c.2.2.getD (advFoldPrefix c q v k) 0)

lemma primrec_cycleMinPrio : Primrec (fun p : DPACode × ℕ × List CommGraph =>
    cycleMinPrio p.1 p.2.1 p.2.2) :=
  primrec_minList.comp
    (Primrec.list_map
      (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)))
      (primrec_list_getD.comp
        ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          ((primrec_advFoldPrefix.comp
            ((Primrec.fst.comp Primrec.fst).pair
              ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
                ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)))).pair
            (Primrec.const 0)))).to₂)

/-- Executable liveness check: `s` reaches a non-empty cycle of length `≤ c.1 + 1` with even
minimum priority along stems of length `≤ c.1 + 1`. -/
def liveStateBool (c : DPACode) (s : ℕ) : Bool :=
  let N := c.1 + 1
  (List.range (N + 1)).any fun k1 =>
    (wordsOf allGraphs k1).any fun u =>
      let q := advFoldNat c s u
      (List.range N).any fun k2 =>
        (wordsOf allGraphs (k2 + 1)).any fun v =>
          decide (advFoldNat c q v = q) && decide (cycleMinPrio c q v % 2 = 0)

private def hasEvenCycleLen (cq : DPACode × ℕ) (k2 : ℕ) : Bool :=
  (wordsOf allGraphs (k2 + 1)).any fun v =>
    decide (advFoldNat cq.1 cq.2 v = cq.2) && decide (cycleMinPrio cq.1 cq.2 v % 2 = 0)

private lemma primrec_hasEvenCycleLen : Primrec₂ hasEvenCycleLen := by
  let X := (DPACode × ℕ) × ℕ
  have hL : Primrec (fun x : X => wordsOf allGraphs (x.2 + 1)) :=
    primrec_wordsOf.comp (Primrec.const allGraphs)
      (Primrec.nat_add.comp (Primrec.snd : Primrec fun x : X => x.2) (Primrec.const 1))
  have hc : Primrec (fun p : X × List CommGraph => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun p : X × List CommGraph => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hv : Primrec (fun p : X × List CommGraph => p.2) := Primrec.snd
  have hend := primrec_advFoldNat.comp (hc.pair (hq.pair hv))
  have hmin := primrec_cycleMinPrio.comp (hc.pair (hq.pair hv))
  have hP := primrec_bool_and.comp
    (Primrec.eq.comp hend hq).decide
    (Primrec.eq.comp (Primrec.nat_mod.comp hmin (Primrec.const 2)) (Primrec.const 0)).decide
  exact primrec_any_clean
    (fun x : X => wordsOf allGraphs (x.2 + 1))
    (fun (x : X) v =>
      decide (advFoldNat x.1.1 x.1.2 v = x.1.2) && decide (cycleMinPrio x.1.1 x.1.2 v % 2 = 0))
    hL (fun _ => rfl) hP (fun _ _ => rfl)

private def hasEvenCycleAt (cq : DPACode × ℕ) : Bool :=
  (List.range (cq.1.1 + 1)).any (hasEvenCycleLen cq)

private lemma primrec_hasEvenCycleAt : Primrec hasEvenCycleAt := by
  have hc1 : Primrec (fun cq : DPACode × ℕ => cq.1.1) := Primrec.fst.comp Primrec.fst
  have hL := Primrec.list_range.comp (Primrec.nat_add.comp hc1 (Primrec.const 1))
  exact primrec_any_clean
    (fun cq : DPACode × ℕ => List.range (cq.1.1 + 1))
    hasEvenCycleLen
    hL (fun _ => rfl) primrec_hasEvenCycleLen (fun _ _ => rfl)

private def reachesEvenCycleLen (cs : DPACode × ℕ) (k1 : ℕ) : Bool :=
  (wordsOf allGraphs k1).any fun u => hasEvenCycleAt (cs.1, advFoldNat cs.1 cs.2 u)

private lemma primrec_reachesEvenCycleLen : Primrec₂ reachesEvenCycleLen := by
  let X := (DPACode × ℕ) × ℕ
  have hL : Primrec (fun x : X => wordsOf allGraphs x.2) :=
    primrec_wordsOf.comp (Primrec.const allGraphs) (Primrec.snd : Primrec fun x : X => x.2)
  have hc : Primrec (fun p : X × List CommGraph => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hs : Primrec (fun p : X × List CommGraph => p.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hu : Primrec (fun p : X × List CommGraph => p.2) := Primrec.snd
  have hq := primrec_advFoldNat.comp (hc.pair (hs.pair hu))
  have hP := primrec_hasEvenCycleAt.comp (hc.pair hq)
  exact primrec_any_clean
    (fun x : X => wordsOf allGraphs x.2)
    (fun (x : X) u => hasEvenCycleAt (x.1.1, advFoldNat x.1.1 x.1.2 u))
    hL (fun _ => rfl) hP (fun _ _ => rfl)

lemma primrec_liveStateBool : Primrec₂ liveStateBool := by
  have hc1 : Primrec (fun cs : DPACode × ℕ => cs.1.1) := Primrec.fst.comp Primrec.fst
  have hL := Primrec.list_range.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp hc1 (Primrec.const 1)) (Primrec.const 1))
  exact (primrec_any_clean
    (fun cs : DPACode × ℕ => List.range ((cs.1.1 + 1) + 1))
    reachesEvenCycleLen
    hL (fun _ => rfl) primrec_reachesEvenCycleLen (fun _ _ => rfl)).of_eq fun cs => by
      unfold liveStateBool reachesEvenCycleLen hasEvenCycleAt hasEvenCycleLen
      rfl

private lemma advFoldNat_eq_foldl (c : DPACode) (s : Fin (c.1 + 1)) (w : List CommGraph) :
    advFoldNat c s.val w = (w.foldl c.toDPA.step s).val := by
  induction w generalizing s with
  | nil => rfl
  | cons g tl ih =>
    simp only [advFoldNat, List.foldl_cons]
    exact ih (c.toDPA.step s g)

lemma liveStateBool_iff (c : DPACode) (s : Fin (c.1 + 1)) :
    liveStateBool c s.val = true ↔
      ∃ suffix : ℕ → CommGraph, ParityCond (fun t => c.toDPA.prio (runFrom c.toDPA s suffix t)) := by
  let N := c.1 + 1
  constructor
  · intro hlive
    unfold liveStateBool at hlive
    simp only [List.any_eq_true, List.mem_range, mem_wordsOf_iff, Bool.and_eq_true,
      decide_eq_true_eq] at hlive
    obtain ⟨k1, _, u, ⟨_, _⟩, k2, _, v, ⟨hv_len, _⟩, hloop, heven_mod⟩ := hlive
    let q : Fin N := u.foldl c.toDPA.step s
    have hq_val : advFoldNat c s.val u = q.val := advFoldNat_eq_foldl c s u
    have hv_pos : 0 < v.length := by omega
    have hv_ne : v ≠ [] := by rintro rfl; simp at hv_pos
    have hv_loop : v.foldl c.toDPA.step q = q := by
      apply Fin.ext
      rw [← advFoldNat_eq_foldl c q v, ← hq_val, hloop]
    let cyc : ℕ → CommGraph := fun m => v[m % v.length]'(Nat.mod_lt m hv_pos)
    have hcyc_block : ∀ m : ℕ, (List.ofFn (fun i : Fin v.length => cyc (m * v.length + i.val))) = v := by
      intro m
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_ofFn, cyc]
        have hmod : (m * v.length + i) % v.length = i :=
          mul_add_mod_alpha v.length m i hi2
        simp [hmod]
    have hcyc_at_mult : ∀ m : ℕ, runFrom c.toDPA q cyc (m * v.length) = q := by
      intro m
      induction m with
      | zero => simp [runFrom]
      | succ m ih =>
        rw [Nat.succ_mul, runFrom_shift, ih, runFrom_eq_foldl_pre]
        have hpre_v : pre (fun n => cyc (m * v.length + n)) v.length = v := hcyc_block m
        rw [hpre_v, hv_loop]
    have hcyc_state : ∀ t : ℕ,
        runFrom c.toDPA q cyc t = (v.take (t % v.length)).foldl c.toDPA.step q := by
      intro t
      have hdiv := (Nat.div_add_mod t v.length).symm
      conv_lhs => rw [hdiv, Nat.mul_comm v.length (t / v.length)]
      rw [runFrom_shift, hcyc_at_mult (t / v.length), runFrom_eq_foldl_pre]
      congr 1
      apply List.ext_getElem
      · simp [pre, Nat.min_eq_left (le_of_lt (Nat.mod_lt t hv_pos))]
      · intro i hi1 hi2
        simp only [pre, List.getElem_ofFn, List.getElem_take, cyc]
        have hi_lt : i < v.length := lt_of_lt_of_le (by simpa [pre] using hi1)
          (le_of_lt (Nat.mod_lt t hv_pos))
        have hmod : (t / v.length * v.length + i) % v.length = i :=
          mul_add_mod_alpha v.length (t / v.length) i hi_lt
        simp [hmod]
    let ps := (List.range v.length).map fun k => c.2.2.getD (advFoldPrefix c q.val v k) 0
    have hps_ne : ps ≠ [] := by simp [ps, hv_ne]
    obtain ⟨hp_mem, hp_le⟩ := minList_mem_and_le ps hps_ne
    let p := cycleMinPrio c q.val v
    have hp_even : Even p := Nat.even_iff.mpr (by simpa [p, hq_val] using heven_mod)
    have hp_eq : p = minList ps := rfl
    simp only [ps, List.mem_map, List.mem_range] at hp_mem
    obtain ⟨k0, hk0_lt, hk0_eq⟩ := hp_mem
    have hprio_k : ∀ k < v.length,
        c.2.2.getD (advFoldPrefix c q.val v k) 0 =
          c.toDPA.prio ((v.take k).foldl c.toDPA.step q) := by
      intro k hk
      rw [advFoldPrefix_eq_take c q.val v k (le_of_lt hk), advFoldNat_eq_foldl]
      rfl
    let suffix := append u cyc
    have hsuf_shift : ∀ t, runFrom c.toDPA s suffix (u.length + t) = runFrom c.toDPA q cyc t := by
      intro t
      rw [runFrom_shift]
      have hpre_u : pre suffix u.length = u := by
        apply List.ext_getElem
        · simp [pre]
        · intro i hi1 hi2; simp [pre, suffix, append]
      have hu_eq : runFrom c.toDPA s suffix u.length = q := by
        rw [runFrom_eq_foldl_pre, hpre_u]
      have hfn : (fun n => suffix (u.length + n)) = cyc := by
        funext n; simp only [suffix, append]; rw [dif_neg (by omega), Nat.add_sub_cancel_left]
      rw [hu_eq, hfn]
    refine ⟨suffix, ?_⟩
    rw [parityCond_shift _ u.length]
    refine ⟨p, hp_even, ?_, ?_⟩
    · rw [Filter.frequently_atTop]
      intro M0
      have hm_ge : M0 ≤ (M0 + 1) * v.length + k0 := by
        have h1 : M0 + 1 ≤ (M0 + 1) * v.length := Nat.le_mul_of_pos_right _ hv_pos
        omega
      refine ⟨(M0 + 1) * v.length + k0, hm_ge, ?_⟩
      dsimp only
      rw [hsuf_shift, hcyc_state]
      have hmod : ((M0 + 1) * v.length + k0) % v.length = k0 :=
        mul_add_mod_alpha v.length (M0 + 1) k0 hk0_lt
      rw [hmod, ← hprio_k k0 hk0_lt, hk0_eq, hp_eq]
    · rw [Filter.eventually_atTop]
      refine ⟨0, fun t _ => ?_⟩
      dsimp only
      rw [hsuf_shift, hcyc_state, ← hprio_k (t % v.length) (Nat.mod_lt t hv_pos), hp_eq]
      exact hp_le _ (List.mem_map.mpr ⟨t % v.length, List.mem_range.mpr (Nat.mod_lt t hv_pos), rfl⟩)
  · rintro ⟨suffix, p, hp_even, hfreq, hev⟩
    rw [Filter.eventually_atTop] at hev
    obtain ⟨T, hT⟩ := hev
    rw [Filter.frequently_atTop] at hfreq
    have hstep_wit : ∀ b, ∃ t ≥ b, c.toDPA.prio (runFrom c.toDPA s suffix t) = p := hfreq
    classical
    let nextWit (b : ℕ) : ℕ := (hstep_wit b).choose
    have hnext_ge : ∀ b, b ≤ nextWit b := fun b => (hstep_wit b).choose_spec.1
    have hnext_p : ∀ b, c.toDPA.prio (runFrom c.toDPA s suffix (nextWit b)) = p :=
      fun b => (hstep_wit b).choose_spec.2
    let tSeq : ℕ → ℕ := fun k => Nat.rec (nextWit T) (fun _ tk => nextWit (tk + 1)) k
    have htSeq_mono : StrictMono tSeq :=
      strictMono_nat_of_lt_succ fun k => lt_of_lt_of_le (Nat.lt_succ_self _) (hnext_ge _)
    have htSeq_T : ∀ k, T ≤ tSeq k := by
      intro k; induction k with
      | zero => exact hnext_ge T
      | succ k ih => exact le_trans ih (le_of_lt (htSeq_mono (Nat.lt_succ_self k)))
    have htSeq_p : ∀ k, c.toDPA.prio (runFrom c.toDPA s suffix (tSeq k)) = p := by
      intro k; cases k with
      | zero => exact hnext_p T
      | succ k => exact hnext_p (tSeq k + 1)
    let rAt : Fin (N + 1) → Fin N := fun k => runFrom c.toDPA s suffix (tSeq k.val)
    have hcard : Fintype.card (Fin N) < Fintype.card (Fin (N + 1)) := by simp
    obtain ⟨i, j, hij_ne, hrij⟩ := Fintype.exists_ne_map_eq_of_card_lt rAt hcard
    have hex_ij : ∃ a b : ℕ, a < b ∧
        runFrom c.toDPA s suffix (tSeq a) = runFrom c.toDPA s suffix (tSeq b) := by
      rcases lt_trichotomy i.val j.val with h1 | h2 | h3
      · exact ⟨i.val, j.val, h1, hrij⟩
      · exact False.elim (hij_ne (Fin.ext h2))
      · exact ⟨j.val, i.val, h3, hrij.symm⟩
    obtain ⟨ia, ib, hiab, hr_eq⟩ := hex_ij
    let ta := tSeq ia
    let tb := tSeq ib
    have htab : ta < tb := htSeq_mono hiab
    let q : Fin N := runFrom c.toDPA s suffix ta
    have hq_prio : c.toDPA.prio q = p := htSeq_p ia
    obtain ⟨u, hu_lt, hu_end, _⟩ := shorten_path_subset c.toDPA.step s (pre suffix ta)
    have hu_q : u.foldl c.toDPA.step s = q := by
      rw [hu_end, ← runFrom_eq_foldl_pre]
    let g0 : CommGraph := suffix ta
    let q1 : Fin N := c.toDPA.step q g0
    let restLen := tb - (ta + 1)
    let restRaw : List CommGraph := pre (fun n => suffix (ta + 1 + n)) restLen
    have hrest_end : restRaw.foldl c.toDPA.step q1 = q := by
      dsimp only [restRaw]
      rw [← runFrom_eq_foldl_pre]
      have hsh1 : runFrom c.toDPA s suffix (ta + 1) = q1 := by simp [runFrom, q1, q, g0]
      have hsh2 : runFrom c.toDPA s suffix ((ta + 1) + restLen) =
          runFrom c.toDPA q1 (fun n => suffix (ta + 1 + n)) restLen := by
        rw [runFrom_shift, hsh1]
      rw [← hsh2, show (ta + 1) + restLen = tb by omega]
      exact hr_eq.symm
    have hrest_prio : ∀ j ≤ restRaw.length,
        p ≤ c.toDPA.prio ((restRaw.take j).foldl c.toDPA.step q1) := by
      intro j hj
      have hj_le : j ≤ restLen := by simpa [restRaw, pre] using hj
      have htake_eq : restRaw.take j = pre (fun n => suffix (ta + 1 + n)) j := by
        apply List.ext_getElem
        · simp [restRaw, pre, Nat.min_eq_left hj_le]
        · intro m hm1 hm2; simp [restRaw, pre]
      rw [htake_eq, ← runFrom_eq_foldl_pre]
      have hsh1 : runFrom c.toDPA s suffix (ta + 1) = q1 := by simp [runFrom, q1, q, g0]
      have hsh2 : runFrom c.toDPA s suffix ((ta + 1) + j) =
          runFrom c.toDPA q1 (fun n => suffix (ta + 1 + n)) j := by
        rw [runFrom_shift, hsh1]
      rw [← hsh2]
      exact hT ((ta + 1) + j) (by have := htSeq_T ia; omega)
    obtain ⟨rest', hrest'_lt, hrest'_end, hrest'_vis⟩ :=
      shorten_path_subset c.toDPA.step q1 restRaw
    let v : List CommGraph := g0 :: rest'
    have hv_loop : v.foldl c.toDPA.step q = q := by
      simp only [v, List.foldl_cons]
      exact hrest'_end.trans hrest_end
    have hv_min : cycleMinPrio c q.val v = p := by
      let ps := (List.range v.length).map fun k => c.2.2.getD (advFoldPrefix c q.val v k) 0
      have hps_ne : ps ≠ [] := by simp [ps, v]
      obtain ⟨hp_mem, hp_le⟩ := minList_mem_and_le ps hps_ne
      have hp0_mem : p ∈ ps := by
        simp only [ps, List.mem_map, List.mem_range]
        exact ⟨0, by simp [v], hq_prio⟩
      have hle_p : minList ps ≤ p := hp_le p hp0_mem
      simp only [ps, List.mem_map, List.mem_range] at hp_mem
      obtain ⟨k, hk_lt, hk_eq⟩ := hp_mem
      have hp_le_min : p ≤ minList ps := by
        rw [← hk_eq, advFoldPrefix_eq_take c q.val v k (le_of_lt hk_lt), advFoldNat_eq_foldl]
        change p ≤ c.toDPA.prio ((v.take k).foldl c.toDPA.step q)
        rcases k with _ | k'
        · simp [hq_prio]
        · change p ≤ c.toDPA.prio ((g0 :: rest'.take k').foldl c.toDPA.step q)
          simp only [List.foldl_cons]
          obtain ⟨j, hj_le, hj_eq⟩ := hrest'_vis k' (by simp [v] at hk_lt; omega)
          rw [show c.toDPA.step q g0 = q1 from rfl, hj_eq]
          exact hrest_prio j hj_le
      exact le_antisymm hle_p hp_le_min
    unfold liveStateBool
    simp only [List.any_eq_true, List.mem_range, mem_wordsOf_iff, Bool.and_eq_true,
      decide_eq_true_eq]
    refine ⟨u.length, by omega, u, ⟨rfl, fun g _ => mem_allGraphs g⟩,
      rest'.length, hrest'_lt, v, ⟨rfl, fun g _ => mem_allGraphs g⟩, ?_, ?_⟩
    · rw [advFoldNat_eq_foldl c s u, hu_q, advFoldNat_eq_foldl c q v, hv_loop]
    · rw [advFoldNat_eq_foldl c s u, hu_q, hv_min]
      exact Nat.even_iff.mp hp_even

lemma liveStateBool_foldl_iff_mem_pref (c : DPACode) (h : List CommGraph) :
    liveStateBool c (h.foldl c.toDPA.step c.toDPA.init).val = true ↔ h ∈ Pref c.lang :=
  (liveStateBool_iff c (h.foldl c.toDPA.step c.toDPA.init)).trans
    (pref_lang_iff_acceptsFrom c.toDPA h).symm

/-! ### Section 6: `D`-Block Grouping & `compileBlockAutomaton` -/

private lemma parityCond_block_min {D : ℕ} (hD : 0 < D) (c_seq : ℕ → ℕ) :
    ParityCond (fun n => minList ((List.range D).map fun t => c_seq (n * D + t))) ↔
      ParityCond c_seq := by
  let b : ℕ → ℕ := fun n => minList ((List.range D).map fun t => c_seq (n * D + t))
  have hb_props : ∀ n,
      (∃ t < D, b n = c_seq (n * D + t)) ∧ (∀ t < D, b n ≤ c_seq (n * D + t)) := by
    intro n
    let ps := (List.range D).map fun t => c_seq (n * D + t)
    have hne : ps ≠ [] := by simp [ps, Nat.ne_of_gt hD]
    obtain ⟨hmem, hle⟩ := minList_mem_and_le ps hne
    simp only [ps, List.mem_map, List.mem_range] at hmem hle
    obtain ⟨t, ht, hteq⟩ := hmem
    exact ⟨⟨t, ht, hteq.symm⟩, fun t' ht' => hle _ ⟨t', ht', rfl⟩⟩
  constructor
  · rintro ⟨p, hp_even, hfreq, hev⟩
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N0, hN0⟩ := hev
    refine ⟨p, hp_even, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro M0
      obtain ⟨n, hn_ge, hbn⟩ := hfreq (max M0 N0)
      obtain ⟨t, ht_lt, hbt⟩ := (hb_props n).1
      refine ⟨n * D + t, ?_, hbt.symm.trans hbn⟩
      have h1 : M0 ≤ n := le_trans (le_max_left M0 N0) hn_ge
      calc M0 = M0 * 1 := (Nat.mul_one M0).symm
        _ ≤ n * D := Nat.mul_le_mul h1 hD
        _ ≤ n * D + t := Nat.le_add_right _ _
    · rw [Filter.eventually_atTop]
      refine ⟨N0 * D, fun m hm => ?_⟩
      let n := m / D
      let t := m % D
      have ht_lt : t < D := Nat.mod_lt m hD
      have hm_eq : m = n * D + t := by
        dsimp only [n, t]; rw [Nat.mul_comm, Nat.div_add_mod]
      have hn_ge : N0 ≤ n := by
        by_contra hlt
        have h1 : n + 1 ≤ N0 := by omega
        have h2 : n * D + t < (n + 1) * D := by rw [Nat.succ_mul]; omega
        have h3 : (n + 1) * D ≤ N0 * D := Nat.mul_le_mul_right D h1
        omega
      rw [hm_eq]
      exact le_trans (hN0 n hn_ge) ((hb_props n).2 t ht_lt)
  · rintro ⟨p, hp_even, hfreq, hev⟩
    rw [Filter.eventually_atTop] at hev
    obtain ⟨M0, hM0⟩ := hev
    refine ⟨p, hp_even, ?_, ?_⟩
    · rw [Filter.frequently_atTop] at hfreq ⊢
      intro N0
      obtain ⟨m, hm_ge, hcm⟩ := hfreq ((max N0 M0 + 1) * D)
      let n := m / D
      let t := m % D
      have ht_lt : t < D := Nat.mod_lt m hD
      have hm_eq : m = n * D + t := by
        dsimp only [n, t]; rw [Nat.mul_comm, Nat.div_add_mod]
      have hn_ge_max : max N0 M0 + 1 ≤ n := by
        by_contra hlt
        have h1 : n ≤ max N0 M0 := by omega
        have h2 : n * D + t < (max N0 M0 + 1) * D := by
          calc n * D + t < n * D + D := Nat.add_lt_add_left ht_lt _
            _ = (n + 1) * D := by rw [Nat.succ_mul]
            _ ≤ (max N0 M0 + 1) * D := Nat.mul_le_mul_right D (by omega)
        omega
      have hnD_ge_M0 : M0 ≤ n * D := by
        calc M0 ≤ max N0 M0 := le_max_right _ _
          _ ≤ n := by omega
          _ = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * D := Nat.mul_le_mul_left n hD
      have h_upper : b n ≤ p := by
        have hle := (hb_props n).2 t ht_lt
        rwa [← hm_eq, hcm] at hle
      have h_lower : p ≤ b n := by
        obtain ⟨t', _, hbt'⟩ := (hb_props n).1
        rw [hbt']
        exact hM0 (n * D + t') (by omega)
      exact ⟨n, le_trans (le_max_left N0 M0) (by omega), le_antisymm h_upper h_lower⟩
    · rw [Filter.eventually_atTop]
      refine ⟨M0, fun n hn => ?_⟩
      obtain ⟨t', _, hbt'⟩ := (hb_props n).1
      change p ≤ b n
      rw [hbt']
      have hnD : M0 ≤ n * D := by
        calc M0 ≤ n := hn
          _ = n * 1 := (Nat.mul_one n).symm
          _ ≤ n * D := Nat.mul_le_mul_left n hD
      exact hM0 (n * D + t') (by omega)

def specStepPrefix (dSpec : GenDPACode) (αLen : ℕ) (q0 bCode k : ℕ) : ℕ :=
  let Q_sp := dSpec.1 + 1
  (List.range k).foldl
    (fun q i => (dSpec.2.1.getD (q * αLen + decodeDigitNat αLen bCode i) 0) % Q_sp) q0

lemma primrec_specStepPrefix :
    Primrec (fun p : GenDPACode × ℕ × ℕ × ℕ × ℕ =>
      specStepPrefix p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let Ctx := GenDPACode × ℕ × ℕ × ℕ × ℕ
  have hd : Primrec (fun x : Ctx => x.1) := Primrec.fst
  have hα : Primrec (fun x : Ctx => x.2.1) := Primrec.fst.comp Primrec.snd
  have hq0 : Primrec (fun x : Ctx => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun x : Ctx => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hk : Primrec (fun x : Ctx => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldl (Primrec.list_range.comp hk) hq0
    (Primrec.nat_mod.comp
      (primrec_list_getD.comp
        ((Primrec.fst.comp (Primrec.snd.comp (hd.comp Primrec.fst))).pair
          ((Primrec.nat_add.comp
            (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (hα.comp Primrec.fst))
            (primrec_decodeDigitNat.comp
              ((hα.comp Primrec.fst).pair
                ((hb.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))).pair
            (Primrec.const 0))))
      (Primrec.succ.comp (Primrec.fst.comp (hd.comp Primrec.fst)))).to₂

def advBlockStep (c : DPACode) (I : Instance) (D s_adv bCode : ℕ) : ℕ :=
  let αLen := roundSize I
  (List.range D).foldl
    (fun s t => advStepNat c s (decodeRoundFields I (decodeDigitNat αLen bCode t)).2.2.1) s_adv

private lemma primrec_advBlockStep :
    Primrec (fun p : DPACode × Instance × ℕ × ℕ × ℕ =>
      advBlockStep p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let Ctx := DPACode × Instance × ℕ × ℕ × ℕ
  have hc : Primrec (fun x : Ctx => x.1) := Primrec.fst
  have hI : Primrec (fun x : Ctx => x.2.1) := Primrec.fst.comp Primrec.snd
  have hD : Primrec (fun x : Ctx => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs0 : Primrec (fun x : Ctx => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun x : Ctx => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hαLen := primrec_roundSize.comp hI
  exact Primrec.list_foldl (Primrec.list_range.comp hD) hs0
    (primrec_advStepNat.comp
      ((hc.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
            (primrec_decodeRoundFields.comp
              (hI.comp Primrec.fst)
              (primrec_decodeDigitNat.comp
                ((hαLen.comp Primrec.fst).pair
                  ((hb.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd))))))))))).to₂

def blockMinPrio (dSpec : GenDPACode) (αLen D q_spec bCode : ℕ) : ℕ :=
  minList ((List.range D).map
    (fun t => dSpec.2.2.getD (specStepPrefix dSpec αLen q_spec bCode t) 0))

private lemma primrec_blockMinPrio :
    Primrec (fun p : GenDPACode × ℕ × ℕ × ℕ × ℕ =>
      blockMinPrio p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let Ctx := GenDPACode × ℕ × ℕ × ℕ × ℕ
  have hd : Primrec (fun x : Ctx => x.1) := Primrec.fst
  have hα : Primrec (fun x : Ctx => x.2.1) := Primrec.fst.comp Primrec.snd
  have hD : Primrec (fun x : Ctx => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq0 : Primrec (fun x : Ctx => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun x : Ctx => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact primrec_minList.comp
    (Primrec.list_map (Primrec.list_range.comp hD)
      (primrec_list_getD.comp
        ((Primrec.snd.comp (Primrec.snd.comp (hd.comp Primrec.fst))).pair
          ((primrec_specStepPrefix.comp
            ((hd.comp Primrec.fst).pair
              ((hα.comp Primrec.fst).pair
                ((hq0.comp Primrec.fst).pair
                  ((hb.comp Primrec.fst).pair Primrec.snd))))).pair
            (Primrec.const 0)))).to₂)

def blockTransEntry (c : DPACode) (I : Instance) (D : ℕ) (dSpec : GenDPACode) (idx : ℕ) : ℕ :=
  let αLen := roundSize I
  let Q_sp := dSpec.1 + 1
  let P_sz := maxList dSpec.2.2 + 1
  let B_len := blockSize I D
  let st := idx / B_len
  let bCode := idx % B_len
  let s_adv := st / (Q_sp * P_sz)
  let q_spec := (st % (Q_sp * P_sz)) / P_sz
  let s_adv' := advBlockStep c I D s_adv bCode
  let q_spec' := specStepPrefix dSpec αLen q_spec bCode D
  let p_min' := blockMinPrio dSpec αLen D q_spec bCode
  s_adv' * (Q_sp * P_sz) + q_spec' * P_sz + p_min'

private lemma primrec_blockTransEntry :
    Primrec (fun x : (DPACode × Instance × ℕ × GenDPACode) × ℕ =>
      blockTransEntry x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2) := by
  let Ctx := (DPACode × Instance × ℕ × GenDPACode) × ℕ
  have hc : Primrec (fun x : Ctx => x.1.1) := Primrec.fst.comp Primrec.fst
  have hI : Primrec (fun x : Ctx => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hD : Primrec (fun x : Ctx => x.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hd : Primrec (fun x : Ctx => x.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hidx : Primrec (fun x : Ctx => x.2) := Primrec.snd
  have hαLen := primrec_roundSize.comp hI
  have hQ_sp := Primrec.succ.comp (Primrec.fst.comp hd)
  have hP_sz := Primrec.succ.comp (primrec_maxList.comp (Primrec.snd.comp (Primrec.snd.comp hd)))
  have hQP := Primrec.nat_mul.comp hQ_sp hP_sz
  have hB_len := primrec_blockSize.comp hI hD
  have hst := Primrec.nat_div.comp hidx hB_len
  have hbCode := Primrec.nat_mod.comp hidx hB_len
  have hs_adv := Primrec.nat_div.comp hst hQP
  have hq_spec := Primrec.nat_div.comp (Primrec.nat_mod.comp hst hQP) hP_sz
  have hs_adv' := primrec_advBlockStep.comp (hc.pair (hI.pair (hD.pair (hs_adv.pair hbCode))))
  have hq_spec' := primrec_specStepPrefix.comp (hd.pair (hαLen.pair (hq_spec.pair (hbCode.pair hD))))
  have hp_min' := primrec_blockMinPrio.comp (hd.pair (hαLen.pair (hD.pair (hq_spec.pair hbCode))))
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hs_adv' hQP) (Primrec.nat_mul.comp hq_spec' hP_sz))
    hp_min').of_eq fun _ => rfl

def blockFromSpec (c : DPACode) (I : Instance) (D : ℕ) (dSpec : GenDPACode) :
    GenDPACode × List Bool :=
  let S_adv := c.1 + 1
  let Q_sp := dSpec.1 + 1
  let P_sz := maxList dSpec.2.2 + 1
  let Q_blk := S_adv * (Q_sp * P_sz)
  let B_len := blockSize I D
  let prios := (List.range Q_blk).map (fun st => st % P_sz)
  let liveFlags := (List.range Q_blk).map (fun st => liveStateBool c (st / (Q_sp * P_sz)))
  let trans := (List.range (Q_blk * B_len)).map (blockTransEntry c I D dSpec)
  ((Q_blk - 1, trans, prios), liveFlags)

private lemma primrec_blockFromSpec :
    Primrec (fun p : DPACode × Instance × ℕ × GenDPACode =>
      blockFromSpec p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let Inp := DPACode × Instance × ℕ × GenDPACode
  have hc : Primrec (fun x : Inp => x.1) := Primrec.fst
  have hI : Primrec (fun x : Inp => x.2.1) := Primrec.fst.comp Primrec.snd
  have hD : Primrec (fun x : Inp => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun x : Inp => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hS_adv := Primrec.nat_add.comp (Primrec.fst.comp hc) (Primrec.const 1)
  have hQ_sp := Primrec.nat_add.comp (Primrec.fst.comp hd) (Primrec.const 1)
  have hP_sz := Primrec.nat_add.comp (primrec_maxList.comp (Primrec.snd.comp (Primrec.snd.comp hd)))
    (Primrec.const 1)
  have hQP := Primrec.nat_mul.comp hQ_sp hP_sz
  have hQ_blk := Primrec.nat_mul.comp hS_adv hQP
  have hB_len := primrec_blockSize.comp hI hD
  have hPrios := primrec_range_map
    (fun p : Inp => (p.1.1 + 1) * ((p.2.2.2.1 + 1) * (maxList p.2.2.2.2.2 + 1)))
    (fun p st => st % (maxList p.2.2.2.2.2 + 1))
    hQ_blk (fun _ => rfl)
    (Primrec.nat_mod.comp Primrec.snd (hP_sz.comp Primrec.fst)) (fun _ _ => rfl)
  have hLive := primrec_range_map
    (fun p : Inp => (p.1.1 + 1) * ((p.2.2.2.1 + 1) * (maxList p.2.2.2.2.2 + 1)))
    (fun p st => liveStateBool p.1 (st / ((p.2.2.2.1 + 1) * (maxList p.2.2.2.2.2 + 1))))
    hQ_blk (fun _ => rfl)
    (primrec_liveStateBool.comp
      (hc.comp Primrec.fst)
      (Primrec.nat_div.comp Primrec.snd (hQP.comp Primrec.fst)))
    (fun _ _ => rfl)
  have hTrans := primrec_range_map
    (fun p : Inp =>
      ((p.1.1 + 1) * ((p.2.2.2.1 + 1) * (maxList p.2.2.2.2.2 + 1))) * blockSize p.2.1 p.2.2.1)
    (fun p idx => blockTransEntry p.1 p.2.1 p.2.2.1 p.2.2.2 idx)
    (Primrec.nat_mul.comp hQ_blk hB_len) (fun _ => rfl)
    primrec_blockTransEntry (fun _ _ => rfl)
  exact (((Primrec.nat_sub.comp hQ_blk (Primrec.const 1)).pair (hTrans.pair hPrios)).pair hLive).of_eq
    fun _ => rfl

/-- Executable compiler producing `(blockCode : GenDPACode, liveFlags : List Bool)` over
`Fin (blockAlphaMinusOne I (D_minus_1 + 1) + 1)` from `(c, I, D_minus_1)`. -/
def compileBlockAutomaton (detNBW : ℕ → NBWCode → GenDPACode)
    (inp : DPACode × Instance × ℕ) : GenDPACode × List Bool :=
  let c := inp.1
  let I := inp.2.1
  let D := inp.2.2 + 1
  match parse I.tokens with
  | none => ((0, [0], [0]), [false])
  | some φ =>
    let αRound := roundAlphaMinusOne I
    let dSpec := detNBW αRound (unionNBW αRound (notAdvNBW c I) (ltlToNBW I φ))
    blockFromSpec c I D dSpec

theorem primrec_compileBlockAutomaton (detNBW : ℕ → NBWCode → GenDPACode)
    (hPrim : Primrec₂ detNBW) :
    Primrec (compileBlockAutomaton detNBW) := by
  let Inp := DPACode × Instance × ℕ
  let InpPhi := Inp × Formula ℕ ℕ ℕ ℕ
  have hc : Primrec (fun x : InpPhi => x.1.1) := Primrec.fst.comp Primrec.fst
  have hI : Primrec (fun x : InpPhi => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hD : Primrec (fun x : InpPhi => x.1.2.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hφ : Primrec (fun x : InpPhi => x.2) := Primrec.snd
  have hαRound := primrec_roundAlphaMinusOne.comp hI
  have hbUnion := primrec_unionNBW.comp
    (hαRound.pair ((primrec_notAdvNBW.comp hc hI).pair (primrec_ltlToNBW.comp hI hφ)))
  have hdSpec := hPrim.comp hαRound hbUnion
  have hSomeBranch := primrec_blockFromSpec.comp (hc.pair (hI.pair (hD.pair hdSpec)))
  have hParse : Primrec (fun inp : Inp => parse inp.2.1.tokens) :=
    primrec_parse.comp (primrec_tokens.comp (Primrec.fst.comp Primrec.snd))
  exact (Primrec.option_casesOn hParse
    (Primrec.const ((0, [0], [0]), [false]))
    hSomeBranch.to₂).of_eq fun inp => by
    unfold compileBlockAutomaton
    dsimp only
    cases parse inp.2.1.tokens <;> rfl

private lemma blockFromSpec_trans_getD (c : DPACode) (I : Instance) (D : ℕ)
    (dSpec : GenDPACode) (st bCode : ℕ)
    (hst : st < (c.1 + 1) * ((dSpec.1 + 1) * (maxList dSpec.2.2 + 1)))
    (hb : bCode < blockAlphaMinusOne I D + 1) :
    let αLen := roundSize I
    let Q_sp := dSpec.1 + 1
    let P_sz := maxList dSpec.2.2 + 1
    let s_adv := st / (Q_sp * P_sz)
    let q_spec := (st % (Q_sp * P_sz)) / P_sz
    (blockFromSpec c I D dSpec).1.2.1.getD (st * (blockAlphaMinusOne I D + 1) + bCode) 0 =
      advBlockStep c I D s_adv bCode * (Q_sp * P_sz) +
        specStepPrefix dSpec αLen q_spec bCode D * P_sz +
        blockMinPrio dSpec αLen D q_spec bCode := by
  have hb_eq : blockAlphaMinusOne I D + 1 = blockSize I D := by
    rw [blockAlphaMinusOne_succ, blockSize_eq]
  rw [hb_eq] at hb ⊢
  dsimp only [blockFromSpec]
  rw [getD_map_range_mul _ _ _ st bCode hst hb]
  unfold blockTransEntry
  dsimp only
  rw [mul_add_div_alpha _ st bCode hb, mul_add_mod_alpha _ st bCode hb]

theorem compileBlockAutomaton_correct
    (detNBW : ℕ → NBWCode → GenDPACode)
    (hCorr : ∀ (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)),
      (toGenDPA αSize (detNBW αSize b)).Accepts w ↔ NBWAccepts αSize b w)
    (c : DPACode) (I : Instance) (D_minus_1 : ℕ)
    {φ : Formula ℕ ℕ ℕ ℕ} (hparse : parse I.tokens = some φ) :
    let D := D_minus_1 + 1
    let res := compileBlockAutomaton detNBW (c, I, D_minus_1)
    let B := blockDPAOf I D res.1
    let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
    IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive := by
  dsimp only
  let D := D_minus_1 + 1
  have hD_pos : 0 < D := Nat.succ_pos _
  let αRound := roundAlphaMinusOne I
  let αLen := roundSize I
  let bUnion := unionNBW αRound (notAdvNBW c I) (ltlToNBW I φ)
  let dSpec := detNBW αRound bUnion
  let M_spec := toGenDPA αRound dSpec
  let S_adv := c.1 + 1
  let Q_sp := dSpec.1 + 1
  let P_sz := maxList dSpec.2.2 + 1
  let Q_blk := S_adv * (Q_sp * P_sz)
  have hS_pos : 0 < S_adv := Nat.succ_pos _
  have hQsp_pos : 0 < Q_sp := Nat.succ_pos _
  have hPsz_pos : 0 < P_sz := Nat.succ_pos _
  have hQP_pos : 0 < Q_sp * P_sz := Nat.mul_pos hQsp_pos hPsz_pos
  have hQblk_pos : 0 < Q_blk := Nat.mul_pos hS_pos hQP_pos
  have hQblk_succ : Q_blk - 1 + 1 = Q_blk := Nat.sub_add_cancel hQblk_pos
  have hα_succ : αRound + 1 = αLen := roundAlphaMinusOne_succ I
  have hres_eq : compileBlockAutomaton detNBW (c, I, D_minus_1) = blockFromSpec c I D dSpec := by
    unfold compileBlockAutomaton
    simp only [hparse]
    rfl
  let res := compileBlockAutomaton detNBW (c, I, D_minus_1)
  have hres1_1 : res.1.1 + 1 = Q_blk := by
    dsimp only [res]
    rw [hres_eq]
    exact hQblk_succ
  have hrun_inv : ∀ (e : ℕ → RoundLetter I) (n : ℕ),
      let st := ((blockDPAOf I D res.1).run (toBlocks D e) n).val
      let w_r : ℕ → Fin (αRound + 1) := fun m => roundLetterEquiv I (e m)
      st / (Q_sp * P_sz) = ((pre (graphOfExec e) (n * D)).foldl c.toDPA.step c.toDPA.init).val ∧
      (st % (Q_sp * P_sz)) / P_sz = (M_spec.run w_r (n * D)).val ∧
      (0 < n → st % P_sz = minList ((List.range D).map
        fun t => M_spec.prio (M_spec.run w_r ((n - 1) * D + t)))) := by
    intro e n
    let w_r : ℕ → Fin (αRound + 1) := fun m => roundLetterEquiv I (e m)
    induction n with
    | zero =>
      simp only [Nat.zero_mul, Nat.lt_irrefl, IsEmpty.forall_iff, and_true]
      change 0 / (Q_sp * P_sz) = 0 ∧ (0 % (Q_sp * P_sz)) / P_sz = 0
      exact ⟨Nat.zero_div _, by rw [Nat.zero_mod, Nat.zero_div]⟩
    | succ n ih =>
      obtain ⟨ih_s, ih_q, _⟩ := ih
      let q_prev := (blockDPAOf I D res.1).run (toBlocks D e) n
      let st := q_prev.val
      have hst_lt : st < Q_blk := q_prev.isLt.trans_eq hres1_1
      let blk := toBlocks D e n
      let bFin := blockLetterEquiv I D blk
      let bCode := bFin.val
      have hdigit : ∀ t : ℕ, (ht : t < D) →
          decodeDigitNat αLen bCode t = (w_r (n * D + t)).val := by
        intro t ht
        simpa [bCode, bFin, blk, toBlocks, w_r] using
          decodeDigitNat_blockLetterEquiv I D blk ⟨t, ht⟩
      have hspec_pref : ∀ k ≤ D,
          specStepPrefix dSpec αLen ((st % (Q_sp * P_sz)) / P_sz) bCode k =
            (M_spec.run w_r (n * D + k)).val := by
        intro k hk
        induction k with
        | zero =>
          simp only [specStepPrefix, List.range_zero, List.foldl_nil, Nat.add_zero]
          exact ih_q
        | succ k ihk =>
          simp only [specStepPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
            List.foldl_nil]
          rw [← specStepPrefix, ihk (by omega), hdigit k (by omega),
              show n * D + (k + 1) = (n * D + k) + 1 by omega]
          rw [← hα_succ]
          rfl
      have hadv_pref : ∀ k ≤ D,
          (List.range k).foldl
            (fun s t => advStepNat c s (decodeRoundFields I (decodeDigitNat αLen bCode t)).2.2.1)
            (st / (Q_sp * P_sz)) =
            ((pre (graphOfExec e) (n * D + k)).foldl c.toDPA.step c.toDPA.init).val := by
        intro k hk
        induction k with
        | zero =>
          simp only [List.range_zero, List.foldl_nil, Nat.add_zero]
          exact ih_s
        | succ k ihk =>
          simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [ihk (by omega), hdigit k (by omega)]
          have hrf := decodeRoundFields_spec I (w_r (n * D + k))
          rw [Equiv.symm_apply_apply] at hrf
          have hg_eq : (decodeRoundFields I (w_r (n * D + k)).val).2.2.1 =
              graphOfExec e (n * D + k) := by
            rw [hrf]; rfl
          have hpre_succ : pre (graphOfExec e) (n * D + (k + 1)) =
              pre (graphOfExec e) (n * D + k) ++ [graphOfExec e (n * D + k)] := by
            rw [show n * D + (k + 1) = (n * D + k) + 1 by omega]
            exact pre_succ (graphOfExec e) (n * D + k)
          rw [hg_eq, hpre_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rfl
      let s_adv' := ((pre (graphOfExec e) ((n + 1) * D)).foldl c.toDPA.step c.toDPA.init).val
      let q_spec' := (M_spec.run w_r ((n + 1) * D)).val
      let p_min' := minList ((List.range D).map
        fun t => M_spec.prio (M_spec.run w_r (n * D + t)))
      have hs'_lt : s_adv' < S_adv :=
        ((pre (graphOfExec e) ((n + 1) * D)).foldl c.toDPA.step c.toDPA.init).isLt
      have hq'_lt : q_spec' < Q_sp := (M_spec.run w_r ((n + 1) * D)).isLt
      have hp'_lt : p_min' < P_sz := by
        let ps := (List.range D).map fun t => M_spec.prio (M_spec.run w_r (n * D + t))
        obtain ⟨hmem, _⟩ := minList_mem_and_le ps (by simp [ps, Nat.ne_of_gt hD_pos])
        simp only [ps, List.mem_map, List.mem_range] at hmem
        obtain ⟨t, _, hteq⟩ := hmem
        have hle : M_spec.prio (M_spec.run w_r (n * D + t)) ≤ maxList dSpec.2.2 :=
          getD_le_maxList dSpec.2.2 _
        change minList ps < maxList dSpec.2.2 + 1
        rw [← hteq]
        exact Nat.lt_succ_of_le hle
      have hrem_lt : q_spec' * P_sz + p_min' < Q_sp * P_sz := by
        have h1 : q_spec' + 1 ≤ Q_sp := hq'_lt
        calc q_spec' * P_sz + p_min' < q_spec' * P_sz + P_sz := Nat.add_lt_add_left hp'_lt _
          _ = (q_spec' + 1) * P_sz := by rw [Nat.succ_mul]
          _ ≤ Q_sp * P_sz := Nat.mul_le_mul_right P_sz h1
      let target := s_adv' * (Q_sp * P_sz) + q_spec' * P_sz + p_min'
      have htarget_lt : target < Q_blk := by
        have h2 : s_adv' + 1 ≤ S_adv := hs'_lt
        calc s_adv' * (Q_sp * P_sz) + q_spec' * P_sz + p_min'
            = s_adv' * (Q_sp * P_sz) + (q_spec' * P_sz + p_min') := Nat.add_assoc _ _ _
          _ < s_adv' * (Q_sp * P_sz) + Q_sp * P_sz := Nat.add_lt_add_left hrem_lt _
          _ = (s_adv' + 1) * (Q_sp * P_sz) := by rw [Nat.succ_mul s_adv']
          _ ≤ S_adv * (Q_sp * P_sz) := Nat.mul_le_mul_right _ h2
      have hget : res.1.2.1.getD (st * (blockAlphaMinusOne I D + 1) + bCode) 0 = target := by
        have hget1 : res.1.2.1.getD (st * (blockAlphaMinusOne I D + 1) + bCode) 0 =
            (blockFromSpec c I D dSpec).1.2.1.getD (st * (blockAlphaMinusOne I D + 1) + bCode) 0 :=
          congrArg (fun r : GenDPACode × List Bool =>
            r.1.2.1.getD (st * (blockAlphaMinusOne I D + 1) + bCode) 0) hres_eq
        rw [hget1, blockFromSpec_trans_getD c I D dSpec st bCode hst_lt bFin.isLt]
        dsimp only [advBlockStep, blockMinPrio]
        rw [hadv_pref D le_rfl, hspec_pref D le_rfl,
            show n * D + D = (n + 1) * D by rw [Nat.succ_mul]]
        have hmap_eq : ((List.range D).map fun t =>
            dSpec.2.2.getD (specStepPrefix dSpec αLen ((st % (Q_sp * P_sz)) / P_sz) bCode t) 0) =
            ((List.range D).map fun t => M_spec.prio (M_spec.run w_r (n * D + t))) := by
          apply List.map_congr_left
          intro t ht
          rw [hspec_pref t (le_of_lt (List.mem_range.mp ht))]
          rfl
        rw [hmap_eq]
      have hst_next : ((blockDPAOf I D res.1).run (toBlocks D e) (n + 1)).val = target := by
        change (res.1.2.1.getD (st * (blockAlphaMinusOne I D + 1) + bCode) 0) % (res.1.1 + 1) = target
        rw [hget, hres1_1, Nat.mod_eq_of_lt htarget_lt]
      rw [hst_next]
      refine ⟨?_, ?_, fun _ => ?_⟩
      · dsimp only [target]
        rw [Nat.add_assoc, mul_add_div_alpha (Q_sp * P_sz) s_adv' _ hrem_lt]
      · dsimp only [target]
        rw [Nat.add_assoc, mul_add_mod_alpha (Q_sp * P_sz) s_adv' _ hrem_lt,
            mul_add_div_alpha P_sz q_spec' p_min' hp'_lt]
      · dsimp only [target]
        have hmul : s_adv' * (Q_sp * P_sz) + q_spec' * P_sz =
            (s_adv' * Q_sp + q_spec') * P_sz := by ring
        rw [hmul, mul_add_mod_alpha P_sz _ p_min' hp'_lt, Nat.add_sub_cancel]
  constructor
  · intro e
    let w_r : ℕ → Fin (αRound + 1) := fun m => roundLetterEquiv I (e m)
    have hprio_step : ∀ n : ℕ,
        (blockDPAOf I D res.1).prio ((blockDPAOf I D res.1).run (toBlocks D e) (n + 1)) =
          minList ((List.range D).map fun t => M_spec.prio (M_spec.run w_r (n * D + t))) := by
      intro n
      let q1 := (blockDPAOf I D res.1).run (toBlocks D e) (n + 1)
      have hq1_lt : q1.val < Q_blk := q1.isLt.trans_eq hres1_1
      have hp_eq : (blockDPAOf I D res.1).prio q1 = q1.val % P_sz := by
        have hget1 : res.1.2.2.getD q1.val 0 = (blockFromSpec c I D dSpec).1.2.2.getD q1.val 0 :=
          congrArg (fun r : GenDPACode × List Bool => r.1.2.2.getD q1.val 0) hres_eq
        change res.1.2.2.getD q1.val 0 = q1.val % P_sz
        rw [hget1]
        dsimp only [blockFromSpec]
        have hlen_p : ((List.range Q_blk).map (fun st => st % P_sz)).length = Q_blk := by
          simp only [List.length_map, List.length_range]
        rw [getD_eq_getElem _ _ _ (by rw [hlen_p]; exact hq1_lt)]
        simp only [List.getElem_map, List.getElem_range]
        rfl
      rw [hp_eq]
      simpa using (hrun_inv e (n + 1)).2.2 (Nat.succ_pos n)
    have hpar_iff : (blockDPAOf I D res.1).Accepts (toBlocks D e) ↔ M_spec.Accepts w_r := by
      unfold DPA.Accepts
      rw [parityCond_shift _ 1]
      have hfn : (fun n => (blockDPAOf I D res.1).prio
          ((blockDPAOf I D res.1).run (toBlocks D e) (1 + n))) =
          (fun n => minList ((List.range D).map fun t =>
            M_spec.prio (M_spec.run w_r (n * D + t)))) := by
        funext n
        rw [Nat.add_comm 1 n, hprio_step n]
      rw [hfn]
      exact parityCond_block_min hD_pos (fun m => M_spec.prio (M_spec.run w_r m))
    rw [hpar_iff, hCorr αRound bUnion w_r, unionNBW_accepts_iff,
        notAdvNBW_accepts_iff, ltlToNBW_accepts_iff, sat_instFormulaOf]
  · intro e n
    let qn := (blockDPAOf I D res.1).run (toBlocks D e) n
    have hqn_lt : qn.val < Q_blk := qn.isLt.trans_eq hres1_1
    have hget_live : res.2.getD qn.val false = liveStateBool c (qn.val / (Q_sp * P_sz)) := by
      have hget1 : res.2.getD qn.val false = (blockFromSpec c I D dSpec).2.getD qn.val false :=
        congrArg (fun r : GenDPACode × List Bool => r.2.getD qn.val false) hres_eq
      rw [hget1]
      dsimp only [blockFromSpec]
      have hlen_l : ((List.range Q_blk).map (fun st => liveStateBool c (st / (Q_sp * P_sz)))).length = Q_blk := by
        simp only [List.length_map, List.length_range]
      rw [getD_eq_getElem _ _ _ (by rw [hlen_l]; exact hqn_lt)]
      simp only [List.getElem_map, List.getElem_range]
      rfl
    change res.2.getD qn.val false = true ↔ pre (graphOfExec e) (n * D) ∈ Pref c.lang
    rw [hget_live, (hrun_inv e n).1]
    exact liveStateBool_foldl_iff_mem_pref c (pre (graphOfExec e) (n * D))

theorem compileBlockAutomaton_spec (det : NBWDeterminizer)
    (c : DPACode) (I : Instance) (D_minus_1 : ℕ)
    {φ : Formula ℕ ℕ ℕ ℕ} (hparse : parse I.tokens = some φ) :
    let D := D_minus_1 + 1
    let res := compileBlockAutomaton det.detNBW (c, I, D_minus_1)
    let B := blockDPAOf I D res.1
    let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
    IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive :=
  compileBlockAutomaton_correct det.detNBW det.hCorr c I D_minus_1 hparse

/-! ### Section 7: `encIOBlockNat` & `encIOBlockTyped` Interface for `lemma_3_7` -/

def pack5Nat (t : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ :=
  Nat.pair t.1 (Nat.pair t.2.1 (Nat.pair t.2.2.1 (Nat.pair t.2.2.2.1 t.2.2.2.2)))

lemma primrec_pack5Nat : Primrec pack5Nat := by
  have h1 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.1 := Primrec.fst
  have hr1 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2 := Primrec.snd
  have h2 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2.1 := Primrec.fst.comp hr1
  have hr2 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2 := Primrec.snd.comp hr1
  have h3 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2.1 := Primrec.fst.comp hr2
  have hr3 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2.2 := Primrec.snd.comp hr2
  have h4 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2.2.1 := Primrec.fst.comp hr3
  have h5 : Primrec fun t : ℕ × ℕ × ℕ × ℕ × ℕ => t.2.2.2.2 := Primrec.snd.comp hr3
  exact Primrec.encode.comp (h1.pair
    (Primrec.encode.comp (h2.pair
      (Primrec.encode.comp (h3.pair
        (Primrec.encode.comp (h4.pair h5)))))))

def encRoundPacked (dims : ℕ) (tp : ℕ) : ℕ :=
  let k2 := dims.unpair.1
  let m1 := dims.unpair.2.unpair.1
  let m2 := dims.unpair.2.unpair.2
  let x1 := tp.unpair.1
  let x2 := tp.unpair.2.unpair.1
  let gIdx := tp.unpair.2.unpair.2.unpair.1
  let y1 := tp.unpair.2.unpair.2.unpair.2.unpair.1
  let y2 := tp.unpair.2.unpair.2.unpair.2.unpair.2
  let sOut := (m1 + 1) * (m2 + 1)
  let sG := 3 * sOut
  let sX2 := (k2 + 1) * sG
  x1 * sX2 + (x2 * sG + (gIdx * sOut + (y1 * (m2 + 1) + y2)))

lemma primrec₂_encRoundPacked : Primrec₂ encRoundPacked := by
  have hk2 : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  have hm1 : Primrec fun p : ℕ × ℕ => p.1.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hm2 : Primrec fun p : ℕ × ℕ => p.1.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
  have hx1 : Primrec fun p : ℕ × ℕ => p.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  have hr1 : Primrec fun p : ℕ × ℕ => p.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  have hx2 : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hr1)
  have hr2 : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hr1)
  have hg : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hr2)
  have hr3 : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hr2)
  have hy1 : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.2.unpair.1 := Primrec.fst.comp (Primrec.unpair.comp hr3)
  have hy2 : Primrec fun p : ℕ × ℕ => p.2.unpair.2.unpair.2.unpair.2.unpair.2 := Primrec.snd.comp (Primrec.unpair.comp hr3)
  have hsOut := Primrec.nat_mul.comp (Primrec.succ.comp hm1) (Primrec.succ.comp hm2)
  have hsG := Primrec.nat_mul.comp (Primrec.const 3) hsOut
  have hsX2 := Primrec.nat_mul.comp (Primrec.succ.comp hk2) hsG
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp hx1 hsX2)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp hx2 hsG)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp hg hsOut)
        (Primrec.nat_add.comp (Primrec.nat_mul.comp hy1 (Primrec.succ.comp hm2)) hy2)))

def evalDigitsList (M : ℕ) (ds : List ℕ) : ℕ :=
  ds.foldr (fun d acc => d + M * acc) 0

lemma primrec₂_evalDigitsList : Primrec₂ evalDigitsList := by
  have hstep : Primrec fun q : (ℕ × List ℕ) × (ℕ × ℕ) => q.2.1 + q.1.1 * q.2.2 :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0) hstep.to₂).of_eq fun _ => by
    unfold evalDigitsList; congr 1

lemma evalDigitsList_ofFn {M : ℕ} :
    ∀ {d : ℕ} (f : Fin d → Fin M),
      evalDigitsList M ((List.ofFn f).map Fin.val) = encodeDigits M f
  | 0, _ => rfl
  | d + 1, f => by
      rw [List.ofFn_succ, List.map_cons, evalDigitsList, List.foldr_cons, ← evalDigitsList,
          evalDigitsList_ofFn (fun i : Fin d => f i.succ), encodeDigits]
      rfl

def encIOBlockNat (I : Instance) (_D : ℕ) (xs : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  let dims := Nat.pair I.k2 (Nat.pair I.m1 I.m2)
  let ds := (xs.map pack5Nat).map (encRoundPacked dims)
  evalDigitsList (roundSize I) ds

def encIOBlockTyped (I : Instance) (D : ℕ)
    (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) : Fin (blockAlphaMinusOne I D + 1) :=
  blockLetterEquiv I D blk

lemma primrec_encIOBlockNat :
    Primrec fun p : (Instance × ℕ) × List (ℕ × ℕ × ℕ × ℕ × ℕ) =>
      encIOBlockNat p.1.1 p.1.2 p.2 := by
  have hmap5 : Primrec (List.map pack5Nat) :=
    Primrec.list_map Primrec.id (primrec_pack5Nat.comp Primrec.snd).to₂
  have hI : Primrec fun p : (Instance × ℕ) × List (ℕ × ℕ × ℕ × ℕ × ℕ) => p.1.1 :=
    Primrec.fst.comp Primrec.fst
  have hdims : Primrec fun I : Instance => Nat.pair I.k2 (Nat.pair I.m1 I.m2) :=
    Primrec.encode.comp (primrec_k2.pair (Primrec.encode.comp (primrec_m1.pair primrec_m2)))
  have hmapDims : Primrec₂ fun (dims : ℕ) (ps : List ℕ) => ps.map (encRoundPacked dims) :=
    Primrec.list_map Primrec.snd (primrec₂_encRoundPacked.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have hds := hmapDims.comp (hdims.comp hI) (hmap5.comp Primrec.snd)
  exact primrec₂_evalDigitsList.comp (primrec_roundSize.comp hI) hds

lemma encIOBlockTyped_val_eq (I : Instance) (D : ℕ)
    (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :
    (encIOBlockTyped I D blk).val =
      encIOBlockNat I D
        ((List.ofFn blk).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) %
        (blockAlphaMinusOne I D + 1) := by
  let f : Fin D → Fin (roundSize I) :=
    fun i => finCongr (roundAlphaMinusOne_succ I) (roundLetterEquiv I (blk i))
  have hround_eq : ∀ s : RoundLetter I,
      encRoundPacked (Nat.pair I.k2 (Nat.pair I.m1 I.m2))
        (pack5Nat (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) =
      (roundLetterEquiv I s).val := by
    rintro ⟨⟨x1, x2, g⟩, y1, y2⟩
    unfold encRoundPacked pack5Nat
    simp only [Nat.unpair_pair]
    unfold roundLetterEquiv
    dsimp only [prodFinEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
    rw [val_finCongr]
    cases g <;> rfl
  have hds_eq :
      ((((List.ofFn blk).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)).map
        pack5Nat).map (encRoundPacked (Nat.pair I.k2 (Nat.pair I.m1 I.m2)))) =
      (List.ofFn f).map Fin.val := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_ofFn]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_ofFn]
      rw [hround_eq (blk ⟨i, by simpa only [List.length_map, List.length_ofFn] using h1⟩)]
      simp only [f, val_finCongr]
  have henc_eq :
      encIOBlockNat I D
        ((List.ofFn blk).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) =
      (encIOBlockTyped I D blk).val := by
    unfold encIOBlockNat encIOBlockTyped blockLetterEquiv
    simp only [Equiv.trans_apply, val_finCongr, finFunEquiv_apply_val]
    rw [hds_eq, evalDigitsList_ofFn f]
    rfl
  rw [henc_eq, Nat.mod_eq_of_lt (encIOBlockTyped I D blk).isLt]

end DistLTLSynth.Char.Thm34LTLBlockAux

open DistLTLSynth.Char in
theorem solution :
    (∃ detNBW : ℕ → NBWCode → GenDPACode, Primrec₂ detNBW ∧
      ∀ (αSize : ℕ) (b : NBWCode) (w : ℕ → Fin (αSize + 1)),
        (toGenDPA αSize (detNBW αSize b)).Accepts w ↔ NBWAccepts αSize b w) →
    ∃ (blockAlphaMinusOne : Instance → ℕ → ℕ)
      (encIOBlockNat : Instance → ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ)
      (encIOBlockTyped : ∀ (I : Instance) (D : ℕ),
        (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) → Fin (blockAlphaMinusOne I D + 1))
      (compileBlock : DPACode × Instance × ℕ → GenDPACode × List Bool),
      Primrec₂ blockAlphaMinusOne ∧
      (Primrec fun p : (Instance × ℕ) × List (ℕ × ℕ × ℕ × ℕ × ℕ) =>
        encIOBlockNat p.1.1 p.1.2 p.2) ∧
      (∀ (I : Instance) (D : ℕ) (blk : Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)),
        (encIOBlockTyped I D blk).val =
          encIOBlockNat I D
            ((List.ofFn blk).map fun s => (s.1.1.val, s.1.2.1.val, s.1.2.2.idx, s.2.1.val, s.2.2.val)) %
            (blockAlphaMinusOne I D + 1)) ∧
      Primrec compileBlock ∧
      (∀ (c : DPACode) (I : Instance) (D_m1 : ℕ) (φ : Formula ℕ ℕ ℕ ℕ),
        parse I.tokens = some φ →
          let D := D_m1 + 1
          let res := compileBlock (c, I, D_m1)
          let dpa := toGenDPA (blockAlphaMinusOne I D) res.1
          let B : DPA (Fin (res.1.1 + 1)) (Fin D → Signal I.X1 I.X2 × (I.Y1 × I.Y2)) :=
            ⟨dpa.init, fun q blk => dpa.step q (encIOBlockTyped I D blk), dpa.prio⟩
          let Qlive : Set (Fin (res.1.1 + 1)) := {q | res.2.getD q.val false = true}
          IsBlockAutomaton c.lang (instFormulaOf I φ) D B Qlive) := by
  rintro ⟨detNBW, hPrim, hCorr⟩
  refine ⟨Thm34LTLBlockAux.blockAlphaMinusOne,
          Thm34LTLBlockAux.encIOBlockNat,
          Thm34LTLBlockAux.encIOBlockTyped,
          Thm34LTLBlockAux.compileBlockAutomaton detNBW,
          Thm34LTLBlockAux.primrec_blockAlphaMinusOne,
          Thm34LTLBlockAux.primrec_encIOBlockNat,
          Thm34LTLBlockAux.encIOBlockTyped_val_eq,
          Thm34LTLBlockAux.primrec_compileBlockAutomaton detNBW hPrim,
          fun c I D_m1 φ hparse =>
            Thm34LTLBlockAux.compileBlockAutomaton_correct detNBW hCorr c I D_m1 hparse⟩
