-- Prove2me | solution 2 for CoDecompFO.fold_codes
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T06:03:42.393429+00:00
-- url     : https://prove2.me/submissions/31a558a4-e6bf-4554-bd9a-4cb7cdb8d917

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_Fold
import Definitions.Def_CoDecompFO_CodeFold
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

namespace CoDecompFO
namespace FoldCodesProof

open FirstOrder FirstOrder.Language SimpleGraph


/-! ### 1. Base-`B` and bit-level packing/unpacking -/

def packList (B : ℕ) (ds : List ℕ) : ℕ :=
  ds.foldr (fun d acc => d + B * acc) 0

def packBase (n B : ℕ) (f : ℕ → ℕ) : ℕ :=
  packList B ((List.range n).map f)

def unpackBase (B m i : ℕ) : ℕ :=
  (m / B ^ i) % B

def packBits (n : ℕ) (f : ℕ → Bool) : ℕ :=
  packBase n 2 (fun i => (f i).toNat)

def unpackBit (m i : ℕ) : Bool :=
  unpackBase 2 m i == 1

@[simp] theorem packList_nil (B : ℕ) : packList B [] = 0 := rfl

@[simp] theorem packList_cons (B d : ℕ) (ds : List ℕ) :
    packList B (d :: ds) = d + B * packList B ds := rfl

theorem packList_lt {B : ℕ} :
    ∀ {ds : List ℕ}, (∀ d ∈ ds, d < B) → packList B ds < B ^ ds.length
  | [], _ => by simp
  | d :: ds, h => by
    have hd : d < B := h d List.mem_cons_self
    have hB : 0 < B := Nat.zero_lt_of_lt hd
    have ih : packList B ds < B ^ ds.length :=
      packList_lt (fun x hx => h x (List.mem_cons_of_mem d hx))
    simp only [packList_cons, List.length_cons]
    calc d + B * packList B ds
        < B + B * packList B ds := Nat.add_lt_add_right hd _
      _ = B * (packList B ds + 1) := by ring
      _ ≤ B * B ^ ds.length := Nat.mul_le_mul_left B ih
      _ = B ^ (ds.length + 1) := (pow_succ' B ds.length).symm

theorem packBase_lt {n B : ℕ} (hB : 0 < B ∨ n = 0) {f : ℕ → ℕ} (hf : ∀ i < n, f i < B) :
    packBase n B f < B ^ n := by
  rcases hB with hB | rfl
  · have h := @packList_lt B ((List.range n).map f) (by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hd
      exact hf i (List.mem_range.1 hi))
    simpa [packBase] using h
  · simp [packBase]

theorem packBits_lt (n : ℕ) (f : ℕ → Bool) : packBits n f < 2 ^ n :=
  packBase_lt (Or.inl (by norm_num)) (fun i _ => Bool.toNat_lt (f i))

theorem unpackBase_packList {B : ℕ} :
    ∀ {ds : List ℕ}, (∀ d ∈ ds, d < B) →
      ∀ {i : ℕ} (hi : i < ds.length), unpackBase B (packList B ds) i = ds[i]
  | [], _, _, hi => nomatch hi
  | d :: ds, h, 0, _ => by
    have hd : d < B := h d List.mem_cons_self
    simp [unpackBase, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  | d :: ds, h, i + 1, hi => by
    have hd : d < B := h d List.mem_cons_self
    have hB : 0 < B := Nat.zero_lt_of_lt hd
    have hi' : i < ds.length := Nat.lt_of_succ_lt_succ hi
    have hdiv : (d + B * packList B ds) / B = packList B ds := by
      rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_zero_iff.2 (Or.inr hd), zero_add]
    have hexp : (d + B * packList B ds) / B ^ (i + 1) = packList B ds / B ^ i := by
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
    simp only [packList_cons, unpackBase, List.getElem_cons_succ]
    rw [hexp]
    exact unpackBase_packList (fun x hx => h x (List.mem_cons_of_mem d hx)) hi'

theorem unpackBase_packBase {n B : ℕ} {f : ℕ → ℕ} (hf : ∀ i < n, f i < B)
    {i : ℕ} (hi : i < n) : unpackBase B (packBase n B f) i = f i := by
  have h := unpackBase_packList (B := B) (ds := (List.range n).map f)
    (fun d hd => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hd
      exact hf j (List.mem_range.1 hj))
    (i := i) (by simp [hi])
  simpa [packBase] using h

theorem unpackBit_packBits (n : ℕ) (f : ℕ → Bool) {i : ℕ} (hi : i < n) :
    unpackBit (packBits n f) i = f i := by
  unfold unpackBit packBits
  rw [unpackBase_packBase (fun j _ => Bool.toNat_lt (f j)) hi]
  cases f i <;> rfl

theorem packBase_congr {n B : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    packBase n B f = packBase n B g := by
  unfold packBase
  congr 1
  exact List.map_congr_left (fun i hi => h i (List.mem_range.1 hi))

theorem packBits_congr {n : ℕ} {f g : ℕ → Bool} (h : ∀ i < n, f i = g i) :
    packBits n f = packBits n g :=
  packBase_congr (fun i hi => congrArg Bool.toNat (h i hi))

theorem packBase_unpackBase {B : ℕ} (hB : 0 < B) :
    ∀ {n m : ℕ}, m < B ^ n → packBase n B (unpackBase B m) = m
  | 0, m, hm => by
    have hm0 : m = 0 := by simpa using hm
    subst hm0
    rfl
  | n + 1, m, hm => by
    have hm' : m / B < B ^ n := by
      rw [Nat.div_lt_iff_lt_mul hB, mul_comm, ← pow_succ']
      exact hm
    have ih := packBase_unpackBase hB hm'
    unfold packBase
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, packList_cons]
    have h1 : unpackBase B m 0 = m % B := by simp [unpackBase]
    have h2 : ((List.range n).map (unpackBase B m ∘ Nat.succ)) =
        (List.range n).map (unpackBase B (m / B)) := by
      refine List.map_congr_left fun i _ => ?_
      simp [Function.comp, unpackBase, pow_succ', Nat.div_div_eq_div_mul]
    rw [h1, h2]
    change m % B + B * packBase n B (unpackBase B (m / B)) = m
    rw [ih, Nat.mod_add_div]

theorem packBits_unpackBit : ∀ {n m : ℕ}, m < 2 ^ n → packBits n (unpackBit m) = m := by
  intro n m hm
  unfold packBits
  have hcongr : packBase n 2 (fun i => (unpackBit m i).toNat) = packBase n 2 (unpackBase 2 m) := by
    refine packBase_congr fun i _ => ?_
    unfold unpackBit
    have hlt : unpackBase 2 m i < 2 := Nat.mod_lt _ (by norm_num)
    interval_cases unpackBase 2 m i <;> rfl
  rw [hcongr]
  exact packBase_unpackBase (by norm_num) hm

theorem packList_append (B : ℕ) :
    ∀ (l₁ l₂ : List ℕ), packList B (l₁ ++ l₂) = packList B l₁ + B ^ l₁.length * packList B l₂
  | [], l₂ => by simp
  | d :: l₁, l₂ => by
    simp only [List.cons_append, packList_cons, List.length_cons, packList_append B l₁ l₂, pow_succ']
    ring

theorem packList_ofFn_eq_finFunctionFinEquiv {a n : ℕ} (args : Fin a → Fin n) :
    packList n (List.ofFn (fun j => (args j).val)) = (finFunctionFinEquiv args).val := by
  rw [finFunctionFinEquiv_apply]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.ofFn_succ, packList_cons, ih (fun j => args j.succ), Fin.sum_univ_succ]
    simp [pow_succ', Finset.mul_sum, mul_left_comm, mul_comm]

/-! ### 2. `frame` and `encBag` parsing -/

def popFrame (s : List ℕ) : List ℕ × List ℕ :=
  (s.tail.take s.headI, s.tail.drop s.headI)

def nthFrame : ℕ → List ℕ → List ℕ
  | 0, s => (popFrame s).1
  | j + 1, s => nthFrame j (popFrame s).2

theorem popFrame_frame_cons (l : List ℕ) (ls : List (List ℕ)) :
    popFrame (frame (l :: ls)) = (l, frame ls) := by
  simp [frame, popFrame]

theorem nthFrame_frame :
    ∀ (ls : List (List ℕ)) {j : ℕ} (hj : j < ls.length), nthFrame j (frame ls) = ls[j]
  | [], _, hj => nomatch hj
  | l :: ls, 0, _ => by simp [nthFrame, popFrame_frame_cons]
  | l :: ls, j + 1, hj => by
    simp only [nthFrame, popFrame_frame_cons]
    exact nthFrame_frame ls (Nat.lt_of_succ_lt_succ hj)

def listSum (xs : List ℕ) : ℕ :=
  xs.foldl (· + ·) 0

theorem listSum_eq_sum (xs : List ℕ) : listSum xs = xs.sum := by
  unfold listSum
  rw [← List.sum_eq_foldl]

def arN (σ : Sig) (i : ℕ) : ℕ := (List.ofFn σ.ar).getD i 0

theorem arN_val (σ : Sig) (i : Fin σ.r) : arN σ i.val = σ.ar i := by
  unfold arN
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp

def arEq (σ : Sig) (i : ℕ) : ℕ :=
  if i = 0 then 2 else arN σ (i - 1)

theorem arEq_val (σ : Sig) (i : Fin (sigmaEq σ).r) : arEq σ i.val = (sigmaEq σ).ar i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp [arEq, sigmaEq, arN_val]

def relOffset (σ : Sig) (n i : ℕ) : ℕ :=
  listSum ((List.range i).map (fun j => n ^ arN σ j))

def bagRelBit (σ : Sig) (bcode : List ℕ) (i : ℕ) (as : List ℕ) : Bool :=
  bcode.tail.getD (relOffset σ bcode.headI i + packList bcode.headI as) 0 == 1

def bagEqRelBit (σ : Sig) (bcode : List ℕ) (i : ℕ) (as : List ℕ) : Bool :=
  if i = 0 then as.getD 0 0 == as.getD 1 0
  else bagRelBit σ bcode (i - 1) as

theorem flatten_lookup :
    ∀ (chunks : List (List ℕ)) {i : ℕ} (hi : i < chunks.length) {k : ℕ}
      (_hk : k < chunks[i].length),
      chunks.flatten[((chunks.take i).map List.length).sum + k]? = chunks[i][k]?
  | [], _, hi, _, _ => nomatch hi
  | c :: cs, 0, _, k, hk => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, zero_add, List.flatten_cons,
      List.getElem_cons_zero]
    exact List.getElem?_append_left hk
  | c :: cs, i + 1, hi, k, hk => by
    have hi' : i < cs.length := Nat.lt_of_succ_lt_succ hi
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
      List.getElem_cons_succ]
    rw [add_assoc, List.getElem?_append_right (by omega)]
    have hsub : c.length + (((cs.take i).map List.length).sum + k) - c.length =
        ((cs.take i).map List.length).sum + k := by omega
    rw [hsub]
    exact flatten_lookup cs hi' hk

theorem bagRelBit_encBag {σ : Sig} (B : Bag σ) (i : Fin σ.r) (args : Fin (σ.ar i) → Fin B.n) :
    bagRelBit σ (encBag B) i.val (List.ofFn (fun j => (args j).val)) = true ↔ B.rel i args := by
  classical
  let chunk : Fin σ.r → List ℕ := fun j =>
    List.ofFn (fun k : Fin (B.n ^ σ.ar j) =>
      if B.rel j (finFunctionFinEquiv.symm k) then 1 else 0)
  let chunks : List (List ℕ) := (List.finRange σ.r).map chunk
  have hhead : (encBag B).headI = B.n := rfl
  have htail : (encBag B).tail = chunks.flatten := rfl
  have hlen_chunks : chunks.length = σ.r := by simp [chunks]
  have hi_lt : i.val < chunks.length := by rw [hlen_chunks]; exact i.isLt
  have hchunk_i : chunks[i.val] = chunk i := by
    rw [List.getElem_map]
    have hfin : (List.finRange σ.r)[i.val]'(by simp [i.isLt]) = i := by
      ext; simp
    rw [hfin]
  let kidx : Fin (B.n ^ σ.ar i) := finFunctionFinEquiv args
  have hpack : packList B.n (List.ofFn (fun j => (args j).val)) = kidx.val :=
    packList_ofFn_eq_finFunctionFinEquiv args
  have hk_lt : kidx.val < chunks[i.val].length := by
    rw [hchunk_i]
    simp [chunk]
  have hoff : relOffset σ B.n i.val = ((chunks.take i.val).map List.length).sum := by
    unfold relOffset
    rw [listSum_eq_sum]
    congr 1
    apply List.ext_getElem
    · simp [chunks]
    · intro j hj1 hj2
      have hjr : j < σ.r := lt_trans (by simpa using hj1) i.isLt
      have hfinj : (List.finRange σ.r)[j]'(by simp [hjr]) = ⟨j, hjr⟩ := by
        ext; simp
      simp [chunks, chunk, hfinj, arN_val σ ⟨j, hjr⟩]
  unfold bagRelBit
  rw [hhead, htail, hoff, hpack, List.getD_eq_getElem?_getD,
    flatten_lookup chunks hi_lt hk_lt]
  have hval : chunks[i.val][kidx.val]? = some (if B.rel i args then 1 else 0) := by
    rw [hchunk_i, List.getElem?_eq_getElem (by simp [chunk]), List.getElem_ofFn]
    have hk_eq : (⟨kidx.val, kidx.isLt⟩ : Fin (B.n ^ σ.ar i)) = kidx := rfl
    rw [hk_eq]
    simp [kidx]
  rw [hval]
  by_cases hrel : B.rel i args <;> simp [hrel]

theorem bagEqRelBit_encBag {σ : Sig} (B : Bag σ) (i : Fin (sigmaEq σ).r)
    (args : Fin ((sigmaEq σ).ar i) → Fin B.withEq.n) :
    bagEqRelBit σ (encBag B) i.val (List.ofFn (fun j => (args j).val)) = true ↔
      (sigmaEq σ).holds (A := Fin B.withEq.n) i args := by
  induction i using Fin.cases with
  | zero =>
    let a : Fin 2 → Fin B.withEq.n := args
    have heq : (List.ofFn fun j => (args j).val) = [(a 0).val, (a 1).val] := rfl
    change bagEqRelBit σ (encBag B) 0 (List.ofFn fun j => (args j).val) = true ↔ a 0 = a 1
    rw [heq]
    simp [bagEqRelBit, Fin.ext_iff]
  | succ j =>
    simp only [bagEqRelBit, Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    exact bagRelBit_encBag B j args

/-! ### 3. `Primrec` combinators -/

theorem primrec_pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

theorem primrec_packList : Primrec₂ packList := by
  unfold packList
  exact (Primrec.list_foldr Primrec.snd (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.snd))).to₂).to₂

theorem primrec_unpackBase : Primrec (fun p : ℕ × ℕ × ℕ => unpackBase p.1 p.2.1 p.2.2) := by
  unfold unpackBase
  exact Primrec.nat_mod.comp
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd)
      (primrec_pow.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
    Primrec.fst

theorem primrec_unpackBit : Primrec₂ unpackBit := by
  unfold unpackBit
  exact (Primrec.beq.comp
    (primrec_unpackBase.comp (Primrec.pair (Primrec.const 2) Primrec.id))
    (Primrec.const 1)).to₂

theorem primrec_popFrame : Primrec popFrame :=
  Primrec.pair (Primrec.list_take.comp Primrec.list_headI Primrec.list_tail)
    (Primrec.list_drop.comp Primrec.list_headI Primrec.list_tail)

theorem primrec_nthFrame : ∀ j : ℕ, Primrec (nthFrame j)
  | 0 => Primrec.fst.comp primrec_popFrame
  | j + 1 => (primrec_nthFrame j).comp (Primrec.snd.comp primrec_popFrame)

theorem primrec_listSum : Primrec listSum := by
  unfold listSum
  exact Primrec.list_foldl Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_arN (σ : Sig) : Primrec (arN σ) :=
  (Primrec.list_getD 0).comp (Primrec.const (List.ofFn σ.ar)) Primrec.id

theorem primrec_arEq (σ : Sig) : Primrec (arEq σ) := by
  unfold arEq
  exact Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 2)
    ((primrec_arN σ).comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)))

theorem primrec_relOffset (σ : Sig) : Primrec₂ (relOffset σ) := by
  show Primrec (fun p : ℕ × ℕ => relOffset σ p.1 p.2)
  unfold relOffset
  refine primrec_listSum.comp ?_
  exact Primrec.list_map (Primrec.list_range.comp (@Primrec.snd ℕ ℕ _ _))
    (primrec_pow.comp (Primrec.fst.comp Primrec.fst) ((primrec_arN σ).comp Primrec.snd)).to₂

theorem primrec_bagRelBit (σ : Sig) :
    Primrec (fun p : List ℕ × ℕ × List ℕ => bagRelBit σ p.1 p.2.1 p.2.2) := by
  unfold bagRelBit
  have hb : Primrec (fun p : List ℕ × ℕ × List ℕ => p.1) := Primrec.fst
  have hi : Primrec (fun p : List ℕ × ℕ × List ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have has : Primrec (fun p : List ℕ × ℕ × List ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun p : List ℕ × ℕ × List ℕ => p.1.headI) := Primrec.list_headI.comp hb
  have idx : Primrec (fun p : List ℕ × ℕ × List ℕ =>
      relOffset σ p.1.headI p.2.1 + packList p.1.headI p.2.2) :=
    Primrec.nat_add.comp ((primrec_relOffset σ).comp hn hi) (primrec_packList.comp hn has)
  exact Primrec.beq.comp ((Primrec.list_getD 0).comp (Primrec.list_tail.comp hb) idx)
    (Primrec.const 1)

theorem primrec_bagEqRelBit (σ : Sig) :
    Primrec (fun p : List ℕ × ℕ × List ℕ => bagEqRelBit σ p.1 p.2.1 p.2.2) := by
  unfold bagEqRelBit
  have hb : Primrec (fun p : List ℕ × ℕ × List ℕ => p.1) := Primrec.fst
  have hi : Primrec (fun p : List ℕ × ℕ × List ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have has : Primrec (fun p : List ℕ × ℕ × List ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  refine Primrec.ite (Primrec.eq.comp hi (Primrec.const 0))
    (Primrec.beq.comp ((Primrec.list_getD 0).comp has (Primrec.const 0))
      ((Primrec.list_getD 0).comp has (Primrec.const 1))) ?_
  exact (primrec_bagEqRelBit_aux : _)
where
  primrec_bagEqRelBit_aux :
      Primrec (fun p : List ℕ × ℕ × List ℕ => bagRelBit σ p.1 (p.2.1 - 1) p.2.2) :=
    (primrec_bagRelBit σ).comp
      (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
          (Primrec.snd.comp Primrec.snd)))

/-! ### 4. Alternating-form scanner on `encF φ` (`quantCount φ :: encF (altMatrix φ)`) -/

abbrev AFSt : Type := List (ℕ × List ℕ) × ℕ × List ℕ

def afStep (ar' : ℕ → ℕ) (s : AFSt) (t : ℕ) : AFSt :=
  if s.1.headI.1 = 2 then (s.1.tail, s.2.1, s.2.2 ++ [s.1.headI.2.getD t 0])
  else if s.1.headI.1 = 3 then
    ((List.range (ar' t)).map (fun _ => ((2 : ℕ), s.1.headI.2)) ++ s.1.tail, s.2.1, s.2.2 ++ [t + 1])
  else if t = 0 then (s.1.tail, s.2.1, s.2.2 ++ [0])
  else if t = 1 then
    ((2, s.1.headI.2) :: (2, s.1.headI.2) :: s.1.tail, s.2.1, s.2.2 ++ [2, 0])
  else if t = 2 then ((3, s.1.headI.2) :: s.1.tail, s.2.1, s.2.2 ++ [2])
  else if t = 3 then
    ((1 - s.1.headI.1, s.1.headI.2) :: (s.1.headI.1, s.1.headI.2) :: s.1.tail, s.2.1, s.2.2 ++ [3])
  else ((s.1.headI.1, s.1.headI.2 ++ [2 * s.2.1 + s.1.headI.1]) :: s.1.tail, s.2.1 + 1, s.2.2)

def altScan (σ : Sig) (l : List ℕ) : List ℕ :=
  let res := l.foldl (afStep (arN σ)) ([(0, [])], 0, [])
  res.2.1 :: res.2.2

theorem afStep_term (ar' : ℕ → ℕ) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ) (out : List ℕ)
    (t : ℕ) : afStep ar' ((2, env) :: rest, q, out) t = (rest, q, out ++ [env.getD t 0]) := by
  simp [afStep]

theorem afStep_idx (ar' : ℕ → ℕ) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ) (out : List ℕ)
    (t : ℕ) : afStep ar' ((3, env) :: rest, q, out) t =
      (List.replicate (ar' t) (2, env) ++ rest, q, out ++ [t + 1]) := by
  simp [afStep]

theorem afStep_form0 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : afStep ar' ((neg.toNat, env) :: rest, q, out) 0 = (rest, q, out ++ [0]) := by
  cases neg <;> simp [afStep]

theorem afStep_form1 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : afStep ar' ((neg.toNat, env) :: rest, q, out) 1 =
      ((2, env) :: (2, env) :: rest, q, out ++ [2, 0]) := by
  cases neg <;> simp [afStep]

theorem afStep_form2 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : afStep ar' ((neg.toNat, env) :: rest, q, out) 2 =
      ((3, env) :: rest, q, out ++ [2]) := by
  cases neg <;> simp [afStep]

theorem afStep_form3 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : afStep ar' ((neg.toNat, env) :: rest, q, out) 3 =
      (((!neg).toNat, env) :: (neg.toNat, env) :: rest, q, out ++ [3]) := by
  cases neg <;> simp [afStep]

theorem afStep_form4 (ar' : ℕ → ℕ) (neg : Bool) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ)
    (out : List ℕ) : afStep ar' ((neg.toNat, env) :: rest, q, out) 4 =
      ((neg.toNat, env ++ [2 * q + neg.toNat]) :: rest, q + 1, out) := by
  cases neg <;> simp [afStep]

theorem afScan_terms (ar' : ℕ → ℕ) (env : List ℕ) (rest : List (ℕ × List ℕ)) (q : ℕ) :
    ∀ (cs toks out : List ℕ),
      (cs ++ toks).foldl (afStep ar') (List.replicate cs.length (2, env) ++ rest, q, out) =
        toks.foldl (afStep ar') (rest, q, out ++ cs.map (fun c => env.getD c 0))
  | [], toks, out => by simp
  | c :: cs, toks, out => by
    rw [List.cons_append, List.foldl_cons, List.length_cons, List.replicate_succ, List.cons_append,
      afStep_term, afScan_terms ar' env rest q cs toks]
    simp

def envL {n k : ℕ} (env : Fin n → Fin k) : List ℕ := List.ofFn (fun j => (env j).val)

theorem encTerm_renameTerm {σ : Sig} {n k : ℕ} (env : Fin n → Fin k)
    (t : σ.lang.Term (Empty ⊕ Fin n)) :
    encTerm (renameTerm env t) = (envL env).getD (encTerm t) 0 := by
  match t with
  | .var (.inl e) => exact e.elim
  | .var (.inr j) =>
    show (env j).val = (envL env).getD j.val 0
    unfold envL
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
    simp
  | .func f _ => exact nomatch (show Empty from f)

theorem envL_snoc {n k : ℕ} (env : Fin n → Fin k) (p : Fin k) :
    envL (Fin.snoc (α := fun _ => Fin k) env p) = envL env ++ [p.val] := by
  unfold envL
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

theorem afScan_matrixOf {σ : Sig} (k : ℕ) :
    ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k) (q : ℕ)
      (neg : Bool) (h : 2 * (q + quantCount f) ≤ k) (rest : List (ℕ × List ℕ)) (out toks : List ℕ),
      (encF f ++ toks).foldl (afStep (arN σ)) ((neg.toNat, envL env) :: rest, q, out) =
        toks.foldl (afStep (arN σ)) (rest, q + quantCount f, out ++ encF (matrixOf k f env q neg h))
  | _, .falsum, env, q, neg, h, rest, out, toks => by
    show ([0] ++ toks).foldl _ _ = toks.foldl _ (rest, q + 0, out ++ [0])
    rw [List.singleton_append, List.foldl_cons, afStep_form0]
    rfl
  | _, .equal t₁ t₂, env, q, neg, h, rest, out, toks => by
    show ([1, encTerm t₁, encTerm t₂] ++ toks).foldl _ _ = toks.foldl _
      (rest, q + 0, out ++ (2 :: 0 :: List.ofFn
        (fun j => encTerm (![renameTerm env t₁, renameTerm env t₂] j))))
    have e : List.ofFn (fun j => encTerm (![renameTerm env t₁, renameTerm env t₂] j)) =
        [(envL env).getD (encTerm t₁) 0, (envL env).getD (encTerm t₂) 0] := by
      simp [List.ofFn_succ, encTerm_renameTerm]
    rw [e]
    simp only [List.cons_append, List.nil_append, List.foldl_cons, afStep_form1, afStep_term]
    simp
  | _, .rel R ts, env, q, neg, h, rest, out, toks => by
    show ((2 :: R.1.val :: List.ofFn (fun j => encTerm (ts j))) ++ toks).foldl _ _ = toks.foldl _
      (rest, q + 0, out ++ (2 :: (R.1.val + 1) :: List.ofFn (fun j => encTerm (renameTerm env (ts j)))))
    have ha : arN σ R.1.val = (List.ofFn (fun j => encTerm (ts j))).length := by
      rw [arN_val, R.2, List.length_ofFn]
    rw [List.cons_append, List.cons_append, List.foldl_cons, List.foldl_cons, afStep_form2,
      afStep_idx, ha, afScan_terms]
    have e : (List.ofFn (fun j => encTerm (ts j))).map (fun c => (envL env).getD c 0) =
        List.ofFn (fun j => encTerm (renameTerm env (ts j))) := by
      rw [List.map_ofFn]
      congr 1
      funext j
      exact (encTerm_renameTerm env (ts j)).symm
    rw [e]
    simp
  | _, .imp f g, env, q, neg, h, rest, out, toks => by
    have hh : 2 * (q + (quantCount f + quantCount g)) ≤ k := h
    have hf2 : 2 * (q + quantCount f) ≤ k := by omega
    have hg2 : 2 * (q + quantCount f + quantCount g) ≤ k := by omega
    show ((3 :: (encF f ++ encF g)) ++ toks).foldl _ _ = toks.foldl _
      (rest, q + (quantCount f + quantCount g),
        out ++ (3 :: (encF (matrixOf k f env q (!neg) hf2) ++
          encF (matrixOf k g env (q + quantCount f) neg hg2))))
    rw [List.cons_append, List.foldl_cons, afStep_form3, List.append_assoc,
      afScan_matrixOf k f env q (!neg) hf2, afScan_matrixOf k g env (q + quantCount f) neg hg2]
    simp [Nat.add_assoc]
  | _, .all f, env, q, neg, h, rest, out, toks => by
    have hh : 2 * (q + (quantCount f + 1)) ≤ k := h
    have hb := neg.toNat_lt
    have hk : 2 * q + neg.toNat < k := by omega
    show ((4 :: encF f) ++ toks).foldl _ _ = toks.foldl _
      (rest, q + (quantCount f + 1), out ++ encF (matrixOf k f
        (Fin.snoc (α := fun _ => Fin k) env ⟨2 * q + neg.toNat, hk⟩) (q + 1) neg (by omega)))
    have hq_add : (q + 1) + quantCount f = q + (quantCount f + 1) := by omega
    rw [List.cons_append, List.foldl_cons, afStep_form4,
      ← envL_snoc env ⟨2 * q + neg.toNat, hk⟩, afScan_matrixOf k f _ (q + 1) neg (by omega)]
    exact congrArg (fun m => toks.foldl (afStep (arN σ)) (rest, m, _)) hq_add

theorem altScan_encF {σ : Sig} (φ : σ.lang.Sentence) :
    altScan σ (encF φ) = quantCount φ :: encF (altMatrix φ) := by
  have h := afScan_matrixOf (σ := σ) (2 * quantCount φ) φ
    (Fin.elim0 : Fin 0 → Fin (2 * quantCount φ)) 0 false (by omega) [] [] []
  have e : envL (Fin.elim0 : Fin 0 → Fin (2 * quantCount φ)) = [] := rfl
  rw [e] at h
  simp only [List.append_nil, List.foldl_nil, Bool.toNat_false, Nat.zero_add, List.nil_append] at h
  unfold altScan altMatrix
  rw [h]

theorem primrec_afStep {ar' : ℕ → ℕ} (har : Primrec ar') : Primrec₂ (afStep ar') := by
  have hstk : Primrec (fun p : AFSt × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hhd : Primrec (fun p : AFSt × ℕ => p.1.1.headI) := Primrec.list_headI.comp hstk
  have htag : Primrec (fun p : AFSt × ℕ => p.1.1.headI.1) := Primrec.fst.comp hhd
  have henv : Primrec (fun p : AFSt × ℕ => p.1.1.headI.2) := Primrec.snd.comp hhd
  have hrest : Primrec (fun p : AFSt × ℕ => p.1.1.tail) := Primrec.list_tail.comp hstk
  have hq : Primrec (fun p : AFSt × ℕ => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hout : Primrec (fun p : AFSt × ℕ => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun p : AFSt × ℕ => p.2) := Primrec.snd
  have h2env : Primrec (fun p : AFSt × ℕ => ((2 : ℕ), p.1.1.headI.2)) :=
    Primrec.pair (Primrec.const 2) henv
  have emit : ∀ {g : AFSt × ℕ → List ℕ}, Primrec g →
      Primrec (fun p : AFSt × ℕ => p.1.2.2 ++ g p) := fun hg => Primrec.list_append.comp hout hg
  have single : ∀ {g : AFSt × ℕ → ℕ}, Primrec g → Primrec (fun p : AFSt × ℕ => [g p]) :=
    fun hg => Primrec.list_cons.comp hg (Primrec.const [])
  show Primrec (fun p : AFSt × ℕ => afStep ar' p.1 p.2)
  unfold afStep
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) ?_ ?_
  · exact Primrec.pair hrest (Primrec.pair hq
      (emit (single ((Primrec.list_getD 0).comp henv ht))))
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) ?_ ?_
  · refine Primrec.pair ?_ (Primrec.pair hq (emit (single (Primrec.succ.comp ht))))
    refine Primrec.list_append.comp ?_ hrest
    exact Primrec.list_map (Primrec.list_range.comp (har.comp ht))
      (h2env.comp Primrec.fst).to₂
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) ?_ ?_
  · exact Primrec.pair hrest (Primrec.pair hq (emit (Primrec.const [0])))
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) ?_ ?_
  · exact Primrec.pair (Primrec.list_cons.comp h2env (Primrec.list_cons.comp h2env hrest))
      (Primrec.pair hq (emit (Primrec.const [2, 0])))
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) ?_ ?_
  · exact Primrec.pair (Primrec.list_cons.comp (Primrec.pair (Primrec.const 3) henv) hrest)
      (Primrec.pair hq (emit (Primrec.const [2])))
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) ?_ ?_
  · exact Primrec.pair
      (Primrec.list_cons.comp (Primrec.pair (Primrec.nat_sub.comp (Primrec.const 1) htag) henv)
        (Primrec.list_cons.comp (Primrec.pair htag henv) hrest))
      (Primrec.pair hq (emit (Primrec.const [3])))
  · refine Primrec.pair (Primrec.list_cons.comp (Primrec.pair htag ?_) hrest)
      (Primrec.pair (Primrec.succ.comp hq) hout)
    exact Primrec.list_append.comp henv
      (single (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hq) htag))

theorem primrec_altScan (σ : Sig) : Primrec (altScan σ) := by
  unfold altScan
  have hfold : Primrec (fun l : List ℕ => l.foldl (afStep (arN σ)) (([(0, [])], 0, []) : AFSt)) :=
    Primrec.list_foldl Primrec.id (Primrec.const _)
      ((primrec_afStep (primrec_arN σ)).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp hfold))
    (Primrec.snd.comp (Primrec.snd.comp hfold))

/-! ### 5. Two-pass prefix formula evaluator (`lexFormula` + `evalOps`) -/

abbrev LexSt : Type := List (ℕ × List ℕ) × List (ℕ × List ℕ)

def lexStep (ar' : ℕ → ℕ) (s : LexSt) (t : ℕ) : LexSt :=
  let hd := s.1.headI
  let rest := s.1.tail
  let out := s.2
  if hd.1 = 1 then ((2, [t]) :: rest, out)
  else if hd.1 = 2 then (rest, out ++ [(1, hd.2 ++ [t])])
  else if hd.1 = 3 then
    if ar' t = 0 then (rest, out ++ [(2, [t])])
    else ((4 + (ar' t - 1), [t]) :: rest, out)
  else if hd.1 = 4 then (rest, out ++ [(2, hd.2 ++ [t])])
  else if 4 < hd.1 then ((hd.1 - 1, hd.2 ++ [t]) :: rest, out)
  else if t = 0 then (rest, out ++ [(0, [])])
  else if t = 1 then ((1, []) :: rest, out)
  else if t = 2 then ((3, []) :: rest, out)
  else if t = 3 then ((0, []) :: (0, []) :: rest, out ++ [(3, [])])
  else ((0, []) :: rest, out ++ [(4, [])])

def lexFormula (ar' : ℕ → ℕ) (toks : List ℕ) : List (ℕ × List ℕ) :=
  (toks.foldl (lexStep ar') ([(0, [])], [])).2

def opsOf {τ : Sig} : {n : ℕ} → τ.lang.BoundedFormula Empty n → List (ℕ × List ℕ)
  | _, .falsum => [(0, [])]
  | _, .equal t₁ t₂ => [(1, [encTerm t₁, encTerm t₂])]
  | _, .rel R ts => [(2, R.1.val :: List.ofFn (fun j => encTerm (ts j)))]
  | _, .imp f g => (3, []) :: (opsOf f ++ opsOf g)
  | _, .all f => (4, []) :: opsOf f

theorem lex_rel_args (ar' : ℕ → ℕ) :
    ∀ (k : ℕ) (cs acc : List ℕ) (rest out : List (ℕ × List ℕ)) (toks : List ℕ),
      cs.length = k + 1 →
      (cs ++ toks).foldl (lexStep ar') ((4 + k, acc) :: rest, out) =
        toks.foldl (lexStep ar') (rest, out ++ [(2, acc ++ cs)])
  | 0, c :: [], acc, rest, out, toks, _ => by
    simp [lexStep]
  | k + 1, c :: cs, acc, rest, out, toks, hlen => by
    have hlen' : cs.length = k + 1 := Nat.succ.inj hlen
    have hgt : 4 < 4 + (k + 1) := by omega
    have hne1 : 4 + (k + 1) ≠ 1 := by omega
    have hne2 : 4 + (k + 1) ≠ 2 := by omega
    have hne3 : 4 + (k + 1) ≠ 3 := by omega
    have hstep : lexStep ar' ((4 + (k + 1), acc) :: rest, out) c =
        ((4 + k, acc ++ [c]) :: rest, out) := by
      simp [lexStep, hne1, hne2, hne3, hgt]
    rw [List.cons_append, List.foldl_cons, hstep, lex_rel_args ar' k cs (acc ++ [c]) rest out toks hlen']
    simp [List.append_assoc]

theorem lexFormula_spec {τ : Sig} (ar' : ℕ → ℕ) (har : ∀ i : Fin τ.r, ar' i.val = τ.ar i) :
    ∀ {n : ℕ} (f : τ.lang.BoundedFormula Empty n) (rest out : List (ℕ × List ℕ)) (toks : List ℕ),
      (encF f ++ toks).foldl (lexStep ar') ((0, []) :: rest, out) =
        toks.foldl (lexStep ar') (rest, out ++ opsOf f)
  | _, .falsum, rest, out, toks => by
    simp [encF, opsOf, lexStep]
  | _, .equal t₁ t₂, rest, out, toks => by
    simp [encF, opsOf, lexStep]
  | _, .rel R ts, rest, out, toks => by
    rename_i n a
    have ha : ar' R.1.val = a := by rw [har R.1, R.2]
    rcases a with _ | k
    · simp [encF, opsOf, lexStep, ha]
    · have h1 : lexStep ar' ((0, []) :: rest, out) 2 = ((3, []) :: rest, out) := by simp [lexStep]
      have h2 : lexStep ar' ((3, []) :: rest, out) R.1.val =
          ((4 + k, [R.1.val]) :: rest, out) := by
        simp [lexStep, ha]
      rw [encF, List.cons_append, List.cons_append, List.foldl_cons, h1, List.foldl_cons, h2]
      have h3 := lex_rel_args ar' k (List.ofFn (fun j => encTerm (ts j))) [R.1.val] rest out toks
        (by simp)
      simpa [opsOf] using h3
  | _, .imp f g, rest, out, toks => by
    have h1 : lexStep ar' ((0, []) :: rest, out) 3 =
        ((0, []) :: (0, []) :: rest, out ++ [(3, [])]) := by simp [lexStep]
    rw [encF, List.cons_append, List.foldl_cons, h1, List.append_assoc,
      lexFormula_spec ar' har f, lexFormula_spec ar' har g]
    simp [opsOf, List.append_assoc]
  | _, .all f, rest, out, toks => by
    have h1 : lexStep ar' ((0, []) :: rest, out) 4 =
        ((0, []) :: rest, out ++ [(4, [])]) := by simp [lexStep]
    rw [encF, List.cons_append, List.foldl_cons, h1, lexFormula_spec ar' har f]
    simp [opsOf, List.append_assoc]

theorem lexFormula_encF {τ : Sig} (ar' : ℕ → ℕ) (har : ∀ i : Fin τ.r, ar' i.val = τ.ar i)
    {n : ℕ} (f : τ.lang.BoundedFormula Empty n) :
    lexFormula ar' (encF f) = opsOf f := by
  have h := lexFormula_spec ar' har f [] [] []
  simp only [List.append_nil, List.foldl_nil, List.nil_append] at h
  unfold lexFormula
  rw [h]

def evalOp (p : List ℕ → Bool) (op : ℕ × List ℕ) (stk : List Bool) : List Bool :=
  if op.1 = 0 then false :: stk
  else if op.1 = 1 then false :: stk
  else if op.1 = 2 then p op.2 :: stk
  else if op.1 = 3 then (!stk.headI || stk.tail.headI) :: stk.tail.tail
  else true :: stk.tail

def evalOps (p : List ℕ → Bool) (ops : List (ℕ × List ℕ)) (stk : List Bool) : List Bool :=
  ops.foldr (evalOp p) stk

def semVal {τ : Sig} (p : List ℕ → Bool) : {n : ℕ} → τ.lang.BoundedFormula Empty n → Bool
  | _, .falsum => false
  | _, .equal _ _ => false
  | _, .rel R ts => p (R.1.val :: List.ofFn (fun j => encTerm (ts j)))
  | _, .imp f g => !semVal p f || semVal p g
  | _, .all _ => true

theorem evalOps_opsOf {τ : Sig} (p : List ℕ → Bool) :
    ∀ {n : ℕ} (f : τ.lang.BoundedFormula Empty n) (stk : List Bool),
      evalOps p (opsOf f) stk = semVal p f :: stk
  | _, .falsum, stk => rfl
  | _, .equal _ _, stk => rfl
  | _, .rel _ _, stk => rfl
  | _, .imp f g, stk => by
    unfold opsOf evalOps
    rw [List.foldr_cons, List.foldr_append]
    change evalOp p (3, []) (evalOps p (opsOf f) (evalOps p (opsOf g) stk)) = _
    rw [evalOps_opsOf p g stk, evalOps_opsOf p f]
    rfl
  | _, .all f, stk => by
    unfold opsOf evalOps
    rw [List.foldr_cons]
    change evalOp p (4, []) (evalOps p (opsOf f) stk) = _
    rw [evalOps_opsOf p f stk]
    rfl

theorem primrec_lexStep {ar' : ℕ → ℕ} (har : Primrec ar') : Primrec₂ (lexStep ar') := by
  have hstk : Primrec (fun p : LexSt × ℕ => p.1.1) := Primrec.fst.comp Primrec.fst
  have hhd : Primrec (fun p : LexSt × ℕ => p.1.1.headI) := Primrec.list_headI.comp hstk
  have htag : Primrec (fun p : LexSt × ℕ => p.1.1.headI.1) := Primrec.fst.comp hhd
  have hacc : Primrec (fun p : LexSt × ℕ => p.1.1.headI.2) := Primrec.snd.comp hhd
  have hrest : Primrec (fun p : LexSt × ℕ => p.1.1.tail) := Primrec.list_tail.comp hstk
  have hout : Primrec (fun p : LexSt × ℕ => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun p : LexSt × ℕ => p.2) := Primrec.snd
  have single : ∀ {g : LexSt × ℕ → ℕ}, Primrec g → Primrec (fun p : LexSt × ℕ => [g p]) :=
    fun hg => Primrec.list_cons.comp hg (Primrec.const [])
  have hacc_t : Primrec (fun p : LexSt × ℕ => p.1.1.headI.2 ++ [p.2]) :=
    Primrec.list_append.comp hacc (single ht)
  have emitOp : ∀ (c : ℕ) {g : LexSt × ℕ → List ℕ}, Primrec g →
      Primrec (fun p : LexSt × ℕ => p.1.2 ++ [(c, g p)]) :=
    fun c {_} hg => Primrec.list_append.comp hout
      (Primrec.list_cons.comp (Primrec.pair (Primrec.const c) hg) (Primrec.const []))
  show Primrec (fun p : LexSt × ℕ => lexStep ar' p.1 p.2)
  unfold lexStep
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
    (Primrec.pair (Primrec.list_cons.comp (Primrec.pair (Primrec.const 2) (single ht)) hrest) hout) ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2))
    (Primrec.pair hrest (emitOp 1 hacc_t)) ?_
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3)) ?_ ?_
  · refine Primrec.ite (Primrec.eq.comp (har.comp ht) (Primrec.const 0))
      (Primrec.pair hrest (emitOp 2 (single ht))) ?_
    exact Primrec.pair (Primrec.list_cons.comp
      (Primrec.pair (Primrec.nat_add.comp (Primrec.const 4)
        (Primrec.nat_sub.comp (har.comp ht) (Primrec.const 1))) (single ht)) hrest) hout
  refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 4))
    (Primrec.pair hrest (emitOp 2 hacc_t)) ?_
  refine Primrec.ite (Primrec.nat_lt.comp (Primrec.const 4) htag)
    (Primrec.pair (Primrec.list_cons.comp
      (Primrec.pair (Primrec.nat_sub.comp htag (Primrec.const 1)) hacc_t) hrest) hout) ?_
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
    (Primrec.pair hrest (emitOp 0 (Primrec.const []))) ?_
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 1))
    (Primrec.pair (Primrec.list_cons.comp (Primrec.const (1, [])) hrest) hout) ?_
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 2))
    (Primrec.pair (Primrec.list_cons.comp (Primrec.const (3, [])) hrest) hout) ?_
  refine Primrec.ite (Primrec.eq.comp ht (Primrec.const 3))
    (Primrec.pair (Primrec.list_cons.comp (Primrec.const (0, []))
      (Primrec.list_cons.comp (Primrec.const (0, [])) hrest)) (emitOp 3 (Primrec.const []))) ?_
  exact Primrec.pair (Primrec.list_cons.comp (Primrec.const (0, [])) hrest)
    (emitOp 4 (Primrec.const []))

theorem primrec_lexFormula {ar' : ℕ → ℕ} (har : Primrec ar') : Primrec (lexFormula ar') := by
  unfold lexFormula
  exact Primrec.snd.comp (Primrec.list_foldl Primrec.id (Primrec.const ([(0, [])], []))
    ((primrec_lexStep har).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

theorem primrec_evalOps {α : Type} [Primcodable α] {p : α → List ℕ → Bool}
    {f : α → List (ℕ × List ℕ)} (hp : Primrec₂ p) (hf : Primrec f) :
    Primrec (fun a => (evalOps (p a) (f a) []).headD false) := by
  have hstep : Primrec₂ (fun (a : α) (q : (ℕ × List ℕ) × List Bool) => evalOp (p a) q.1 q.2) := by
    show Primrec (fun x : α × ((ℕ × List ℕ) × List Bool) => evalOp (p x.1) x.2.1 x.2.2)
    unfold evalOp
    have ha : Primrec (fun x : α × ((ℕ × List ℕ) × List Bool) => x.1) := Primrec.fst
    have hop : Primrec (fun x : α × ((ℕ × List ℕ) × List Bool) => x.2.1) :=
      Primrec.fst.comp Primrec.snd
    have htag : Primrec (fun x : α × ((ℕ × List ℕ) × List Bool) => x.2.1.1) :=
      Primrec.fst.comp hop
    have hargs : Primrec (fun x : α × ((ℕ × List ℕ) × List Bool) => x.2.1.2) :=
      Primrec.snd.comp hop
    have hstk : Primrec (fun x : α × ((ℕ × List ℕ) × List Bool) => x.2.2) :=
      Primrec.snd.comp Primrec.snd
    refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
      (Primrec.list_cons.comp (Primrec.const false) hstk) ?_
    refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 1))
      (Primrec.list_cons.comp (Primrec.const false) hstk) ?_
    refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 2))
      (Primrec.list_cons.comp (hp.comp ha hargs) hstk) ?_
    refine Primrec.ite (Primrec.eq.comp htag (Primrec.const 3))
      (Primrec.list_cons.comp
        (Primrec.or.comp (Primrec.not.comp (Primrec.list_headI.comp hstk))
          (Primrec.list_headI.comp (Primrec.list_tail.comp hstk)))
        (Primrec.list_tail.comp (Primrec.list_tail.comp hstk))) ?_
    exact Primrec.list_cons.comp (Primrec.const true) (Primrec.list_tail.comp hstk)
  have hfold : Primrec (fun a => evalOps (p a) (f a) []) :=
    Primrec.list_foldr hf (Primrec.const []) hstep
  exact ((Primrec.list_getD false).comp hfold (Primrec.const 0)).of_eq fun a => by
    cases evalOps (p a) (f a) [] <;> rfl

/-! ### 6. Semantic evaluation on empty structures and on matrix heads -/

def evalEmptyCode (σ : Sig) (mask : ℕ) (fcode : List ℕ) : Bool :=
  (evalOps (fun xs => unpackBit mask xs.headI) (lexFormula (arN σ) fcode) []).headD false

theorem primrec_evalEmptyCode (σ : Sig) : Primrec₂ (evalEmptyCode σ) := by
  show Primrec (fun p : ℕ × List ℕ => evalEmptyCode σ p.1 p.2)
  unfold evalEmptyCode
  refine primrec_evalOps ?_ ((primrec_lexFormula (primrec_arN σ)).comp Primrec.snd)
  exact (primrec_unpackBit.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.list_headI.comp Primrec.snd)).to₂

theorem empty_term_elim {σ : Sig} (t : σ.lang.Term (Empty ⊕ Fin 0)) : False := by
  match t with
  | .var (.inl e) => exact e.elim
  | .var (.inr j) => exact j.elim0
  | .func f _ => exact nomatch (show Empty from f)

theorem semVal_empty_iff {σ : Sig} {M : Type} [S : σ.lang.Structure M] [IsEmpty M] {mask : ℕ}
    (hmask : ∀ (i : Fin σ.r) (hi : σ.ar i = 0) (args : Fin 0 → M),
      unpackBit mask i.val = true ↔
        @FirstOrder.Language.Structure.RelMap σ.lang M S 0 ⟨i, hi⟩ args) :
    ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (_hn : n = 0) (v : Empty → M) (xs : Fin n → M),
      semVal (fun ys => unpackBit mask ys.headI) f = true ↔ f.Realize v xs
  | _, .falsum, _, _, _ => by
    show false = true ↔ False
    simp
  | _, .equal t₁ _, rfl, _, _ => False.elim (empty_term_elim t₁)
  | _, .rel R ts, rfl, v, xs => by
    rename_i a
    rcases a with _ | a
    · have hts : List.ofFn (fun j => encTerm (ts j)) = [] := by simp
      obtain ⟨i, hi⟩ := R
      change unpackBit mask (i.val :: List.ofFn (fun j => encTerm (ts j))).headI = true ↔
        @FirstOrder.Language.Structure.RelMap σ.lang M S 0 ⟨i, hi⟩
          (fun j => (ts j).realize (Sum.elim v xs))
      rw [hts]
      exact hmask i hi (fun j => (ts j).realize (Sum.elim v xs))
    · exact False.elim (empty_term_elim (ts 0))
  | _, .imp f g, hn, v, xs => by
    let p : List ℕ → Bool := fun ys => unpackBit mask ys.headI
    have ihf := semVal_empty_iff hmask f hn v xs
    have ihg := semVal_empty_iff hmask g hn v xs
    change (!semVal p f || semVal p g) = true ↔ (f.Realize v xs → g.Realize v xs)
    rw [← ihf, ← ihg]
    cases semVal p f <;> cases semVal p g <;> simp
  | _, .all f, _, v, xs => by
    simp only [semVal, BoundedFormula.realize_all, true_iff]
    intro a
    exact isEmptyElim a

theorem evalEmptyCode_spec {σ : Sig} {M : Type} [S : σ.lang.Structure M] [IsEmpty M] {mask : ℕ}
    (hmask : ∀ (i : Fin σ.r) (hi : σ.ar i = 0) (args : Fin 0 → M),
      unpackBit mask i.val = true ↔
        @FirstOrder.Language.Structure.RelMap σ.lang M S 0 ⟨i, hi⟩ args)
    (φ : σ.lang.Sentence) :
    evalEmptyCode σ mask (encF φ) = true ↔ M ⊨ φ := by
  unfold evalEmptyCode
  rw [lexFormula_encF (arN σ) (arN_val σ), evalOps_opsOf]
  exact semVal_empty_iff hmask φ rfl default default

/-! ### 7. Bijections for `Atom`, `Set`, `Fin n → Fin B`, and `HTh` -/

def atomOff (τ : Sig) (k i : ℕ) : ℕ :=
  listSum ((List.range i).map (fun j => k ^ (List.ofFn τ.ar).getD j 0))

def atomCnt (τ : Sig) (k : ℕ) : ℕ :=
  atomOff τ k τ.r

def encAtom (τ : Sig) (k : ℕ) (A : τ.Atom k) : ℕ :=
  atomOff τ k A.1.val + packList k (List.ofFn (fun j => (A.2 j).val))

theorem primrec_atomOff (τ : Sig) : Primrec₂ (atomOff τ) := by
  show Primrec (fun p : ℕ × ℕ => atomOff τ p.1 p.2)
  unfold atomOff
  refine primrec_listSum.comp ?_
  exact Primrec.list_map (Primrec.list_range.comp (@Primrec.snd ℕ ℕ _ _))
    (primrec_pow.comp (Primrec.fst.comp Primrec.fst)
      ((Primrec.list_getD 0).comp (Primrec.const (List.ofFn τ.ar)) Primrec.snd)).to₂

theorem primrec_atomCnt (τ : Sig) : Primrec (atomCnt τ) :=
  (primrec_atomOff τ).comp Primrec.id (Primrec.const τ.r)

theorem atomOff_succ (τ : Sig) (k : ℕ) (i : Fin τ.r) :
    atomOff τ k (i.val + 1) = atomOff τ k i.val + k ^ τ.ar i := by
  simp only [atomOff, listSum_eq_sum]
  rw [List.range_succ, List.map_append, List.sum_append]
  have hget : (List.ofFn τ.ar).getD i.val 0 = τ.ar i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
    simp
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hget]

theorem atomOff_mono (τ : Sig) (k : ℕ) {i₁ i₂ : ℕ} (h : i₁ ≤ i₂) :
    atomOff τ k i₁ ≤ atomOff τ k i₂ := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    simp only [atomOff, listSum_eq_sum] at ih ⊢
    rw [List.range_succ, List.map_append, List.sum_append]
    exact le_trans ih (Nat.le_add_right _ _)

theorem atomCnt_eq_sum (τ : Sig) (k : ℕ) :
    atomCnt τ k = ∑ i : Fin τ.r, k ^ τ.ar i := by
  have key : ∀ n ≤ τ.r, atomOff τ k n = ∑ i : Fin n, k ^ (List.ofFn τ.ar).getD i.val 0 := by
    intro n hn
    induction n with
    | zero => simp [atomOff, listSum_eq_sum]
    | succ n ih =>
      unfold atomOff
      rw [listSum_eq_sum, List.range_succ, List.map_append, List.sum_append, ← listSum_eq_sum]
      change atomOff τ k n + [k ^ (List.ofFn τ.ar).getD n 0].sum = _
      rw [ih (Nat.le_of_succ_le hn), Fin.sum_univ_castSucc]
      simp
  unfold atomCnt
  rw [key τ.r le_rfl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp

theorem encAtom_args_lt {a k : ℕ} (args : Fin a → Fin k) :
    packList k (List.ofFn (fun j => (args j).val)) < k ^ a := by
  rcases a with _ | a
  · simp
  · have hk : 0 < k := Nat.zero_lt_of_lt (args 0).isLt
    have h := @packList_lt k (List.ofFn (fun j => (args j).val)) (by
      intro d hd
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
      exact (args j).isLt)
    simpa using h

theorem encAtom_lt (τ : Sig) (k : ℕ) (A : τ.Atom k) : encAtom τ k A < atomCnt τ k := by
  unfold encAtom atomCnt
  calc atomOff τ k A.1.val + packList k (List.ofFn (fun j => (A.2 j).val))
      < atomOff τ k A.1.val + k ^ τ.ar A.1 := Nat.add_lt_add_left (encAtom_args_lt A.2) _
    _ = atomOff τ k (A.1.val + 1) := (atomOff_succ τ k A.1).symm
    _ ≤ atomOff τ k τ.r := atomOff_mono τ k A.1.isLt

theorem encAtom_injective (τ : Sig) (k : ℕ) : Function.Injective (encAtom τ k) := by
  rintro ⟨i₁, f₁⟩ ⟨i₂, f₂⟩ heq
  have hi : i₁ = i₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have h1 : encAtom τ k ⟨i₁, f₁⟩ < atomOff τ k (i₁.val + 1) := by
        unfold encAtom
        rw [atomOff_succ]
        exact Nat.add_lt_add_left (encAtom_args_lt f₁) _
      have h2 : atomOff τ k (i₁.val + 1) ≤ atomOff τ k i₂.val := atomOff_mono τ k hlt
      have h3 : atomOff τ k i₂.val ≤ encAtom τ k ⟨i₂, f₂⟩ := Nat.le_add_right _ _
      omega
    · have h1 : encAtom τ k ⟨i₂, f₂⟩ < atomOff τ k (i₂.val + 1) := by
        unfold encAtom
        rw [atomOff_succ]
        exact Nat.add_lt_add_left (encAtom_args_lt f₂) _
      have h2 : atomOff τ k (i₂.val + 1) ≤ atomOff τ k i₁.val := atomOff_mono τ k hgt
      have h3 : atomOff τ k i₁.val ≤ encAtom τ k ⟨i₁, f₁⟩ := Nat.le_add_right _ _
      omega
  subst hi
  have hp : packList k (List.ofFn (fun j => (f₁ j).val)) =
      packList k (List.ofFn (fun j => (f₂ j).val)) := by
    unfold encAtom at heq
    dsimp at heq
    omega
  have hf : f₁ = f₂ := by
    funext j
    ext
    have h1 := unpackBase_packList (B := k) (ds := List.ofFn (fun j' => (f₁ j').val))
      (fun d hd => by obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hd; exact (f₁ j').isLt)
      (i := j.val) (by simp [j.isLt])
    have h2 := unpackBase_packList (B := k) (ds := List.ofFn (fun j' => (f₂ j').val))
      (fun d hd => by obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hd; exact (f₂ j').isLt)
      (i := j.val) (by simp [j.isLt])
    rw [hp] at h1
    have h12 := h1.symm.trans h2
    simpa using h12
  subst hf
  rfl

noncomputable def atomEquiv (τ : Sig) (k : ℕ) : τ.Atom k ≃ Fin (atomCnt τ k) := by
  refine Equiv.ofBijective (fun A => ⟨encAtom τ k A, encAtom_lt τ k A⟩) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun A B h => encAtom_injective τ k (congrArg Fin.val h), ?_⟩
  rw [Fintype.card_sigma, Fintype.card_fin, atomCnt_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

@[simp] theorem atomEquiv_val (τ : Sig) (k : ℕ) (A : τ.Atom k) :
    (atomEquiv τ k A).val = encAtom τ k A := rfl

open Classical in
noncomputable def setEquivFin {α : Type} {M : ℕ} (e : α ≃ Fin M) : Set α ≃ Fin (2 ^ M) where
  toFun S := ⟨packBits M (fun i => if h : i < M then decide (e.symm ⟨i, h⟩ ∈ S) else false),
    packBits_lt M _⟩
  invFun c := {a | unpackBit c.val (e a).val = true}
  left_inv S := by
    ext a
    simp [unpackBit_packBits M _ (e a).isLt, (e a).isLt]
  right_inv c := by
    ext
    dsimp
    refine (packBits_congr (g := unpackBit c.val) fun i hi => ?_).trans (packBits_unpackBit c.isLt)
    simp [hi]

theorem mem_setEquivFin_symm {α : Type} {M : ℕ} (e : α ≃ Fin M) (c : Fin (2 ^ M)) (a : α) :
    a ∈ (setEquivFin e).symm c ↔ unpackBit c.val (e a).val = true := Iff.rfl

theorem unpackBit_setEquivFin {α : Type} {M : ℕ} (e : α ≃ Fin M) (S : Set α) (a : α) :
    unpackBit (setEquivFin e S).val (e a).val = true ↔ a ∈ S := by
  have := (setEquivFin e).left_inv S
  conv_rhs => rw [← this]
  rfl

def funEquivFin {n B : ℕ} (hB : 0 < B) : (Fin n → Fin B) ≃ Fin (B ^ n) where
  toFun f := ⟨packBase n B (fun i => if h : i < n then (f ⟨i, h⟩).val else 0),
    packBase_lt (Or.inl hB) (fun i hi => by simp [hi, (f ⟨i, hi⟩).isLt])⟩
  invFun c i := ⟨unpackBase B c.val i.val, Nat.mod_lt _ hB⟩
  left_inv f := by
    funext i
    ext
    dsimp
    rw [unpackBase_packBase (fun j hj => by simp [hj, (f ⟨j, hj⟩).isLt]) i.isLt]
    simp [i.isLt]
  right_inv c := by
    ext
    dsimp
    have hcongr : packBase n B (fun i => if i < n then unpackBase B c.val i else 0) =
        packBase n B (unpackBase B c.val) :=
      packBase_congr (fun i hi => by simp [hi])
    rw [hcongr, packBase_unpackBase hB c.isLt]

def prodEquivFin {n M : ℕ} (hM : 0 < M) : Fin n × Fin M ≃ Fin (n * M) where
  toFun p := ⟨p.2.val + M * p.1.val, by
    calc p.2.val + M * p.1.val
        < M + M * p.1.val := Nat.add_lt_add_right p.2.isLt _
      _ = M * (p.1.val + 1) := by ring
      _ ≤ M * n := Nat.mul_le_mul_left M p.1.isLt
      _ = n * M := Nat.mul_comm M n⟩
  invFun u := (⟨u.val / M, (Nat.div_lt_iff_lt_mul hM).2 u.isLt⟩, ⟨u.val % M, Nat.mod_lt _ hM⟩)
  left_inv p := by
    rcases p with ⟨x, y⟩
    ext <;> dsimp
    · rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_zero_iff.2 (Or.inr y.isLt), zero_add]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
  right_inv u := by
    ext
    dsimp
    exact Nat.mod_add_div u.val M

theorem tower_pos (w q : ℕ) : ∀ m : ℕ, 0 < tower w q m
  | 0 => Nat.two_pow_pos _
  | _ + 1 => Nat.two_pow_pos _

noncomputable def hthEquiv (τ : Sig) (n k : ℕ) :
    (m : ℕ) → HTh τ (Fin n) k m ≃ Fin (tower n (atomCnt τ k) m)
  | 0 => setEquivFin (setEquivFin (atomEquiv τ k))
  | m + 1 =>
    let M := tower n (atomCnt τ k) m
    have hM : 0 < M := tower_pos n (atomCnt τ k) m
    let pairEq : Fin n × HTh τ (Fin n) k m ≃ Fin (n * M) :=
      (Equiv.prodCongr (Equiv.refl (Fin n)) (hthEquiv τ n k m)).trans (prodEquivFin hM)
    let persEq : Set (Fin n × HTh τ (Fin n) k m) ≃ Fin (2 ^ (n * M)) := setEquivFin pairEq
    let famEq : Set (Set (Fin n × HTh τ (Fin n) k m)) ≃ Fin (2 ^ 2 ^ (n * M)) := setEquivFin persEq
    let hpow : (2 ^ 2 ^ (n * M)) ^ n = tower n (atomCnt τ k) (m + 1) := by
      show (2 ^ 2 ^ (n * M)) ^ n = 2 ^ (n * 2 ^ (n * M))
      rw [← pow_mul, Nat.mul_comm]
    ((Equiv.arrowCongr (Equiv.refl (Fin n)) famEq).trans (funEquivFin (Nat.two_pow_pos _))).trans
      (finCongr hpow)

/-! ### 8. Matrix-head evaluation on `setEquivFin (atomEquiv ...)` -/

def holdsMatCode (σ : Sig) (k : ℕ) (ψcode : List ℕ) (h : ℕ) : Bool :=
  (evalOps (fun xs => unpackBit h (atomOff (sigmaEq σ) k xs.headI + packList k xs.tail))
    (lexFormula (arEq σ) ψcode) []).headD false

theorem primrec_holdsMatCode (σ : Sig) :
    Primrec (fun p : ℕ × List ℕ × ℕ => holdsMatCode σ p.1 p.2.1 p.2.2) := by
  unfold holdsMatCode
  refine primrec_evalOps ?_
    ((primrec_lexFormula (primrec_arEq σ)).comp (Primrec.fst.comp Primrec.snd))
  have hk : Primrec (fun q : (ℕ × List ℕ × ℕ) × List ℕ => q.1.1) := Primrec.fst.comp Primrec.fst
  have hh : Primrec (fun q : (ℕ × List ℕ × ℕ) × List ℕ => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hxs : Primrec (fun q : (ℕ × List ℕ × ℕ) × List ℕ => q.2) := Primrec.snd
  exact (primrec_unpackBit.comp hh
    (Primrec.nat_add.comp ((primrec_atomOff (sigmaEq σ)).comp hk (Primrec.list_headI.comp hxs))
      (primrec_packList.comp hk (Primrec.list_tail.comp hxs)))).to₂

theorem term_inr {τ : Sig} {k : ℕ} (t : τ.lang.Term (Empty ⊕ Fin k)) :
    ∃ p : Fin k, t = Term.var (Sum.inr p) := by
  match t with
  | .var (.inl e) => exact e.elim
  | .var (.inr p) => exact ⟨p, rfl⟩
  | .func f _ => exact nomatch (show Empty from f)

theorem semVal_matrix_iff {τ : Sig} {k : ℕ} {ψ : τ.lang.BoundedFormula Empty k}
    (hqf : ψ.IsQF) (hef : EqFree ψ) (N : Set (τ.Atom k)) :
    semVal (fun xs => unpackBit (setEquivFin (atomEquiv τ k) N).val
      (atomOff τ k xs.headI + packList k xs.tail)) ψ = true ↔ Holds ψ N := by
  induction hqf with
  | falsum =>
    show false = true ↔ False
    simp
  | of_isAtomic hat =>
    cases hat with
    | equal _ _ => exact hef.elim
    | rel R ts =>
      obtain ⟨i, rfl⟩ := R
      choose p hp using fun j => term_inr (ts j)
      obtain rfl : ts = fun j => Term.var (Sum.inr (p j)) := funext hp
      show unpackBit (setEquivFin (atomEquiv τ k) N).val (encAtom τ k ⟨i, p⟩) = true ↔
        (⟨i, p⟩ : τ.Atom k) ∈ N
      exact unpackBit_setEquivFin (atomEquiv τ k) N ⟨i, p⟩
  | @imp f₁ f₂ h₁ h₂ ih₁ ih₂ =>
    let p : List ℕ → Bool := fun xs =>
      unpackBit (setEquivFin (atomEquiv τ k) N).val (atomOff τ k xs.headI + packList k xs.tail)
    have himp : Holds (f₁.imp f₂) N ↔ (Holds f₁ N → Holds f₂ N) := Iff.rfl
    change (!semVal p f₁ || semVal p f₂) = true ↔ Holds (f₁.imp f₂) N
    rw [himp, ← ih₁ hef.1, ← ih₂ hef.2]
    cases semVal p f₁ <;> cases semVal p f₂ <;> simp

theorem holdsMatCode_spec {σ : Sig} {k : ℕ} {ψ : (sigmaEq σ).lang.BoundedFormula Empty k}
    (hψ : IsMatrix ψ) (N : Set ((sigmaEq σ).Atom k)) :
    holdsMatCode σ k (encF ψ) (setEquivFin (atomEquiv (sigmaEq σ) k) N).val = true ↔ Holds ψ N := by
  unfold holdsMatCode
  rw [lexFormula_encF (arEq σ) (arEq_val σ), evalOps_opsOf]
  exact semVal_matrix_iff hψ.1 hψ.2 N

/-! ### 9. High-level `Primrec` combinators for `packBase`, `packBits`, `any`, `all` -/

theorem primrec_packBase {α : Type} [Primcodable α] {fn fB : α → ℕ} {g : α → ℕ → ℕ}
    (hn : Primrec fn) (hB : Primrec fB) (hg : Primrec₂ g) :
    Primrec (fun a => packBase (fn a) (fB a) (g a)) :=
  primrec_packList.comp hB (Primrec.list_map (Primrec.list_range.comp hn) hg)

theorem primrec_packBits {α : Type} [Primcodable α] {fn : α → ℕ} {g : α → ℕ → Bool}
    (hn : Primrec fn) (hg : Primrec₂ g) :
    Primrec (fun a => packBits (fn a) (g a)) :=
  primrec_packBase hn (Primrec.const 2) ((Primrec.dom_bool Bool.toNat).comp₂ hg)

theorem list_any_eq_foldr {β : Type} (l : List β) (p : β → Bool) :
    l.any p = l.foldr (fun b acc => p b || acc) false := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [List.any_cons, ih]

theorem list_all_eq_foldr {β : Type} (l : List β) (p : β → Bool) :
    l.all p = l.foldr (fun b acc => p b && acc) true := by
  induction l with
  | nil => rfl
  | cons b bs ih => simp [List.all_cons, ih]

theorem primrec_list_any {α β : Type} [Primcodable α] [Primcodable β]
    {fl : α → List β} {g : α → β → Bool} (hl : Primrec fl) (hg : Primrec₂ g) :
    Primrec (fun a => (fl a).any (g a)) :=
  (Primrec.list_foldr hl (Primrec.const false)
    (Primrec.or.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => by
    dsimp
    exact (list_any_eq_foldr (fl a) (g a)).symm

theorem primrec_list_all {α β : Type} [Primcodable α] [Primcodable β]
    {fl : α → List β} {g : α → β → Bool} (hl : Primrec fl) (hg : Primrec₂ g) :
    Primrec (fun a => (fl a).all (g a)) :=
  (Primrec.list_foldr hl (Primrec.const true)
    (Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun a => by
    dsimp
    exact (list_all_eq_foldr (fl a) (g a)).symm

theorem primrec_range_any {α : Type} [Primcodable α] {fn : α → ℕ} {g : α → ℕ → Bool}
    (hn : Primrec fn) (hg : Primrec₂ g) :
    Primrec (fun a => (List.range (fn a)).any (g a)) :=
  primrec_list_any (Primrec.list_range.comp hn) hg

theorem primrec_range_all {α : Type} [Primcodable α] {fn : α → ℕ} {g : α → ℕ → Bool}
    (hn : Primrec fn) (hg : Primrec₂ g) :
    Primrec (fun a => (List.range (fn a)).all (g a)) :=
  primrec_list_all (Primrec.list_range.comp hn) hg

theorem primrec_nat_beq : Primrec₂ ((· == ·) : ℕ → ℕ → Bool) := Primrec.beq

def singletonBits (K v : ℕ) : ℕ :=
  packBits K (fun i => i == v)

theorem primrec_singletonBits : Primrec₂ singletonBits := by
  show Primrec (fun p : ℕ × ℕ => singletonBits p.1 p.2)
  unfold singletonBits
  exact primrec_packBits Primrec.fst
    (primrec_nat_beq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂

open Classical in
theorem setEquivFin_val {α : Type} {M : ℕ} (e : α ≃ Fin M) (S : Set α) :
    (setEquivFin e S).val =
      packBits M (fun i => if h : i < M then decide (e.symm ⟨i, h⟩ ∈ S) else false) := rfl

open Classical in
theorem packBits_eq_singleton_setEquivFin {α : Type} {M : ℕ} (e : α ≃ Fin M) (x₀ : α) :
    packBits M (fun c => c == (e x₀).val) = (setEquivFin e ({x₀} : Set α)).val := by
  rw [setEquivFin_val]
  refine packBits_congr fun c hc => ?_
  rw [dif_pos hc]
  apply Bool.eq_iff_iff.2
  simp only [beq_iff_eq, decide_eq_true_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    apply e.injective
    rw [e.apply_symm_apply]
    ext
    exact h
  · intro h
    rw [← h]
    simp

/-! ### 10. Unfolding lemmas for `hthEquiv` at level `m + 1` -/

noncomputable def pairEquiv (τ : Sig) (n k m : ℕ) :
    Fin n × HTh τ (Fin n) k m ≃ Fin (n * tower n (atomCnt τ k) m) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) (hthEquiv τ n k m)).trans
    (prodEquivFin (tower_pos n (atomCnt τ k) m))

noncomputable def persEquiv (τ : Sig) (n k m : ℕ) :
    Set (Fin n × HTh τ (Fin n) k m) ≃ Fin (2 ^ (n * tower n (atomCnt τ k) m)) :=
  setEquivFin (pairEquiv τ n k m)

noncomputable def famEquiv (τ : Sig) (n k m : ℕ) :
    Set (Set (Fin n × HTh τ (Fin n) k m)) ≃ Fin (2 ^ 2 ^ (n * tower n (atomCnt τ k) m)) :=
  setEquivFin (persEquiv τ n k m)

theorem pairEquiv_val (τ : Sig) (n k m : ℕ) (yc : Fin n × HTh τ (Fin n) k m) :
    (pairEquiv τ n k m yc).val = (hthEquiv τ n k m yc.2).val + tower n (atomCnt τ k) m * yc.1.val :=
  rfl

theorem pairEquiv_symm_fst (τ : Sig) (n k m : ℕ) (u : Fin (n * tower n (atomCnt τ k) m)) :
    ((pairEquiv τ n k m).symm u).1.val = u.val / tower n (atomCnt τ k) m := rfl

theorem pairEquiv_symm_snd (τ : Sig) (n k m : ℕ) (u : Fin (n * tower n (atomCnt τ k) m)) :
    ((pairEquiv τ n k m).symm u).2 =
      (hthEquiv τ n k m).symm ⟨u.val % tower n (atomCnt τ k) m,
        Nat.mod_lt _ (tower_pos n (atomCnt τ k) m)⟩ := rfl

theorem hthEquiv_succ_val (τ : Sig) (n k m : ℕ) (H : HTh τ (Fin n) k (m + 1)) :
    (hthEquiv τ n k (m + 1) H).val =
      packBase n (2 ^ 2 ^ (n * tower n (atomCnt τ k) m))
        (fun x => if hx : x < n then (famEquiv τ n k m (H ⟨x, hx⟩)).val else 0) := rfl

theorem unpackBase_hthEquiv_succ (τ : Sig) (n k m : ℕ) (H : HTh τ (Fin n) k (m + 1)) (x : Fin n) :
    unpackBase (2 ^ 2 ^ (n * tower n (atomCnt τ k) m)) (hthEquiv τ n k (m + 1) H).val x.val =
      (famEquiv τ n k m (H x)).val := by
  rw [hthEquiv_succ_val,
    unpackBase_packBase (fun j hj => by simp [hj, (famEquiv τ n k m _).isLt]) x.isLt]
  simp [x.isLt]

/-! ### 11. `evalHThCode`: alternating evaluation on `hthEquiv` codes (factored) -/

def evalBaseCell (σ : Sig) (k : ℕ) (ψcode : List ℕ) (ac : ℕ) : Bool :=
  (List.range (2 ^ atomCnt (sigmaEq σ) k)).all
    (fun h => !unpackBit ac h || holdsMatCode σ k ψcode h)

def evalBase (σ : Sig) (k : ℕ) (ψcode : List ℕ) : ℕ × List Bool :=
  (2 ^ 2 ^ atomCnt (sigmaEq σ) k,
    (List.range (2 ^ 2 ^ atomCnt (sigmaEq σ) k)).map (evalBaseCell σ k ψcode))

def evalStepPers (n M : ℕ) (E : List Bool) (fx p : ℕ) : Bool :=
  !unpackBit fx p ||
    (List.range (n * M)).any (fun u => unpackBit p u && E.getD (u % M) false)

def evalStepX (n M : ℕ) (E : List Bool) (ac x : ℕ) : Bool :=
  (List.range (2 ^ (n * M))).all
    (evalStepPers n M E (unpackBase (2 ^ 2 ^ (n * M)) ac x))

def evalStepCell (n M : ℕ) (E : List Bool) (ac : ℕ) : Bool :=
  (List.range n).all (evalStepX n M E ac)

def evalStep (n : ℕ) (st : ℕ × List Bool) : ℕ × List Bool :=
  (2 ^ (n * 2 ^ (n * st.1)),
    (List.range (2 ^ (n * 2 ^ (n * st.1)))).map (evalStepCell n st.1 st.2))

def evalHThCode (σ : Sig) (n ℓ : ℕ) (ψcode : List ℕ) (hcode : ℕ) : Bool :=
  (((evalStep n)^[ℓ] (evalBase σ (2 * ℓ) ψcode)).2).getD hcode false

theorem primrec_evalBaseCell (σ : Sig) :
    Primrec (fun a : (ℕ × List ℕ) × ℕ => evalBaseCell σ a.1.1 a.1.2 a.2) := by
  unfold evalBaseCell
  let Dom := (ℕ × List ℕ) × ℕ
  have hk : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hψ : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp Primrec.fst
  have hac : Primrec (fun a : Dom => a.2) := Primrec.snd
  have h2q : Primrec (fun a : Dom => 2 ^ atomCnt (sigmaEq σ) a.1.1) :=
    primrec_pow.comp (Primrec.const 2) ((primrec_atomCnt (sigmaEq σ)).comp hk)
  refine primrec_range_all h2q ?_
  have ha1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hh1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (Primrec.or.comp (Primrec.not.comp (primrec_unpackBit.comp (hac.comp ha1) hh1))
    ((primrec_holdsMatCode σ).comp
      (Primrec.pair (hk.comp ha1) (Primrec.pair (hψ.comp ha1) hh1)))).to₂

theorem primrec_evalBase (σ : Sig) : Primrec₂ (evalBase σ) := by
  show Primrec (fun p : ℕ × List ℕ => evalBase σ p.1 p.2)
  unfold evalBase
  have hM0 : Primrec (fun p : ℕ × List ℕ => 2 ^ 2 ^ atomCnt (sigmaEq σ) p.1) :=
    primrec_pow.comp (Primrec.const 2)
      (primrec_pow.comp (Primrec.const 2) ((primrec_atomCnt (sigmaEq σ)).comp Primrec.fst))
  exact Primrec.pair hM0
    (Primrec.list_map (Primrec.list_range.comp hM0) (primrec_evalBaseCell σ).to₂)

theorem primrec_evalStepPers :
    Primrec (fun a : (ℕ × ℕ × List Bool × ℕ) × ℕ =>
      evalStepPers a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  unfold evalStepPers
  let Dom := (ℕ × ℕ × List Bool × ℕ) × ℕ
  have hn : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hM : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hE : Primrec (fun a : Dom => a.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hfx : Primrec (fun a : Dom => a.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hp : Primrec (fun a : Dom => a.2) := Primrec.snd
  refine Primrec.or.comp (Primrec.not.comp (primrec_unpackBit.comp hfx hp)) ?_
  refine primrec_range_any (Primrec.nat_mul.comp hn hM) ?_
  have ha1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hu1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (Primrec.and.comp (primrec_unpackBit.comp (hp.comp ha1) hu1)
    ((Primrec.list_getD false).comp (hE.comp ha1)
      (Primrec.nat_mod.comp hu1 (hM.comp ha1)))).to₂

theorem primrec_evalStepX :
    Primrec (fun a : (ℕ × ℕ × List Bool × ℕ) × ℕ =>
      evalStepX a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  unfold evalStepX
  let Dom := (ℕ × ℕ × List Bool × ℕ) × ℕ
  have hn : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hM : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hE : Primrec (fun a : Dom => a.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hac : Primrec (fun a : Dom => a.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hx : Primrec (fun a : Dom => a.2) := Primrec.snd
  have hP : Primrec (fun a : Dom => 2 ^ (a.1.1 * a.1.2.1)) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hn hM)
  have hfx : Primrec (fun a : Dom => unpackBase (2 ^ 2 ^ (a.1.1 * a.1.2.1)) a.1.2.2.2 a.2) :=
    primrec_unpackBase.comp
      (Primrec.pair (primrec_pow.comp (Primrec.const 2) hP) (Primrec.pair hac hx))
  refine primrec_range_all hP ?_
  have ha1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hp1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (primrec_evalStepPers.comp
    (Primrec.pair
      (Primrec.pair (hn.comp ha1)
        (Primrec.pair (hM.comp ha1) (Primrec.pair (hE.comp ha1) (hfx.comp ha1))))
      hp1)).to₂

theorem primrec_evalStepCell :
    Primrec (fun a : (ℕ × (ℕ × List Bool)) × ℕ => evalStepCell a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold evalStepCell
  let Dom := (ℕ × (ℕ × List Bool)) × ℕ
  have hn : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hM : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hE : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hac : Primrec (fun a : Dom => a.2) := Primrec.snd
  refine primrec_range_all hn ?_
  have ha1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hx1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (primrec_evalStepX.comp
    (Primrec.pair
      (Primrec.pair (hn.comp ha1)
        (Primrec.pair (hM.comp ha1) (Primrec.pair (hE.comp ha1) (hac.comp ha1))))
      hx1)).to₂

theorem primrec_evalStep : Primrec₂ evalStep := by
  show Primrec (fun a : ℕ × (ℕ × List Bool) => evalStep a.1 a.2)
  unfold evalStep
  have hn : Primrec (fun a : ℕ × (ℕ × List Bool) => a.1) := Primrec.fst
  have hM : Primrec (fun a : ℕ × (ℕ × List Bool) => a.2.1) := Primrec.fst.comp Primrec.snd
  have hM' : Primrec (fun a : ℕ × (ℕ × List Bool) => 2 ^ (a.1 * 2 ^ (a.1 * a.2.1))) :=
    primrec_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hn (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hn hM)))
  exact Primrec.pair hM' (Primrec.list_map (Primrec.list_range.comp hM') primrec_evalStepCell.to₂)

theorem primrec_evalHThCode (σ : Sig) :
    Primrec (fun p : ℕ × ℕ × List ℕ × ℕ => evalHThCode σ p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold evalHThCode
  have hn : Primrec (fun p : ℕ × ℕ × List ℕ × ℕ => p.1) := Primrec.fst
  have hℓ : Primrec (fun p : ℕ × ℕ × List ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hψ : Primrec (fun p : ℕ × ℕ × List ℕ × ℕ => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hhc : Primrec (fun p : ℕ × ℕ × List ℕ × ℕ => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinit : Primrec (fun p : ℕ × ℕ × List ℕ × ℕ => evalBase σ (2 * p.2.1) p.2.2.1) :=
    (primrec_evalBase σ).comp (Primrec.nat_mul.comp (Primrec.const 2) hℓ) hψ
  have hiter : Primrec (fun p : ℕ × ℕ × List ℕ × ℕ =>
      (evalStep p.1)^[p.2.1] (evalBase σ (2 * p.2.1) p.2.2.1)) :=
    Primrec.nat_iterate hℓ hinit (primrec_evalStep.comp (hn.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_getD false).comp (Primrec.snd.comp hiter) hhc

theorem evalIter_spec {σ : Sig} (n k : ℕ) {ψ : (sigmaEq σ).lang.BoundedFormula Empty k}
    (hψ : IsMatrix ψ) :
    ∀ m : ℕ,
      ((evalStep n)^[m] (evalBase σ k (encF ψ))).1 = tower n (atomCnt (sigmaEq σ) k) m ∧
      ((evalStep n)^[m] (evalBase σ k (encF ψ))).2.length = tower n (atomCnt (sigmaEq σ) k) m ∧
      ∀ H : HTh (sigmaEq σ) (Fin n) k m,
        (((evalStep n)^[m] (evalBase σ k (encF ψ))).2.getD
          (hthEquiv (sigmaEq σ) n k m H).val false = true ↔ eval ψ m H)
  | 0 => by
    simp only [Function.iterate_zero, id_eq]
    let τ := sigmaEq σ
    let q := atomCnt τ k
    refine ⟨rfl, by simp [evalBase, tower], fun H => ?_⟩
    have hlt : (hthEquiv τ n k 0 H).val < (evalBase σ k (encF ψ)).2.length := by
      simp only [evalBase, List.length_map, List.length_range]
      exact (hthEquiv τ n k 0 H).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    simp only [evalBase, evalBaseCell, List.getElem_map, List.getElem_range, List.all_eq_true,
      List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
    show (∀ h < 2 ^ q, unpackBit (hthEquiv τ n k 0 H).val h = false ∨
        holdsMatCode σ k (encF ψ) h = true) ↔ ∀ N ∈ HTh.hyps H, Holds ψ N
    constructor
    · intro hall N hN
      let hc := setEquivFin (atomEquiv τ k) N
      have hmem : unpackBit (hthEquiv τ n k 0 H).val hc.val = true :=
        (unpackBit_setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps H) N).2 hN
      rcases hall hc.val hc.isLt with hf | ht
      · rw [hmem] at hf; cases hf
      · exact (holdsMatCode_spec hψ N).1 ht
    · intro hall h hh
      by_cases hb : unpackBit (hthEquiv τ n k 0 H).val h = true
      · right
        let N := (setEquivFin (atomEquiv τ k)).symm ⟨h, hh⟩
        have hcode : (setEquivFin (atomEquiv τ k) N).val = h := by simp [N]
        have hN : N ∈ HTh.hyps H := by
          have := unpackBit_setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps H) N
          rw [hcode] at this; exact this.1 hb
        rw [← hcode]
        exact (holdsMatCode_spec hψ N).2 (hall N hN)
      · left; exact Bool.eq_false_iff.2 hb
  | m + 1 => by
    let τ := sigmaEq σ
    let q := atomCnt τ k
    let M := tower n q m
    rw [Function.iterate_succ_apply']
    generalize hst : (evalStep n)^[m] (evalBase σ k (encF ψ)) = st
    have ih_full := evalIter_spec n k hψ m
    rw [hst] at ih_full
    obtain ⟨hM, _, ih⟩ := ih_full
    have hM_eq : st.1 = M := hM
    refine ⟨by simp [evalStep, hM_eq, M, tower, q, τ],
      by simp [evalStep, hM_eq, M, tower, q, τ], fun H => ?_⟩
    have hlt : (hthEquiv τ n k (m + 1) H).val < (evalStep n st).2.length := by
      simp only [evalStep, List.length_map, List.length_range, hM_eq]
      exact (hthEquiv τ n k (m + 1) H).isLt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    simp only [evalStep, evalStepCell, evalStepX, evalStepPers, hM_eq, List.getElem_map,
      List.getElem_range, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.and_eq_true, Bool.not_eq_true']
    change (∀ x < n, ∀ p < 2 ^ (n * M),
        unpackBit (unpackBase (2 ^ 2 ^ (n * M)) (hthEquiv τ n k (m + 1) H).val x) p = false ∨
        ∃ u < n * M, unpackBit p u = true ∧ st.2.getD (u % M) false = true) ↔
      ∀ (x' : Fin n), ∀ p ∈ H x', ∃ c ∈ p, eval ψ m c.2
    constructor
    · intro hall x' pset hpset
      have hfx := unpackBase_hthEquiv_succ τ n k m H x'
      let pc := persEquiv τ n k m pset
      have hmem_p : unpackBit (famEquiv τ n k m (H x')).val pc.val = true :=
        (unpackBit_setEquivFin (persEquiv τ n k m) (H x') pset).2 hpset
      rcases hall x'.val x'.isLt pc.val pc.isLt with hf | ⟨u, hu, hpu, heu⟩
      · rw [hfx, hmem_p] at hf; cases hf
      · let yc := (pairEquiv τ n k m).symm ⟨u, hu⟩
        have hyc_code : (pairEquiv τ n k m yc).val = u := by simp [yc]
        have hyc_mem : yc ∈ pset := by
          have := unpackBit_setEquivFin (pairEquiv τ n k m) pset yc
          rw [hyc_code] at this; exact this.1 hpu
        have hc2_code : (hthEquiv τ n k m yc.2).val = u % M := by
          rw [pairEquiv_symm_snd]; simp [M, q, τ]
        rw [← hc2_code] at heu
        exact ⟨yc, hyc_mem, (ih yc.2).1 heu⟩
    · intro hall x hx p hp
      let x' : Fin n := ⟨x, hx⟩
      have hfx := unpackBase_hthEquiv_succ τ n k m H x'
      change unpackBit (unpackBase _ _ x'.val) p = false ∨ _
      rw [hfx]
      by_cases hpb : unpackBit (famEquiv τ n k m (H x')).val p = true
      · right
        let pset := (persEquiv τ n k m).symm ⟨p, hp⟩
        have hp_code : (persEquiv τ n k m pset).val = p := by simp [pset]
        have hpset : pset ∈ H x' := by
          have := unpackBit_setEquivFin (persEquiv τ n k m) (H x') pset
          rw [hp_code] at this; exact this.1 hpb
        obtain ⟨yc, hyc_mem, heval⟩ := hall x' pset hpset
        let u := pairEquiv τ n k m yc
        refine ⟨u.val, u.isLt, ?_, ?_⟩
        · have := (unpackBit_setEquivFin (pairEquiv τ n k m) pset yc).2 hyc_mem
          change (setEquivFin (pairEquiv τ n k m) pset).val = p at hp_code
          rw [hp_code] at this
          exact this
        · have umod : u.val % M = (hthEquiv τ n k m yc.2).val := by
            show ((hthEquiv τ n k m yc.2).val + M * yc.1.val) % M = _
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hthEquiv τ n k m yc.2).isLt]
          rw [umod]
          exact (ih yc.2).2 heval
      · left; exact Bool.eq_false_iff.2 hpb

theorem evalHThCode_spec {σ : Sig} (n ℓ : ℕ) {ψ : (sigmaEq σ).lang.BoundedFormula Empty (2 * ℓ)}
    (hψ : IsMatrix ψ) (H : HTh (sigmaEq σ) (Fin n) (2 * ℓ) ℓ) :
    evalHThCode σ n ℓ (encF ψ) (hthEquiv (sigmaEq σ) n (2 * ℓ) ℓ H).val = true ↔ eval ψ ℓ H :=
  (evalIter_spec n (2 * ℓ) hψ ℓ).2.2 H

/-! ### 12. `leafHThCode`: full-strategy induced hypothetical on a bag (factored) -/

def leafHeadAtomArgs (n u k i t : ℕ) (σ : Sig) : List ℕ :=
  (List.range (arEq σ i)).map (fun j => unpackBase n u (unpackBase k t j))

def leafHeadBit (σ : Sig) (bcode : List ℕ) (k u a : ℕ) : Bool :=
  (List.range (sigmaEq σ).r).any (fun i =>
    (List.range (k ^ arEq σ i)).any (fun t =>
      (atomOff (sigmaEq σ) k i + t == a) &&
        bagEqRelBit σ bcode i (leafHeadAtomArgs bcode.headI u k i t σ)))

def leafHeadCode (σ : Sig) (bcode : List ℕ) (k u : ℕ) : ℕ :=
  packBits (atomCnt (sigmaEq σ) k) (leafHeadBit σ bcode k u)

def leafBaseCell (σ : Sig) (bcode : List ℕ) (k u : ℕ) : ℕ :=
  singletonBits (2 ^ atomCnt (sigmaEq σ) k) (leafHeadCode σ bcode k u)

def leafBase (σ : Sig) (bcode : List ℕ) (k : ℕ) : ℕ × ℕ × List ℕ :=
  (k, 2 ^ 2 ^ atomCnt (sigmaEq σ) k,
    (List.range (bcode.headI ^ k)).map (leafBaseCell σ bcode k))

def leafStepPers (n len' M : ℕ) (L : List ℕ) (u x : ℕ) : ℕ :=
  packBits (n * M) (fun pu =>
    (List.range n).any (fun y => L.getD (u + n ^ len' * (x + n * y)) 0 + M * y == pu))

def leafStepFam (n len' M : ℕ) (L : List ℕ) (u x : ℕ) : ℕ :=
  singletonBits (2 ^ (n * M)) (leafStepPers n len' M L u x)

def leafStepCell (n len' M : ℕ) (L : List ℕ) (u : ℕ) : ℕ :=
  packBase n (2 ^ 2 ^ (n * M)) (leafStepFam n len' M L u)

def leafStep (n : ℕ) (st : ℕ × ℕ × List ℕ) : ℕ × ℕ × List ℕ :=
  (st.1 - 2, 2 ^ (n * 2 ^ (n * st.2.1)),
    (List.range (n ^ (st.1 - 2))).map (leafStepCell n (st.1 - 2) st.2.1 st.2.2))

def leafHThCode (σ : Sig) (bcode : List ℕ) (ℓ : ℕ) : ℕ :=
  (((leafStep bcode.headI)^[ℓ] (leafBase σ bcode (2 * ℓ))).2.2).getD 0 0

theorem primrec_leafHeadAtomArgs (σ : Sig) :
    Primrec (fun a : ℕ × ℕ × ℕ × ℕ × ℕ =>
      leafHeadAtomArgs a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 σ) := by
  unfold leafHeadAtomArgs
  let Dom := ℕ × ℕ × ℕ × ℕ × ℕ
  have hn : Primrec (fun a : Dom => a.1) := Primrec.fst
  have hu : Primrec (fun a : Dom => a.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun a : Dom => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun a : Dom => a.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec (fun a : Dom => a.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  refine Primrec.list_map (Primrec.list_range.comp ((primrec_arEq σ).comp hi)) ?_
  have ha1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hj1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  have inner : Primrec (fun b : Dom × ℕ => unpackBase b.1.2.2.1 b.1.2.2.2.2 b.2) :=
    primrec_unpackBase.comp (Primrec.pair (hk.comp ha1) (Primrec.pair (ht.comp ha1) hj1))
  exact (primrec_unpackBase.comp
    (Primrec.pair (hn.comp ha1) (Primrec.pair (hu.comp ha1) inner))).to₂

theorem primrec_leafHeadBit (σ : Sig) :
    Primrec (fun a : (List ℕ × ℕ × ℕ) × ℕ => leafHeadBit σ a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold leafHeadBit
  let Dom := (List ℕ × ℕ × ℕ) × ℕ
  have hb : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hk : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hu : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun a : Dom => a.2) := Primrec.snd
  refine primrec_range_any (Primrec.const (sigmaEq σ).r) ?_
  have hd1 : Primrec (fun x : Dom × ℕ => x.1) := Primrec.fst
  have hi1 : Primrec (fun x : Dom × ℕ => x.2) := Primrec.snd
  have hinner : Primrec (fun x : Dom × ℕ =>
      (List.range (x.1.1.2.1 ^ arEq σ x.2)).any (fun t =>
        (atomOff (sigmaEq σ) x.1.1.2.1 x.2 + t == x.1.2) &&
          bagEqRelBit σ x.1.1.1 x.2
            (leafHeadAtomArgs x.1.1.1.headI x.1.1.2.2 x.1.1.2.1 x.2 t σ))) := by
    refine primrec_range_any (primrec_pow.comp (hk.comp hd1) ((primrec_arEq σ).comp hi1)) ?_
    have hx2 : Primrec (fun y : (Dom × ℕ) × ℕ => y.1) := Primrec.fst
    have ht2 : Primrec (fun y : (Dom × ℕ) × ℕ => y.2) := Primrec.snd
    have hd2 := hd1.comp hx2
    have hi2 := hi1.comp hx2
    have heqA : Primrec (fun y : (Dom × ℕ) × ℕ =>
        atomOff (sigmaEq σ) y.1.1.1.2.1 y.1.2 + y.2 == y.1.1.2) :=
      primrec_nat_beq.comp (Primrec.nat_add.comp
        ((primrec_atomOff (sigmaEq σ)).comp (hk.comp hd2) hi2) ht2) (ha.comp hd2)
    have hargs : Primrec (fun y : (Dom × ℕ) × ℕ =>
        leafHeadAtomArgs y.1.1.1.1.headI y.1.1.1.2.2 y.1.1.1.2.1 y.1.2 y.2 σ) :=
      (primrec_leafHeadAtomArgs σ).comp
        (Primrec.pair (Primrec.list_headI.comp (hb.comp hd2))
          (Primrec.pair (hu.comp hd2)
            (Primrec.pair (hk.comp hd2) (Primrec.pair hi2 ht2))))
    exact (Primrec.and.comp heqA
      ((primrec_bagEqRelBit σ).comp (Primrec.pair (hb.comp hd2) (Primrec.pair hi2 hargs)))).to₂
  exact hinner.to₂

theorem primrec_leafHeadCode (σ : Sig) :
    Primrec (fun p : List ℕ × ℕ × ℕ => leafHeadCode σ p.1 p.2.1 p.2.2) := by
  unfold leafHeadCode
  exact primrec_packBits
    ((primrec_atomCnt (sigmaEq σ)).comp (Primrec.fst.comp Primrec.snd))
    (primrec_leafHeadBit σ).to₂

theorem primrec_leafBaseCell (σ : Sig) :
    Primrec (fun a : (List ℕ × ℕ) × ℕ => leafBaseCell σ a.1.1 a.1.2 a.2) := by
  unfold leafBaseCell
  let Dom := (List ℕ × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have hb : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have hk : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have hu : Primrec (fun a : Dom => a.2) := Primrec.snd
  have h2q : Primrec (fun a : Dom => 2 ^ atomCnt (sigmaEq σ) a.1.2) :=
    primrec_pow.comp (Primrec.const 2) ((primrec_atomCnt (sigmaEq σ)).comp hk)
  have hh : Primrec (fun a : Dom => leafHeadCode σ a.1.1 a.1.2 a.2) :=
    (primrec_leafHeadCode σ).comp (Primrec.pair hb (Primrec.pair hk hu))
  exact primrec_singletonBits.comp h2q hh

theorem primrec_leafBase (σ : Sig) : Primrec₂ (leafBase σ) := by
  show Primrec (fun p : List ℕ × ℕ => leafBase σ p.1 p.2)
  unfold leafBase
  have hn : Primrec (fun p : List ℕ × ℕ => p.1.headI) := Primrec.list_headI.comp Primrec.fst
  have hk : Primrec (fun p : List ℕ × ℕ => p.2) := Primrec.snd
  have hM0 : Primrec (fun p : List ℕ × ℕ => 2 ^ 2 ^ atomCnt (sigmaEq σ) p.2) :=
    primrec_pow.comp (Primrec.const 2)
      (primrec_pow.comp (Primrec.const 2) ((primrec_atomCnt (sigmaEq σ)).comp hk))
  exact Primrec.pair hk (Primrec.pair hM0
    (Primrec.list_map (Primrec.list_range.comp (primrec_pow.comp hn hk))
      (primrec_leafBaseCell σ).to₂))

theorem primrec_leafStepPers :
    Primrec (fun a : ((ℕ × ℕ × ℕ × List ℕ) × ℕ) × ℕ =>
      leafStepPers a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.1.2.2.2 a.1.2 a.2) := by
  unfold leafStepPers
  let Dom := ((ℕ × ℕ × ℕ × List ℕ) × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have ha11 : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have ha112 : Primrec (fun a : Dom => a.1.1.2) := Primrec.snd.comp ha11
  have ha1122 : Primrec (fun a : Dom => a.1.1.2.2) := Primrec.snd.comp ha112
  have hn : Primrec (fun a : Dom => a.1.1.1) := Primrec.fst.comp ha11
  have hlen' : Primrec (fun a : Dom => a.1.1.2.1) := Primrec.fst.comp ha112
  have hM : Primrec (fun a : Dom => a.1.1.2.2.1) := Primrec.fst.comp ha1122
  have hL : Primrec (fun a : Dom => a.1.1.2.2.2) := Primrec.snd.comp ha1122
  have hu : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have hx : Primrec (fun a : Dom => a.2) := Primrec.snd
  refine primrec_packBits (Primrec.nat_mul.comp hn hM) ?_
  have hd1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hpu1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  have hinner : Primrec (fun b : Dom × ℕ =>
      (List.range b.1.1.1.1).any (fun y =>
        b.1.1.1.2.2.2.getD (b.1.1.2 + b.1.1.1.1 ^ b.1.1.1.2.1 * (b.1.2 + b.1.1.1.1 * y)) 0 +
          b.1.1.1.2.2.1 * y == b.2)) := by
    refine primrec_range_any (hn.comp hd1) ?_
    have hb2 : Primrec (fun c : (Dom × ℕ) × ℕ => c.1) := Primrec.fst
    have hy2 : Primrec (fun c : (Dom × ℕ) × ℕ => c.2) := Primrec.snd
    have hd2 := hd1.comp hb2
    have hidx : Primrec (fun c : (Dom × ℕ) × ℕ =>
        c.1.1.1.2 + c.1.1.1.1.1 ^ c.1.1.1.1.2.1 * (c.1.1.2 + c.1.1.1.1.1 * c.2)) :=
      Primrec.nat_add.comp (hu.comp hd2)
        (Primrec.nat_mul.comp (primrec_pow.comp (hn.comp hd2) (hlen'.comp hd2))
          (Primrec.nat_add.comp (hx.comp hd2) (Primrec.nat_mul.comp (hn.comp hd2) hy2)))
    have hval : Primrec (fun c : (Dom × ℕ) × ℕ =>
        c.1.1.1.1.2.2.2.getD
            (c.1.1.1.2 + c.1.1.1.1.1 ^ c.1.1.1.1.2.1 * (c.1.1.2 + c.1.1.1.1.1 * c.2)) 0 +
          c.1.1.1.1.2.2.1 * c.2) :=
      Primrec.nat_add.comp ((Primrec.list_getD 0).comp (hL.comp hd2) hidx)
        (Primrec.nat_mul.comp (hM.comp hd2) hy2)
    exact (primrec_nat_beq.comp hval (hpu1.comp hb2)).to₂
  exact hinner.to₂

theorem primrec_leafStepFam :
    Primrec (fun a : ((ℕ × ℕ × ℕ × List ℕ) × ℕ) × ℕ =>
      leafStepFam a.1.1.1 a.1.1.2.1 a.1.1.2.2.1 a.1.1.2.2.2 a.1.2 a.2) := by
  unfold leafStepFam
  let Dom := ((ℕ × ℕ × ℕ × List ℕ) × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have ha11 : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have hn : Primrec (fun a : Dom => a.1.1.1) := Primrec.fst.comp ha11
  have ha112 : Primrec (fun a : Dom => a.1.1.2) := Primrec.snd.comp ha11
  have ha1122 : Primrec (fun a : Dom => a.1.1.2.2) := Primrec.snd.comp ha112
  have hM : Primrec (fun a : Dom => a.1.1.2.2.1) := Primrec.fst.comp ha1122
  have hP : Primrec (fun a : Dom => 2 ^ (a.1.1.1 * a.1.1.2.2.1)) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hn hM)
  exact primrec_singletonBits.comp hP primrec_leafStepPers

theorem primrec_leafStepCell :
    Primrec (fun a : (ℕ × ℕ × ℕ × List ℕ) × ℕ =>
      leafStepCell a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  unfold leafStepCell
  let Dom := (ℕ × ℕ × ℕ × List ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have ha12 : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have ha122 : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp ha12
  have hn : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have hM : Primrec (fun a : Dom => a.1.2.2.1) := Primrec.fst.comp ha122
  have hFm : Primrec (fun a : Dom => 2 ^ 2 ^ (a.1.1 * a.1.2.2.1)) :=
    primrec_pow.comp (Primrec.const 2)
      (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hn hM))
  exact primrec_packBase hn hFm primrec_leafStepFam.to₂

theorem primrec_leafStep : Primrec₂ leafStep := by
  show Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => leafStep a.1 a.2)
  unfold leafStep
  have hn : Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => a.1) := Primrec.fst
  have hlen' : Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => a.2.1 - 2) :=
    Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)
  have hM : Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hL : Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hM' : Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => 2 ^ (a.1 * 2 ^ (a.1 * a.2.2.1))) :=
    primrec_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hn (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hn hM)))
  have hcfg : Primrec (fun a : ℕ × (ℕ × ℕ × List ℕ) => (a.1, a.2.1 - 2, a.2.2.1, a.2.2.2)) :=
    Primrec.pair hn (Primrec.pair hlen' (Primrec.pair hM hL))
  exact Primrec.pair hlen' (Primrec.pair hM'
    (Primrec.list_map (Primrec.list_range.comp (primrec_pow.comp hn hlen'))
      (primrec_leafStepCell.comp (Primrec.pair (hcfg.comp Primrec.fst) Primrec.snd)).to₂))

theorem primrec_leafHThCode (σ : Sig) : Primrec₂ (leafHThCode σ) := by
  show Primrec (fun p : List ℕ × ℕ => leafHThCode σ p.1 p.2)
  unfold leafHThCode
  have hb : Primrec (fun p : List ℕ × ℕ => p.1) := Primrec.fst
  have hℓ : Primrec (fun p : List ℕ × ℕ => p.2) := Primrec.snd
  have hn : Primrec (fun p : List ℕ × ℕ => p.1.headI) := Primrec.list_headI.comp hb
  have hinit : Primrec (fun p : List ℕ × ℕ => leafBase σ p.1 (2 * p.2)) :=
    (primrec_leafBase σ).comp hb (Primrec.nat_mul.comp (Primrec.const 2) hℓ)
  have hiter : Primrec (fun p : List ℕ × ℕ =>
      (leafStep p.1.headI)^[p.2] (leafBase σ p.1 (2 * p.2))) :=
    Primrec.nat_iterate hℓ hinit (primrec_leafStep.comp (hn.comp Primrec.fst) Primrec.snd).to₂
  exact (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp hiter)) (Primrec.const 0)

theorem unpackBase_lt {k : ℕ} (hk : 0 < k) (t j : ℕ) : unpackBase k t j < k :=
  Nat.mod_lt _ hk

open Classical in
theorem leafHeadCode_spec {σ : Sig} (B : Bag σ) (k : ℕ) (l : List (Fin B.withEq.n))
    (hl : l.length = k) :
    leafHeadCode σ (encBag B) k (packList B.withEq.n (l.map Fin.val)) =
      (setEquivFin (atomEquiv (sigmaEq σ) k) (atomsOf (sigmaEq σ) k l)).val := by
  unfold leafHeadCode leafHeadBit leafHeadAtomArgs
  rw [setEquivFin_val]
  refine packBits_congr fun a ha => ?_
  rw [dif_pos ha]
  have hA_val : encAtom (sigmaEq σ) k ((atomEquiv (sigmaEq σ) k).symm ⟨a, ha⟩) = a := by
    change (atomEquiv (sigmaEq σ) k ((atomEquiv (sigmaEq σ) k).symm ⟨a, ha⟩)).val = a
    simp
  generalize hA_def : (atomEquiv (sigmaEq σ) k).symm ⟨a, ha⟩ = A at hA_val ⊢
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, t, ht, hsum, hrel⟩
    let i' : Fin (sigmaEq σ).r := ⟨i, hi⟩
    have har_i : arEq σ i = (sigmaEq σ).ar i' := arEq_val σ i'
    rw [har_i] at ht hrel
    have hj_lt_k : ∀ j : Fin ((sigmaEq σ).ar i'), unpackBase k t j.val < k := by
      intro j
      rcases eq_or_ne k 0 with rfl | hk0
      · rcases eq_or_ne ((sigmaEq σ).ar i') 0 with har0 | har0
        · exact absurd j.isLt (by omega)
        · exfalso; rw [zero_pow har0] at ht; omega
      · exact unpackBase_lt (Nat.pos_of_ne_zero hk0) t j.val
    have hA_eq : A = ⟨i', fun j => ⟨unpackBase k t j.val, hj_lt_k j⟩⟩ := by
      apply encAtom_injective (sigmaEq σ) k
      rw [hA_val]
      unfold encAtom
      have hpack_t : packList k (List.ofFn (fun j : Fin ((sigmaEq σ).ar i') => unpackBase k t j.val)) = t := by
        rcases eq_or_ne ((sigmaEq σ).ar i') 0 with har0 | har0
        · have ht1 : t < 1 := by simpa [har0] using ht
          have ht0 : t = 0 := by omega
          subst ht0
          have hnil : List.ofFn (fun j : Fin ((sigmaEq σ).ar i') => unpackBase k 0 j.val) = [] := by
            rw [List.ofFn_eq_nil_iff]; exact har0
          rw [hnil]
          rfl
        · have hk0 : 0 < k := by
            by_contra hk0
            have hkz : k = 0 := by omega
            rw [hkz, zero_pow har0] at ht
            omega
          have hfn : List.ofFn (fun j : Fin ((sigmaEq σ).ar i') => unpackBase k t j.val) =
              (List.range ((sigmaEq σ).ar i')).map (unpackBase k t) := by
            apply List.ext_getElem <;> simp
          rw [hfn]
          exact packBase_unpackBase hk0 ht
      rw [hpack_t]
      exact hsum.symm
    rw [hA_eq]
    have hj_lt_l : ∀ j : Fin ((sigmaEq σ).ar i'), unpackBase k t j.val < l.length := by
      intro j; rw [hl]; exact hj_lt_k j
    let args : Fin ((sigmaEq σ).ar i') → Fin B.withEq.n := fun j => l[unpackBase k t j.val]'(hj_lt_l j)
    refine ⟨args, fun j => ?_, ?_⟩
    · simp [args]
    · have hmap_eq : (List.range ((sigmaEq σ).ar i')).map
          (fun j => unpackBase (encBag B).headI (packList B.withEq.n (l.map Fin.val)) (unpackBase k t j)) =
          List.ofFn (fun j => (args j).val) := by
        apply List.ext_getElem
        · simp
        · intro j hj1 hj2
          simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, args]
          have hj' : j < (sigmaEq σ).ar i' := by simpa using hj1
          have hlt_l : unpackBase k t j < (l.map Fin.val).length := by
            rw [List.length_map]; exact hj_lt_l ⟨j, hj'⟩
          change unpackBase B.withEq.n (packList B.withEq.n (l.map Fin.val)) (unpackBase k t j) =
            (l[unpackBase k t j]'(hj_lt_l ⟨j, hj'⟩)).val
          have hu_unp := unpackBase_packList (B := B.withEq.n) (ds := l.map Fin.val)
            (fun d hd => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact x.isLt) hlt_l
          simpa using hu_unp
      rw [hmap_eq] at hrel
      exact (bagEqRelBit_encBag B i' args).1 hrel
  · rintro ⟨args, hargs, hholds⟩
    let t := packList k (List.ofFn (fun j => (A.2 j).val))
    have ht_lt : t < k ^ arEq σ A.1.val := by
      rw [arEq_val]
      exact encAtom_args_lt A.2
    refine ⟨A.1.val, A.1.isLt, t, ht_lt, hA_val, ?_⟩
    have hargs_eq : ∀ j : Fin ((sigmaEq σ).ar A.1),
        args j = l[(A.2 j).val]'(by rw [hl]; exact (A.2 j).isLt) := by
      intro j
      have h1 := hargs j
      rw [List.getElem?_eq_getElem (by rw [hl]; exact (A.2 j).isLt)] at h1
      exact (Option.some.inj h1).symm
    have hmap_eq : (List.range (arEq σ A.1.val)).map
        (fun j => unpackBase (encBag B).headI (packList B.withEq.n (l.map Fin.val)) (unpackBase k t j)) =
        List.ofFn (fun j => (args j).val) := by
      rw [arEq_val]
      apply List.ext_getElem
      · simp
      · intro j hj1 hj2
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
        have hj' : j < (sigmaEq σ).ar A.1 := by simpa using hj1
        have ht_unp := unpackBase_packList (B := k) (ds := List.ofFn (fun j' => (A.2 j').val))
          (fun d hd => by obtain ⟨j', rfl⟩ := List.mem_ofFn.1 hd; exact (A.2 j').isLt)
          (i := j) (by simp [hj'])
        simp only [List.getElem_ofFn] at ht_unp
        change unpackBase B.withEq.n (packList B.withEq.n (l.map Fin.val)) (unpackBase k t j) =
          (args ⟨j, hj'⟩).val
        rw [ht_unp, hargs_eq ⟨j, hj'⟩]
        have hu_unp := unpackBase_packList (B := B.withEq.n) (ds := l.map Fin.val)
          (fun d hd => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact x.isLt)
          (i := (A.2 ⟨j, hj'⟩).val) (by simp [hl, (A.2 ⟨j, hj'⟩).isLt])
        simpa using hu_unp
    rw [hmap_eq]
    exact (bagEqRelBit_encBag B A.1 args).2 hholds

theorem ind_full_succ' {τ : Sig} {G : Type} [τ.lang.Structure G] (k m : ℕ) (l : List G) (x : G) :
    ind τ k (m + 1) (Strat.full G (m + 1)) l x =
      {Set.range (fun y : G => (y, ind τ k m (Strat.full G m) (l ++ [x, y])))} := by
  show ({(fun c : G × Strat G m => (c.1, ind τ k m c.2 (l ++ [x, c.1]))) ''
      Set.range (fun y : G => (y, Strat.full G m))} : Set (Set (G × HTh τ G k m))) = _
  rw [← Set.range_comp]
  rfl

open Classical in
theorem leafIter_spec {σ : Sig} (B : Bag σ) (ℓ : ℕ) :
    ∀ m ≤ ℓ,
      ((leafStep B.withEq.n)^[m] (leafBase σ (encBag B) (2 * ℓ))).1 = 2 * ℓ - 2 * m ∧
      ((leafStep B.withEq.n)^[m] (leafBase σ (encBag B) (2 * ℓ))).2.1 =
        tower B.withEq.n (atomCnt (sigmaEq σ) (2 * ℓ)) m ∧
      ((leafStep B.withEq.n)^[m] (leafBase σ (encBag B) (2 * ℓ))).2.2.length =
        B.withEq.n ^ (2 * ℓ - 2 * m) ∧
      ∀ (l : List (Fin B.withEq.n)), l.length = 2 * ℓ - 2 * m →
        ((leafStep B.withEq.n)^[m] (leafBase σ (encBag B) (2 * ℓ))).2.2.getD
            (packList B.withEq.n (l.map Fin.val)) 0 =
          (hthEquiv (sigmaEq σ) B.withEq.n (2 * ℓ) m
            (ind (sigmaEq σ) (2 * ℓ) m (Strat.full (Fin B.withEq.n) m) l)).val
  | 0, _ => by
    simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.sub_zero]
    let τ := sigmaEq σ
    let k := 2 * ℓ
    let q := atomCnt τ k
    have hhead : (encBag B).headI = B.withEq.n := rfl
    refine ⟨rfl, rfl, by simp [leafBase, hhead], fun l hl => ?_⟩
    have hu_lt : packList B.withEq.n (l.map Fin.val) < B.withEq.n ^ (2 * ℓ) := by
      rcases eq_or_ne (2 * ℓ) 0 with hkz | hkz
      · have hlnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hlnil; simp [hkz]
      · have h := @packList_lt B.withEq.n (l.map Fin.val)
          (fun d hd => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact x.isLt)
        simpa [hl] using h
    have hlt_len : packList B.withEq.n (l.map Fin.val) < (leafBase σ (encBag B) (2 * ℓ)).2.2.length := by
      simpa [leafBase, hhead] using hu_lt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_len, Option.getD_some]
    simp only [leafBase, leafBaseCell, singletonBits, List.getElem_map, List.getElem_range]
    rw [leafHeadCode_spec B (2 * ℓ) l hl]
    exact packBits_eq_singleton_setEquivFin (setEquivFin (atomEquiv τ k)) (atomsOf τ k l)
  | m + 1, hm1 => by
    let τ := sigmaEq σ
    let k := 2 * ℓ
    let q := atomCnt τ k
    let n := B.withEq.n
    rw [Function.iterate_succ_apply']
    generalize hst : (leafStep n)^[m] (leafBase σ (encBag B) (2 * ℓ)) = st
    have ih_full := leafIter_spec B ℓ m (Nat.le_of_succ_le hm1)
    rw [hst] at ih_full
    obtain ⟨hlen_st, hM_st, _, ih⟩ := ih_full
    let len' := 2 * ℓ - 2 * (m + 1)
    have hsub : st.1 - 2 = len' := by omega
    have hM_eq : st.2.1 = tower n q m := hM_st
    refine ⟨by simp [leafStep, hsub, len'],
      by simp [leafStep, hM_eq, tower, n, q, τ, k],
      by simp [leafStep, hsub, len'], fun l hl => ?_⟩
    have hu_lt : packList n (l.map Fin.val) < n ^ len' := by
      rcases eq_or_ne len' 0 with hkz | hkz
      · have hlnil : l = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hlnil; simp [hkz]
      · have h := @packList_lt n (l.map Fin.val)
          (fun d hd => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hd; exact x.isLt)
        simpa [hl] using h
    have hlt_len : packList n (l.map Fin.val) < (leafStep n st).2.2.length := by
      simpa [leafStep, hsub] using hu_lt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_len, Option.getD_some]
    simp only [leafStep, leafStepCell, hsub, hM_eq, List.getElem_map, List.getElem_range]
    rw [hthEquiv_succ_val]
    refine packBase_congr fun x hx => ?_
    rw [dif_pos hx]
    unfold leafStepFam singletonBits leafStepPers
    let x' : Fin B.withEq.n := ⟨x, hx⟩
    change packBits _ _ =
      (famEquiv τ n k m (ind τ k (m + 1) (Strat.full (Fin B.withEq.n) (m + 1)) l x')).val
    rw [ind_full_succ']
    let targetPers : Set (Fin n × HTh τ (Fin n) k m) :=
      Set.range (fun y : Fin B.withEq.n => (y, ind τ k m (Strat.full (Fin B.withEq.n) m) (l ++ [x', y])))
    have hpCode_eq : packBits (n * tower n q m) (fun pair_u =>
        (List.range n).any (fun y =>
          st.2.2.getD (packList n (l.map Fin.val) + n ^ len' * (x + n * y)) 0 +
            tower n q m * y == pair_u)) =
        (persEquiv τ n k m targetPers).val := by
      unfold persEquiv
      rw [setEquivFin_val]
      refine packBits_congr fun pu hpu => ?_
      rw [dif_pos hpu]
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨y, hy, heq⟩
        let y' : Fin B.withEq.n := ⟨y, hy⟩
        have happ : packList n ((l ++ [x', y']).map Fin.val) =
            packList n (l.map Fin.val) + n ^ len' * (x + n * y) := by
          rw [List.map_append, packList_append, List.length_map, hl]
          simp [x', y', packList, n, len']
        have hih := ih (l ++ [x', y']) (by simp [hl]; omega)
        rw [happ] at hih
        rw [hih] at heq
        let yc : Fin n × HTh τ (Fin n) k m :=
          (y', ind τ k m (Strat.full (Fin B.withEq.n) m) (l ++ [x', y']))
        have hyc_val : (pairEquiv τ n k m yc).val = pu := heq
        have hyc_eq : (pairEquiv τ n k m).symm ⟨pu, hpu⟩ = yc := by
          apply (pairEquiv τ n k m).injective
          ext; simpa using hyc_val.symm
        rw [hyc_eq]
        exact ⟨y', rfl⟩
      · rintro ⟨y', hy'⟩
        dsimp only at hy'
        refine ⟨y'.val, y'.isLt, ?_⟩
        have happ : packList n ((l ++ [x', y']).map Fin.val) =
            packList n (l.map Fin.val) + n ^ len' * (x + n * y'.val) := by
          rw [List.map_append, packList_append, List.length_map, hl]
          simp [x', packList, n, len']
        have hih := ih (l ++ [x', y']) (by simp [hl]; omega)
        rw [happ] at hih
        rw [hih]
        have hpair : pairEquiv τ n k m (y', ind τ k m (Strat.full (Fin B.withEq.n) m) (l ++ [x', y'])) =
            ⟨pu, hpu⟩ := by
          rw [hy']; simp
        exact congrArg Fin.val hpair
    rw [hpCode_eq]
    exact packBits_eq_singleton_setEquivFin (persEquiv τ n k m) targetPers

theorem leafHThCode_spec {σ : Sig} (B : Bag σ) (ℓ : ℕ) :
    leafHThCode σ (encBag B) ℓ =
      (hthEquiv (sigmaEq σ) B.withEq.n (2 * ℓ) ℓ
        (ind (sigmaEq σ) (2 * ℓ) ℓ (Strat.full (Fin B.withEq.n) ℓ) [])).val := by
  have h := (leafIter_spec B ℓ ℓ le_rfl).2.2.2 [] (by simp)
  simpa [leafHThCode, encBag, Bag.withEq] using h

/-! ### 13. `joinHThCode`: fused pullback + projection on `hthEquiv` codes (factored) -/

theorem push_snd_pb_succ {τ : Sig} {k : ℕ} {P Q K : Type} (g : P → K) (h : Q → K)
    (m : ℕ) (A : HTh τ P k (m + 1)) (B : HTh τ Q k (m + 1)) (xt : Q) :
    push (Fib.snd : Fib g h → Q) (m + 1) (pb g h (m + 1) A B) xt =
      {q | ∃ xc : P, g xc = h xt ∧ ∃ p₁ ∈ A xc, ∃ p₂ ∈ B xt,
        q = {yd : Q × HTh τ Q k m | ∃ yc c₁ c₂, g yc = h yd.1 ∧ (yc, c₁) ∈ p₁ ∧ (yd.1, c₂) ∈ p₂ ∧
          yd.2 = push (Fib.snd : Fib g h → Q) m (pb g h m c₁ c₂)}} := by
  ext q
  constructor
  · rintro ⟨z, p, rfl, ⟨p₁, hp₁, p₂, hp₂, rfl⟩, rfl⟩
    refine ⟨z.fst, z.eq, p₁, hp₁, p₂, hp₂, ?_⟩
    ext ⟨yt, d⟩
    constructor
    · rintro ⟨⟨⟨yc, yt', hy_eq⟩, c⟩, ⟨c₁, c₂, hc₁, hc₂, rfl⟩, hpair⟩
      cases hpair
      exact ⟨yc, c₁, c₂, hy_eq, hc₁, hc₂, rfl⟩
    · rintro ⟨yc, c₁, c₂, hy_eq, hc₁, hc₂, rfl⟩
      exact ⟨(⟨yc, yt, hy_eq⟩, pb g h m c₁ c₂), ⟨c₁, c₂, hc₁, hc₂, rfl⟩, rfl⟩
  · rintro ⟨xc, h_eq, p₁, hp₁, p₂, hp₂, rfl⟩
    let z : Fib g h := ⟨xc, xt, h_eq⟩
    let p : Set (Fib g h × HTh τ (Fib g h) k m) :=
      {c | ∃ c₁ c₂, (c.1.fst, c₁) ∈ p₁ ∧ (c.1.snd, c₂) ∈ p₂ ∧ c.2 = pb g h m c₁ c₂}
    refine ⟨z, p, rfl, ⟨p₁, hp₁, p₂, hp₂, rfl⟩, ?_⟩
    ext ⟨yt, d⟩
    constructor
    · rintro ⟨yc, c₁, c₂, hy_eq, hc₁, hc₂, rfl⟩
      exact ⟨(⟨yc, yt, hy_eq⟩, pb g h m c₁ c₂), ⟨c₁, c₂, hc₁, hc₂, rfl⟩, rfl⟩
    · rintro ⟨⟨⟨yc, yt', hy_eq⟩, c⟩, ⟨c₁, c₂, hc₁, hc₂, rfl⟩, hpair⟩
      cases hpair
      exact ⟨yc, c₁, c₂, hy_eq, hc₁, hc₂, rfl⟩

def interHeadCode (q h₁ h₂ : ℕ) : ℕ :=
  packBits q (fun a => unpackBit h₁ a && unpackBit h₂ a)

def joinBaseBit (q ac at_ h : ℕ) : Bool :=
  (List.range (2 ^ q)).any (fun h₁ =>
    unpackBit ac h₁ &&
      (List.range (2 ^ q)).any (fun h₂ =>
        unpackBit at_ h₂ && (interHeadCode q h₁ h₂ == h)))

def joinBaseCell (q idx : ℕ) : ℕ :=
  packBits (2 ^ q)
    (joinBaseBit q (idx % (2 ^ 2 ^ q)) (idx / (2 ^ 2 ^ q)))

def joinBase (σ : Sig) (k : ℕ) : ℕ × ℕ × List ℕ :=
  let q := atomCnt (sigmaEq σ) k
  let M0 := 2 ^ 2 ^ q
  (M0, M0, (List.range (M0 * M0)).map (joinBaseCell q))

abbrev JoinEnv : Type := (ℕ × ℕ × ℕ × ℕ) × (List ℕ × List ℕ × List ℕ)

def joinPersInner (env : JoinEnv) (p₁ p₂ u yc c₁ : ℕ) : Bool :=
  unpackBit p₁ (c₁ + env.1.2.2.1 * yc) &&
    (List.range env.1.2.2.2).any (fun c₂ =>
      unpackBit p₂ (c₂ + env.1.2.2.2 * (u / env.1.2.2.2)) &&
        (env.2.2.2.getD (c₁ + env.1.2.2.1 * c₂) 0 == u % env.1.2.2.2))

def joinPersBit (env : JoinEnv) (p₁ p₂ u : ℕ) : Bool :=
  (List.range env.1.1).any (fun yc =>
    (env.2.1.getD yc 0 == env.2.2.1.getD (u / env.1.2.2.2) 0) &&
      (List.range env.1.2.2.1).any (joinPersInner env p₁ p₂ u yc))

def joinPersCode (env : JoinEnv) (p₁ p₂ : ℕ) : ℕ :=
  packBits (env.1.2.1 * env.1.2.2.2) (joinPersBit env p₁ p₂)

def joinFamInner (env : JoinEnv) (famc famt qc p₁ : ℕ) : Bool :=
  unpackBit famc p₁ &&
    (List.range (2 ^ (env.1.2.1 * env.1.2.2.2))).any (fun p₂ =>
      unpackBit famt p₂ && (joinPersCode env p₁ p₂ == qc))

def joinFamBit (env : JoinEnv) (ac famt xt qc : ℕ) : Bool :=
  (List.range env.1.1).any (fun xc =>
    (env.2.1.getD xc 0 == env.2.2.1.getD xt 0) &&
      (List.range (2 ^ (env.1.1 * env.1.2.2.1))).any
        (joinFamInner env (unpackBase (2 ^ 2 ^ (env.1.1 * env.1.2.2.1)) ac xc) famt qc))

def joinStepFam (env : JoinEnv) (ac at_ xt : ℕ) : ℕ :=
  packBits (2 ^ (env.1.2.1 * env.1.2.2.2))
    (joinFamBit env ac (unpackBase (2 ^ 2 ^ (env.1.2.1 * env.1.2.2.2)) at_ xt) xt)

def joinStepCell (env : JoinEnv) (idx : ℕ) : ℕ :=
  let Mc' := 2 ^ (env.1.1 * 2 ^ (env.1.1 * env.1.2.2.1))
  packBase env.1.2.1 (2 ^ 2 ^ (env.1.2.1 * env.1.2.2.2))
    (joinStepFam env (idx % Mc') (idx / Mc'))

def joinStep (nc nt : ℕ) (gc gt : List ℕ) (st : ℕ × ℕ × List ℕ) : ℕ × ℕ × List ℕ :=
  let env : JoinEnv := ((nc, nt, st.1, st.2.1), (gc, gt, st.2.2))
  let Mc' := 2 ^ (nc * 2 ^ (nc * st.1))
  let Mt' := 2 ^ (nt * 2 ^ (nt * st.2.1))
  (Mc', Mt', (List.range (Mc' * Mt')).map (joinStepCell env))

def joinHThCode (σ : Sig) (nt nc : ℕ) (gt gc : List ℕ) (ℓ vc vt : ℕ) : ℕ :=
  let st := (joinStep nc nt gc gt)^[ℓ] (joinBase σ (2 * ℓ))
  st.2.2.getD (vc + st.1 * vt) 0

theorem primrec_interHeadCode : Primrec (fun p : ℕ × ℕ × ℕ => interHeadCode p.1 p.2.1 p.2.2) := by
  unfold interHeadCode
  refine primrec_packBits Primrec.fst ?_
  exact (Primrec.and.comp
    (primrec_unpackBit.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (primrec_unpackBit.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂

theorem primrec_joinBaseBit :
    Primrec (fun a : (ℕ × ℕ × ℕ) × ℕ => joinBaseBit a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold joinBaseBit
  let Dom := (ℕ × ℕ × ℕ) × ℕ
  have hq : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hac : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hat : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hh : Primrec (fun a : Dom => a.2) := Primrec.snd
  have h2q : Primrec (fun a : Dom => 2 ^ a.1.1) := primrec_pow.comp (Primrec.const 2) hq
  refine primrec_range_any h2q ?_
  have hd1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hh1 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  have hinner : Primrec (fun b : Dom × ℕ =>
      unpackBit b.1.1.2.1 b.2 &&
        (List.range (2 ^ b.1.1.1)).any (fun h₂ =>
          unpackBit b.1.1.2.2 h₂ && (interHeadCode b.1.1.1 b.2 h₂ == b.1.2))) := by
    refine Primrec.and.comp (primrec_unpackBit.comp (hac.comp hd1) hh1) ?_
    refine primrec_range_any (h2q.comp hd1) ?_
    have hb2 : Primrec (fun c : (Dom × ℕ) × ℕ => c.1) := Primrec.fst
    have hh2 : Primrec (fun c : (Dom × ℕ) × ℕ => c.2) := Primrec.snd
    have hd2 := hd1.comp hb2
    exact (Primrec.and.comp (primrec_unpackBit.comp (hat.comp hd2) hh2)
      (primrec_nat_beq.comp (primrec_interHeadCode.comp
        (Primrec.pair (hq.comp hd2) (Primrec.pair (hh1.comp hb2) hh2))) (hh.comp hd2))).to₂
  exact hinner.to₂

theorem primrec_joinBaseCell : Primrec₂ joinBaseCell := by
  show Primrec (fun a : ℕ × ℕ => joinBaseCell a.1 a.2)
  unfold joinBaseCell
  have hq : Primrec (fun a : ℕ × ℕ => a.1) := Primrec.fst
  have hidx : Primrec (fun a : ℕ × ℕ => a.2) := Primrec.snd
  have h2q : Primrec (fun a : ℕ × ℕ => 2 ^ a.1) := primrec_pow.comp (Primrec.const 2) hq
  have hM0 : Primrec (fun a : ℕ × ℕ => 2 ^ 2 ^ a.1) := primrec_pow.comp (Primrec.const 2) h2q
  have hcfg : Primrec (fun a : ℕ × ℕ => (a.1, a.2 % 2 ^ 2 ^ a.1, a.2 / 2 ^ 2 ^ a.1)) :=
    Primrec.pair hq (Primrec.pair (Primrec.nat_mod.comp hidx hM0) (Primrec.nat_div.comp hidx hM0))
  exact primrec_packBits h2q
    (primrec_joinBaseBit.comp (Primrec.pair (hcfg.comp Primrec.fst) Primrec.snd)).to₂

theorem primrec_joinBase (σ : Sig) : Primrec (joinBase σ) := by
  unfold joinBase
  have hq : Primrec (fun k : ℕ => atomCnt (sigmaEq σ) k) := primrec_atomCnt (sigmaEq σ)
  have hM0 : Primrec (fun k : ℕ => 2 ^ 2 ^ atomCnt (sigmaEq σ) k) :=
    primrec_pow.comp (Primrec.const 2) (primrec_pow.comp (Primrec.const 2) hq)
  exact Primrec.pair hM0 (Primrec.pair hM0
    (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hM0 hM0))
      (primrec_joinBaseCell.comp (hq.comp Primrec.fst) Primrec.snd).to₂))

theorem primrec_env_nc : Primrec (fun e : JoinEnv => e.1.1) := by
  have h1 : Primrec (fun e : JoinEnv => e.1) := Primrec.fst
  exact Primrec.fst.comp h1

theorem primrec_env_nt : Primrec (fun e : JoinEnv => e.1.2.1) := by
  have h1 : Primrec (fun e : JoinEnv => e.1) := Primrec.fst
  have h12 : Primrec (fun e : JoinEnv => e.1.2) := Primrec.snd.comp h1
  exact Primrec.fst.comp h12

theorem primrec_env_Mc : Primrec (fun e : JoinEnv => e.1.2.2.1) := by
  have h1 : Primrec (fun e : JoinEnv => e.1) := Primrec.fst
  have h12 : Primrec (fun e : JoinEnv => e.1.2) := Primrec.snd.comp h1
  have h122 : Primrec (fun e : JoinEnv => e.1.2.2) := Primrec.snd.comp h12
  exact Primrec.fst.comp h122

theorem primrec_env_Mt : Primrec (fun e : JoinEnv => e.1.2.2.2) := by
  have h1 : Primrec (fun e : JoinEnv => e.1) := Primrec.fst
  have h12 : Primrec (fun e : JoinEnv => e.1.2) := Primrec.snd.comp h1
  have h122 : Primrec (fun e : JoinEnv => e.1.2.2) := Primrec.snd.comp h12
  exact Primrec.snd.comp h122

theorem primrec_env_gc : Primrec (fun e : JoinEnv => e.2.1) := by
  have h2 : Primrec (fun e : JoinEnv => e.2) := Primrec.snd
  exact Primrec.fst.comp h2

theorem primrec_env_gt : Primrec (fun e : JoinEnv => e.2.2.1) := by
  have h2 : Primrec (fun e : JoinEnv => e.2) := Primrec.snd
  have h22 : Primrec (fun e : JoinEnv => e.2.2) := Primrec.snd.comp h2
  exact Primrec.fst.comp h22

theorem primrec_env_J : Primrec (fun e : JoinEnv => e.2.2.2) := by
  have h2 : Primrec (fun e : JoinEnv => e.2) := Primrec.snd
  have h22 : Primrec (fun e : JoinEnv => e.2.2) := Primrec.snd.comp h2
  exact Primrec.snd.comp h22

theorem primrec_joinPersInner :
    Primrec (fun a : (JoinEnv × ℕ × ℕ × ℕ × ℕ) × ℕ =>
      joinPersInner a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 a.1.2.2.2.2 a.2) := by
  unfold joinPersInner
  let Dom := (JoinEnv × ℕ × ℕ × ℕ × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have henv : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have ha12 : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have ha122 : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp ha12
  have ha1222 : Primrec (fun a : Dom => a.1.2.2.2) := Primrec.snd.comp ha122
  have hMc := primrec_env_Mc.comp henv
  have hMt := primrec_env_Mt.comp henv
  have hJ := primrec_env_J.comp henv
  have hp1 : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp ha12
  have hp2 : Primrec (fun a : Dom => a.1.2.2.1) := Primrec.fst.comp ha122
  have hu : Primrec (fun a : Dom => a.1.2.2.2.1) := Primrec.fst.comp ha1222
  have hyc : Primrec (fun a : Dom => a.1.2.2.2.2) := Primrec.snd.comp ha1222
  have hc1 : Primrec (fun a : Dom => a.2) := Primrec.snd
  have hbit1 := primrec_unpackBit.comp hp1
    (Primrec.nat_add.comp hc1 (Primrec.nat_mul.comp hMc hyc))
  refine Primrec.and.comp hbit1 (primrec_range_any hMt ?_)
  have hd1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hc2 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  have hbit2 := primrec_unpackBit.comp (hp2.comp hd1)
    (Primrec.nat_add.comp hc2
      (Primrec.nat_mul.comp (hMt.comp hd1) (Primrec.nat_div.comp (hu.comp hd1) (hMt.comp hd1))))
  have hj := primrec_nat_beq.comp
    ((Primrec.list_getD 0).comp (hJ.comp hd1)
      (Primrec.nat_add.comp (hc1.comp hd1) (Primrec.nat_mul.comp (hMc.comp hd1) hc2)))
    (Primrec.nat_mod.comp (hu.comp hd1) (hMt.comp hd1))
  exact (Primrec.and.comp hbit2 hj).to₂

theorem primrec_joinPersBit :
    Primrec (fun a : (JoinEnv × ℕ × ℕ) × ℕ => joinPersBit a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold joinPersBit
  let Dom := (JoinEnv × ℕ × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have henv : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have ha12 : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have hnc := primrec_env_nc.comp henv
  have hMc := primrec_env_Mc.comp henv
  have hMt := primrec_env_Mt.comp henv
  have hgc := primrec_env_gc.comp henv
  have hgt := primrec_env_gt.comp henv
  have hp1 : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp ha12
  have hp2 : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp ha12
  have hu : Primrec (fun a : Dom => a.2) := Primrec.snd
  refine primrec_range_any hnc ?_
  have hd1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hyc : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  have hedge := primrec_nat_beq.comp ((Primrec.list_getD 0).comp (hgc.comp hd1) hyc)
    ((Primrec.list_getD 0).comp (hgt.comp hd1)
      (Primrec.nat_div.comp (hu.comp hd1) (hMt.comp hd1)))
  have hpack5 : Primrec (fun b : Dom × ℕ =>
      (b.1.1.1, b.1.1.2.1, b.1.1.2.2, b.1.2, b.2)) :=
    Primrec.pair (henv.comp hd1)
      (Primrec.pair (hp1.comp hd1) (Primrec.pair (hp2.comp hd1) (Primrec.pair (hu.comp hd1) hyc)))
  have hinner : Primrec (fun b : Dom × ℕ =>
      (b.1.1.1.2.1.getD b.2 0 == b.1.1.1.2.2.1.getD (b.1.2 / b.1.1.1.1.2.2.2) 0) &&
        (List.range b.1.1.1.1.2.2.1).any
          (joinPersInner b.1.1.1 b.1.1.2.1 b.1.1.2.2 b.1.2 b.2)) := by
    refine Primrec.and.comp hedge (primrec_range_any (hMc.comp hd1) ?_)
    have hc_fst : Primrec (fun c : (Dom × ℕ) × ℕ => c.1) := Primrec.fst
    have hc_snd : Primrec (fun c : (Dom × ℕ) × ℕ => c.2) := Primrec.snd
    exact (primrec_joinPersInner.comp (Primrec.pair (hpack5.comp hc_fst) hc_snd)).to₂
  exact hinner.to₂

theorem primrec_joinPersCode :
    Primrec (fun a : JoinEnv × ℕ × ℕ => joinPersCode a.1 a.2.1 a.2.2) := by
  unfold joinPersCode
  let Dom := JoinEnv × ℕ × ℕ
  have henv : Primrec (fun a : Dom => a.1) := Primrec.fst
  have hnt := primrec_env_nt.comp henv
  have hMt := primrec_env_Mt.comp henv
  exact primrec_packBits (Primrec.nat_mul.comp hnt hMt) primrec_joinPersBit.to₂

theorem primrec_joinFamInner :
    Primrec (fun a : (JoinEnv × ℕ × ℕ × ℕ) × ℕ =>
      joinFamInner a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  unfold joinFamInner
  let Dom := (JoinEnv × ℕ × ℕ × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have henv : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have ha12 : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have ha122 : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp ha12
  have hnt := primrec_env_nt.comp henv
  have hMt := primrec_env_Mt.comp henv
  have hfamc : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp ha12
  have hfamt : Primrec (fun a : Dom => a.1.2.2.1) := Primrec.fst.comp ha122
  have hqc : Primrec (fun a : Dom => a.1.2.2.2) := Primrec.snd.comp ha122
  have hp1 : Primrec (fun a : Dom => a.2) := Primrec.snd
  have hPt : Primrec (fun a : Dom => 2 ^ (a.1.1.1.2.1 * a.1.1.1.2.2.2)) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnt hMt)
  refine Primrec.and.comp (primrec_unpackBit.comp hfamc hp1) (primrec_range_any hPt ?_)
  have hd1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hp2 : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (Primrec.and.comp (primrec_unpackBit.comp (hfamt.comp hd1) hp2)
    (primrec_nat_beq.comp
      (primrec_joinPersCode.comp
        (Primrec.pair (henv.comp hd1) (Primrec.pair (hp1.comp hd1) hp2)))
      (hqc.comp hd1))).to₂

theorem primrec_joinFamBit :
    Primrec (fun a : (JoinEnv × ℕ × ℕ × ℕ) × ℕ =>
      joinFamBit a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  unfold joinFamBit
  let Dom := (JoinEnv × ℕ × ℕ × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have henv : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have ha12 : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have ha122 : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp ha12
  have hnc := primrec_env_nc.comp henv
  have hMc := primrec_env_Mc.comp henv
  have hgc := primrec_env_gc.comp henv
  have hgt := primrec_env_gt.comp henv
  have hac : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp ha12
  have hfamt : Primrec (fun a : Dom => a.1.2.2.1) := Primrec.fst.comp ha122
  have hxt : Primrec (fun a : Dom => a.1.2.2.2) := Primrec.snd.comp ha122
  have hqc : Primrec (fun a : Dom => a.2) := Primrec.snd
  have hPc : Primrec (fun a : Dom => 2 ^ (a.1.1.1.1 * a.1.1.1.2.2.1)) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnc hMc)
  have hFc : Primrec (fun a : Dom => 2 ^ 2 ^ (a.1.1.1.1 * a.1.1.1.2.2.1)) :=
    primrec_pow.comp (Primrec.const 2) hPc
  refine primrec_range_any hnc ?_
  have hd1 : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hxc : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  have hedge := primrec_nat_beq.comp ((Primrec.list_getD 0).comp (hgc.comp hd1) hxc)
    ((Primrec.list_getD 0).comp (hgt.comp hd1) (hxt.comp hd1))
  have hfamc := primrec_unpackBase.comp
    (Primrec.pair (hFc.comp hd1) (Primrec.pair (hac.comp hd1) hxc))
  have hpack4 : Primrec (fun b : Dom × ℕ =>
      (b.1.1.1, unpackBase (2 ^ 2 ^ (b.1.1.1.1.1 * b.1.1.1.1.2.2.1)) b.1.1.2.1 b.2,
        b.1.1.2.2.1, b.1.2)) :=
    Primrec.pair (henv.comp hd1)
      (Primrec.pair hfamc (Primrec.pair (hfamt.comp hd1) (hqc.comp hd1)))
  have hinner : Primrec (fun b : Dom × ℕ =>
      (b.1.1.1.2.1.getD b.2 0 == b.1.1.1.2.2.1.getD b.1.1.2.2.2 0) &&
        (List.range (2 ^ (b.1.1.1.1.1 * b.1.1.1.1.2.2.1))).any
          (joinFamInner b.1.1.1
            (unpackBase (2 ^ 2 ^ (b.1.1.1.1.1 * b.1.1.1.1.2.2.1)) b.1.1.2.1 b.2)
            b.1.1.2.2.1 b.1.2)) := by
    refine Primrec.and.comp hedge (primrec_range_any (hPc.comp hd1) ?_)
    have hc_fst : Primrec (fun c : (Dom × ℕ) × ℕ => c.1) := Primrec.fst
    have hc_snd : Primrec (fun c : (Dom × ℕ) × ℕ => c.2) := Primrec.snd
    exact (primrec_joinFamInner.comp (Primrec.pair (hpack4.comp hc_fst) hc_snd)).to₂
  exact hinner.to₂

theorem primrec_joinStepFam :
    Primrec (fun a : (JoinEnv × ℕ × ℕ) × ℕ => joinStepFam a.1.1 a.1.2.1 a.1.2.2 a.2) := by
  unfold joinStepFam
  let Dom := (JoinEnv × ℕ × ℕ) × ℕ
  have ha1 : Primrec (fun a : Dom => a.1) := Primrec.fst
  have henv : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp ha1
  have ha12 : Primrec (fun a : Dom => a.1.2) := Primrec.snd.comp ha1
  have hnt := primrec_env_nt.comp henv
  have hMt := primrec_env_Mt.comp henv
  have hac : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp ha12
  have hat : Primrec (fun a : Dom => a.1.2.2) := Primrec.snd.comp ha12
  have hxt : Primrec (fun a : Dom => a.2) := Primrec.snd
  have hPt : Primrec (fun a : Dom => 2 ^ (a.1.1.1.2.1 * a.1.1.1.2.2.2)) :=
    primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnt hMt)
  have hFt : Primrec (fun a : Dom => 2 ^ 2 ^ (a.1.1.1.2.1 * a.1.1.1.2.2.2)) :=
    primrec_pow.comp (Primrec.const 2) hPt
  have hfamt := primrec_unpackBase.comp (Primrec.pair hFt (Primrec.pair hat hxt))
  have hpack4 := Primrec.pair henv (Primrec.pair hac (Primrec.pair hfamt hxt))
  refine primrec_packBits hPt ?_
  have hb_fst : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hb_snd : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (primrec_joinFamBit.comp (Primrec.pair (hpack4.comp hb_fst) hb_snd)).to₂

theorem primrec_joinStepCell : Primrec₂ joinStepCell := by
  show Primrec (fun a : JoinEnv × ℕ => joinStepCell a.1 a.2)
  unfold joinStepCell
  let Dom := JoinEnv × ℕ
  have henv : Primrec (fun a : Dom => a.1) := Primrec.fst
  have hidx : Primrec (fun a : Dom => a.2) := Primrec.snd
  have hnc := primrec_env_nc.comp henv
  have hnt := primrec_env_nt.comp henv
  have hMc := primrec_env_Mc.comp henv
  have hMt := primrec_env_Mt.comp henv
  have hMc' : Primrec (fun a : Dom => 2 ^ (a.1.1.1 * 2 ^ (a.1.1.1 * a.1.1.2.2.1))) :=
    primrec_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hnc (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnc hMc)))
  have hFt : Primrec (fun a : Dom => 2 ^ 2 ^ (a.1.1.2.1 * a.1.1.2.2.2)) :=
    primrec_pow.comp (Primrec.const 2)
      (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnt hMt))
  have hpack3 := Primrec.pair henv
    (Primrec.pair (Primrec.nat_mod.comp hidx hMc') (Primrec.nat_div.comp hidx hMc'))
  refine primrec_packBase hnt hFt ?_
  have hb_fst : Primrec (fun b : Dom × ℕ => b.1) := Primrec.fst
  have hb_snd : Primrec (fun b : Dom × ℕ => b.2) := Primrec.snd
  exact (primrec_joinStepFam.comp (Primrec.pair (hpack3.comp hb_fst) hb_snd)).to₂

theorem primrec_joinStep :
    Primrec (fun a : (ℕ × ℕ × List ℕ × List ℕ) × (ℕ × ℕ × List ℕ) =>
      joinStep a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  unfold joinStep
  let Dom := (ℕ × ℕ × List ℕ × List ℕ) × (ℕ × ℕ × List ℕ)
  have hnc : Primrec (fun a : Dom => a.1.1) := Primrec.fst.comp Primrec.fst
  have hnt : Primrec (fun a : Dom => a.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hgc : Primrec (fun a : Dom => a.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hgt : Primrec (fun a : Dom => a.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hMc : Primrec (fun a : Dom => a.2.1) := Primrec.fst.comp Primrec.snd
  have hMt : Primrec (fun a : Dom => a.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hJ : Primrec (fun a : Dom => a.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have henv : Primrec (fun a : Dom =>
      (((a.1.1, a.1.2.1, a.2.1, a.2.2.1), (a.1.2.2.1, a.1.2.2.2, a.2.2.2)) : JoinEnv)) :=
    Primrec.pair (Primrec.pair hnc (Primrec.pair hnt (Primrec.pair hMc hMt)))
      (Primrec.pair hgc (Primrec.pair hgt hJ))
  have hMc' : Primrec (fun a : Dom => 2 ^ (a.1.1 * 2 ^ (a.1.1 * a.2.1))) :=
    primrec_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hnc (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnc hMc)))
  have hMt' : Primrec (fun a : Dom => 2 ^ (a.1.2.1 * 2 ^ (a.1.2.1 * a.2.2.1))) :=
    primrec_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp hnt (primrec_pow.comp (Primrec.const 2) (Primrec.nat_mul.comp hnt hMt)))
  exact Primrec.pair hMc' (Primrec.pair hMt'
    (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hMc' hMt'))
      (primrec_joinStepCell.comp (henv.comp Primrec.fst) Primrec.snd).to₂))

theorem primrec_joinHThCode (σ : Sig) :
    Primrec (fun p : (ℕ × ℕ) × (List ℕ × List ℕ) × (ℕ × ℕ × ℕ) =>
      joinHThCode σ p.1.1 p.1.2 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold joinHThCode
  let Dom := (ℕ × ℕ) × (List ℕ × List ℕ) × (ℕ × ℕ × ℕ)
  have hnt : Primrec (fun p : Dom => p.1.1) := Primrec.fst.comp Primrec.fst
  have hnc : Primrec (fun p : Dom => p.1.2) := Primrec.snd.comp Primrec.fst
  have hgt : Primrec (fun p : Dom => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hgc : Primrec (fun p : Dom => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hℓ : Primrec (fun p : Dom => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hvc : Primrec (fun p : Dom => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hvt : Primrec (fun p : Dom => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hinit : Primrec (fun p : Dom => joinBase σ (2 * p.2.2.1)) :=
    (primrec_joinBase σ).comp (Primrec.nat_mul.comp (Primrec.const 2) hℓ)
  have hcfg : Primrec (fun p : Dom => (p.1.2, p.1.1, p.2.1.2, p.2.1.1)) :=
    Primrec.pair hnc (Primrec.pair hnt (Primrec.pair hgc hgt))
  have hiter : Primrec (fun p : Dom =>
      (joinStep p.1.2 p.1.1 p.2.1.2 p.2.1.1)^[p.2.2.1] (joinBase σ (2 * p.2.2.1))) :=
    Primrec.nat_iterate hℓ hinit
      (primrec_joinStep.comp (Primrec.pair (hcfg.comp Primrec.fst) Primrec.snd)).to₂
  exact (Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp hiter))
    (Primrec.nat_add.comp hvc (Primrec.nat_mul.comp (Primrec.fst.comp hiter) hvt))

open Classical in
theorem interHeadCode_spec (τ : Sig) (k : ℕ) (N₁ N₂ : Set (τ.Atom k)) :
    interHeadCode (atomCnt τ k)
        (setEquivFin (atomEquiv τ k) N₁).val (setEquivFin (atomEquiv τ k) N₂).val =
      (setEquivFin (atomEquiv τ k) (N₁ ∩ N₂)).val := by
  unfold interHeadCode
  rw [setEquivFin_val (atomEquiv τ k) (N₁ ∩ N₂)]
  refine packBits_congr fun a ha => ?_
  rw [dif_pos ha]
  let A := (atomEquiv τ k).symm ⟨a, ha⟩
  have ha_eq : (atomEquiv τ k A).val = a := by simp [A]
  have h1 := unpackBit_setEquivFin (atomEquiv τ k) N₁ A
  have h2 := unpackBit_setEquivFin (atomEquiv τ k) N₂ A
  rw [ha_eq] at h1 h2
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, Set.mem_inter_iff]
  exact ⟨fun ⟨b1, b2⟩ => ⟨h1.1 b1, h2.1 b2⟩, fun ⟨m1, m2⟩ => ⟨h1.2 m1, h2.2 m2⟩⟩

open Classical in
theorem joinIter_spec {σ : Sig} {nt nc na : ℕ} (gt_fn : Fin nt → Fin na) (gc_fn : Fin nc → Fin na)
    (k : ℕ) :
    let gt := List.ofFn (fun x => (gt_fn x).val)
    let gc := List.ofFn (fun x => (gc_fn x).val)
    ∀ m : ℕ,
      ((joinStep nc nt gc gt)^[m] (joinBase σ k)).1 = tower nc (atomCnt (sigmaEq σ) k) m ∧
      ((joinStep nc nt gc gt)^[m] (joinBase σ k)).2.1 = tower nt (atomCnt (sigmaEq σ) k) m ∧
      ((joinStep nc nt gc gt)^[m] (joinBase σ k)).2.2.length =
        tower nc (atomCnt (sigmaEq σ) k) m * tower nt (atomCnt (sigmaEq σ) k) m ∧
      ∀ (Hc : HTh (sigmaEq σ) (Fin nc) k m) (H : HTh (sigmaEq σ) (Fin nt) k m),
        ((joinStep nc nt gc gt)^[m] (joinBase σ k)).2.2.getD
          ((hthEquiv (sigmaEq σ) nc k m Hc).val +
            ((joinStep nc nt gc gt)^[m] (joinBase σ k)).1 *
              (hthEquiv (sigmaEq σ) nt k m H).val) 0 =
          (hthEquiv (sigmaEq σ) nt k m
            (push (Fib.snd : Fib gc_fn gt_fn → Fin nt) m (pb gc_fn gt_fn m Hc H))).val := by
  intro gt gc m
  let τ := sigmaEq σ
  let q := atomCnt τ k
  induction m with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    refine ⟨rfl, rfl, by simp [joinBase, tower], fun Hc H => ?_⟩
    let M0 := 2 ^ 2 ^ q
    generalize hac_def : (hthEquiv τ nc k 0 Hc).val = ac
    generalize hat_def : (hthEquiv τ nt k 0 H).val = at_
    have hac_lt : ac < M0 := hac_def ▸ (hthEquiv τ nc k 0 Hc).isLt
    have hat_lt : at_ < M0 := hat_def ▸ (hthEquiv τ nt k 0 H).isLt
    have hM0_pos : 0 < M0 := Nat.two_pow_pos _
    have hidx_lt : ac + M0 * at_ < M0 * M0 :=
      (prodEquivFin hM0_pos (⟨at_, hat_lt⟩, ⟨ac, hac_lt⟩)).isLt
    have hbase1 : (joinBase σ k).1 = M0 := rfl
    have hlt_len : ac + M0 * at_ < (joinBase σ k).2.2.length := by
      simpa [joinBase, M0, q, τ] using hidx_lt
    rw [hbase1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_len, Option.getD_some]
    simp only [joinBase, joinBaseCell, List.getElem_map, List.getElem_range]
    unfold joinBaseBit
    have hmod : (ac + M0 * at_) % M0 = ac := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hac_lt]
    have hdiv : (ac + M0 * at_) / M0 = at_ := by
      rw [Nat.add_mul_div_left _ _ hM0_pos, Nat.div_eq_zero_iff.2 (Or.inr hac_lt), zero_add]
    change packBits (2 ^ q) (fun h => (List.range (2 ^ q)).any fun h₁ =>
        unpackBit ((ac + M0 * at_) % M0) h₁ && (List.range (2 ^ q)).any fun h₂ =>
          unpackBit ((ac + M0 * at_) / M0) h₂ && (interHeadCode q h₁ h₂ == h)) =
      (setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps (pb gc_fn gt_fn 0 Hc H))).val
    rw [hmod, hdiv, setEquivFin_val]
    refine packBits_congr fun h hh => ?_
    rw [dif_pos hh]
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      pb, Set.mem_ofPred]
    have hac_hyps : (setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps Hc)).val = ac := hac_def
    have hat_hyps : (setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps H)).val = at_ := hat_def
    constructor
    · rintro ⟨h₁, hh₁, hbit₁, h₂, hh₂, hbit₂, hinter⟩
      let N₁ := (setEquivFin (atomEquiv τ k)).symm ⟨h₁, hh₁⟩
      let N₂ := (setEquivFin (atomEquiv τ k)).symm ⟨h₂, hh₂⟩
      have hc1 : (setEquivFin (atomEquiv τ k) N₁).val = h₁ := by simp [N₁]
      have hc2 : (setEquivFin (atomEquiv τ k) N₂).val = h₂ := by simp [N₂]
      have hN₁ : N₁ ∈ HTh.hyps Hc := by
        have := unpackBit_setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps Hc) N₁
        rw [hac_hyps, hc1] at this; exact this.1 hbit₁
      have hN₂ : N₂ ∈ HTh.hyps H := by
        have := unpackBit_setEquivFin (setEquivFin (atomEquiv τ k)) (HTh.hyps H) N₂
        rw [hat_hyps, hc2] at this; exact this.1 hbit₂
      refine ⟨N₁, hN₁, N₂, hN₂, ?_⟩
      rw [← hc1, ← hc2, interHeadCode_spec τ k N₁ N₂] at hinter
      apply (setEquivFin (atomEquiv τ k)).injective
      ext; simpa using hinter.symm
    · rintro ⟨N₁, hN₁, N₂, hN₂, heq⟩
      let c₁ := setEquivFin (atomEquiv τ k) N₁
      let c₂ := setEquivFin (atomEquiv τ k) N₂
      refine ⟨c₁.val, c₁.isLt, ?_, c₂.val, c₂.isLt, ?_, ?_⟩
      · rw [← hac_hyps]; exact (unpackBit_setEquivFin _ (HTh.hyps Hc) N₁).2 hN₁
      · rw [← hat_hyps]; exact (unpackBit_setEquivFin _ (HTh.hyps H) N₂).2 hN₂
      · rw [interHeadCode_spec τ k N₁ N₂, ← heq]; simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    generalize hst : (joinStep nc nt gc gt)^[m] (joinBase σ k) = st
    rw [hst] at ih
    obtain ⟨hMc, hMt, _, ih_spec⟩ := ih
    let Mc := tower nc q m
    let Mt := tower nt q m
    have hMc_eq : st.1 = Mc := hMc
    have hMt_eq : st.2.1 = Mt := hMt
    have hMc_pos : 0 < Mc := tower_pos nc q m
    have hMt_pos : 0 < Mt := tower_pos nt q m
    let Mc' := tower nc q (m + 1)
    let Mt' := tower nt q (m + 1)
    have hMc'_pos : 0 < Mc' := tower_pos nc q (m + 1)
    have hstep1 : (joinStep nc nt gc gt st).1 = Mc' := by
      simp [joinStep, hMc_eq, Mc', Mc, tower, q, τ]
    refine ⟨hstep1, by simp [joinStep, hMt_eq, Mt, tower, q, τ],
      by simp [joinStep, hMc_eq, hMt_eq, Mc, Mt, tower, q, τ], fun Hc H => ?_⟩
    generalize hac_def : (hthEquiv τ nc k (m + 1) Hc).val = ac
    generalize hat_def : (hthEquiv τ nt k (m + 1) H).val = at_
    have hac_lt : ac < Mc' := hac_def ▸ (hthEquiv τ nc k (m + 1) Hc).isLt
    have hat_lt : at_ < Mt' := hat_def ▸ (hthEquiv τ nt k (m + 1) H).isLt
    have hidx_lt : ac + Mc' * at_ < Mc' * Mt' :=
      ((prodEquivFin hMc'_pos (⟨at_, hat_lt⟩, ⟨ac, hac_lt⟩)).isLt).trans_eq (Nat.mul_comm Mt' Mc')
    have hlt_len : ac + Mc' * at_ < (joinStep nc nt gc gt st).2.2.length := by
      simpa [joinStep, hMc_eq, hMt_eq, Mc', Mt', Mc, Mt, tower, q, τ] using hidx_lt
    rw [hstep1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt_len, Option.getD_some]
    simp only [joinStep, joinStepCell, hMc_eq, hMt_eq, List.getElem_map, List.getElem_range]
    have hMc'_def : 2 ^ (nc * 2 ^ (nc * Mc)) = Mc' := rfl
    have hmod : (ac + Mc' * at_) % (2 ^ (nc * 2 ^ (nc * Mc))) = ac := by
      rw [hMc'_def, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hac_lt]
    have hdiv : (ac + Mc' * at_) / (2 ^ (nc * 2 ^ (nc * Mc))) = at_ := by
      rw [hMc'_def, Nat.add_mul_div_left _ _ hMc'_pos, Nat.div_eq_zero_iff.2 (Or.inr hac_lt),
        zero_add]
    rw [hthEquiv_succ_val]
    refine packBase_congr fun xt hxt => ?_
    rw [dif_pos hxt, hmod, hdiv]
    let xt' : Fin nt := ⟨xt, hxt⟩
    have hfamt_eq : unpackBase (2 ^ 2 ^ (nt * Mt)) at_ xt = (famEquiv τ nt k m (H xt')).val := by
      rw [← hat_def]
      exact unpackBase_hthEquiv_succ τ nt k m H xt'
    let env : JoinEnv := ((nc, nt, Mc, Mt), (gc, gt, st.2.2))
    change joinStepFam env ac at_ xt =
      (famEquiv τ nt k m (push (Fib.snd : Fib gc_fn gt_fn → Fin nt) (m + 1)
        (pb gc_fn gt_fn (m + 1) Hc H) xt')).val
    refine Eq.trans ?_
      (congrArg (fun S => (famEquiv τ nt k m S).val) (push_snd_pb_succ gc_fn gt_fn m Hc H xt')).symm
    unfold joinStepFam joinFamBit joinFamInner
    dsimp only [env]
    rw [hfamt_eq]
    have hpers_spec : ∀ (p₁ : Set (Fin nc × HTh τ (Fin nc) k m))
        (p₂ : Set (Fin nt × HTh τ (Fin nt) k m)),
        joinPersCode env (persEquiv τ nc k m p₁).val (persEquiv τ nt k m p₂).val =
          (persEquiv τ nt k m
            {yd : Fin nt × HTh τ (Fin nt) k m | ∃ yc c₁ c₂, gc_fn yc = gt_fn yd.1 ∧
              (yc, c₁) ∈ p₁ ∧ (yd.1, c₂) ∈ p₂ ∧
              yd.2 = push (Fib.snd : Fib gc_fn gt_fn → Fin nt) m (pb gc_fn gt_fn m c₁ c₂)}).val := by
      intro p₁ p₂
      let targetSet : Set (Fin nt × HTh τ (Fin nt) k m) :=
        {yd : Fin nt × HTh τ (Fin nt) k m | ∃ yc c₁ c₂, gc_fn yc = gt_fn yd.1 ∧
          (yc, c₁) ∈ p₁ ∧ (yd.1, c₂) ∈ p₂ ∧
          yd.2 = push (Fib.snd : Fib gc_fn gt_fn → Fin nt) m (pb gc_fn gt_fn m c₁ c₂)}
      change joinPersCode env (setEquivFin (pairEquiv τ nc k m) p₁).val
          (setEquivFin (pairEquiv τ nt k m) p₂).val =
        (setEquivFin (pairEquiv τ nt k m) targetSet).val
      unfold joinPersCode joinPersBit joinPersInner
      dsimp only [env]
      rw [setEquivFin_val (pairEquiv τ nt k m) targetSet]
      refine packBits_congr fun u hu => ?_
      rw [dif_pos hu]
      apply Bool.eq_iff_iff.2
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
        targetSet, Set.mem_ofPred]
      have hdiv_lt : u / Mt < nt := (Nat.div_lt_iff_lt_mul hMt_pos).2 hu
      let yt' : Fin nt := ⟨u / Mt, hdiv_lt⟩
      have hyt_eq : ((pairEquiv τ nt k m).symm ⟨u, hu⟩).1 = yt' := rfl
      have hgt_yt : gt.getD (u / Mt) 0 = (gt_fn yt').val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [gt, hdiv_lt])]
        simp [gt, yt']
      constructor
      · rintro ⟨yc, hyc, hedge, c₁, hc₁, hbit₁, c₂, hc₂, hbit₂, hj_eq⟩
        let yc' : Fin nc := ⟨yc, hyc⟩
        have hgc_yc : gc.getD yc 0 = (gc_fn yc').val := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [gc, hyc])]
          simp [gc, yc']
        rw [hgc_yc, hgt_yt] at hedge
        let Hc₁ := (hthEquiv τ nc k m).symm ⟨c₁, hc₁⟩
        let H₂ := (hthEquiv τ nt k m).symm ⟨c₂, hc₂⟩
        have hc1_val : (hthEquiv τ nc k m Hc₁).val = c₁ := by simp [Hc₁]
        have hc2_val : (hthEquiv τ nt k m H₂).val = c₂ := by simp [H₂]
        have hmem1 : (yc', Hc₁) ∈ p₁ := by
          have := unpackBit_setEquivFin (pairEquiv τ nc k m) p₁ (yc', Hc₁)
          rw [pairEquiv_val, hc1_val] at this; exact this.1 hbit₁
        have hmem2 : (yt', H₂) ∈ p₂ := by
          have := unpackBit_setEquivFin (pairEquiv τ nt k m) p₂ (yt', H₂)
          rw [pairEquiv_val, hc2_val] at this; exact this.1 hbit₂
        have hih := ih_spec Hc₁ H₂
        rw [hMc_eq, hc1_val, hc2_val] at hih
        rw [hih] at hj_eq
        refine ⟨yc', Hc₁, H₂, ?_, hmem1, ?_, ?_⟩
        · rw [hyt_eq]; ext; exact hedge
        · rw [hyt_eq]; exact hmem2
        · rw [pairEquiv_symm_snd]
          apply (hthEquiv τ nt k m).injective
          ext; simpa using hj_eq.symm
      · rintro ⟨yc', Hc₁, H₂, hedge, hmem1, hmem2, hd_eq⟩
        rw [hyt_eq] at hedge hmem2
        let c₁ := (hthEquiv τ nc k m Hc₁).val
        let c₂ := (hthEquiv τ nt k m H₂).val
        have hgc_yc : gc.getD yc'.val 0 = (gc_fn yc').val := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [gc, yc'.isLt])]
          simp [gc]
        refine ⟨yc'.val, yc'.isLt, ?_, c₁, (hthEquiv τ nc k m Hc₁).isLt, ?_,
          c₂, (hthEquiv τ nt k m H₂).isLt, ?_, ?_⟩
        · rw [hgc_yc, hgt_yt]; exact congrArg Fin.val hedge
        · have := (unpackBit_setEquivFin (pairEquiv τ nc k m) p₁ (yc', Hc₁)).2 hmem1
          simpa [pairEquiv_val, c₁, Mc, q, τ] using this
        · have := (unpackBit_setEquivFin (pairEquiv τ nt k m) p₂ (yt', H₂)).2 hmem2
          simpa [pairEquiv_val, c₂, yt', Mt, q, τ] using this
        · have hih := ih_spec Hc₁ H₂
          rw [hMc_eq] at hih
          rw [hih, ← hd_eq, pairEquiv_symm_snd]
          simp [Mt, q, τ]
    unfold famEquiv
    rw [setEquivFin_val (persEquiv τ nt k m)]
    refine packBits_congr fun qc hqc => ?_
    rw [dif_pos hqc]
    have hgt_xt : gt.getD xt 0 = (gt_fn xt').val := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [gt, hxt])]
      simp [gt, xt']
    apply Bool.eq_iff_iff.2
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨xc, hxc, hedge, p₁c, hp₁c, hbit₁, p₂c, hp₂c, hbit₂, hpers_eq⟩
      let xc' : Fin nc := ⟨xc, hxc⟩
      have hgc_xc : gc.getD xc 0 = (gc_fn xc').val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [gc, hxc])]
        simp [gc, xc']
      rw [hgc_xc, hgt_xt] at hedge
      have hfamc_eq : unpackBase (2 ^ 2 ^ (nc * Mc)) ac xc =
          (setEquivFin (persEquiv τ nc k m) (Hc xc')).val := by
        rw [← hac_def]
        exact unpackBase_hthEquiv_succ τ nc k m Hc xc'
      rw [hfamc_eq] at hbit₁
      let p₁ := (persEquiv τ nc k m).symm ⟨p₁c, hp₁c⟩
      let p₂ := (persEquiv τ nt k m).symm ⟨p₂c, hp₂c⟩
      have hp1_val : (persEquiv τ nc k m p₁).val = p₁c := by simp [p₁]
      have hp2_val : (persEquiv τ nt k m p₂).val = p₂c := by simp [p₂]
      have hp₁_mem : p₁ ∈ Hc xc' := by
        have := unpackBit_setEquivFin (persEquiv τ nc k m) (Hc xc') p₁
        rw [hp1_val] at this; exact this.1 hbit₁
      have hp₂_mem : p₂ ∈ H xt' := by
        have := unpackBit_setEquivFin (persEquiv τ nt k m) (H xt') p₂
        rw [hp2_val] at this; exact this.1 hbit₂
      change joinPersCode env p₁c p₂c = qc at hpers_eq
      rw [← hp1_val, ← hp2_val, hpers_spec p₁ p₂] at hpers_eq
      refine ⟨xc', ?_, p₁, hp₁_mem, p₂, hp₂_mem, ?_⟩
      · ext; exact hedge
      · apply (persEquiv τ nt k m).injective
        ext; simpa using hpers_eq.symm
    · rintro ⟨xc', hedge, p₁, hp₁_mem, p₂, hp₂_mem, hq_eq⟩
      have hgc_xc : gc.getD xc'.val 0 = (gc_fn xc').val := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [gc, xc'.isLt])]
        simp [gc]
      have hfamc_eq : unpackBase (2 ^ 2 ^ (nc * Mc)) ac xc'.val =
          (setEquivFin (persEquiv τ nc k m) (Hc xc')).val := by
        rw [← hac_def]
        exact unpackBase_hthEquiv_succ τ nc k m Hc xc'
      let p₁c := persEquiv τ nc k m p₁
      let p₂c := persEquiv τ nt k m p₂
      refine ⟨xc'.val, xc'.isLt, ?_, p₁c.val, p₁c.isLt, ?_, p₂c.val, p₂c.isLt, ?_, ?_⟩
      · rw [hgc_xc, hgt_xt]; exact congrArg Fin.val hedge
      · rw [hfamc_eq]; exact (unpackBit_setEquivFin (persEquiv τ nc k m) (Hc xc') p₁).2 hp₁_mem
      · exact (unpackBit_setEquivFin (persEquiv τ nt k m) (H xt') p₂).2 hp₂_mem
      · change joinPersCode env p₁c.val p₂c.val = qc
        rw [hpers_spec p₁ p₂, ← hq_eq]; simp

theorem joinHThCode_spec {σ : Sig} {nt nc na : ℕ} (gt_fn : Fin nt → Fin na) (gc_fn : Fin nc → Fin na)
    (ℓ : ℕ) (Hc : HTh (sigmaEq σ) (Fin nc) (2 * ℓ) ℓ) (H : HTh (sigmaEq σ) (Fin nt) (2 * ℓ) ℓ) :
    joinHThCode σ nt nc (List.ofFn (fun x => (gt_fn x).val)) (List.ofFn (fun x => (gc_fn x).val)) ℓ
        (hthEquiv (sigmaEq σ) nc (2 * ℓ) ℓ Hc).val
        (hthEquiv (sigmaEq σ) nt (2 * ℓ) ℓ H).val =
      (hthEquiv (sigmaEq σ) nt (2 * ℓ) ℓ
        (push (Fib.snd : Fib gc_fn gt_fn → Fin nt) ℓ (pb gc_fn gt_fn ℓ Hc H))).val :=
  (joinIter_spec gt_fn gc_fn (2 * ℓ) ℓ).2.2.2 Hc H

attribute [local irreducible] evalHThCode leafHThCode joinHThCode

/-! ### 14. Matrix property of `altMatrix φ` and bound monotonicity -/

theorem matrixOf_isQF {σ : Sig} (k : ℕ) :
    ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k) (q : ℕ)
      (neg : Bool) (h : 2 * (q + quantCount f) ≤ k), (matrixOf k f env q neg h).IsQF
  | _, .falsum, _, _, _, _ => BoundedFormula.IsQF.falsum
  | _, .equal _ _, _, _, _, _ => BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | _, .rel _ _, _, _, _, _ => BoundedFormula.IsQF.of_isAtomic (BoundedFormula.IsAtomic.rel _ _)
  | _, .imp f g, _, _, _, _ =>
      BoundedFormula.IsQF.imp (matrixOf_isQF k f _ _ _ _) (matrixOf_isQF k g _ _ _ _)
  | _, .all f, _, _, _, _ => matrixOf_isQF k f _ _ _ _

theorem matrixOf_eqFree {σ : Sig} (k : ℕ) :
    ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n) (env : Fin n → Fin k) (q : ℕ)
      (neg : Bool) (h : 2 * (q + quantCount f) ≤ k), EqFree (matrixOf k f env q neg h)
  | _, .falsum, _, _, _, _ => trivial
  | _, .equal _ _, _, _, _, _ => trivial
  | _, .rel _ _, _, _, _, _ => trivial
  | _, .imp f g, _, _, _, _ => ⟨matrixOf_eqFree k f _ _ _ _, matrixOf_eqFree k g _ _ _ _⟩
  | _, .all f, _, _, _, _ => matrixOf_eqFree k f _ _ _ _

theorem isMatrix_altMatrix {σ : Sig} (φ : σ.lang.Sentence) : IsMatrix (altMatrix φ) :=
  ⟨matrixOf_isQF _ _ _ _ _ _, matrixOf_eqFree _ _ _ _ _ _⟩

theorem quantCount_le_sentLen {σ : Sig} :
    ∀ {n : ℕ} (f : σ.lang.BoundedFormula Empty n), quantCount f ≤ sentLen f
  | _, .falsum => by simp [quantCount, sentLen, encF]
  | _, .equal _ _ => by simp [quantCount, sentLen, encF]
  | _, .rel _ _ => by simp [quantCount, sentLen, encF]
  | _, .imp f g => by
    have h1 := quantCount_le_sentLen f
    have h2 := quantCount_le_sentLen g
    simp only [sentLen] at h1 h2
    simp only [quantCount, sentLen, encF, List.length_cons, List.length_append]
    omega
  | _, .all f => by
    have h1 := quantCount_le_sentLen f
    simp only [sentLen] at h1
    simp only [quantCount, sentLen, encF, List.length_cons]
    omega

theorem atomCnt_mono (τ : Sig) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) : atomCnt τ k₁ ≤ atomCnt τ k₂ := by
  rw [atomCnt_eq_sum, atomCnt_eq_sum]
  exact Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left hk _

theorem tower_mono_wq {w₁ w₂ q₁ q₂ : ℕ} (hw : w₁ ≤ w₂) (hq : q₁ ≤ q₂) :
    ∀ m : ℕ, tower w₁ q₁ m ≤ tower w₂ q₂ m
  | 0 => Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hq)
  | m + 1 => by
    have ih := tower_mono_wq hw hq m
    unfold tower
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.mul_le_mul hw (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hw ih))

theorem tower_le_succ (w q m : ℕ) (hw : 1 ≤ w) : tower w q m ≤ tower w q (m + 1) := by
  let X := tower w q m
  change X ≤ 2 ^ (w * 2 ^ (w * X))
  have h1 : X ≤ w * X := Nat.le_mul_of_pos_left X hw
  have h2 : w * X ≤ 2 ^ (w * X) := (Nat.lt_two_pow_self (n := w * X)).le
  have h3 : 2 ^ (w * X) ≤ w * 2 ^ (w * X) := Nat.le_mul_of_pos_left _ hw
  have h4 : w * 2 ^ (w * X) ≤ 2 ^ (w * 2 ^ (w * X)) := (Nat.lt_two_pow_self).le
  exact le_trans h1 (le_trans h2 (le_trans h3 h4))

theorem tower_mono_m (w q : ℕ) (hw : 1 ≤ w) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    tower w q m₁ ≤ tower w q m₂ := by
  induction hm with
  | refl => exact le_rfl
  | @step m _ ih => exact le_trans ih (tower_le_succ w q m hw)

theorem nat_pair_le_quad (a b : ℕ) : Nat.pair a b ≤ (a + b) * (a + b) + (a + b) := by
  unfold Nat.pair
  split_ifs <;> nlinarith

/-! ### 15. Empty vs non-empty limits of tree co-decompositions -/

theorem graph_adj {σ : Sig} (T : CoDecomp σ) (e : Fin T.m) :
    T.graph.Adj (T.ends e).1 (T.ends e).2 := by
  rw [CoDecomp.graph, fromEdgeSet_adj]
  exact ⟨⟨e, rfl⟩, T.ends_ne e⟩

theorem exists_edge_of_adj {σ : Sig} (T : CoDecomp σ) {u v : Fin T.b} (h : T.graph.Adj u v) :
    ∃ e, ((T.ends e).1 = u ∧ (T.ends e).2 = v) ∨ ((T.ends e).1 = v ∧ (T.ends e).2 = u) := by
  rw [CoDecomp.graph, fromEdgeSet_adj] at h
  obtain ⟨⟨e, he⟩, -⟩ := h
  exact ⟨e, Sym2.eq_iff.1 he⟩

theorem edge_unique {σ : Sig} (T : CoDecomp σ) {e e' : Fin T.m}
    (h : ((T.ends e).1 = (T.ends e').1 ∧ (T.ends e).2 = (T.ends e').2) ∨
      ((T.ends e).1 = (T.ends e').2 ∧ (T.ends e).2 = (T.ends e').1)) : e = e' :=
  T.ends_inj (Sym2.eq_iff.2 h)

theorem exists_adj_dist {V : Type} {G : SimpleGraph V} (hG : G.Connected) {u c : V} (h : u ≠ c) :
    ∃ u', G.Adj u u' ∧ G.dist u' c + 1 = G.dist u c := by
  obtain ⟨p, -, hlen⟩ := hG.exists_path_of_dist u c
  cases p with
  | nil => exact absurd rfl h
  | @cons _ w _ hadj q =>
    refine ⟨w, hadj, ?_⟩
    have h1 : G.dist w c ≤ q.length := dist_le q
    have h2 : G.dist u c ≤ G.dist u w + G.dist w c := hG.dist_triangle
    have h3 : G.dist u w = 1 := dist_eq_one_iff_adj.2 hadj
    rw [Walk.length_cons] at hlen
    omega

theorem parent_unique {V : Type} {G : SimpleGraph V} (hG : G.IsTree) {r v w₁ w₂ : V}
    (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂)
    (d₁ : G.dist w₁ r + 1 = G.dist v r) (d₂ : G.dist w₂ r + 1 = G.dist v r) : w₁ = w₂ := by
  classical
  obtain ⟨p₁, hp₁, l₁⟩ := hG.connected.exists_path_of_dist w₁ r
  obtain ⟨p₂, hp₂, l₂⟩ := hG.connected.exists_path_of_dist w₂ r
  have n₁ : v ∉ p₁.support := by
    intro hv
    have a1 := dist_le (p₁.dropUntil v hv)
    have a2 := p₁.length_dropUntil_le_length hv
    omega
  have n₂ : v ∉ p₂.support := by
    intro hv
    have a1 := dist_le (p₂.dropUntil v hv)
    have a2 := p₂.length_dropUntil_le_length hv
    omega
  have e := (hG.isAcyclic.subsingleton_path v r).elim
    ⟨Walk.cons h₁ p₁, hp₁.cons n₁⟩ ⟨Walk.cons h₂ p₂, hp₂.cons n₂⟩
  have e' : Walk.cons h₁ p₁ = Walk.cons h₂ p₂ := congrArg Subtype.val e
  simpa using congrArg Walk.snd e'

theorem bag_zero_ends {σ : Sig} (T : CoDecomp σ) (e : Fin T.m) :
    (T.bag (T.ends e).1).n = 0 ↔ (T.bag (T.ends e).2).n = 0 := by
  constructor
  · intro h1
    by_contra h2
    obtain ⟨x, -⟩ := T.gl_surj e (T.gr e ⟨0, Nat.pos_of_ne_zero h2⟩)
    have hx := x.isLt
    omega
  · intro h2
    by_contra h1
    obtain ⟨y, -⟩ := T.gr_surj e (T.gl e ⟨0, Nat.pos_of_ne_zero h1⟩)
    have hy := y.isLt
    omega

theorem bag_zero_adj {σ : Sig} {T : CoDecomp σ} {u v : Fin T.b} (h : T.graph.Adj u v) :
    (T.bag u).n = 0 ↔ (T.bag v).n = 0 := by
  obtain ⟨e, ⟨he1, he2⟩ | ⟨he1, he2⟩⟩ := exists_edge_of_adj T h
  · rw [← he1, ← he2]; exact bag_zero_ends T e
  · rw [← he1, ← he2]; exact (bag_zero_ends T e).symm

theorem bag_zero_iff {σ : Sig} {T : CoDecomp σ} (s t : Fin T.b) :
    (T.bag s).n = 0 ↔ (T.bag t).n = 0 := by
  have hTree : T.graph.IsTree := T.isTree
  obtain ⟨p⟩ := hTree.connected s t
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (bag_zero_adj hadj).trans ih

theorem edgeMap_surj {σ : Sig} (T : CoDecomp σ) (e : Fin T.m) (s : Fin T.b)
    (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) :
    Function.Surjective (T.edgeMap e s hs) := by
  intro z
  unfold CoDecomp.edgeMap
  split_ifs with h
  · subst h
    obtain ⟨x, hx⟩ := T.gl_surj e z
    exact ⟨x, hx⟩
  · have h2 : s = (T.ends e).2 := hs.resolve_left h
    subst h2
    obtain ⟨x, hx⟩ := T.gr_surj e z
    exact ⟨x, hx⟩

theorem edgeMap_val_gl {σ : Sig} (T : CoDecomp σ) {e e' : Fin T.m} (he : e' = e)
    {s : Fin T.b} (hs_mem : s = (T.ends e').1 ∨ s = (T.ends e').2)
    (hs1 : s = (T.ends e).1) (x : Fin (T.bag s).n) (x' : Fin (T.bag (T.ends e).1).n)
    (hx : x.val = x'.val) :
    (T.edgeMap e' s hs_mem x).val = (T.gl e x').val := by
  subst he
  subst hs1
  have hxx : x = x' := Fin.ext hx
  subst hxx
  unfold CoDecomp.edgeMap
  rw [dif_pos rfl]

theorem edgeMap_val_gr {σ : Sig} (T : CoDecomp σ) {e e' : Fin T.m} (he : e' = e)
    {s : Fin T.b} (hs_mem : s = (T.ends e').1 ∨ s = (T.ends e').2)
    (hs2 : s = (T.ends e).2) (x : Fin (T.bag s).n) (x' : Fin (T.bag (T.ends e).2).n)
    (hx : x.val = x'.val) :
    (T.edgeMap e' s hs_mem x).val = (T.gr e x').val := by
  subst he
  subst hs2
  have hxx : x = x' := Fin.ext hx
  subst hxx
  unfold CoDecomp.edgeMap
  rw [dif_neg (fun h => T.ends_ne e' h.symm)]

theorem limOn_val_eq {σ : Sig} {T : CoDecomp σ} {S : Set (Fin T.b)} (y : T.LimOn S)
    {s₁ s₂ : Fin T.b} (h : s₁ = s₂) (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) :
    (y.val ⟨s₁, h₁⟩).val = (y.val ⟨s₂, h₂⟩).val := by
  subst h
  rfl

theorem nonempty_lim_of_bag_pos {σ : Sig} {T : CoDecomp σ} (r : Fin T.b) (hr : 0 < (T.bag r).n) :
    Nonempty T.Lim := by
  classical
  have hTree : T.graph.IsTree := T.isTree
  have dist_self_zero : ∀ s : Fin T.b, T.graph.dist s s = 0 := fun s =>
    Nat.eq_zero_of_le_zero (dist_le Walk.nil)
  have eq_of_dist_zero : ∀ s : Fin T.b, T.graph.dist s r = 0 → s = r := by
    intro s hs
    obtain ⟨p, -, hlen⟩ := hTree.connected.exists_path_of_dist s r
    cases p with
    | nil => rfl
    | cons _ _ => simp [Walk.length_cons] at hlen; omega
  have ball_nonempty : ∀ d : ℕ, Nonempty (T.LimOn {s : Fin T.b | T.graph.dist s r ≤ d}) := by
    intro d
    induction d with
    | zero =>
      refine ⟨⟨fun s => ?_, fun e h₁ h₂ => ?_⟩⟩
      · have hsr : s.1 = r := eq_of_dist_zero s.1 (Nat.eq_zero_of_le_zero s.2)
        exact ⟨0, by rw [hsr]; exact hr⟩
      · have e1 : (T.ends e).1 = r := eq_of_dist_zero _ (Nat.eq_zero_of_le_zero h₁)
        have e2 : (T.ends e).2 = r := eq_of_dist_zero _ (Nat.eq_zero_of_le_zero h₂)
        exact absurd (e1.trans e2.symm) (T.ends_ne e)
    | succ d ih =>
      obtain ⟨y⟩ := ih
      have step_ext : ∀ (s : Fin T.b), T.graph.dist s r = d + 1 →
          ∃ (p : Fin T.b) (hp : T.graph.dist p r = d) (e : Fin T.m)
            (hs_mem : s = (T.ends e).1 ∨ s = (T.ends e).2)
            (hp_mem : p = (T.ends e).1 ∨ p = (T.ends e).2)
            (xs : Fin (T.bag s).n),
            T.graph.Adj s p ∧
            T.edgeMap e s hs_mem xs = T.edgeMap e p hp_mem (y.val ⟨p, hp.le⟩) := by
        intro s hs
        have hne : s ≠ r := by intro h; rw [h, dist_self_zero] at hs; omega
        obtain ⟨p, hadj, hdp⟩ := exists_adj_dist hTree.connected hne
        have hp : T.graph.dist p r = d := by omega
        obtain ⟨e, he⟩ := exists_edge_of_adj T hadj
        have hs_mem : s = (T.ends e).1 ∨ s = (T.ends e).2 := by
          rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact Or.inl h1.symm
          · exact Or.inr h2.symm
        have hp_mem : p = (T.ends e).1 ∨ p = (T.ends e).2 := by
          rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact Or.inr h2.symm
          · exact Or.inl h1.symm
        obtain ⟨xs, hxs⟩ := edgeMap_surj T e s hs_mem (T.edgeMap e p hp_mem (y.val ⟨p, hp.le⟩))
        exact ⟨p, hp, e, hs_mem, hp_mem, xs, hadj, hxs⟩
      choose pFn hpFn eFn hsMem hpMem xsFn hadjFn hxsFn using step_ext
      let val' : (s : {s : Fin T.b | T.graph.dist s r ≤ d + 1}) → Fin (T.bag s.1).n :=
        fun s => if h : T.graph.dist s.1 r ≤ d then y.val ⟨s.1, h⟩
          else xsFn s.1 (by have := s.2; change T.graph.dist s.1 r ≤ d + 1 at this; omega)
      refine ⟨⟨val', fun e h₁ h₂ => ?_⟩⟩
      have hu_le : T.graph.dist (T.ends e).1 r ≤ d + 1 := h₁
      have hv_le : T.graph.dist (T.ends e).2 r ≤ d + 1 := h₂
      have hadj_uv : T.graph.Adj (T.ends e).1 (T.ends e).2 := graph_adj T e
      have hdist_step : T.graph.dist (T.ends e).1 r = T.graph.dist (T.ends e).2 r + 1 ∨
          T.graph.dist (T.ends e).2 r = T.graph.dist (T.ends e).1 r + 1 := by
        have := hTree.dist_eq_dist_add_one_of_adj r hadj_uv
        rw [dist_comm (u := r) (v := (T.ends e).1), dist_comm (u := r) (v := (T.ends e).2)] at this
        exact this
      by_cases ku : T.graph.dist (T.ends e).1 r ≤ d <;>
        by_cases kv : T.graph.dist (T.ends e).2 r ≤ d
      · simp only [val', ku, kv, ↓reduceDIte]
        exact y.compat e ku kv
      · have hdv : T.graph.dist (T.ends e).2 r = d + 1 := by omega
        have hdu : T.graph.dist (T.ends e).1 r = d := by omega
        simp only [val', ku, kv, ↓reduceDIte]
        have hp_eq : (T.ends e).1 = pFn (T.ends e).2 hdv :=
          parent_unique (r := r) hTree hadj_uv.symm (hadjFn (T.ends e).2 hdv)
            (by omega) (by rw [hpFn (T.ends e).2 hdv]; omega)
        have he_eq : e = eFn (T.ends e).2 hdv := by
          apply edge_unique T
          rcases hsMem (T.ends e).2 hdv with hv1 | hv2 <;>
            rcases hpMem (T.ends e).2 hdv with hp1 | hp2
          · exfalso; exact hadj_uv.ne (hp_eq.trans (hp1.trans hv1.symm))
          · right; exact ⟨hp_eq.trans hp2, hv1⟩
          · left; exact ⟨hp_eq.trans hp1, hv2⟩
          · exfalso; exact hadj_uv.ne (hp_eq.trans (hp2.trans hv2.symm))
        have hspec_val := congrArg Fin.val (hxsFn (T.ends e).2 hdv)
        have hv_em := edgeMap_val_gr T he_eq.symm (hsMem (T.ends e).2 hdv) rfl
          (xsFn (T.ends e).2 hdv) (xsFn (T.ends e).2 hdv) rfl
        have hp_em := edgeMap_val_gl T he_eq.symm (hpMem (T.ends e).2 hdv) hp_eq.symm
          (y.val ⟨pFn (T.ends e).2 hdv, (hpFn (T.ends e).2 hdv).le⟩)
          (y.val ⟨(T.ends e).1, ku⟩)
          (limOn_val_eq y hp_eq.symm (hpFn (T.ends e).2 hdv).le ku)
        rw [hv_em, hp_em] at hspec_val
        exact Fin.ext hspec_val.symm
      · have hdu : T.graph.dist (T.ends e).1 r = d + 1 := by omega
        have hdv : T.graph.dist (T.ends e).2 r = d := by omega
        simp only [val', ku, kv, ↓reduceDIte]
        have hp_eq : (T.ends e).2 = pFn (T.ends e).1 hdu :=
          parent_unique (r := r) hTree hadj_uv (hadjFn (T.ends e).1 hdu)
            (by omega) (by rw [hpFn (T.ends e).1 hdu]; omega)
        have he_eq : e = eFn (T.ends e).1 hdu := by
          apply edge_unique T
          rcases hsMem (T.ends e).1 hdu with hu1 | hu2 <;>
            rcases hpMem (T.ends e).1 hdu with hp1 | hp2
          · exfalso; exact hadj_uv.ne ((hu1.trans hp1.symm).trans hp_eq.symm)
          · left; exact ⟨hu1, hp_eq.trans hp2⟩
          · right; exact ⟨hu2, hp_eq.trans hp1⟩
          · exfalso; exact hadj_uv.ne ((hu2.trans hp2.symm).trans hp_eq.symm)
        have hspec_val := congrArg Fin.val (hxsFn (T.ends e).1 hdu)
        have hu_em := edgeMap_val_gl T he_eq.symm (hsMem (T.ends e).1 hdu) rfl
          (xsFn (T.ends e).1 hdu) (xsFn (T.ends e).1 hdu) rfl
        have hp_em := edgeMap_val_gr T he_eq.symm (hpMem (T.ends e).1 hdu) hp_eq.symm
          (y.val ⟨pFn (T.ends e).1 hdu, (hpFn (T.ends e).1 hdu).le⟩)
          (y.val ⟨(T.ends e).2, kv⟩)
          (limOn_val_eq y hp_eq.symm (hpFn (T.ends e).1 hdu).le kv)
        rw [hu_em, hp_em] at hspec_val
        exact Fin.ext hspec_val
      · omega
  let D := Finset.univ.sup (fun s : Fin T.b => T.graph.dist s r)
  obtain ⟨yD⟩ := ball_nonempty D
  have hD : ∀ s : Fin T.b, T.graph.dist s r ≤ D := fun s =>
    Finset.le_sup (f := fun s : Fin T.b => T.graph.dist s r) (Finset.mem_univ s)
  exact ⟨⟨fun t => yD.val ⟨t, hD t⟩, fun e => yD.compat e (hD _) (hD _)⟩⟩

/-! ### 16. Top-level numeric operations `leafFn`, `joinFn`, `accFn`, `boundFn` -/

def leafFn (σ : Sig) (s : List ℕ) : ℕ :=
  let fcode := nthFrame 0 s
  let bcode := nthFrame 1 s
  if bcode.headI = 0 then
    2 * packBits σ.r (fun i => decide (arN σ i = 0) && bagRelBit σ bcode i [])
  else
    let ℓ := (altScan σ fcode).headI
    2 * Nat.pair bcode.headI (leafHThCode σ bcode ℓ) + 1

def joinFn (σ : Sig) (s : List ℕ) : ℕ :=
  let fcode := nthFrame 0 s
  let bt := nthFrame 1 s
  let bc := nthFrame 2 s
  let gt := nthFrame 4 s
  let gc := nthFrame 5 s
  let vt := (nthFrame 6 s).headI
  let vc := (nthFrame 7 s).headI
  if bt.headI = 0 then
    2 * packBits σ.r (fun i => unpackBit (vt / 2) i && unpackBit (vc / 2) i)
  else
    let ℓ := (altScan σ fcode).headI
    let nt := bt.headI
    let nc := bc.headI
    let ht := ((vt - 1) / 2).unpair.2
    let hc := ((vc - 1) / 2).unpair.2
    2 * Nat.pair nt (joinHThCode σ nt nc gt gc ℓ hc ht) + 1

def accFn (σ : Sig) (s : List ℕ) : ℕ :=
  let fcode := nthFrame 0 s
  let v := (nthFrame 1 s).headI
  if v % 2 = 0 then
    if evalEmptyCode σ (v / 2) fcode then 1 else 0
  else
    let af := altScan σ fcode
    let ℓ := af.headI
    let ψcode := af.tail
    let nh := ((v - 1) / 2).unpair
    if evalHThCode σ nh.1 ℓ ψcode nh.2 then 1 else 0

def boundFn (σ : Sig) (w s : ℕ) : ℕ :=
  let T := tower (w + 1) (atomCnt (sigmaEq σ) (2 * s)) s
  2 * 2 ^ σ.r + 2 * ((w + T) * (w + T) + (w + T)) + 1

theorem primrec_leafFn (σ : Sig) : Primrec (leafFn σ) := by
  unfold leafFn
  have hfcode : Primrec (nthFrame 0) := primrec_nthFrame 0
  have hbcode : Primrec (nthFrame 1) := primrec_nthFrame 1
  have hn : Primrec (fun s : List ℕ => (nthFrame 1 s).headI) := Primrec.list_headI.comp hbcode
  refine Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) ?_ ?_
  · refine Primrec.nat_mul.comp (Primrec.const 2) (primrec_packBits (Primrec.const σ.r) ?_)
    have hs1 : Primrec (fun p : List ℕ × ℕ => p.1) := Primrec.fst
    have hi1 : Primrec (fun p : List ℕ × ℕ => p.2) := Primrec.snd
    have har0 : Primrec (fun p : List ℕ × ℕ => decide (arN σ p.2 = 0)) :=
      (Primrec.eq.comp ((primrec_arN σ).comp hi1) (Primrec.const 0)).decide
    have hrel : Primrec (fun p : List ℕ × ℕ => bagRelBit σ (nthFrame 1 p.1) p.2 []) :=
      (primrec_bagRelBit σ).comp (Primrec.pair (hbcode.comp hs1) (Primrec.pair hi1 (Primrec.const [])))
    exact (Primrec.and.comp har0 hrel).to₂
  · have hℓ : Primrec (fun s : List ℕ => (altScan σ (nthFrame 0 s)).headI) :=
      Primrec.list_headI.comp ((primrec_altScan σ).comp hfcode)
    have hleaf : Primrec (fun s : List ℕ => leafHThCode σ (nthFrame 1 s) (altScan σ (nthFrame 0 s)).headI) :=
      (primrec_leafHThCode σ).comp hbcode hℓ
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp hn hleaf))
      (Primrec.const 1)

theorem primrec_joinFn (σ : Sig) : Primrec (joinFn σ) := by
  unfold joinFn
  have hfcode : Primrec (nthFrame 0) := primrec_nthFrame 0
  have hbt : Primrec (nthFrame 1) := primrec_nthFrame 1
  have hbc : Primrec (nthFrame 2) := primrec_nthFrame 2
  have hgt : Primrec (nthFrame 4) := primrec_nthFrame 4
  have hgc : Primrec (nthFrame 5) := primrec_nthFrame 5
  have hvt : Primrec (fun s : List ℕ => (nthFrame 6 s).headI) :=
    Primrec.list_headI.comp (primrec_nthFrame 6)
  have hvc : Primrec (fun s : List ℕ => (nthFrame 7 s).headI) :=
    Primrec.list_headI.comp (primrec_nthFrame 7)
  have hnt : Primrec (fun s : List ℕ => (nthFrame 1 s).headI) := Primrec.list_headI.comp hbt
  have hnc : Primrec (fun s : List ℕ => (nthFrame 2 s).headI) := Primrec.list_headI.comp hbc
  refine Primrec.ite (Primrec.eq.comp hnt (Primrec.const 0)) ?_ ?_
  · refine Primrec.nat_mul.comp (Primrec.const 2) (primrec_packBits (Primrec.const σ.r) ?_)
    have hs1 : Primrec (fun p : List ℕ × ℕ => p.1) := Primrec.fst
    have hi1 : Primrec (fun p : List ℕ × ℕ => p.2) := Primrec.snd
    exact (Primrec.and.comp
      (primrec_unpackBit.comp (Primrec.nat_div.comp (hvt.comp hs1) (Primrec.const 2)) hi1)
      (primrec_unpackBit.comp (Primrec.nat_div.comp (hvc.comp hs1) (Primrec.const 2)) hi1)).to₂
  · have hℓ : Primrec (fun s : List ℕ => (altScan σ (nthFrame 0 s)).headI) :=
      Primrec.list_headI.comp ((primrec_altScan σ).comp hfcode)
    have unp_t : Primrec (fun s : List ℕ => (((nthFrame 6 s).headI - 1) / 2).unpair) :=
      Primrec.unpair.comp
        (Primrec.nat_div.comp (Primrec.nat_sub.comp hvt (Primrec.const 1)) (Primrec.const 2))
    have unp_c : Primrec (fun s : List ℕ => (((nthFrame 7 s).headI - 1) / 2).unpair) :=
      Primrec.unpair.comp
        (Primrec.nat_div.comp (Primrec.nat_sub.comp hvc (Primrec.const 1)) (Primrec.const 2))
    have hht : Primrec (fun s : List ℕ => (((nthFrame 6 s).headI - 1) / 2).unpair.2) :=
      Primrec.snd.comp unp_t
    have hhc : Primrec (fun s : List ℕ => (((nthFrame 7 s).headI - 1) / 2).unpair.2) :=
      Primrec.snd.comp unp_c
    have hjoin : Primrec (fun s : List ℕ =>
        joinHThCode σ (nthFrame 1 s).headI (nthFrame 2 s).headI (nthFrame 4 s) (nthFrame 5 s)
          (altScan σ (nthFrame 0 s)).headI (((nthFrame 7 s).headI - 1) / 2).unpair.2
          (((nthFrame 6 s).headI - 1) / 2).unpair.2) :=
      (primrec_joinHThCode σ).comp (Primrec.pair (Primrec.pair hnt hnc)
        (Primrec.pair (Primrec.pair hgt hgc) (Primrec.pair hℓ (Primrec.pair hhc hht))))
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp hnt hjoin))
      (Primrec.const 1)

theorem primrec_accFn (σ : Sig) : Primrec (accFn σ) := by
  unfold accFn
  have hfcode : Primrec (nthFrame 0) := primrec_nthFrame 0
  have hv : Primrec (fun s : List ℕ => (nthFrame 1 s).headI) :=
    Primrec.list_headI.comp (primrec_nthFrame 1)
  refine Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp hv (Primrec.const 2)) (Primrec.const 0)) ?_ ?_
  · have hev0 : Primrec (fun s : List ℕ => evalEmptyCode σ ((nthFrame 1 s).headI / 2) (nthFrame 0 s)) :=
      (primrec_evalEmptyCode σ).comp (Primrec.nat_div.comp hv (Primrec.const 2)) hfcode
    exact Primrec.ite (Primrec.eq.comp hev0 (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)
  · have haf : Primrec (fun s : List ℕ => altScan σ (nthFrame 0 s)) :=
      (primrec_altScan σ).comp hfcode
    have hℓ : Primrec (fun s : List ℕ => (altScan σ (nthFrame 0 s)).headI) :=
      Primrec.list_headI.comp haf
    have hψ : Primrec (fun s : List ℕ => (altScan σ (nthFrame 0 s)).tail) :=
      Primrec.list_tail.comp haf
    have hnh : Primrec (fun s : List ℕ => (((nthFrame 1 s).headI - 1) / 2).unpair) :=
      Primrec.unpair.comp
        (Primrec.nat_div.comp (Primrec.nat_sub.comp hv (Primrec.const 1)) (Primrec.const 2))
    have hnh1 : Primrec (fun s : List ℕ => (((nthFrame 1 s).headI - 1) / 2).unpair.1) :=
      Primrec.fst.comp hnh
    have hnh2 : Primrec (fun s : List ℕ => (((nthFrame 1 s).headI - 1) / 2).unpair.2) :=
      Primrec.snd.comp hnh
    have hev : Primrec (fun s : List ℕ =>
        evalHThCode σ (((nthFrame 1 s).headI - 1) / 2).unpair.1
          (altScan σ (nthFrame 0 s)).headI (altScan σ (nthFrame 0 s)).tail
          (((nthFrame 1 s).headI - 1) / 2).unpair.2) :=
      (primrec_evalHThCode σ).comp (Primrec.pair hnh1 (Primrec.pair hℓ (Primrec.pair hψ hnh2)))
    exact Primrec.ite (Primrec.eq.comp hev (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)

theorem accFn_le_one (σ : Sig) (l : List ℕ) : accFn σ l ≤ 1 := by
  unfold accFn
  dsimp
  split_ifs <;> omega

theorem primrec_tower : Primrec (fun p : ℕ × ℕ × ℕ => tower p.1 p.2.1 p.2.2) := by
  have hw : Primrec (fun p : ℕ × ℕ × ℕ => p.1) := Primrec.fst
  have hq : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : ℕ × ℕ × ℕ => 2 ^ 2 ^ p.2.1) :=
    primrec_pow.comp (Primrec.const 2) (primrec_pow.comp (Primrec.const 2) hq)
  have hstep : Primrec₂ (fun (p : ℕ × ℕ × ℕ) (x : ℕ) => 2 ^ (p.1 * 2 ^ (p.1 * x))) :=
    (primrec_pow.comp (Primrec.const 2)
      (Primrec.nat_mul.comp (hw.comp Primrec.fst)
        (primrec_pow.comp (Primrec.const 2)
          (Primrec.nat_mul.comp (hw.comp Primrec.fst) Primrec.snd)))).to₂
  refine (Primrec.nat_iterate hm h0 hstep).of_eq fun p => ?_
  rcases p with ⟨w, q, m⟩
  dsimp
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

theorem primrec_boundFn (σ : Sig) : Primrec₂ (boundFn σ) := by
  show Primrec (fun p : ℕ × ℕ => boundFn σ p.1 p.2)
  unfold boundFn
  have hw : Primrec (fun p : ℕ × ℕ => p.1) := Primrec.fst
  have hs : Primrec (fun p : ℕ × ℕ => p.2) := Primrec.snd
  have hq : Primrec (fun p : ℕ × ℕ => atomCnt (sigmaEq σ) (2 * p.2)) :=
    (primrec_atomCnt (sigmaEq σ)).comp (Primrec.nat_mul.comp (Primrec.const 2) hs)
  have hT : Primrec (fun p : ℕ × ℕ =>
      tower (p.1 + 1) (atomCnt (sigmaEq σ) (2 * p.2)) p.2) :=
    primrec_tower.comp (Primrec.pair (Primrec.succ.comp hw) (Primrec.pair hq hs))
  have hwT : Primrec (fun p : ℕ × ℕ => p.1 + tower (p.1 + 1) (atomCnt (sigmaEq σ) (2 * p.2)) p.2) :=
    Primrec.nat_add.comp hw hT
  have hquad : Primrec (fun p : ℕ × ℕ =>
      let x := p.1 + tower (p.1 + 1) (atomCnt (sigmaEq σ) (2 * p.2)) p.2
      x * x + x) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp hwT hwT) hwT
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const (2 * 2 ^ σ.r))
      (Primrec.nat_mul.comp (Primrec.const 2) hquad))
    (Primrec.const 1)

/-! ### 17. `CodeFold` invariants and main theorem -/

def zeroTuple {a n : ℕ} (ha : a = 0) : Fin a → Fin n :=
  fun j => absurd j.isLt (by omega)

open Classical in
noncomputable def zeroMask {σ : Sig} (T : CoDecomp σ) (S : Set (Fin T.b)) : ℕ :=
  packBits σ.r (fun i =>
    if hi : i < σ.r then
      decide (∃ har : σ.ar ⟨i, hi⟩ = 0, ∀ s ∈ S,
        σ.holds (A := Fin (T.bag s).n) ⟨i, hi⟩ (zeroTuple har))
    else false)

theorem joinFn_zero (σ : Sig) (fcode bt bc ba gt gc : List ℕ) (vt vc : ℕ)
    (hbt : bt.headI = 0) :
    joinFn σ (frame [fcode, bt, bc, ba, gt, gc, [vt], [vc] ]) =
      2 * packBits σ.r (fun i => unpackBit (vt / 2) i && unpackBit (vc / 2) i) := by
  let ls := [fcode, bt, bc, ba, gt, gc, [vt], [vc] ]
  have hf1 : nthFrame 1 (frame ls) = bt := nthFrame_frame ls (by simp [ls])
  have hf6 : nthFrame 6 (frame ls) = [vt] := nthFrame_frame ls (by simp [ls])
  have hf7 : nthFrame 7 (frame ls) = [vc] := nthFrame_frame ls (by simp [ls])
  change joinFn σ (frame ls) = _
  unfold joinFn
  dsimp only
  simp only [hf1, hf6, hf7, hbt, List.headI_cons, ↓reduceIte]

theorem joinFn_pos (σ : Sig) (φ : σ.lang.Sentence) (bt bc ba gt gc : List ℕ)
    (nt nc ht hc : ℕ) (hbt : bt.headI = nt) (hnt : nt ≠ 0) :
    joinFn σ (frame [encF φ, bt, bc, ba, gt, gc,
        [2 * Nat.pair nt ht + 1], [2 * Nat.pair nc hc + 1] ]) =
      2 * Nat.pair nt (joinHThCode σ nt bc.headI gt gc (quantCount φ) hc ht) + 1 := by
  let ls := [encF φ, bt, bc, ba, gt, gc,
    [2 * Nat.pair nt ht + 1], [2 * Nat.pair nc hc + 1] ]
  have hf0 : nthFrame 0 (frame ls) = encF φ := nthFrame_frame ls (by simp [ls])
  have hf1 : nthFrame 1 (frame ls) = bt := nthFrame_frame ls (by simp [ls])
  have hf2 : nthFrame 2 (frame ls) = bc := nthFrame_frame ls (by simp [ls])
  have hf4 : nthFrame 4 (frame ls) = gt := nthFrame_frame ls (by simp [ls])
  have hf5 : nthFrame 5 (frame ls) = gc := nthFrame_frame ls (by simp [ls])
  have hf6 : nthFrame 6 (frame ls) = [2 * Nat.pair nt ht + 1] :=
    nthFrame_frame ls (by simp [ls])
  have hf7 : nthFrame 7 (frame ls) = [2 * Nat.pair nc hc + 1] :=
    nthFrame_frame ls (by simp [ls])
  have untag : ∀ p : ℕ, ((2 * p + 1) - 1) / 2 = p := fun p => by omega
  change joinFn σ (frame ls) = _
  unfold joinFn
  dsimp only
  simp only [hf0, hf1, hf2, hf4, hf5, hf6, hf7, hbt, hnt, ↓reduceIte,
    List.headI_cons, altScan_encF, untag, Nat.unpair_pair]

open Classical in
theorem codeFold_zero_inv {σ : Sig} {T : CoDecomp σ} {r : Fin T.b} (hr0 : (T.bag r).n = 0)
    (φ : σ.lang.Sentence) :
    ∀ {t : Fin T.b} {S : Set (Fin T.b)} {v : ℕ},
      T.CodeFold r (encF φ) (leafFn σ) (joinFn σ) t S v →
      v = 2 * zeroMask T S := by
  intro t S v hv
  induction hv with
  | base t =>
    have ht0 : (T.bag t).n = 0 := (bag_zero_iff r t).1 hr0
    unfold leafFn zeroMask
    have hf1 : nthFrame 1 (frame [encF φ, encBag (T.bag t)]) = encBag (T.bag t) :=
      nthFrame_frame [encF φ, encBag (T.bag t)] (by simp)
    have hhead : (encBag (T.bag t)).headI = 0 := ht0
    dsimp only
    simp only [hf1, hhead, ↓reduceIte]
    congr 1
    refine packBits_congr fun i hi => ?_
    simp only [hi, ↓reduceDIte]
    let i' : Fin σ.r := ⟨i, hi⟩
    have har_eq : arN σ i = σ.ar i' := arN_val σ i'
    rw [har_eq]
    by_cases har : σ.ar i' = 0
    · have hnil : (List.ofFn fun j => (zeroTuple (n := (T.bag t).n) har j).val) = [] := by
        rw [List.ofFn_eq_nil_iff]; exact har
      have hrel := bagRelBit_encBag (T.bag t) i' (zeroTuple har)
      rw [hnil] at hrel
      apply Bool.eq_iff_iff.2
      simp only [har, decide_true, Bool.true_and, decide_eq_true_eq, Set.mem_singleton_iff]
      exact ⟨fun h => ⟨har, fun s hs => by subst hs; exact hrel.1 h⟩,
        fun ⟨_, hall⟩ => hrel.2 (hall t rfl)⟩
    · simp only [har, decide_false, Bool.false_and]
      apply Bool.eq_iff_iff.2
      simp only [Bool.false_eq_true, decide_eq_true_eq, false_iff]
      rintro ⟨h0, -⟩
      exact har h0
  | step t S e he vt vc _ _ _ ih1 ih2 =>
    have ht0 : (T.bag t).n = 0 := (bag_zero_iff r t).1 hr0
    have hhead : (encBag (T.bag t)).headI = 0 := ht0
    rw [joinFn_zero σ (encF φ) (encBag (T.bag t)) (encBag (T.bag (T.child e t))) (encBag (T.adh e))
      _ _ vt vc hhead, ih1, ih2, Nat.mul_div_right _ (by norm_num), Nat.mul_div_right _ (by norm_num)]
    unfold zeroMask
    congr 1
    refine packBits_congr fun i hi => ?_
    rw [unpackBit_packBits σ.r _ hi, unpackBit_packBits σ.r _ hi]
    simp only [hi, ↓reduceDIte]
    apply Bool.eq_iff_iff.2
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨har, hS⟩, ⟨_, hsub⟩⟩
      refine ⟨har, fun s hs => ?_⟩
      rcases hs with hs | hs
      · exact hS s hs
      · exact hsub s hs
    · rintro ⟨har, hall⟩
      exact ⟨⟨har, fun s hs => hall s (Or.inl hs)⟩, ⟨har, fun s hs => hall s (Or.inr hs)⟩⟩

theorem codeFold_pos_inv {σ : Sig} {T : CoDecomp σ} {r : Fin T.b} (hr_pos : 0 < (T.bag r).n)
    (φ : σ.lang.Sentence) :
    ∀ {t : Fin T.b} {S : Set (Fin T.b)} {v : ℕ},
      T.CodeFold r (encF φ) (leafFn σ) (joinFn σ) t S v →
      ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag t).n) (2 * quantCount φ) (quantCount φ),
        T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) t S H ∧
        v = 2 * Nat.pair (T.bag t).n
          (hthEquiv (sigmaEq σ) (T.bag t).n (2 * quantCount φ) (quantCount φ) H).val + 1 := by
  intro t S v hv
  induction hv with
  | base t =>
    have ht_ne : (T.bag t).n ≠ 0 := fun h0 => by
      have := (bag_zero_iff t r).1 h0; omega
    let H := ind (sigmaEq σ) (2 * quantCount φ) (quantCount φ)
      (Strat.full (Fin (T.withEq.bag t).n) (quantCount φ)) []
    refine ⟨H, CoDecomp.IsFold.leaf (T := T.withEq) t, ?_⟩
    unfold leafFn
    dsimp only
    have hf0 : nthFrame 0 (frame [encF φ, encBag (T.bag t)]) = encF φ :=
      nthFrame_frame [encF φ, encBag (T.bag t)] (by simp)
    have hf1 : nthFrame 1 (frame [encF φ, encBag (T.bag t)]) = encBag (T.bag t) :=
      nthFrame_frame [encF φ, encBag (T.bag t)] (by simp)
    have hhead : (encBag (T.bag t)).headI = (T.bag t).n := rfl
    simp only [hf0, hf1, hhead, ht_ne, ↓reduceIte, altScan_encF, List.headI_cons]
    exact congrArg (fun x => 2 * Nat.pair (T.bag t).n x + 1)
      (leafHThCode_spec (T.bag t) (quantCount φ))
  | step t S e he vt vc _ hnotmem _ ih1 ih2 =>
    have ht_ne : (T.bag t).n ≠ 0 := fun h0 => by
      have := (bag_zero_iff t r).1 h0; omega
    obtain ⟨H, hH, rfl⟩ := ih1
    obtain ⟨Hc, hHc, rfl⟩ := ih2
    let H' := push (Fib.snd :
        Fib (T.withEq.edgeMap e (T.withEq.child e t) he.child_mem)
          (T.withEq.edgeMap e t he.top_mem) → Fin (T.withEq.bag t).n) (quantCount φ)
      (pb (T.withEq.edgeMap e (T.withEq.child e t) he.child_mem)
        (T.withEq.edgeMap e t he.top_mem) (quantCount φ) Hc H)
    refine ⟨H', CoDecomp.IsFold.join (T := T.withEq) t S e he H Hc hH hnotmem hHc, ?_⟩
    have hhead_t : (encBag (T.bag t)).headI = (T.bag t).n := rfl
    have hhead_c : (encBag (T.bag (T.child e t))).headI = (T.bag (T.child e t)).n := rfl
    have hj := joinFn_pos σ φ (encBag (T.bag t)) (encBag (T.bag (T.child e t))) (encBag (T.adh e))
      (List.ofFn (fun x => (T.edgeMap e t he.top_mem x).val))
      (List.ofFn (fun x => (T.edgeMap e (T.child e t) he.child_mem x).val))
      (T.bag t).n (T.bag (T.child e t)).n
      (hthEquiv (sigmaEq σ) (T.bag t).n (2 * quantCount φ) (quantCount φ) H).val
      (hthEquiv (sigmaEq σ) (T.bag (T.child e t)).n (2 * quantCount φ) (quantCount φ) Hc).val
      hhead_t ht_ne
    rw [hhead_c] at hj
    exact hj.trans (congrArg (fun x => 2 * Nat.pair (T.bag t).n x + 1)
      (joinHThCode_spec (T.edgeMap e t he.top_mem)
        (T.edgeMap e (T.child e t) he.child_mem) (quantCount φ) Hc H))

theorem accFn_even (σ : Sig) (fcode : List ℕ) (mask : ℕ) :
    accFn σ (frame [fcode, [2 * mask] ]) = if evalEmptyCode σ mask fcode then 1 else 0 := by
  have hf0 : nthFrame 0 (frame [fcode, [2 * mask] ]) = fcode :=
    nthFrame_frame [fcode, [2 * mask] ] (by simp)
  have hf1 : nthFrame 1 (frame [fcode, [2 * mask] ]) = [2 * mask] :=
    nthFrame_frame [fcode, [2 * mask] ] (by simp)
  have hdiv : 2 * mask / 2 = mask := by omega
  unfold accFn
  dsimp only
  simp only [hf0, hf1, List.headI_cons, Nat.mul_mod_right, ↓reduceIte, hdiv]

theorem accFn_odd (σ : Sig) (φ : σ.lang.Sentence) (n hc : ℕ) :
    accFn σ (frame [encF φ, [2 * Nat.pair n hc + 1] ]) =
      if evalHThCode σ n (quantCount φ) (encF (altMatrix φ)) hc then 1 else 0 := by
  set p := Nat.pair n hc
  have hf0 : nthFrame 0 (frame [encF φ, [2 * p + 1] ]) = encF φ :=
    nthFrame_frame [encF φ, [2 * p + 1] ] (by simp)
  have hf1 : nthFrame 1 (frame [encF φ, [2 * p + 1] ]) = [2 * p + 1] :=
    nthFrame_frame [encF φ, [2 * p + 1] ] (by simp)
  have hmod : (2 * p + 1) % 2 ≠ 0 := by omega
  have hdiv : (2 * p + 1 - 1) / 2 = p := by omega
  have hunp : p.unpair = (n, hc) := Nat.unpair_pair n hc
  unfold accFn
  dsimp only
  simp only [hf0, hf1, List.headI_cons, hmod, ↓reduceIte, hdiv, altScan_encF, List.tail_cons, hunp]

open Classical in
theorem fold_codes_main (σ : Sig) :
    ∃ (leaf join acc : List ℕ → ℕ) (B : ℕ → ℕ → ℕ),
      Primrec leaf ∧ Primrec join ∧ Primrec acc ∧ (∀ l, acc l ≤ 1) ∧ Computable₂ B ∧
      ∀ (T : CoDecomp σ) (φ : σ.lang.Sentence) (w : ℕ), width T ≤ w →
        (∀ (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ),
          T.CodeFold r (encF φ) leaf join t S v → v ≤ B w (sentLen φ)) ∧
        (∀ (r : Fin T.b) (v : ℕ), T.CodeFold r (encF φ) leaf join r Set.univ v →
          (IsEmpty T.Lim → (acc (frame [encF φ, [v] ]) = 1 ↔ T.Lim ⊨ φ)) ∧
          (Nonempty T.Lim →
            ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag r).n) (2 * quantCount φ) (quantCount φ),
              T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) r Set.univ H ∧
              (acc (frame [encF φ, [v] ]) = 1 ↔ eval (altMatrix φ) (quantCount φ) H))) := by
  refine ⟨leafFn σ, joinFn σ, accFn σ, boundFn σ,
    primrec_leafFn σ, primrec_joinFn σ, primrec_accFn σ, accFn_le_one σ,
    (primrec_boundFn σ).to_comp, fun T φ w hw => ⟨?_, ?_⟩⟩
  · intro r t S v hv
    rcases Nat.eq_zero_or_pos (T.bag r).n with hr0 | hr_pos
    · rw [codeFold_zero_inv hr0 φ hv]
      have hlt : zeroMask T S < 2 ^ σ.r := packBits_lt σ.r _
      unfold boundFn
      dsimp only
      omega
    · obtain ⟨H, -, rfl⟩ := codeFold_pos_inv hr_pos φ hv
      have hn_le : (T.bag t).n ≤ w := le_trans (Finset.le_sup (f := fun s => (T.bag s).n)
        (Finset.mem_univ t)) hw
      let ℓ := quantCount φ
      let s := sentLen φ
      have hℓ_le : ℓ ≤ s := quantCount_le_sentLen φ
      have hval_lt : (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val <
          tower (T.bag t).n (atomCnt (sigmaEq σ) (2 * ℓ)) ℓ :=
        (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).isLt
      have hT_mono1 : tower (T.bag t).n (atomCnt (sigmaEq σ) (2 * ℓ)) ℓ ≤
          tower (w + 1) (atomCnt (sigmaEq σ) (2 * s)) ℓ :=
        tower_mono_wq (le_trans hn_le (Nat.le_succ w))
          (atomCnt_mono (sigmaEq σ) (by omega)) ℓ
      have hT_mono2 : tower (w + 1) (atomCnt (sigmaEq σ) (2 * s)) ℓ ≤
          tower (w + 1) (atomCnt (sigmaEq σ) (2 * s)) s :=
        tower_mono_m (w + 1) _ (by omega) hℓ_le
      let Tbound := tower (w + 1) (atomCnt (sigmaEq σ) (2 * s)) s
      have hval_le : (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val ≤ Tbound :=
        le_trans hval_lt.le (le_trans hT_mono1 hT_mono2)
      have hpair := nat_pair_le_quad (T.bag t).n
        (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val
      have hsum_le : (T.bag t).n + (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val ≤
          w + Tbound := Nat.add_le_add hn_le hval_le
      have hquad_le : ((T.bag t).n + (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val) *
            ((T.bag t).n + (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val) +
          ((T.bag t).n + (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val) ≤
          (w + Tbound) * (w + Tbound) + (w + Tbound) :=
        Nat.add_le_add (Nat.mul_le_mul hsum_le hsum_le) hsum_le
      unfold boundFn
      dsimp only
      change 2 * Nat.pair (T.bag t).n (hthEquiv (sigmaEq σ) (T.bag t).n (2 * ℓ) ℓ H).val + 1 ≤
        2 * 2 ^ σ.r + 2 * ((w + Tbound) * (w + Tbound) + (w + Tbound)) + 1
      omega
  · intro r v hv
    refine ⟨fun he => ?_, fun hne => ?_⟩
    · have hr0 : (T.bag r).n = 0 := by
        by_contra hne0
        have := nonempty_lim_of_bag_pos r (Nat.pos_of_ne_zero hne0)
        exact not_nonempty_iff.2 he this
      have hv_mask : v = 2 * zeroMask T Set.univ := codeFold_zero_inv hr0 φ hv
      have hacc_eq : accFn σ (frame [encF φ, [v] ]) =
          if evalEmptyCode σ (zeroMask T Set.univ) (encF φ) then 1 else 0 := by
        rw [hv_mask]
        exact accFn_even σ (encF φ) (zeroMask T Set.univ)
      have hmask : ∀ (i : Fin σ.r) (hi : σ.ar i = 0) (args : Fin 0 → T.Lim),
          unpackBit (zeroMask T Set.univ) i.val = true ↔
            @FirstOrder.Language.Structure.RelMap σ.lang T.Lim _ 0 ⟨i, hi⟩ args := by
        intro i hi args
        unfold zeroMask
        rw [unpackBit_packBits σ.r _ i.isLt]
        simp only [i.isLt, ↓reduceDIte, decide_eq_true_eq]
        show (∃ har : σ.ar i = 0, ∀ s ∈ (Set.univ : Set (Fin T.b)),
            σ.holds (A := Fin (T.bag s).n) i (zeroTuple har)) ↔
          ∀ t : Fin T.b, σ.holds (A := Fin (T.bag t).n) i (fun j => (args (Fin.cast hi j)).val t)
        constructor
        · rintro ⟨har, hall⟩ t
          have hfn : (fun j => (args (Fin.cast hi j)).val t) = zeroTuple har :=
            funext fun j => absurd j.isLt (by omega)
          rw [hfn]
          exact hall t trivial
        · intro hall
          refine ⟨hi, fun t _ => ?_⟩
          have hfn : zeroTuple (n := (T.bag t).n) hi = (fun j => (args (Fin.cast hi j)).val t) :=
            funext fun j => absurd j.isLt (by omega)
          rw [hfn]
          exact hall t
      have hspec := evalEmptyCode_spec (M := T.Lim) hmask φ
      have hiff1 : accFn σ (frame [encF φ, [v] ]) = 1 ↔
          evalEmptyCode σ (zeroMask T Set.univ) (encF φ) = true := by
        rw [hacc_eq]
        cases evalEmptyCode σ (zeroMask T Set.univ) (encF φ) <;> simp
      exact hiff1.trans hspec
    · obtain ⟨x₀⟩ := hne
      have hr_pos : 0 < (T.bag r).n := Nat.zero_lt_of_lt (x₀.val r).isLt
      obtain ⟨H, hH, hv_eq⟩ := codeFold_pos_inv hr_pos φ hv
      refine ⟨H, hH, ?_⟩
      let hc := (hthEquiv (sigmaEq σ) (T.bag r).n (2 * quantCount φ) (quantCount φ) H).val
      have hacc_eq : accFn σ (frame [encF φ, [v] ]) =
          if evalHThCode σ (T.bag r).n (quantCount φ) (encF (altMatrix φ)) hc then 1 else 0 := by
        rw [hv_eq]
        exact accFn_odd σ φ (T.bag r).n hc
      have hspec := evalHThCode_spec (T.bag r).n (quantCount φ) (isMatrix_altMatrix φ) H
      have hiff1 : accFn σ (frame [encF φ, [v] ]) = 1 ↔
          evalHThCode σ (T.bag r).n (quantCount φ) (encF (altMatrix φ)) hc = true := by
        rw [hacc_eq]
        cases evalHThCode σ (T.bag r).n (quantCount φ) (encF (altMatrix φ)) hc <;> simp
      exact hiff1.trans hspec

end FoldCodesProof
end CoDecompFO

open CoDecompFO FirstOrder

theorem solution (σ : Sig) :
    ∃ (leaf join acc : List ℕ → ℕ) (B : ℕ → ℕ → ℕ),
      Primrec leaf ∧ Primrec join ∧ Primrec acc ∧ (∀ l, acc l ≤ 1) ∧ Computable₂ B ∧
      ∀ (T : CoDecomp σ) (φ : σ.lang.Sentence) (w : ℕ), width T ≤ w →
        (∀ (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ),
          T.CodeFold r (encF φ) leaf join t S v → v ≤ B w (sentLen φ)) ∧
        (∀ (r : Fin T.b) (v : ℕ), T.CodeFold r (encF φ) leaf join r Set.univ v →
          (IsEmpty T.Lim → (acc (frame [encF φ, [v] ]) = 1 ↔ T.Lim ⊨ φ)) ∧
          (Nonempty T.Lim →
            ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag r).n) (2 * quantCount φ) (quantCount φ),
              T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) r Set.univ H ∧
              (acc (frame [encF φ, [v] ]) = 1 ↔ eval (altMatrix φ) (quantCount φ) H))) :=
  CoDecompFO.FoldCodesProof.fold_codes_main σ
