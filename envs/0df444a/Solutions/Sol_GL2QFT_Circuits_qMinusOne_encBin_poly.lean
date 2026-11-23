-- Prove2me | solution 1 for GL2QFT.Circuits.qMinusOne_encBin_poly
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:51.903566+00:00
-- url     : https://prove2.me/submissions/29213946-fc3e-40ca-a3ca-2eb9ce097e79

import Definitions.Def_GL2QFT_Circuits_Leaves
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

open Classical
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_QMinusOnePoly_Aux

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open Polynomial

inductive ParseState
  | pStart | pBit | pEnd | rStart | rBit | done
  deriving DecidableEq

instance : Fintype ParseState :=
  ⟨{.pStart, .pBit, .pEnd, .rStart, .rBit, .done}, by intro s; cases s <;> simp⟩

def parsePR : Transducer where
  Q := ParseState
  initial := .pStart
  next q b := match q with
    | .pStart => if b then (.pBit, []) else (.pEnd, [false])
    | .pBit => (.pStart, [true, b])
    | .pEnd => (.rStart, [])
    | .rStart => if b then (.rBit, []) else (.done, [])
    | .rBit => (.rStart, [b])
    | .done => (.done, [])
  finish q := match q with
    | .pStart => [false]
    | .pBit => [false]
    | _ => []

def parseP : List Bool → List Bool × List Bool
  | true :: b :: xs => let res := parseP xs; (b :: res.1, res.2)
  | false :: _ :: xs => ([], xs)
  | _ => ([], [])

def parseR : List Bool → List Bool
  | true :: b :: xs => b :: parseR xs
  | _ => []

lemma parsePR_done (xs : List Bool) : parsePR.run .done xs = [] := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (parsePR.next .done b).2 ++ parsePR.run (parsePR.next .done b).1 xs = []
      simpa [parsePR] using ih

lemma parsePR_rStart (xs : List Bool) : parsePR.run .rStart xs = parseR xs := by
  match xs with
  | [] => rfl
  | [false] =>
      change [] ++ parsePR.run .done [] = []
      rw [parsePR_done]
      rfl
  | [true] => rfl
  | false :: b :: xs' =>
      change [] ++ parsePR.run .done (b :: xs') = []
      rw [parsePR_done]
      rfl
  | true :: b :: xs' =>
      change [] ++ ([b] ++ parsePR.run .rStart xs') = b :: parseR xs'
      rw [parsePR_rStart xs']
      rfl
termination_by xs.length

lemma parsePR_pStart (xs : List Bool) :
    parsePR.run .pStart xs = encodePair id id ((parseP xs).1, parseR (parseP xs).2) := by
  match xs with
  | [] => rfl
  | [false] => rfl
  | [true] => rfl
  | false :: b :: xs' =>
      change [false] ++ ([] ++ parsePR.run .rStart xs') = quote [] ++ parseR xs'
      rw [parsePR_rStart xs']
      rfl
  | true :: b :: xs' =>
      change [] ++ ([true, b] ++ parsePR.run .pStart xs') =
        quote (b :: (parseP xs').1) ++ parseR (parseP xs').2
      rw [parsePR_pStart xs']
      rfl
termination_by xs.length

lemma parseP_encBin_bits (bs tail : List Bool) :
    parseP ((bs.flatMap (fun β => [true, β]) ++ [false, false]) ++ tail) = (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simpa [List.flatMap_cons, List.append_assoc, parseP] using
        congrArg (fun p => (b :: p.1, p.2)) ih

lemma parseR_encBin_bits (bs tail : List Bool) :
    parseR ((bs.flatMap (fun β => [true, β]) ++ [false, false]) ++ tail) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simpa [List.flatMap_cons, List.append_assoc, parseR] using congrArg (List.cons b) ih

lemma parseP_encBin (m : ℕ) (tail : List Bool) :
    parseP (LocalHamiltonian.encBin m ++ tail) = (m.bits, tail) :=
  parseP_encBin_bits m.bits tail

lemma parseR_encBin (m : ℕ) (tail : List Bool) :
    parseR (LocalHamiltonian.encBin m ++ tail) = m.bits :=
  parseR_encBin_bits m.bits tail

def pVal (xs : List Bool) : ℕ := Word.value (parseP xs).1
def rVal (xs : List Bool) : ℕ := Word.value (parseR (parseP xs).2)

lemma pVal_encData (D : FieldData) : pVal D.encData = D.p := by
  unfold pVal FieldData.encData
  simp only [List.append_assoc]
  rw [parseP_encBin, Word.value_bits]

lemma rVal_encData (D : FieldData) : rVal D.encData = D.r := by
  unfold rVal FieldData.encData
  simp only [List.append_assoc]
  rw [parseP_encBin, parseR_encBin, Word.value_bits]

lemma flatMap_encBin_length (ls : List ℕ) (g : ℕ → ℕ) :
    ls.length ≤ (ls.flatMap fun j => LocalHamiltonian.encBin (g j)).length := by
  induction ls with
  | nil => simp
  | cons x ls ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        LocalHamiltonian.encBin] at ih ⊢
      omega

lemma r_le_encData_length (D : FieldData) : D.r ≤ D.encData.length := by
  unfold FieldData.encData
  have h := flatMap_encBin_length (List.range (D.r + 1)) (fun j => (D.f.coeff j).val)
  rw [List.length_range] at h
  simp only [List.length_append]
  omega

noncomputable def parseNatPairProg :
    PolyProgram id (encodePair Nat.bits Nat.bits) (fun xs => (pVal xs, rVal xs)) :=
  (parsePR.program.recode id (fun _ => rfl) parsePR_pStart).comp
    (PolyProgram.product PolyProgram.toBits PolyProgram.toBits)

@[fun_prop] theorem parseNatPair_poly : Automatic.Poly (fun xs : List Bool => (pVal xs, rVal xs)) :=
  ⟨(BooleanLists.unpackProgram.comp parseNatPairProg).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem pVal_poly : Automatic.Poly pVal :=
  Automatic.Poly.comp (f := Prod.fst) Automatic.Poly.fst parseNatPair_poly

@[fun_prop] theorem rVal_poly : Automatic.Poly rVal :=
  Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd parseNatPair_poly

def powStep (st : ℕ × (ℕ × ℕ)) (_ : Bool) : ℕ × (ℕ × ℕ) :=
  if st.2.1 = 0 then st else (st.1, (st.2.1 - 1, st.2.2 * st.1))

@[fun_prop] theorem powStep_poly :
    Automatic.Poly (fun x : (ℕ × (ℕ × ℕ)) × Bool => powStep x.1 x.2) := by
  unfold powStep
  exact Automatic.Poly.ite_prop
    (Automatic.Poly.nat_eq_comp
      (Automatic.Poly.comp (f := Prod.fst) Automatic.Poly.fst
        (Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd Automatic.Poly.fst))
      (Automatic.Poly.const 0))
    (by fun_prop) (by fun_prop)

lemma powStep_fold_eq (ls : List Bool) (p r acc : ℕ) :
    ls.foldl (fun st a => powStep st a) (p, r, acc) =
      (p, r - ls.length, acc * p ^ min r ls.length) := by
  induction ls generalizing r acc with
  | nil => simp
  | cons a ls ih =>
      simp only [List.foldl_cons, List.length_cons]
      cases r with
      | zero =>
          have h0 : powStep (p, 0, acc) a = (p, 0, acc) := rfl
          rw [h0]
          simpa using ih 0 acc
      | succ r' =>
          have h1 : powStep (p, r' + 1, acc) a = (p, r', acc * p) := by simp [powStep]
          rw [h1, ih r' (acc * p)]
          have hmin : min (r' + 1) (ls.length + 1) = min r' ls.length + 1 := by omega
          rw [hmin, pow_succ']
          simp [mul_assoc]

lemma powStep_fold_bound (pre : List Bool) (st : ℕ × (ℕ × ℕ)) :
    let res := pre.foldl (fun s a => powStep s a) st
    res.1 = st.1 ∧ res.2.1 ≤ st.2.1 ∧
      res.2.2.bits.length ≤ st.2.2.bits.length + pre.length * st.1.bits.length := by
  induction pre generalizing st with
  | nil => simp
  | cons a pre ih =>
      simp only [List.foldl_cons, List.length_cons]
      by_cases hz : st.2.1 = 0
      · have h0 : powStep st a = st := by simp [powStep, hz]
        rw [h0]
        have h := ih st
        exact ⟨h.1, h.2.1, h.2.2.trans (by nlinarith)⟩
      · have h1 : powStep st a = (st.1, (st.2.1 - 1, st.2.2 * st.1)) := by simp [powStep, hz]
        rw [h1]
        have h := ih (st.1, (st.2.1 - 1, st.2.2 * st.1))
        have hm := NatBinary.mul_length st.2.2 st.1
        refine ⟨h.1, h.2.1.trans (Nat.sub_le _ _), ?_⟩
        calc
          (pre.foldl (fun s a => powStep s a) (st.1, st.2.1 - 1, st.2.2 * st.1)).2.2.bits.length
              ≤ (st.2.2 * st.1).bits.length + pre.length * st.1.bits.length := h.2.2
          _ ≤ (st.2.2.bits.length + st.1.bits.length) + pre.length * st.1.bits.length :=
              Nat.add_le_add_right hm _
          _ = st.2.2.bits.length + (pre.length + 1) * st.1.bits.length := by
              rw [Nat.add_mul, one_mul]; omega

noncomputable def powFoldProg :
    PolyProgram (encodePair (encodeList encodeBool) (encodePair Nat.bits (encodePair Nat.bits Nat.bits)))
      (encodePair Nat.bits (encodePair Nat.bits Nat.bits))
      (fun x : List Bool × (ℕ × (ℕ × ℕ)) => x.1.foldl (fun s a => powStep s a) x.2) := by
  refine PolyProgram.listFold powStep_poly.program false (X + X ^ 2) (fun as st pre suf he => ?_)
  have hb := powStep_fold_bound pre st
  have hlen := NatBinary.length_mono hb.2.1
  have hpre : pre.length ≤ (encodeList encodeBool as).length := by
    have h1 : pre.length ≤ as.length := by rw [he, List.length_append]; omega
    exact h1.trans (EncodedList.length_le encodeBool as)
  let N := (encodePair (encodeList encodeBool) (encodePair Nat.bits (encodePair Nat.bits Nat.bits)) (as, st)).length
  have hN_list : (encodeList encodeBool as).length ≤ N := by
    simp only [N, encodePair_length]; omega
  have hN_st : (encodePair Nat.bits (encodePair Nat.bits Nat.bits) st).length ≤ N := by
    simp only [N, encodePair_length]; omega
  have hst1 : st.1.bits.length ≤ N := by
    have h0 : st.1.bits.length ≤ (encodePair Nat.bits (encodePair Nat.bits Nat.bits) st).length := by
      simp only [encodePair_length]; omega
    exact h0.trans hN_st
  have hmul : pre.length * st.1.bits.length ≤ N ^ 2 := by
    rw [sq]
    exact Nat.mul_le_mul (hpre.trans hN_list) hst1
  change (encodePair Nat.bits (encodePair Nat.bits Nat.bits) (pre.foldl (fun s a => powStep s a) st)).length ≤
    (X + X ^ 2).eval N
  simp only [eval_add, eval_X, eval_pow]
  simp only [encodePair_length, hb.1]
  have h_res22 := hb.2.2
  simp only [encodePair_length] at hN_st
  omega

@[fun_prop] theorem powFold_poly :
    Automatic.Poly (fun x : List Bool × (ℕ × (ℕ × ℕ)) => x.1.foldl (fun s a => powStep s a) x.2) :=
  ⟨powFoldProg⟩

def qRaw (xs : List Bool) : ℕ :=
  (xs.foldl (fun s a => powStep s a) (pVal xs, rVal xs, 1)).2.2

@[fun_prop] theorem qRaw_poly : Automatic.Poly qRaw := by
  unfold qRaw
  exact Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd
    (Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd
      (Automatic.Poly.comp powFold_poly
        (Automatic.Poly.pair Automatic.Poly.identity
          (Automatic.Poly.pair pVal_poly
            (Automatic.Poly.pair rVal_poly (Automatic.Poly.const 1))))))

lemma qRaw_eq (xs : List Bool) : qRaw xs = (pVal xs) ^ min (rVal xs) xs.length := by
  unfold qRaw
  rw [powStep_fold_eq, one_mul]

lemma qRaw_encData (D : FieldData) : qRaw D.encData = D.q := by
  rw [qRaw_eq, pVal_encData, rVal_encData, min_eq_left (r_le_encData_length D)]
  rfl

def qMinusOneRaw (xs : List Bool) : ℕ := qRaw xs - 1

@[fun_prop] theorem qMinusOneRaw_poly : Automatic.Poly qMinusOneRaw := by
  unfold qMinusOneRaw
  exact Automatic.Poly.comp Automatic.Poly.nat_sub
    (Automatic.Poly.pair qRaw_poly (Automatic.Poly.const 1))

lemma qMinusOneRaw_encData (D : FieldData) : qMinusOneRaw D.encData = D.q - 1 := by
  unfold qMinusOneRaw
  rw [qRaw_encData]

noncomputable def qMinusOneBitsProg : PolyProgram id Nat.bits qMinusOneRaw :=
  (BooleanLists.packProgram.comp qMinusOneRaw_poly.program).recode id (fun _ => rfl) (fun _ => rfl)

def encBinTransducer : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [true, b])
  finish _ := [false, false]

lemma encBinTransducer_run (bs : List Bool) :
    encBinTransducer.run () bs = bs.flatMap (fun β => [true, β]) ++ [false, false] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      change [true, b] ++ encBinTransducer.run () bs = _
      rw [ih]
      rfl

noncomputable def encBinFromBitsProg : PolyProgram Nat.bits id (fun n => LocalHamiltonian.encBin n) :=
  encBinTransducer.program.recode Nat.bits (fun _ => rfl) (fun n => by
    change encBinTransducer.run () n.bits = LocalHamiltonian.encBin n
    rw [encBinTransducer_run]
    rfl)

end GL2QFT_QMinusOnePoly_Aux

open OAI.MetricKMedian.Binary

theorem solution : ∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = LocalHamiltonian.encBin (D.q - 1) := by
  let P : PolyProgram id id (fun xs => LocalHamiltonian.encBin (GL2QFT_QMinusOnePoly_Aux.qMinusOneRaw xs)) :=
    (GL2QFT_QMinusOnePoly_Aux.qMinusOneBitsProg.comp GL2QFT_QMinusOnePoly_Aux.encBinFromBitsProg).congr _
      (fun _ => rfl)
  refine ⟨fun xs => LocalHamiltonian.encBin (GL2QFT_QMinusOnePoly_Aux.qMinusOneRaw xs), ⟨P.stock⟩, ?_⟩
  intro D
  change LocalHamiltonian.encBin (GL2QFT_QMinusOnePoly_Aux.qMinusOneRaw D.encData) = _
  rw [GL2QFT_QMinusOnePoly_Aux.qMinusOneRaw_encData]
