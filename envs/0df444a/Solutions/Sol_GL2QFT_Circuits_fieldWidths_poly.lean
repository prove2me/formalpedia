-- Prove2me | solution 1 for GL2QFT.Circuits.fieldWidths_poly
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:25:52.090737+00:00
-- url     : https://prove2.me/submissions/9b904833-e960-494c-94c9-da6d203f1b5d

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

open Classical
open GL2QFT QAlgorithms QAlgorithms.Complexity

namespace GL2QFT_FieldWidthsPoly_Aux

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

lemma parseP_fst_length (xs : List Bool) : (parseP xs).1.length ≤ xs.length := by
  match xs with
  | [] => simp [parseP]
  | [_] => simp [parseP]
  | false :: _ :: _ => simp [parseP]
  | true :: b :: xs' =>
      have ih := parseP_fst_length xs'
      simp only [parseP, List.length_cons]
      omega
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

lemma pVal_bits_length (xs : List Bool) : (pVal xs).bits.length ≤ xs.length :=
  (Word.bits_value_length (parseP xs).1).trans (parseP_fst_length xs)

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

@[fun_prop] theorem nat_size_poly : Automatic.Poly Nat.size := ⟨PolyProgram.natSize⟩

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

lemma powStep_fold_eq (ls : List Bool) (p2 r acc : ℕ) :
    ls.foldl (fun st a => powStep st a) (p2, r, acc) =
      (p2, r - ls.length, acc * p2 ^ min r ls.length) := by
  induction ls generalizing r acc with
  | nil => simp
  | cons a ls ih =>
      simp only [List.foldl_cons, List.length_cons]
      cases r with
      | zero =>
          have h0 : powStep (p2, 0, acc) a = (p2, 0, acc) := rfl
          rw [h0]
          simpa using ih 0 acc
      | succ r' =>
          have h1 : powStep (p2, r' + 1, acc) a = (p2, r', acc * p2) := by simp [powStep]
          rw [h1, ih r' (acc * p2)]
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

def q2Raw (xs : List Bool) : ℕ :=
  (xs.foldl (fun s a => powStep s a) (pVal xs * pVal xs, rVal xs, 1)).2.2

@[fun_prop] theorem q2Raw_poly : Automatic.Poly q2Raw := by
  unfold q2Raw
  exact Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd
    (Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd
      (Automatic.Poly.comp powFold_poly
        (Automatic.Poly.pair Automatic.Poly.identity
          (Automatic.Poly.pair
            (Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2) Automatic.Poly.nat_mul
              (Automatic.Poly.pair pVal_poly pVal_poly))
            (Automatic.Poly.pair rVal_poly (Automatic.Poly.const 1))))))

lemma q2Raw_eq (xs : List Bool) : q2Raw xs = (pVal xs * pVal xs) ^ min (rVal xs) xs.length := by
  unfold q2Raw
  rw [powStep_fold_eq, one_mul]

lemma q2Raw_encData (D : FieldData) : q2Raw D.encData = D.q ^ 2 := by
  rw [q2Raw_eq, pVal_encData, rVal_encData, min_eq_left (r_le_encData_length D)]
  unfold FieldData.q
  ring

lemma clog_two_eq_pred_size (n : ℕ) : Nat.clog 2 n = (n - 1).size := by
  cases n with
  | zero => simp
  | succ m =>
      apply le_antisymm
      · rw [Nat.clog_le_iff_le_pow (by decide), Nat.succ_le_iff]
        exact Nat.lt_size_self m
      · rw [Nat.size_le, ← Nat.succ_le_iff]
        exact Nat.le_pow_clog (by decide) (m + 1)

def labWRaw (xs : List Bool) : ℕ := (q2Raw xs - 1).size

@[fun_prop] theorem labWRaw_poly : Automatic.Poly labWRaw := by
  unfold labWRaw
  exact Automatic.Poly.comp nat_size_poly
    (Automatic.Poly.comp Automatic.Poly.nat_sub (Automatic.Poly.pair q2Raw_poly (Automatic.Poly.const 1)))

lemma labWRaw_encData (D : FieldData) : labWRaw D.encData = D.labW := by
  unfold labWRaw FieldData.labW
  rw [q2Raw_encData, clog_two_eq_pred_size]

def rCap (xs : List Bool) : ℕ := if rVal xs ≤ xs.length then rVal xs else xs.length

@[fun_prop] theorem rCap_poly : Automatic.Poly rCap := by
  unfold rCap
  exact Automatic.Poly.ite_prop
    (Automatic.Poly.nat_le_comp rVal_poly Automatic.Poly.list_length)
    rVal_poly Automatic.Poly.list_length

lemma rCap_encData (D : FieldData) : rCap D.encData = D.r := by
  unfold rCap
  rw [rVal_encData, if_pos (r_le_encData_length D)]

def targetWidth (a b c : ℕ) (xs : List Bool) : ℕ :=
  a * labWRaw xs + b * ((rCap xs + 1) * labWRaw xs) + c

@[fun_prop] theorem targetWidth_poly (a b c : ℕ) : Automatic.Poly (targetWidth a b c) := by
  unfold targetWidth
  fun_prop

lemma targetWidth_encData (a b c : ℕ) (D : FieldData) :
    targetWidth a b c D.encData = a * D.labW + b * ((D.r + 1) * D.labW) + c := by
  unfold targetWidth
  rw [labWRaw_encData, rCap_encData]

lemma labWRaw_le (xs : List Bool) : labWRaw xs ≤ 2 * xs.length ^ 2 := by
  unfold labWRaw
  rw [Nat.size_le, q2Raw_eq]
  have hp : pVal xs < 2 ^ xs.length := by
    have h1 := Nat.lt_size_self (pVal xs)
    have h2 : (pVal xs).size ≤ xs.length := by
      rw [← Nat.size_eq_bits_len]
      exact pVal_bits_length xs
    exact h1.trans_le (Nat.pow_le_pow_right (by decide) h2)
  have hp2 : pVal xs * pVal xs < 2 ^ (2 * xs.length) := by
    rw [two_mul, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt hp hp
  have hpow : (pVal xs * pVal xs) ^ min (rVal xs) xs.length ≤ (2 ^ (2 * xs.length)) ^ xs.length := by
    cases hmin : min (rVal xs) xs.length with
    | zero =>
        rw [pow_zero]
        exact Nat.one_le_pow _ _ (Nat.pow_pos (by decide))
    | succ k =>
        have hk : k + 1 ≤ xs.length := by rw [← hmin]; exact min_le_right _ _
        have hle1 : (pVal xs * pVal xs) ^ (k + 1) ≤ (2 ^ (2 * xs.length)) ^ (k + 1) :=
          Nat.pow_le_pow_left hp2.le _
        have hle2 : (2 ^ (2 * xs.length)) ^ (k + 1) ≤ (2 ^ (2 * xs.length)) ^ xs.length :=
          Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by decide)) hk
        exact hle1.trans hle2
  have hexp : (2 ^ (2 * xs.length)) ^ xs.length = 2 ^ (2 * xs.length ^ 2) := by
    rw [← pow_mul, sq, mul_assoc]
  rw [hexp] at hpow
  have hpos : 0 < 2 ^ (2 * xs.length ^ 2) := Nat.pow_pos (by decide)
  omega

lemma targetWidth_le (a b c : ℕ) (xs : List Bool) :
    targetWidth a b c xs ≤ (2 * a + 2 * b + c) * (xs.length + 1) ^ 3 := by
  unfold targetWidth
  have hlab : labWRaw xs ≤ 2 * (xs.length + 1) ^ 2 :=
    (labWRaw_le xs).trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (Nat.le_succ _) 2))
  have hlab3 : labWRaw xs ≤ 2 * (xs.length + 1) ^ 3 := by
    have h1 : (xs.length + 1) ^ 2 ≤ (xs.length + 1) ^ 3 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    exact hlab.trans (Nat.mul_le_mul_left 2 h1)
  have hrc : rCap xs + 1 ≤ xs.length + 1 := by
    unfold rCap; split_ifs with h <;> omega
  have hterm2 : (rCap xs + 1) * labWRaw xs ≤ 2 * (xs.length + 1) ^ 3 := by
    calc
      (rCap xs + 1) * labWRaw xs ≤ (xs.length + 1) * (2 * (xs.length + 1) ^ 2) :=
        Nat.mul_le_mul hrc hlab
      _ = 2 * (xs.length + 1) ^ 3 := by ring
  have hc1 : 1 ≤ (xs.length + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  calc
    a * labWRaw xs + b * ((rCap xs + 1) * labWRaw xs) + c
        ≤ a * (2 * (xs.length + 1) ^ 3) + b * (2 * (xs.length + 1) ^ 3) + c * (xs.length + 1) ^ 3 :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left a hlab3) (Nat.mul_le_mul_left b hterm2))
            (by simpa using Nat.mul_le_mul_left c hc1)
    _ = (2 * a + 2 * b + c) * (xs.length + 1) ^ 3 := by ring

def fuelList (a b c : ℕ) (xs : List Bool) : List Bool :=
  let xs1 := true :: xs
  let xs2 := xs1.flatMap (fun _ => xs1)
  let xs3 := xs2.flatMap (fun _ => xs1)
  xs3.flatMap (fun _ => List.replicate (2 * a + 2 * b + c) true)

@[fun_prop] theorem fuelList_poly (a b c : ℕ) : Automatic.Poly (fuelList a b c) := by
  unfold fuelList
  fun_prop

lemma fuelList_length (a b c : ℕ) (xs : List Bool) :
    (fuelList a b c xs).length = (2 * a + 2 * b + c) * (xs.length + 1) ^ 3 := by
  unfold fuelList
  simp only [List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul,
    List.length_cons, List.length_replicate]
  ring

def repStep (st : ℕ × List Bool) (_ : Bool) : ℕ × List Bool :=
  if st.1 = 0 then st else (st.1 - 1, true :: st.2)

@[fun_prop] theorem repStep_poly :
    Automatic.Poly (fun x : (ℕ × List Bool) × Bool => repStep x.1 x.2) := by
  unfold repStep
  exact Automatic.Poly.ite_prop
    (Automatic.Poly.nat_eq_comp
      (Automatic.Poly.comp (f := Prod.fst) Automatic.Poly.fst Automatic.Poly.fst)
      (Automatic.Poly.const 0))
    (by fun_prop) (by fun_prop)

lemma repStep_fold_eq (ls : List Bool) (k : ℕ) (acc : List Bool) :
    ls.foldl (fun st a => repStep st a) (k, acc) =
      (k - ls.length, List.replicate (min k ls.length) true ++ acc) := by
  induction ls generalizing k acc with
  | nil => simp
  | cons a ls ih =>
      simp only [List.foldl_cons, List.length_cons]
      cases k with
      | zero =>
          have h0 : repStep (0, acc) a = (0, acc) := rfl
          rw [h0]
          simpa using ih 0 acc
      | succ k' =>
          have h1 : repStep (k' + 1, acc) a = (k', true :: acc) := by simp [repStep]
          rw [h1, ih k' (true :: acc)]
          have hmin : min (k' + 1) (ls.length + 1) = min k' ls.length + 1 := by omega
          rw [hmin, List.replicate_succ', List.append_assoc, List.singleton_append]
          simp [Nat.succ_sub_succ_eq_sub]

noncomputable def repFoldProg :
    PolyProgram (encodePair (encodeList encodeBool) (encodePair Nat.bits (encodeList encodeBool)))
      (encodePair Nat.bits (encodeList encodeBool))
      (fun x : List Bool × (ℕ × List Bool) => x.1.foldl (fun st a => repStep st a) x.2) := by
  refine PolyProgram.listFoldLinear repStep_poly.program false 1 (fun st a => ?_)
  by_cases hz : st.1 = 0
  · simp only [repStep, hz, ↓reduceIte]; omega
  · simp only [repStep, hz, ↓reduceIte]
    change (encodePair Nat.bits (encodeList encodeBool) (st.1 - 1, true :: st.2)).length ≤
      (encodePair Nat.bits (encodeList encodeBool) st).length + 1 * (2 * (encodeBool a).length + 1)
    have hm := NatBinary.length_mono (Nat.sub_le st.1 1)
    simp only [encodePair_length, EncodedList.cons_length, encodeBool, List.length_cons,
      List.length_nil]
    omega

@[fun_prop] theorem repFold_poly :
    Automatic.Poly (fun x : List Bool × (ℕ × List Bool) => x.1.foldl (fun st a => repStep st a) x.2) :=
  ⟨repFoldProg⟩

def encWidthFun (a b c : ℕ) (xs : List Bool) : List Bool :=
  ((fuelList a b c xs).foldl (fun st d => repStep st d) (targetWidth a b c xs, [false])).2

@[fun_prop] theorem encWidthFun_poly (a b c : ℕ) : Automatic.Poly (encWidthFun a b c) := by
  unfold encWidthFun
  exact Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd
    (Automatic.Poly.comp repFold_poly
      (Automatic.Poly.pair (fuelList_poly a b c)
        (Automatic.Poly.pair (targetWidth_poly a b c) (Automatic.Poly.const [false]))))

lemma encWidthFun_encData (a b c : ℕ) (D : FieldData) :
    encWidthFun a b c D.encData = encNat (a * D.labW + b * ((D.r + 1) * D.labW) + c) := by
  unfold encWidthFun
  rw [repStep_fold_eq]
  have hle : targetWidth a b c D.encData ≤ (fuelList a b c D.encData).length := by
    rw [fuelList_length]
    exact targetWidth_le a b c D.encData
  rw [min_eq_left hle, targetWidth_encData]
  rfl

lemma width_linear_poly (a b c : ℕ) :
    ∃ f : Str → Str, PolyTimeComputable f ∧
      ∀ D : FieldData, f D.encData = encNat (a * D.labW + b * ((D.r + 1) * D.labW) + c) := by
  let P : PolyProgram id id (encWidthFun a b c) :=
    (BooleanLists.packProgram.comp (encWidthFun_poly a b c).program).comp
      BooleanLists.unpackProgram
  refine ⟨encWidthFun a b c, ⟨P.stock⟩, fun D => encWidthFun_encData a b c D⟩

end GL2QFT_FieldWidthsPoly_Aux

theorem solution :
    (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat D.labW) ∧
    (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat ((D.r + 1) * D.labW)) ∧
    (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat ((D.r + 1) * D.labW + (D.r + 1) * D.labW)) ∧
    (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat (1 + (D.r + 1) * D.labW)) ∧
    (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat (2 * D.labW)) ∧
    (∃ f : Str → Str, PolyTimeComputable f ∧ ∀ D : FieldData, f D.encData = encNat (5 * D.labW)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f, hf, heq⟩ := GL2QFT_FieldWidthsPoly_Aux.width_linear_poly 1 0 0
    exact ⟨f, hf, fun D => by simpa using heq D⟩
  · obtain ⟨f, hf, heq⟩ := GL2QFT_FieldWidthsPoly_Aux.width_linear_poly 0 1 0
    exact ⟨f, hf, fun D => by simpa using heq D⟩
  · obtain ⟨f, hf, heq⟩ := GL2QFT_FieldWidthsPoly_Aux.width_linear_poly 0 2 0
    exact ⟨f, hf, fun D => by
      have h := heq D
      simpa [two_mul] using h⟩
  · obtain ⟨f, hf, heq⟩ := GL2QFT_FieldWidthsPoly_Aux.width_linear_poly 0 1 1
    exact ⟨f, hf, fun D => by
      have h := heq D
      simpa [Nat.add_comm] using h⟩
  · obtain ⟨f, hf, heq⟩ := GL2QFT_FieldWidthsPoly_Aux.width_linear_poly 2 0 0
    exact ⟨f, hf, fun D => by simpa using heq D⟩
  · obtain ⟨f, hf, heq⟩ := GL2QFT_FieldWidthsPoly_Aux.width_linear_poly 5 0 0
    exact ⟨f, hf, fun D => by simpa using heq D⟩
