-- Prove2me | solution 1 for EditGV897.Main.codec_input_programs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:08.561261+00:00
-- url     : https://prove2.me/submissions/ed50b33f-6644-45a5-8378-4638e1f7535a

import Definitions.Def_EditGV897_Main_Codec
import Theorems.Thm_EditGV897_Main_binary_program_realization
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Size
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Binary
namespace EditGV897.Main

 theorem bit_zero_or_one (a : Bit) : a = 0 ∨ a = 1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl


@[simp] theorem wordList_length {n : ℕ} (x : Word n) : (wordList x).length = n := by
  simp [wordList, DeletionHash.MixedEdit.letters]

@[simp] theorem listWord_wordList {n : ℕ} (x : Word n) : listWord n (wordList x) = x := by
  funext i
  simp [listWord, wordList, DeletionHash.MixedEdit.letters]

theorem wordList_listWord {n : ℕ} (p : List Bit) (hp : p.length = n) :
    wordList (listWord n p) = p := by
  apply List.ext_getElem
  · simp [hp]
  · intro i hi hj
    simp only [wordList, DeletionHash.MixedEdit.letters, List.getElem_ofFn, listWord]
    simp [List.getElem?_eq_getElem, hj]


end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawEquation := List Bool × Bool

abbrev rawEquationEncoding : RawEquation ↪ List Bool := encPair encBits encBool

def rawXorEquation (a b : RawEquation) : RawEquation :=
  (a.1.zipWith Bool.xor b.1, Bool.xor a.2 b.2)

def rawCoordinate (e : RawEquation) (k : ℕ) : Bool := e.1[k]?.getD false

def rawZero (e : RawEquation) : Bool := !(e.1.any id)

@[fun_prop]
theorem rawXorEquation_polytime : ComputableTidilyInPolyTime
    (fun p : RawEquation × RawEquation => rawXorEquation p.1 p.2)
    (encPair rawEquationEncoding rawEquationEncoding) rawEquationEncoding := by
  let left := fst rawEquationEncoding rawEquationEncoding
  let right := snd rawEquationEncoding rawEquationEncoding
  have hl := (fst encBits encBool).comp left
  have hr := (fst encBits encBool).comp right
  have hbl := (snd encBits encBool).comp left
  have hbr := (snd encBits encBool).comp right
  have hxor : ComputableTidilyInPolyTime (fun p : Bool × Bool => Bool.xor p.1 p.2)
      (encPair encBool encBool) encBool := of_finite _
  exact ((bitsZipWith Bool.xor).comp (hl.prod hr)).prod (hxor.comp (hbl.prod hbr))

@[fun_prop]
theorem rawCoordinate_polytime : ComputableTidilyInPolyTime
    (fun p : RawEquation × ℕ => rawCoordinate p.1 p.2)
    (encPair rawEquationEncoding encUnary) encBool := by
  have hl := (fst encBits encBool).comp (fst rawEquationEncoding encUnary)
  have hi := snd rawEquationEncoding encUnary
  have hg := bitsGetElem? hl hi
  have hd : ComputableTidilyInPolyTime (fun a : Option Bool => a.getD false) (encOption encBool) encBool :=
    of_finite _
  exact hd.comp hg

@[fun_prop]
theorem rawZero_polytime : ComputableTidilyInPolyTime rawZero rawEquationEncoding encBool := by
  have ha := bitsAnyWithInput (test := fun _ b => b) (fst encBits encBool) (snd rawEquationEncoding encBool)
  have hn : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _
  exact hn.comp ha

theorem listErase_polytime {α : Type} [DecidableEq α] (enc : α ↪ List Bool) :
    ComputableTidilyInPolyTime (fun p : List α × α => p.1.erase p.2)
      (encPair (encList enc) enc) (encList enc) := by
  have hl := fst (encList enc) enc
  have hv := snd (encList enc) enc
  have hi := idxOfWithInput hl hv
  have hs := unary_add.comp (hi.prod (const (encMid := encUnary) 1))
  have ht := listTakeWithInput hl hi
  have hd := listDropWithInput hl hs
  convert listAppend' ht hd using 1
  funext p
  dsimp only [Function.comp_def]
  rw [← List.eraseIdx_eq_take_drop_succ, List.eraseIdx_idxOf_eq_erase]

abbrev RawEliminationState := ℕ × (ℕ × List RawEquation)
abbrev rawStateEncoding := encPair encUnary (encPair encUnary (encList rawEquationEncoding))

def rawPivot (k : ℕ) (E : List RawEquation) : Option RawEquation :=
  E.find? (fun e => rawCoordinate e k)

def rawClear (k : ℕ) (E : List RawEquation) (pivot : RawEquation) : List RawEquation :=
  (@List.erase RawEquation instBEqOfDecidableEq E pivot).map (fun e => if rawCoordinate e k then rawXorEquation e pivot else e)

def rawEliminationStep (s : RawEliminationState) : RawEliminationState :=
  let p := rawPivot s.1 s.2.2
  (s.1 + 1, if p.isSome then
    (s.2.1 + 1, rawClear s.1 s.2.2 (p.getD ([], false))) else s.2)

@[fun_prop]
theorem rawPivot_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawPivot p.1 p.2)
    (encPair encUnary (encList rawEquationEncoding)) (encOption rawEquationEncoding) := by
  apply findWithInput (snd encUnary (encList rawEquationEncoding))
  exact rawCoordinate_polytime.comp ((snd _ _).prod ((fst _ _).fst'))

@[fun_prop]
theorem rawClear_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawEquation) × RawEquation => rawClear p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList rawEquationEncoding)) rawEquationEncoding)
    (encList rawEquationEncoding) := by
  unfold rawClear
  have he := listErase_polytime rawEquationEncoding
  let en := encPair encUnary (encList rawEquationEncoding)
  have hfirst := fst en rawEquationEncoding
  have hsecond := snd en rawEquationEncoding
  have hl := he.comp (hfirst.snd'.prod hsecond)
  have houter := fst (encPair en rawEquationEncoding) rawEquationEncoding
  have helem := snd (encPair en rawEquationEncoding) rawEquationEncoding
  have hc := rawCoordinate_polytime.comp (helem.prod houter.fst'.fst')
  have hx := rawXorEquation_polytime.comp (helem.prod houter.snd')
  simpa only [Function.comp_def] using mapWithInput (encB := rawEquationEncoding)
    (f := fun (p : (ℕ × List RawEquation) × RawEquation) (e : RawEquation) =>
      if rawCoordinate e p.1.1 then rawXorEquation e p.2 else e)
    hl (by simpa only [Function.comp_def] using hc.cond hx helem)

@[fun_prop]
theorem rawEliminationStep_polytime : ComputableTidilyInPolyTime rawEliminationStep
    rawStateEncoding rawStateEncoding := by
  unfold rawEliminationStep
  have hk := fst encUnary (encPair encUnary (encList rawEquationEncoding))
  have hs := snd encUnary (encPair encUnary (encList rawEquationEncoding))
  have hr := hs.fst'
  have he := hs.snd'
  have hp := rawPivot_polytime.comp (hk.prod he)
  have hd := optionGetDWithInput hp (const (encMid := rawEquationEncoding) ([], false))
  have hc := rawClear_polytime.comp ((hk.prod he).prod hd)
  exact (unary_add.comp (hk.prod (const (encMid := encUnary) 1))).pair
    (hp.optionIsSome.cond ((unary_add.comp (hr.prod (const (encMid := encUnary) 1))).prod hc) hs)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

theorem rawClear_size (k : ℕ) (E : List RawEquation) (p : RawEquation) :
    (encList rawEquationEncoding (rawClear k E p)).length ≤
      (encList rawEquationEncoding E).length := by
  letI : BEq RawEquation := instBEqOfDecidableEq
  unfold rawClear
  refine (length_encList_map_le rawEquationEncoding rawEquationEncoding ?_).trans
    (length_encList_sublist rawEquationEncoding (by exact List.erase_sublist))
  intro e he
  split
  · simp only [rawXorEquation, rawEquationEncoding, length_encPair,
      encBits_apply, encBool_apply, List.length_singleton, List.length_zipWith]
    omega
  · exact le_rfl

theorem rawEliminationStep_growth (s : RawEliminationState) :
    (rawStateEncoding (rawEliminationStep s)).length ≤ (rawStateEncoding s).length + 4 := by
  dsimp only [rawEliminationStep]
  split
  · have h := rawClear_size s.1 s.2.2 ((rawPivot s.1 s.2.2).getD ([], false))
    simp only [rawStateEncoding, length_encPair, encUnary_apply, List.length_replicate,
      Prod.fst, Prod.snd]
    omega
  · simp only [rawStateEncoding, length_encPair, encUnary_apply, List.length_replicate,
      Prod.fst, Prod.snd]
    omega

def rawEliminate (n : ℕ) (E : List RawEquation) : RawEliminationState :=
  rawEliminationStep^[n] (0, (0, E))

@[fun_prop]
theorem rawEliminate_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawEliminate p.1 p.2)
    (encPair encUnary (encList rawEquationEncoding)) rawStateEncoding := by
  exact iterate_of_bounded_growth (fst _ _)
    ((const (encMid := encUnary) 0).prod
      ((const (encMid := encUnary) 0).prod (snd _ _)))
    rawEliminationStep_polytime rawEliminationStep_growth

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawBad (e : RawEquation) : Bool := rawZero e && e.2

def rawPivotCount (E : List RawEquation) : ℕ := (E.filter (fun e => !rawZero e)).length

def rawGaussian : ℕ → ℕ → List RawEquation → List RawEquation
  | 0, _, E => E
  | fuel + 1, k, E => match rawPivot k E with
    | none => rawGaussian fuel (k+1) E
    | some p => p :: rawGaussian fuel (k+1) (rawClear k E p)

def rawSummary (s : RawEliminationState) : ℕ × Bool :=
  (s.2.1 + rawPivotCount s.2.2, s.2.2.any rawBad)

theorem rawCoordinate_nonzero (e : RawEquation) (k : ℕ) (h : rawCoordinate e k = true) :
    rawZero e = false := by
  unfold rawCoordinate at h
  have hm : true ∈ e.1 := by
    cases he : e.1[k]? with
    | none => simp [he] at h
    | some b =>
      have hb : b = true := by simpa only [he, Option.getD_some] using h
      exact hb ▸ List.mem_of_getElem? he
  have ha : e.1.any id = true := List.any_eq_true.mpr ⟨true, hm, rfl⟩
  simp [rawZero, ha]

theorem rawGaussian_summary (fuel : ℕ) (s : RawEliminationState) :
    rawSummary (rawEliminationStep^[fuel] s) =
      (s.2.1 + rawPivotCount (rawGaussian fuel s.1 s.2.2),
        (rawGaussian fuel s.1 s.2.2).any rawBad) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply, ih]
    cases hp : rawPivot s.1 s.2.2 with
    | none => simp [rawEliminationStep, hp, rawGaussian]
    | some p =>
      have hcoord : rawCoordinate p s.1 = true :=
        List.find?_some (p := fun e : RawEquation => rawCoordinate e s.1) hp
      have hz : rawZero p = false := rawCoordinate_nonzero p s.1 hcoord
      simp [rawEliminationStep, hp, rawGaussian, rawPivotCount, rawBad, hz,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[fun_prop]
theorem rawBad_polytime : ComputableTidilyInPolyTime rawBad rawEquationEncoding encBool := by
  have hand : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := of_finite _
  exact hand.comp (rawZero_polytime.prod (snd encBits encBool))

@[fun_prop]
theorem rawPivotCount_polytime : ComputableTidilyInPolyTime rawPivotCount
    (encList rawEquationEncoding) encUnary := by
  unfold rawPivotCount
  apply length_list rawEquationEncoding |>.comp
  apply filterWithInput (id' (encIn := encList rawEquationEncoding))
  have hn : ComputableTidilyInPolyTime Bool.not encBool encBool := of_finite _
  exact hn.comp (rawZero_polytime.comp (snd _ _))

@[fun_prop]
theorem rawSummary_polytime : ComputableTidilyInPolyTime rawSummary
    rawStateEncoding (encPair encUnary encBool) := by
  have hs := snd encUnary (encPair encUnary (encList rawEquationEncoding))
  have hr := hs.fst'
  have he := hs.snd'
  have hc := rawPivotCount_polytime.comp he
  have ha := anyWithInput (test := fun _ e => rawBad e) he
    (rawBad_polytime.comp (snd _ _))
  exact (unary_add.comp (hr.prod hc)).prod ha

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main

def bitBool (a : Bit) : Bool := decide (a ≠ 0)

@[simp] theorem bitBool_zero : bitBool 0 = false := by decide
@[simp] theorem bitBool_one : bitBool 1 = true := by decide

theorem bitBool_injective : Function.Injective bitBool := by
  intro a b
  fin_cases a <;> fin_cases b <;> norm_num [bitBool]

@[simp] theorem bitBool_add (a b : Bit) : bitBool (a+b) = Bool.xor (bitBool a) (bitBool b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem wordCode_injective {n : ℕ} : Function.Injective (@wordCode n) := by
  intro x y h
  have hw : wordList x = wordList y := (List.map_inj_right bitBool_injective).mp h
  simpa only [listWord_wordList] using congrArg (listWord n) hw

@[simp] theorem wordCode_length {n : ℕ} (x : Word n) : (wordCode x).length = n := by
  simp [wordCode, bitCode]

@[simp] theorem wordCode_get {n : ℕ} (x : Word n) (i : Fin n) :
    (wordCode x)[i.val]? = some (bitBool (x i)) := by
  simp [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters, bitBool]

@[simp] theorem wordCode_add {n : ℕ} (x y : Word n) :
    wordCode (x+y) = (wordCode x).zipWith Bool.xor (wordCode y) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [wordCode_length] at hi
    have heq := bitBool_add (x ⟨i, hi⟩) (y ⟨i, hi⟩)
    simpa [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
      List.getElem_zipWith, bitBool] using heq

def rawEquation {n : ℕ} (e : Equation n) : EditGV897.Runtime.RawEquation :=
  (wordCode e.1, bitBool e.2)

theorem rawEquation_injective {n : ℕ} : Function.Injective (@rawEquation n) := by
  intro a b h
  exact Prod.ext (wordCode_injective (congrArg Prod.fst h))
    (bitBool_injective (congrArg Prod.snd h))

@[simp] theorem rawEquation_xor {n : ℕ} (a b : Equation n) :
    rawEquation (xorEquation a b) = EditGV897.Runtime.rawXorEquation (rawEquation a) (rawEquation b) := by
  simp [rawEquation, xorEquation, EditGV897.Runtime.rawXorEquation]

@[simp] theorem rawEquation_coordinate {n k : ℕ} (e : Equation n) (hk : k < n) :
    EditGV897.Runtime.rawCoordinate (rawEquation e) k = decide (e.1 ⟨k, hk⟩ ≠ 0) := by
  change (wordCode e.1)[k]?.getD false = bitBool (e.1 ⟨k, hk⟩)
  rw [wordCode_get e.1 ⟨k, hk⟩]
  rfl

@[simp] theorem rawEquation_zero {n : ℕ} (e : Equation n) :
    EditGV897.Runtime.rawZero (rawEquation e) = decide (e.1 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [EditGV897.Runtime.rawZero, rawEquation, Bool.not_eq_true',
    List.any_eq_false, wordCode, bitCode, List.forall_mem_map, bitBool,
    decide_eq_false_iff_not, ne_eq, not_not, decide_eq_true_eq]
  constructor
  · intro h
    funext i
    simpa using h (e.1 i) (by simp [wordList, DeletionHash.MixedEdit.letters])
  · intro h
    simp [h, wordList, DeletionHash.MixedEdit.letters]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawCount (n : ℕ) (E : List RawEquation) : ℕ :=
  let result := rawSummary (rawEliminate n E)
  if result.2 then 0 else 2 ^ (n - result.1)

@[fun_prop]
theorem rawCount_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawCount p.1 p.2)
    (encPair encUnary (encList rawEquationEncoding)) encNat := by
  unfold rawCount
  have hr := rawSummary_polytime.comp rawEliminate_polytime
  have hn := fst encUnary (encList rawEquationEncoding)
  have he := unary_sub.comp (hn.prod hr.fst')
  exact hr.snd'.cond (const 0) (binary_two_pow.comp he)

def readUnary (w : List Bool) : ℕ := w.idxOf false

def dropHeader (w : List Bool) : List Bool := w.drop (readUnary w + 1)

@[fun_prop]
theorem readUnary_polytime : ComputableTidilyInPolyTime readUnary encBits encUnary := by
  exact idxOfWithInput bitsToList (const false)

@[fun_prop]
theorem dropHeader_polytime : ComputableTidilyInPolyTime dropHeader encBits encBits := by
  unfold dropHeader
  exact bitsDropWithInput id' (unary_add.comp (readUnary_polytime.prod (const (encMid := encUnary) 1)))

/-- A bounded total parser: malformed data is truncated or padded by zero bits. -/
def rawReadEquation (n : ℕ) (w : List Bool) : RawEquation :=
  (w.take n, w[n]?.getD false)

@[fun_prop]
theorem rawReadEquation_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawReadEquation p.1 p.2)
    (encPair encUnary encBits) rawEquationEncoding := by
  exact (bitsTakeWithInput (snd _ _) (fst _ _)).prod
    (by simpa only [List.getD_eq_getElem?_getD] using bitsGetDWithInput (snd encUnary encBits) (fst encUnary encBits) false)

/-- Parse a fixed number of dense equations of a declared common width. -/
def rawReadEquations (n m : ℕ) (w : List Bool) : List RawEquation :=
  (List.range m).map (fun i => rawReadEquation n (w.drop (i * (n+1))))

@[fun_prop]
theorem rawReadEquations_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => rawReadEquations p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList rawEquationEncoding) := by
  unfold rawReadEquations
  have hlist := range.comp ((fst (encPair encUnary encUnary) encBits).snd')
  apply mapWithInput (encB := rawEquationEncoding) hlist
  have houter := fst (encPair (encPair encUnary encUnary) encBits) encUnary
  have hi := snd (encPair (encPair encUnary encUnary) encBits) encUnary
  have hn := houter.fst'.fst'
  have hw := houter.snd'
  exact rawReadEquation_polytime.comp (hn.prod
    (bitsDropWithInput hw (unary_mul.comp (hi.prod
      (unary_add.comp (hn.prod (const (encMid := encUnary) 1)))))))

def rawCounter (w : List Bool) : ℕ :=
  let n := readUnary w
  let w' := dropHeader w
  let m := readUnary w'
  rawCount n (rawReadEquations n m (dropHeader w'))

@[fun_prop]
theorem rawCounter_polytime : ComputableTidilyInPolyTime rawCounter encBits encNat := by
  unfold rawCounter
  have hn := readUnary_polytime
  have hw := dropHeader_polytime
  have hm := readUnary_polytime.comp hw
  have hw' := dropHeader_polytime.comp hw
  exact rawCount_polytime.comp
    (hn.prod (rawReadEquations_polytime.comp ((hn.prod hm).prod hw')))

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

theorem rawPivot_equations {n k : ℕ} (E : List (Equation n)) (hk : k < n) :
    rawPivot k (E.map rawEquation) =
      (E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0))).map rawEquation := by
  simp [rawPivot, List.find?_map, Function.comp_def, rawEquation_coordinate, hk]

theorem rawClear_equations {n k : ℕ} (E : List (Equation n)) (p : Equation n) (hk : k < n) :
    rawClear k (E.map rawEquation) (rawEquation p) =
      ((E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p)).map rawEquation := by
  letI : BEq RawEquation := instBEqOfDecidableEq
  unfold rawClear
  rw [← List.map_erase rawEquation_injective]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro e he
  rw [rawEquation_coordinate e hk]
  by_cases hz : e.1 ⟨k, hk⟩ = 0 <;> simp [hz]

theorem rawGaussian_equations {n : ℕ} (fuel k : ℕ) (E : List (Equation n))
    (h : fuel + k ≤ n) :
    rawGaussian fuel k (E.map rawEquation) = (gaussian fuel k E).map rawEquation := by
  induction fuel generalizing k E with
  | zero => rfl
  | succ fuel ih =>
    have hk : k < n := by omega
    unfold rawGaussian gaussian
    rw [dif_pos hk, rawPivot_equations E hk]
    cases hp : E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0)) with
    | none =>
      simp only [Option.map_none]
      exact ih (k+1) E (by omega)
    | some p =>
      simp only [Option.map_some, List.map_cons]
      rw [rawClear_equations E p hk, ih (k+1) _ (by omega)]

theorem rawPivotCount_equations {n : ℕ} (E : List (Equation n)) :
    rawPivotCount (E.map rawEquation) = pivotCount E := by
  unfold rawPivotCount pivotCount
  rw [List.filter_map]
  simp [Function.comp_def, rawEquation_zero]

theorem rawBad_equations {n : ℕ} (E : List (Equation n)) :
    (E.map rawEquation).any rawBad = E.any (fun e => decide (e.1 = 0 ∧ e.2 ≠ 0)) := by
  simp only [List.any_map]
  congr 1
  funext e
  dsimp only [Function.comp_def]
  unfold rawBad
  rw [rawEquation_zero]
  simp [rawEquation, bitBool]

theorem rawCount_equations {n : ℕ} (E : List (Equation n)) :
    rawCount n (E.map rawEquation) = affineCount E := by
  unfold rawCount rawEliminate
  rw [rawGaussian_summary n (0, (0, E.map rawEquation)),
    rawGaussian_equations n 0 E (by omega)]
  simp only [Nat.zero_add, rawPivotCount_equations, rawBad_equations, affineCount]

@[simp] theorem readUnary_prefix (n : ℕ) (w : List Bool) :
    readUnary (unary n ++ w) = n := by
  induction n with
  | zero => simp [unary, readUnary]
  | succ n ih =>
    have he : unary (n+1) ++ w = true :: (unary n ++ w) := by simp [unary, List.replicate_succ]
    rw [he]
    simpa [readUnary, List.idxOf_cons] using ih

@[simp] theorem dropHeader_prefix (n : ℕ) (w : List Bool) :
    dropHeader (unary n ++ w) = w := by
  unfold dropHeader
  rw [readUnary_prefix]
  simp [unary, List.drop_append]

@[simp] theorem rawReadEquation_code {n : ℕ} (e : Equation n) (tail : List Bool) :
    rawReadEquation n (wordCode e.1 ++ bitBool e.2 :: tail) = rawEquation e := by
  simp [rawReadEquation, rawEquation, List.take_append, List.getElem?_append_right,
    wordCode_length, List.take_of_length_le]

theorem rawReadEquations_codes {n : ℕ} (E : List (Equation n)) :
    rawReadEquations n E.length
      (E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2])) = E.map rawEquation := by
  induction E with
  | nil => simp [rawReadEquations]
  | cons e E ih =>
    simp only [rawReadEquations, List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.flatMap_cons, List.drop_zero, List.map_cons] at *
    simp only [Nat.zero_mul, List.drop_zero, List.singleton_append]
    rw [List.append_assoc]
    simp only [List.cons_append, List.nil_append, rawReadEquation_code]
    congr 1
    rw [← ih]
    apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    congr 1
    have hlen : (wordCode e.1 ++ [bitBool e.2]).length = n + 1 := by simp
    have heq : (i+1)*(n+1) = (n+1) + i*(n+1) := by ring
    change (wordCode e.1 ++ ([bitBool e.2] ++
      E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2]))).drop ((i+1)*(n+1)) = _
    rw [← List.append_assoc, heq, ← List.drop_drop]
    have hdrop : ((wordCode e.1 ++ [bitBool e.2]) ++
        E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2])).drop (n+1) =
        E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2]) := by
      rw [← hlen, List.drop_left]
    rw [hdrop]

 theorem rawCounter_correct {n : ℕ} (E : List (Equation n)) :
    rawCounter (unary n ++ equationCode E) = affineCount E := by
  simp only [rawCounter, equationCode, readUnary_prefix, dropHeader_prefix]
  change rawCount n (rawReadEquations n E.length
    (E.flatMap (fun e => wordCode e.1 ++ [bitBool e.2]))) = _
  rw [rawReadEquations_codes, rawCount_equations]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawAffine := List (List Bool) × List Bool
abbrev rawAffineEncoding := encPair (encList encBits) encBits

def rawDot (x y : List Bool) : Bool := (x.zipWith Bool.and y).foldl Bool.xor false

def rawUnit (n k : ℕ) : List Bool := (List.range n).map (fun i => decide (i=k))

def rawRow (A : List (List Bool)) (i : ℕ) : List Bool := A[i]?.getD []

def rawColumn (n : ℕ) (A : List (List Bool)) (j : ℕ) : List Bool :=
  (List.range n).map (fun i => (rawRow A i)[j]?.getD false)

def rawPull (n : ℕ) (f : RawAffine) (h : List Bool) : RawEquation :=
  ((List.range n).map (fun j => Bool.xor (h[j]?.getD false)
      (rawDot h (rawColumn n f.1 j))), rawDot h f.2)

def rawFixed (n : ℕ) (f : RawAffine) : List RawEquation :=
  (List.range n).map (fun i =>
    ((rawUnit n i).zipWith Bool.xor (rawRow f.1 i), f.2[i]?.getD false))

def rawCollision (n : ℕ) (f : RawAffine) (G : List (List Bool)) : List RawEquation :=
  G.map (rawPull n f)

@[fun_prop]
theorem rawDot_polytime : ComputableTidilyInPolyTime
    (fun p : List Bool × List Bool => rawDot p.1 p.2)
    (encPair encBits encBits) encBool := by
  exact bitsFoldlWithInput Bool.xor (bitsZipWith Bool.and) (const false)

@[fun_prop]
theorem rawUnit_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => rawUnit p.1 p.2)
    (encPair encUnary encUnary) encBits := by
  unfold rawUnit
  apply mapToBitsWithInput (range.comp (fst _ _))
  exact unary_beq ((snd _ _)) ((fst _ _).snd')

@[fun_prop]
theorem rawRow_polytime : ComputableTidilyInPolyTime
    (fun p : List (List Bool) × ℕ => rawRow p.1 p.2)
    (encPair (encList encBits) encUnary) encBits := by
  unfold rawRow
  exact optionGetDWithInput (getElem? (fst (encList encBits) encUnary) (snd (encList encBits) encUnary)) (const [])

@[fun_prop]
theorem rawColumn_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List (List Bool)) × ℕ => rawColumn p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList encBits)) encUnary) encBits := by
  unfold rawColumn
  have hlist := range.comp ((fst (encPair encUnary (encList encBits)) encUnary).fst')
  apply mapToBitsWithInput hlist
  have ho := fst (encPair (encPair encUnary (encList encBits)) encUnary) encUnary
  have hi := snd (encPair (encPair encUnary (encList encBits)) encUnary) encUnary
  have hr := rawRow_polytime.comp (ho.fst'.snd'.prod hi)
  simpa only [List.getD_eq_getElem?_getD, Function.comp_def] using bitsGetDWithInput hr ho.snd' false

@[fun_prop]
theorem rawPull_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × RawAffine) × List Bool => rawPull p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary rawAffineEncoding) encBits) rawEquationEncoding := by
  unfold rawPull
  let en := encPair (encPair encUnary rawAffineEncoding) encBits
  have hp := fst (encPair encUnary rawAffineEncoding) encBits
  have hn := hp.fst'
  have hf := hp.snd'
  have hh := snd (encPair encUnary rawAffineEncoding) encBits
  have hright := rawDot_polytime.comp (hh.prod hf.snd')
  have hlist := range.comp hn
  have hleft : ComputableTidilyInPolyTime
      (fun p : (ℕ × RawAffine) × List Bool => (List.range p.1.1).map
        (fun j => Bool.xor (p.2[j]?.getD false) (rawDot p.2 (rawColumn p.1.1 p.1.2.1 j))))
      en encBits := by
    apply mapToBitsWithInput hlist
    have ho := fst en encUnary
    have hj := snd en encUnary
    have hc := rawColumn_polytime.comp ((ho.fst'.fst'.prod ho.fst'.snd'.fst').prod hj)
    have hd := rawDot_polytime.comp (ho.snd'.prod hc)
    have hb := bitsGetDWithInput ho.snd' hj false
    have hx : ComputableTidilyInPolyTime (fun p : Bool × Bool => Bool.xor p.1 p.2)
        (encPair encBool encBool) encBool := of_finite _
    simpa only [Function.comp_def, List.getD_eq_getElem?_getD] using hx.comp (hb.prod hd)
  exact hleft.prod hright

@[fun_prop]
theorem rawFixed_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × RawAffine => rawFixed p.1 p.2)
    (encPair encUnary rawAffineEncoding) (encList rawEquationEncoding) := by
  unfold rawFixed
  let en := encPair encUnary rawAffineEncoding
  have hlist := range.comp (fst encUnary rawAffineEncoding)
  apply mapWithInput (encB := rawEquationEncoding) hlist
  have ho := fst en encUnary
  have hi := snd en encUnary
  have hu := rawUnit_polytime.comp (ho.fst'.prod hi)
  have hr := rawRow_polytime.comp (ho.snd'.fst'.prod hi)
  have hb := bitsGetDWithInput ho.snd'.snd' hi false
  simpa only [Function.comp_def, List.getD_eq_getElem?_getD] using
    ((bitsZipWith Bool.xor).comp (hu.prod hr)).prod hb

set_option maxHeartbeats 1200000 in
theorem rawCollision_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × RawAffine) × List (List Bool) => rawCollision p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary rawAffineEncoding) (encList encBits)) (encList rawEquationEncoding) := by
  unfold rawCollision
  let en := encPair (encPair encUnary rawAffineEncoding) (encList encBits)
  apply mapWithInput (encB := rawEquationEncoding)
    (snd (encPair encUnary rawAffineEncoding) (encList encBits))
  have ho := fst en encBits
  have hh := snd en encBits
  exact rawPull_polytime.comp (ho.fst'.prod hh)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

@[simp] theorem bitBool_mul (a b : Bit) : bitBool (a*b) = (bitBool a && bitBool b) := by
  fin_cases a <;> fin_cases b <;> decide

theorem bitBool_foldl (L : List Bit) (a : Bit) :
    bitBool (L.foldl (·+·) a) = (L.map bitBool).foldl Bool.xor (bitBool a) := by
  induction L generalizing a with
  | nil => rfl
  | cons b L ih => simp only [List.foldl_cons, List.map_cons, ← bitBool_add, ih]

theorem bitBool_sum (L : List Bit) : bitBool L.sum = (L.map bitBool).foldl Bool.xor false := by
  simpa only [List.sum_eq_foldl, bitBool_zero] using bitBool_foldl L 0

theorem rawDot_words {n : ℕ} (x y : Word n) :
    rawDot (wordCode x) (wordCode y) = bitBool (dot x y) := by
  have he : (wordCode x).zipWith Bool.and (wordCode y) =
      (List.ofFn (fun i : Fin n => x i * y i)).map bitBool := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < n := by simpa using hi
      simp [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
        List.getElem_zipWith, ← bitBool_mul, bitBool]
  rw [rawDot, he, ← bitBool_sum, List.sum_ofFn]
  rfl

 theorem rawUnit_word {n k : ℕ} : rawUnit n k = wordCode (unitWord n k) := by
  apply List.ext_getElem
  · simp [rawUnit]
  · intro i hi hj
    simp [rawUnit, wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
      unitWord, bitBool]

def rawAffine {n : ℕ} (f : Affine n) : RawAffine :=
  (List.ofFn (fun i : Fin n => wordCode (f.matrix i)), wordCode f.offset)

@[simp] theorem rawRow_matrix {n : ℕ} (f : Affine n) (i : Fin n) :
    rawRow (rawAffine f).1 i.val = wordCode (f.matrix i) := by
  simp [rawRow, rawAffine]

 theorem rawColumn_matrix {n : ℕ} (f : Affine n) (j : Fin n) :
    rawColumn n (rawAffine f).1 j.val = wordCode (fun i => f.matrix i j) := by
  apply List.ext_getElem
  · simp [rawColumn]
  · intro i hi hj
    have hi' : i < n := by simpa [rawColumn] using hi
    simp only [rawColumn, List.getElem_map, List.getElem_range]
    rw [rawRow_matrix f ⟨i, hi'⟩, wordCode_get _ j]
    simp [wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters, bitBool]

 theorem rawPull_equation {n : ℕ} (f : Affine n) (h : Word n) :
    rawPull n (rawAffine f) (wordCode h) = rawEquation (pullZero (difference f) h) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [rawPull, rawEquation]
    · intro j hj hj'
      have hjn : j < n := by simpa [rawPull] using hj
      simp only [rawPull, List.getElem_map, List.getElem_range]
      rw [wordCode_get h ⟨j,hjn⟩, rawColumn_matrix f ⟨j,hjn⟩, rawDot_words]
      simp only [Option.getD_some, ← bitBool_add]
      have heq : (pullZero (difference f) h).1 ⟨j,hjn⟩ =
          h ⟨j,hjn⟩ + dot h (fun i => f.matrix i ⟨j,hjn⟩) := by
        simp [pullZero, difference, dot, mul_add, Finset.sum_add_distrib]
      simpa [rawEquation, wordCode, bitCode, wordList, DeletionHash.MixedEdit.letters,
        bitBool] using congrArg bitBool heq.symm
  · simpa [rawPull, rawAffine, rawEquation, pullZero, difference] using rawDot_words h f.offset

 theorem rawFixed_equations {n : ℕ} (f : Affine n) :
    rawFixed n (rawAffine f) = (fixedEquations f).map rawEquation := by
  apply List.ext_getElem
  · simp [rawFixed, fixedEquations]
  · intro i hi hj
    have hin : i < n := by simpa [rawFixed] using hi
    simp only [rawFixed, List.getElem_map, List.getElem_range, fixedEquations, List.getElem_ofFn]
    rw [rawUnit_word, rawRow_matrix f ⟨i,hin⟩, ← wordCode_add]
    have hd : unitWord n i + f.matrix ⟨i,hin⟩ = (difference f).matrix ⟨i,hin⟩ := by
      funext j
      simp [unitWord, difference, Fin.ext_iff, eq_comm]
    rw [hd]
    simp only [rawEquation, rawAffine]
    rw [wordCode_get f.offset ⟨i,hin⟩]
    rfl

 theorem rawCollision_equations {n : ℕ} (f : Affine n) (G : Rows n) :
    rawCollision n (rawAffine f) (G.map wordCode) = (collisionEquations f G).map rawEquation := by
  simp only [rawCollision, collisionEquations, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun h hh => rawPull_equation f h)

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev rawContributionEncoding := encPair (encPair encUnary rawAffineEncoding)
  (encPair (encList encBits) (encList rawEquationEncoding))

def rawContribution (n : ℕ) (f : RawAffine) (G : List (List Bool)) (E : List RawEquation) : ℕ :=
  rawCount n (E ++ rawCollision n f G) - rawCount n (E ++ rawFixed n f)

set_option maxHeartbeats 1200000 in
theorem rawContribution_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × RawAffine) × (List (List Bool) × List RawEquation) =>
      rawContribution p.1.1 p.1.2 p.2.1 p.2.2)
    rawContributionEncoding encNat := by
  unfold rawContribution
  have hnF := fst (encPair encUnary rawAffineEncoding) (encPair (encList encBits) (encList rawEquationEncoding))
  have hGE := snd (encPair encUnary rawAffineEncoding) (encPair (encList encBits) (encList rawEquationEncoding))
  have hn := hnF.fst'
  have hE := hGE.snd'
  have hc := rawCollision_polytime.comp (hnF.prod hGE.fst')
  have hf := rawFixed_polytime.comp hnF
  have hleft := rawCount_polytime.comp (hn.prod (listAppend' hE hc))
  have hright := rawCount_polytime.comp (hn.prod (listAppend' hE hf))
  exact binary_sub.comp (hleft.prod hright)

abbrev rawWitnessEncoding := encPair (encPair encUnary (encList rawAffineEncoding))
  (encPair (encList encBits) (encList rawEquationEncoding))

def rawWitness (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (E : List RawEquation) : ℕ :=
  (F.map (fun f => rawContribution n f G E)).sum

set_option maxHeartbeats 1200000 in
theorem rawWitness_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × List RawEquation) =>
      rawWitness p.1.1 p.1.2 p.2.1 p.2.2)
    rawWitnessEncoding encNat := by
  unfold rawWitness
  apply binary_sum.comp
  have hF := (fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) (encList rawEquationEncoding))).snd'
  apply mapWithInput (encB := encNat) hF
  have ho := fst rawWitnessEncoding rawAffineEncoding
  have hf := snd rawWitnessEncoding rawAffineEncoding
  exact rawContribution_polytime.comp ((ho.fst'.fst'.prod hf).prod ho.snd')

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawContribution_equations {n : ℕ} (f : Affine n) (G : Rows n) (E : List (Equation n)) :
    rawContribution n (rawAffine f) (G.map wordCode) (E.map rawEquation) =
      affineCount (E ++ collisionEquations f G) - affineCount (E ++ fixedEquations f) := by
  unfold rawContribution
  rw [rawCollision_equations, rawFixed_equations, ← List.map_append, ← List.map_append,
    rawCount_equations, rawCount_equations]

 theorem rawWitness_equations {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    rawWitness n (F.map rawAffine) (G.map wordCode) (E.map rawEquation) = witnessCount F G E := by
  unfold rawWitness witnessCount
  simp only [List.map_map, Function.comp_def, rawContribution_equations]

end EditGV897.Main
namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime
abbrev rawPrefixEncoding := encPair (encPair encUnary (encList rawAffineEncoding)) (encPair (encList encBits) encBits)
abbrev rawParametersEncoding := encPair (encList encBits) encBits
def rawUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]
theorem rawUnary_polytime : ComputableTidilyInPolyTime rawUnary encUnary encBits :=
  bitsAppend (bitsReplicate true) (const [false])
def rawPad (n : ℕ) (w : List Bool) : List Bool :=
  (List.range n).map (fun i => w[i]?.getD false)

theorem rawPad_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawPad p.1 p.2) (encPair encUnary encBits) encBits := by
  unfold rawPad
  apply mapToBitsWithInput (range.comp (fst _ _))
  have ho := fst (encPair encUnary encBits) encUnary
  have hi := snd (encPair encUnary encBits) encUnary
  simpa only [List.getD_eq_getElem?_getD] using bitsGetDWithInput ho.snd' hi false


end EditGV897.Runtime
namespace EditGV897.Main
open EditGV897.Runtime
 theorem rawPad_prefix {n : ℕ} (p : List Bit) :
    rawPad n (bitCode p) = wordCode (listWord n p) := by
  apply List.ext_getElem
  · simp [rawPad]
  · intro i hi hj
    have hi' : i < n := by simpa [rawPad] using hi
    simp only [rawPad, List.getElem_map, List.getElem_range]
    change ((p.map bitBool)[i]?).getD false =
      (wordCode (listWord n p))[i]'hj
    have he := wordCode_get (listWord n p) ⟨i,hi'⟩
    have hr : (wordCode (listWord n p))[i]'hj = bitBool (p[i]?.getD 0) := by
      have hsome := List.getElem?_eq_getElem hj
      rw [hsome] at he
      exact Option.some.inj he
    rw [hr]
    cases hp : p[i]? with
    | none => simp [List.getElem?_map, hp]
    | some b => simp [List.getElem?_map, hp]

 theorem wordCode_zero (n : ℕ) : wordCode (0 : Word n) = List.replicate n false := by
  simp [wordCode,bitCode,wordList,DeletionHash.MixedEdit.letters]
  exact List.ofFn_const n false


end EditGV897.Main


set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawCodecData := (ℕ × List RawAffine) × (List (List Bool) × List Bool)

def rawPrefixEquations (n : ℕ) (p : List Bool) : List RawEquation :=
  (List.range p.length).map (fun k => (rawUnit n k, p[k]?.getD false))

def rawPrefixNumbers (D : RawCodecData) (p : List Bool) : ℕ × ℕ :=
  let E := D.2.1.zip D.2.2 ++ rawPrefixEquations D.1.1 p
  (rawCount D.1.1 E, rawWitness D.1.1 D.1.2 D.2.1 E)

def rawEncodeStep (D : RawCodecData) (s : List Bool × ℕ) : List Bool × ℕ :=
  let c := rawPrefixNumbers D (s.1 ++ [false])
  if s.2+c.2 < c.1 then (s.1++[false],s.2)
  else (s.1++[true],s.2-(c.1-c.2))

def rawEncode (D : RawCodecData) (u : List Bool) : List Bool :=
  ((rawEncodeStep D)^[D.1.1] ([],Cslib.BitString.binaryValue u)).1

 theorem rawPrefixEquations_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawPrefixEquations p.1 p.2)
    (encPair encUnary encBits) (encList rawEquationEncoding) := by
  unfold rawPrefixEquations
  have hlen := length_bits_comp (snd encUnary encBits)
  apply mapWithInput (encB := rawEquationEncoding) (range.comp hlen)
  have ho := fst (encPair encUnary encBits) encUnary
  have hi := snd (encPair encUnary encBits) encUnary
  have hu := rawUnit_polytime.comp (ho.fst'.prod hi)
  have hb := bitsGetDWithInput ho.snd' hi false
  simpa only [Function.comp_def,List.getD_eq_getElem?_getD] using hu.prod hb

set_option maxHeartbeats 1600000 in
theorem rawPrefixNumbers_polytime : ComputableTidilyInPolyTime
    (fun p : RawCodecData × List Bool => rawPrefixNumbers p.1 p.2)
    (encPair rawPrefixEncoding encBits) (encPair encNat encNat) := by
  unfold rawPrefixNumbers
  have hD := fst rawPrefixEncoding encBits
  have hp := snd rawPrefixEncoding encBits
  have hn := hD.fst'.fst'
  have hG := hD.snd'.fst'
  have hβ := hD.snd'.snd'
  have hcoset := (zip encBits encBool).comp (hG.prod (bitsToList.comp hβ))
  have hprefix := rawPrefixEquations_polytime.comp (hn.prod hp)
  have hE := listAppend' hcoset hprefix
  simpa only [Function.comp_def] using
    (rawCount_polytime.comp (hn.prod hE)).prod
      (rawWitness_polytime.comp (hD.fst'.prod (hG.prod hE)))

set_option maxHeartbeats 1600000 in
theorem rawEncodeStep_polytime : ComputableTidilyInPolyTime
    (fun p : RawCodecData × (List Bool × ℕ) => rawEncodeStep p.1 p.2)
    (encPair rawPrefixEncoding (encPair encBits encNat)) (encPair encBits encNat) := by
  unfold rawEncodeStep
  have hD := fst rawPrefixEncoding (encPair encBits encNat)
  have hs := snd rawPrefixEncoding (encPair encBits encNat)
  have hp := hs.fst'
  have hm := hs.snd'
  have hp0 := bitsAppend hp (const [false])
  have hp1 := bitsAppend hp (const [true])
  have hc := rawPrefixNumbers_polytime.comp (hD.prod hp0)
  have hsum := binary_add.comp (hm.prod hc.snd')
  have htest := binary_lt.comp (hsum.prod hc.fst')
  have hdiff := binary_sub.comp (hc.fst'.prod hc.snd')
  have hrest := binary_sub.comp (hm.prod hdiff)
  simpa only [Function.comp_def,decide_eq_true_eq] using
    htest.cond (hp0.prod hm) (hp1.prod hrest)

theorem rawEncodeStep_growth (D : RawCodecData) (s : List Bool × ℕ) :
    (encPair encBits encNat (rawEncodeStep D s)).length ≤
      (encPair encBits encNat s).length + 2 := by
  dsimp only [rawEncodeStep]
  split
  · simp [length_encPair]
    omega
  · have hsize := Nat.size_le_size (Nat.sub_le s.2
      ((rawPrefixNumbers D (s.1 ++ [false])).1 - (rawPrefixNumbers D (s.1 ++ [false])).2))
    simp only [length_encPair,encBits_apply,encNat_apply,Nat.size_eq_bits_len,
      List.length_append,List.length_singleton]
    omega

 theorem rawEncode_polytime : ComputableTidilyInPolyTime
    (fun p : RawCodecData × List Bool => rawEncode p.1 p.2)
    (encPair rawPrefixEncoding encBits) encBits := by
  have hD := fst rawPrefixEncoding encBits
  have hu := snd rawPrefixEncoding encBits
  have hinit := (const (encMid := encBits) []).prod (bitsBinaryValue.comp hu)
  have hi := iterateWith_of_bounded_growth hD hD.fst'.fst' hinit rawEncodeStep_polytime
    (growth := fun _ => 2) (.const 2) (fun x state => rawEncodeStep_growth x.1 state)
  exact hi.fst'

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawInverseStep (D : RawCodecData) (s : List Bool × ℕ) (a : Bool) : List Bool × ℕ :=
  let c := rawPrefixNumbers D (s.1 ++ [false])
  (s.1 ++ [a],s.2 + if a then c.1-c.2 else 0)

def rawInverseIndex (D : RawCodecData) (x : List Bool) : ℕ :=
  (x.foldl (rawInverseStep D) ([],0)).2

def rawIndexBits (K m : ℕ) : List Bool :=
  (List.range K).map (fun j => m.testBit (K-1-j))

def rawInverse (D : RawCodecData) (x : List Bool) : List Bool :=
  rawIndexBits (D.1.1-D.2.1.length-1) (rawInverseIndex D x)

set_option maxHeartbeats 1600000 in
theorem rawInverseStep_polytime : ComputableTidilyInPolyTime
    (fun p : (RawCodecData × (List Bool × ℕ)) × Bool => rawInverseStep p.1.1 p.1.2 p.2)
    (encPair (encPair rawPrefixEncoding (encPair encBits encNat)) encBool) (encPair encBits encNat) := by
  unfold rawInverseStep
  have hp := fst (encPair rawPrefixEncoding (encPair encBits encNat)) encBool
  have hD := hp.fst'
  have hs := hp.snd'
  have ha := snd (encPair rawPrefixEncoding (encPair encBits encNat)) encBool
  have hp0 := bitsAppend hs.fst' (const [false])
  have hc := rawPrefixNumbers_polytime.comp (hD.prod hp0)
  have hdiff := binary_sub.comp (hc.fst'.prod hc.snd')
  have hadd := ha.cond hdiff (const (encMid := encNat) 0)
  simpa only [Function.comp_def] using (bitsAppend hs.fst' (bitsCons ha (const []))).prod
    (binary_add.comp (hs.snd'.prod hadd))

 theorem rawCount_le_power (n : ℕ) (E : List RawEquation) : rawCount n E ≤ 2^n := by
  dsimp only [rawCount]
  split
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)

 theorem rawInverseStep_growth (D : RawCodecData) (s : List Bool × ℕ) (a : Bool) :
    (encPair encBits encNat (rawInverseStep D s a)).length ≤
      (encPair encBits encNat s).length + (D.1.1+4) := by
  have hcount : (rawPrefixNumbers D (s.1++[false])).1 ≤ 2^D.1.1 := rawCount_le_power _ _
  have hdiff : (rawPrefixNumbers D (s.1++[false])).1 -
      (rawPrefixNumbers D (s.1++[false])).2 ≤ 2^D.1.1 :=
    (Nat.sub_le _ _).trans hcount
  have hpow : 2^D.1.1 < 2^(D.1.1+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsize : (if a then (rawPrefixNumbers D (s.1++[false])).1 -
      (rawPrefixNumbers D (s.1++[false])).2 else 0).size ≤ D.1.1+1 := by
    apply Nat.size_le.mpr
    split
    · exact hdiff.trans_lt hpow
    · positivity
  have hsum := Nat.size_add_le s.2 (if a then (rawPrefixNumbers D (s.1++[false])).1 -
    (rawPrefixNumbers D (s.1++[false])).2 else 0)
  simp only [rawInverseStep,length_encPair,encBits_apply,encNat_apply,
    Nat.size_eq_bits_len,List.length_append,List.length_singleton]
  omega

 theorem rawInverseIndex_polytime : ComputableTidilyInPolyTime
    (fun p : RawCodecData × List Bool => rawInverseIndex p.1 p.2)
    (encPair rawPrefixEncoding encBits) encNat := by
  have hD := fst rawPrefixEncoding encBits
  have hx := snd rawPrefixEncoding encBits
  have hn := hD.fst'.fst'
  have hg := unary_add.comp (hn.prod (const (encMid := encUnary) 4))
  have hi := foldlWith_of_bounded_growth (encA := encBool) (encL := encBits)
    hD hx (const ([],0)) rawInverseStep_polytime hg.polyBounded
    (fun x state a ha => rawInverseStep_growth x.1 state a)
  exact hi.snd'

 theorem rawIndexBits_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × ℕ => rawIndexBits p.1 p.2)
    (encPair encUnary encNat) encBits := by
  unfold rawIndexBits
  have hl := range.comp (fst encUnary encNat)
  apply mapToBitsWithInput hl
  have ho := fst (encPair encUnary encNat) encUnary
  have hj := snd (encPair encUnary encNat) encUnary
  have hm := ho.snd'
  have hk := unary_sub.comp (ho.fst'.prod (const (encMid := encUnary) 1))
  have hi := unary_sub.comp (hk.prod hj)
  exact binary_testBit hm hi

 theorem rawInverse_polytime : ComputableTidilyInPolyTime
    (fun p : RawCodecData × List Bool => rawInverse p.1 p.2)
    (encPair rawPrefixEncoding encBits) encBits := by
  unfold rawInverse
  have hd := fst rawPrefixEncoding encBits
  have hn := hd.fst'.fst'
  have hb := (length_list encBits).comp hd.snd'.fst'
  have hk := unary_sub.comp ((unary_sub.comp (hn.prod hb)).prod (const (encMid := encUnary) 1))
  exact rawIndexBits_polytime.comp (hk.prod rawInverseIndex_polytime)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

def rawCodec {n : ℕ} (F : Family n) (P : Parameters n) : RawCodecData :=
  ((n,F.map rawAffine),(P.rows.map wordCode,bitCode P.beta))

 theorem rawPrefixEquations_correct (n : ℕ) (p : List Bit) :
    rawPrefixEquations n (bitCode p) = (prefixEquations n p).map rawEquation := by
  simp only [rawPrefixEquations,prefixEquations,bitCode,List.length_map,List.map_map]
  apply List.map_congr_left
  intro k hk
  rw [rawUnit_word]
  apply Prod.ext
  · rfl
  · change ((p.map bitBool)[k]?).getD false = bitBool (p[k]?.getD 0)
    cases hp : p[k]? <;> simp [List.getElem?_map,hp]

 theorem rawPrefixNumbers_correct {n : ℕ} (F : Family n) (P : Parameters n) (p : List Bit) :
    rawPrefixNumbers (rawCodec F P) (bitCode p) =
      (affineCount (cosetEquations P.rows P.beta ++ prefixEquations n p),
        witnessCount F P.rows (cosetEquations P.rows P.beta ++ prefixEquations n p)) := by
  have hz : (P.rows.map wordCode).zip (bitCode P.beta) = (P.rows.zip P.beta).map rawEquation := by
    simp [bitCode,rawEquation,List.zip_map,List.map_map,Function.comp_def,bitBool]
  dsimp only [rawPrefixNumbers,rawCodec]
  rw [hz,rawPrefixEquations_correct,← List.map_append,rawCount_equations,rawWitness_equations]
  rfl

 theorem rawPrefixNumbers_bound {n : ℕ} (F : Family n) (P : Parameters n) (p : List Bit) :
    ((rawPrefixNumbers (rawCodec F P) (bitCode p)).1 : ℤ) -
      ((rawPrefixNumbers (rawCodec F P) (bitCode p)).2 : ℤ) = prefixBound F P.rows P.beta p := by
  rw [rawPrefixNumbers_correct]
  rfl

 theorem nat_sub_cast_max (A W : ℕ) : ((A-W : ℕ) : ℤ) = max 0 ((A : ℤ)-(W : ℤ)) := by
  by_cases h : W ≤ A
  · rw [Int.natCast_sub h,max_eq_right (by omega)]
  · rw [Nat.sub_eq_zero_of_le (by omega),max_eq_left (by omega)]
    rfl

 theorem rawEncode_compare {n : ℕ} (F : Family n) (P : Parameters n) (p : List Bit) (m : ℕ) :
    m+(rawPrefixNumbers (rawCodec F P) (bitCode p)).2 <
      (rawPrefixNumbers (rawCodec F P) (bitCode p)).1 ↔ (m : ℤ) < prefixBound F P.rows P.beta p := by
  rw [← rawPrefixNumbers_bound F P p]
  omega

 theorem rawEncode_subtract {n : ℕ} (F : Family n) (P : Parameters n) (p : List Bit) (m : ℕ)
    (hm : ¬ (m : ℤ) < prefixBound F P.rows P.beta p) :
    ((m - ((rawPrefixNumbers (rawCodec F P) (bitCode p)).1 -
      (rawPrefixNumbers (rawCodec F P) (bitCode p)).2) : ℕ) : ℤ) =
      (m : ℤ)-max 0 (prefixBound F P.rows P.beta p) := by
  have hmax := nat_sub_cast_max (rawPrefixNumbers (rawCodec F P) (bitCode p)).1
    (rawPrefixNumbers (rawCodec F P) (bitCode p)).2
  rw [rawPrefixNumbers_bound F P p] at hmax
  have hle : (rawPrefixNumbers (rawCodec F P) (bitCode p)).1 -
      (rawPrefixNumbers (rawCodec F P) (bitCode p)).2 ≤ m := by omega
  rw [Int.natCast_sub hle,hmax]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawEncodeSteps_correct {n : ℕ} (F : Family n) (P : Parameters n)
    (k : ℕ) (p : List Bit) (m : ℕ) :
    let R := (rawEncodeStep (rawCodec F P))^[k] (bitCode p,m)
    R.1 = bitCode (encodeSteps F P k p (m : ℤ)).1 ∧
      (R.2 : ℤ) = (encodeSteps F P k p (m : ℤ)).2 := by
  induction k generalizing p m with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    dsimp only
    rw [Function.iterate_succ_apply]
    have hp0 : bitCode p ++ [false] = bitCode (p++[0]) := by simp [bitCode]
    have hp1 : bitCode p ++ [true] = bitCode (p++[1]) := by simp [bitCode]
    dsimp only [rawEncodeStep]
    rw [hp0]
    by_cases hm : (m : ℤ) < prefixBound F P.rows P.beta (p++[0])
    · have hn := (rawEncode_compare F P (p++[0]) m).mpr hm
      simp only [if_pos hn,encodeSteps,if_pos hm]
      exact ih (p++[0]) m
    · have hn := (rawEncode_compare F P (p++[0]) m).not.mpr hm
      simp only [if_neg hn,encodeSteps,if_neg hm]
      rw [hp1]
      have hh := ih (p++[1]) (m - ((rawPrefixNumbers (rawCodec F P) (bitCode (p++[0]))).1 -
        (rawPrefixNumbers (rawCodec F P) (bitCode (p++[0]))).2))
      rw [rawEncode_subtract F P (p++[0]) m hm] at hh
      exact hh

 theorem rawMessageIndex_fold (p : List Bit) (m : ℕ) :
    (((bitCode p).foldl (fun m a => 2*m+a.toNat) m : ℕ) : ℤ) =
      p.foldl (fun m a => 2*m+if a=0 then 0 else 1) (m : ℤ) := by
  induction p generalizing m with
  | nil => rfl
  | cons a p ih =>
    simp only [bitCode,List.map_cons,List.foldl_cons] at *
    rw [ih]
    congr 1
    rcases bit_zero_or_one a with rfl | rfl <;> simp

 theorem rawMessageIndex (p : List Bit) :
    (Cslib.BitString.binaryValue (bitCode p) : ℤ) = messageIndex p :=
  rawMessageIndex_fold p 0

 theorem encodeSteps_length {n : ℕ} (F : Family n) (P : Parameters n)
    (k : ℕ) (p : List Bit) (m : ℤ) : (encodeSteps F P k p m).1.length = p.length+k := by
  induction k generalizing p m with
  | zero => simp [encodeSteps]
  | succ k ih =>
    dsimp only [encodeSteps]
    split <;> rw [ih] <;> simp <;> omega

 theorem rawEncode_correct {n : ℕ} (F : Family n) (P : Parameters n) (u : Word (messageLength P)) :
    rawEncode (rawCodec F P) (wordCode u) = wordCode (encodeWord F P u) := by
  have hh := (rawEncodeSteps_correct F P n [] (Cslib.BitString.binaryValue (wordCode u))).1
  have hcast : (Cslib.BitString.binaryValue (wordCode u) : ℤ) = messageIndex (wordList u) :=
    rawMessageIndex (wordList u)
  rw [hcast] at hh
  change rawEncode (rawCodec F P) (wordCode u) = bitCode (wordList (listWord n (encodeList F P u)))
  have hlen : (encodeList F P u).length = n := by
    simpa only [encodeList,List.length_nil,Nat.zero_add] using
      (encodeSteps_length F P n [] (messageIndex (wordList u)))
  rw [wordList_listWord _ hlen]
  exact hh

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawInverse_delta {n : ℕ} (F : Family n) (P : Parameters n) (p : List Bit) (a : Bit) :
    ((if bitBool a then (rawPrefixNumbers (rawCodec F P) (bitCode (p++[0]))).1 -
      (rawPrefixNumbers (rawCodec F P) (bitCode (p++[0]))).2 else 0 : ℕ) : ℤ) =
      if a=0 then 0 else max 0 (prefixBound F P.rows P.beta (p++[0])) := by
  rcases bit_zero_or_one a with rfl | rfl
  · simp
  · simp only [bitBool_one,if_true,one_ne_zero,if_false]
    rw [nat_sub_cast_max,rawPrefixNumbers_bound]

 theorem rawInverseFold_correct {n : ℕ} (F : Family n) (P : Parameters n)
    (x p : List Bit) (m : ℕ) :
    let R := (bitCode x).foldl (rawInverseStep (rawCodec F P)) (bitCode p,m)
    let S := x.foldl (fun s a =>
      let L := prefixBound F P.rows P.beta (s.1++[0])
      (s.1++[a],s.2+if a=0 then 0 else max 0 L)) (p,(m : ℤ))
    R.1 = bitCode S.1 ∧ (R.2 : ℤ) = S.2 := by
  induction x generalizing p m with
  | nil => exact ⟨rfl,rfl⟩
  | cons a x ih =>
    dsimp only
    rw [show bitCode (a::x) = bitBool a :: bitCode x from rfl]
    simp only [List.foldl_cons,rawInverseStep]
    have hp0 : bitCode p ++ [false] = bitCode (p++[0]) := by simp [bitCode]
    have hpa : bitCode p ++ [bitBool a] = bitCode (p++[a]) := by simp [bitCode,bitBool]
    change _ ∧ _
    rw [hp0,hpa]
    have hh := ih (p++[a]) (m+if bitBool a then
      (rawPrefixNumbers (rawCodec F P) (bitCode (p++[0]))).1 -
      (rawPrefixNumbers (rawCodec F P) (bitCode (p++[0]))).2 else 0)
    rw [Nat.cast_add,rawInverse_delta F P p a] at hh
    exact hh

 theorem rawInverseIndex_correct {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bit) :
    (rawInverseIndex (rawCodec F P) (bitCode x) : ℤ) = inverseIndex F P x :=
  (rawInverseFold_correct F P x [] 0).2

 theorem rawIndexBits_correct (K m : ℕ) : rawIndexBits K m = bitCode (indexBits K m) := by
  simp only [rawIndexBits,indexBits,bitCode,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro j hj
  split <;> simp_all

 theorem rawInverse_correct {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bit) :
    rawInverse (rawCodec F P) (bitCode x) = bitCode (inverseList F P x) := by
  have hh := congrArg Int.toNat (rawInverseIndex_correct F P x)
  simp only [Int.toNat_natCast] at hh
  unfold rawInverse
  rw [hh,rawIndexBits_correct]
  simp only [rawCodec,List.length_map,inverseList,messageLength]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawReadRows (n b : ℕ) (w : List Bool) : List (List Bool) :=
  (List.range b).map (fun i => (w.drop (i*n)).take n)

def rawReadAffine (n : ℕ) (w : List Bool) : RawAffine :=
  (rawReadRows n n w, (w.drop (n*n)).take n)

def rawReadFamily (n M : ℕ) (w : List Bool) : List RawAffine :=
  (List.range M).map (fun i => rawReadAffine n (w.drop (i*(n*n+n))))

/-- Return dimension, family, parity rows, and the remaining unparsed suffix. -/
def rawParseFamilyRows (w : List Bool) :
    (ℕ × List RawAffine) × (List (List Bool) × List Bool) :=
  let n := readUnary w
  let w₁ := dropHeader w
  let M := readUnary w₁
  let w₂ := dropHeader w₁
  let F := rawReadFamily n M w₂
  let w₃ := w₂.drop (M*(n*n+n))
  let b := readUnary w₃
  let w₄ := dropHeader w₃
  ((n,F),(rawReadRows n b w₄, w₄.drop (b*n)))

/-- Parse the final length-framed prefix after the family and parity rows. -/
def rawParseExpectation (w : List Bool) :
    (ℕ × List RawAffine) × (List (List Bool) × List Bool) :=
  let p := rawParseFamilyRows w
  (p.1, (p.2.1, (dropHeader p.2.2).take (readUnary p.2.2)))

@[fun_prop]
theorem rawReadRows_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => rawReadRows p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList encBits) := by
  unfold rawReadRows
  have hl := range.comp ((fst (encPair encUnary encUnary) encBits).snd')
  apply mapWithInput (encB := encBits) hl
  have ho := fst (encPair (encPair encUnary encUnary) encBits) encUnary
  have hi := snd (encPair (encPair encUnary encUnary) encBits) encUnary
  have hn := ho.fst'.fst'
  exact bitsTakeWithInput (bitsDropWithInput ho.snd' (unary_mul.comp (hi.prod hn))) hn

@[fun_prop]
theorem rawReadAffine_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawReadAffine p.1 p.2)
    (encPair encUnary encBits) rawAffineEncoding := by
  unfold rawReadAffine
  have hn := fst encUnary encBits
  have hw := snd encUnary encBits
  exact (rawReadRows_polytime.comp ((hn.prod hn).prod hw)).prod
    (bitsTakeWithInput (bitsDropWithInput hw (unary_mul.comp (hn.prod hn))) hn)

@[fun_prop]
theorem rawReadFamily_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => rawReadFamily p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) encBits) (encList rawAffineEncoding) := by
  unfold rawReadFamily
  have hl := range.comp ((fst (encPair encUnary encUnary) encBits).snd')
  apply mapWithInput (encB := rawAffineEncoding) hl
  have ho := fst (encPair (encPair encUnary encUnary) encBits) encUnary
  have hi := snd (encPair (encPair encUnary encUnary) encBits) encUnary
  have hn := ho.fst'.fst'
  have hwidth := unary_add.comp ((unary_mul.comp (hn.prod hn)).prod hn)
  exact rawReadAffine_polytime.comp (hn.prod
    (bitsDropWithInput ho.snd' (unary_mul.comp (hi.prod hwidth))))

@[fun_prop]
theorem rawParseFamilyRows_polytime : ComputableTidilyInPolyTime rawParseFamilyRows
    encBits rawPrefixEncoding := by
  unfold rawParseFamilyRows
  have hn := readUnary_polytime
  have hw₁ := dropHeader_polytime
  have hM := readUnary_polytime.comp hw₁
  have hw₂ := dropHeader_polytime.comp hw₁
  have hF := rawReadFamily_polytime.comp ((hn.prod hM).prod hw₂)
  have hwidth := unary_add.comp ((unary_mul.comp (hn.prod hn)).prod hn)
  have hw₃ := bitsDropWithInput hw₂ (unary_mul.comp (hM.prod hwidth))
  have hb := readUnary_polytime.comp hw₃
  have hw₄ := dropHeader_polytime.comp hw₃
  have hG := rawReadRows_polytime.comp ((hn.prod hb).prod hw₄)
  exact (hn.prod hF).prod (hG.prod (bitsDropWithInput hw₄ (unary_mul.comp (hb.prod hn))))

@[fun_prop]
theorem rawParseExpectation_polytime : ComputableTidilyInPolyTime rawParseExpectation
    encBits rawPrefixEncoding := by
  unfold rawParseExpectation
  have hr := rawParseFamilyRows_polytime
  have ht := hr.snd'.snd'
  exact hr.fst'.prod (hr.snd'.fst'.prod (bitsTakeWithInput
    (dropHeader_polytime.comp ht) (readUnary_polytime.comp ht)))

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem flatMap_length_fixed {α : Type} (xs : List α) (f : α → List Bool) (w : ℕ)
    (hf : ∀ a ∈ xs, (f a).length = w) : (xs.flatMap f).length = xs.length*w := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp),
      ih (fun a ha => hf a (by simp [ha]))]
    simp [Nat.add_mul, Nat.add_comm]

 theorem decode_fixed_blocks {α β : Type} (w : ℕ) (enc : α → List Bool)
    (dec : List Bool → β) (out : α → β)
    (hlen : ∀ a, (enc a).length = w)
    (hread : ∀ a tail, dec (enc a ++ tail) = out a)
    (xs : List α) (tail : List Bool) :
    (List.range xs.length).map (fun i => dec ((xs.flatMap enc ++ tail).drop (i*w))) = xs.map out := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, List.flatMap_cons, List.append_assoc, Nat.zero_mul, List.drop_zero]
    rw [hread]
    congr 1
    rw [← ih]
    apply List.map_congr_left
    intro i hi
    dsimp only [Function.comp_def]
    have heq : (i+1)*w = w+i*w := by ring
    have hdrop : (enc a ++ (xs.flatMap enc ++ tail)).drop w = xs.flatMap enc ++ tail := by
      rw [← hlen a, List.drop_left]
    rw [heq, ← List.drop_drop, hdrop]

 theorem rawReadRows_codes {n : ℕ} (G : Rows n) (tail : List Bool) :
    rawReadRows n G.length (G.flatMap wordCode ++ tail) = G.map wordCode := by
  apply decode_fixed_blocks n wordCode (List.take n) wordCode wordCode_length
    (fun a tail => ?_) G tail
  exact List.take_left' (wordCode_length a)

 def affineBytes {n : ℕ} (f : Affine n) : List Bool :=
  (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten ++ wordCode f.offset

 theorem matrixBytes_length {n : ℕ} (f : Affine n) :
    (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten.length = n*n := by
  rw [List.flatten_eq_flatMap]
  have hh := flatMap_length_fixed (List.ofFn (fun i : Fin n => wordCode (f.matrix i))) id n
    (by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact wordCode_length _)
  simpa only [List.length_ofFn] using hh

 theorem affineBytes_length {n : ℕ} (f : Affine n) : (affineBytes f).length = n*n+n := by
  simp only [affineBytes, List.length_append, matrixBytes_length, wordCode_length]

 theorem rawReadAffine_code {n : ℕ} (f : Affine n) (tail : List Bool) :
    rawReadAffine n (affineBytes f ++ tail) = rawAffine f := by
  apply Prod.ext
  · change rawReadRows n n _ = _
    let G : Rows n := List.ofFn (fun i : Fin n => f.matrix i)
    have hG : G.length = n := by simp [G]
    have hm : G.flatMap wordCode = (List.ofFn (fun i : Fin n => wordCode (f.matrix i))).flatten := by
      simp [G, List.flatMap, List.map_ofFn, Function.comp_def]
    have hh := rawReadRows_codes G (wordCode f.offset ++ tail)
    simpa only [hG, hm, G, affineBytes, rawAffine, List.append_assoc, List.map_ofFn, Function.comp_def] using hh
  · change ((affineBytes f ++ tail).drop (n*n)).take n = wordCode f.offset
    unfold affineBytes
    rw [List.append_assoc, ← matrixBytes_length f, List.drop_left]
    exact List.take_left' (wordCode_length f.offset)

 theorem rawReadFamily_codes {n : ℕ} (F : Family n) (tail : List Bool) :
    rawReadFamily n F.length (F.flatMap affineBytes ++ tail) = F.map rawAffine := by
  exact decode_fixed_blocks (n*n+n) affineBytes (rawReadAffine n) rawAffine
    affineBytes_length rawReadAffine_code F tail

 theorem rawParseFamilyRows_correct {n : ℕ} (F : Family n) (G : Rows n) (tail : List Bool) :
    rawParseFamilyRows (familyRowsInput F G ++ tail) =
      ((n,F.map rawAffine),(G.map wordCode,tail)) := by
  have hF : (F.flatMap affineBytes).length = F.length*(n*n+n) :=
    flatMap_length_fixed F affineBytes _ (fun a ha => affineBytes_length a)
  have hG : (G.flatMap wordCode).length = G.length*n :=
    flatMap_length_fixed G wordCode _ (fun a ha => wordCode_length a)
  change rawParseFamilyRows (((unary n ++ (unary F.length ++ F.flatMap affineBytes)) ++
      (unary G.length ++ G.flatMap wordCode)) ++ tail) = _
  simp only [rawParseFamilyRows, List.append_assoc, readUnary_prefix, dropHeader_prefix]
  rw [rawReadFamily_codes]
  rw [← hF, List.drop_left]
  simp only [readUnary_prefix, dropHeader_prefix]
  rw [rawReadRows_codes, ← hG, List.drop_left]

 theorem rawParseExpectation_correct {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawParseExpectation (expectationInput F G p) =
      ((n,F.map rawAffine),(G.map wordCode,bitCode p)) := by
  unfold rawParseExpectation expectationInput
  rw [rawParseFamilyRows_correct]
  simp only [frame, dropHeader_prefix, readUnary_prefix, List.take_length]

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawParseCodec (w : List Bool) : RawCodecData × List Bool :=
  let D := rawParseFamilyRows w
  let β := (dropHeader D.2.2).take (readUnary D.2.2)
  let rest := (dropHeader D.2.2).drop (readUnary D.2.2)
  let u := (dropHeader rest).take (readUnary rest)
  ((D.1,(D.2.1,β)),u)

def rawEncodeInput (w : List Bool) : List Bool :=
  let D := rawParseCodec w
  rawEncode D.1 D.2

def rawInverseInput (w : List Bool) : List Bool :=
  let D := rawParseCodec w
  rawInverse D.1 D.2

 theorem rawParseCodec_polytime : ComputableTidilyInPolyTime rawParseCodec
    encBits (encPair rawPrefixEncoding encBits) := by
  unfold rawParseCodec
  have hD := rawParseFamilyRows_polytime
  have ht := hD.snd'.snd'
  have hβ := bitsTakeWithInput (dropHeader_polytime.comp ht) (readUnary_polytime.comp ht)
  have hr := bitsDropWithInput (dropHeader_polytime.comp ht) (readUnary_polytime.comp ht)
  have hu := bitsTakeWithInput (dropHeader_polytime.comp hr) (readUnary_polytime.comp hr)
  exact (hD.fst'.prod (hD.snd'.fst'.prod hβ)).prod hu

 theorem rawEncodeInput_polytime : ComputableTidilyInPolyTime rawEncodeInput encBits encBits :=
  rawEncode_polytime.comp rawParseCodec_polytime

 theorem rawInverseInput_polytime : ComputableTidilyInPolyTime rawInverseInput encBits encBits :=
  rawInverse_polytime.comp rawParseCodec_polytime

end EditGV897.Runtime
namespace EditGV897.Main
open EditGV897.Runtime
 theorem rawParseCodec_correct {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bool) :
    rawParseCodec (familyRowsInput F P.rows ++ frame (bitCode P.beta) ++ frame x) =
      (rawCodec F P,x) := by
  unfold rawParseCodec
  rw [List.append_assoc,rawParseFamilyRows_correct]
  simp only [frame,List.append_assoc,readUnary_prefix,dropHeader_prefix,List.take_left,
    List.drop_left,List.take_length]
  rfl

 theorem rawEncodeInput_correct {n : ℕ} (F : Family n) (P : Parameters n)
    (u : Word (messageLength P)) :
    rawEncodeInput (encoderInput F P u) = wordCode (encodeWord F P u) := by
  unfold rawEncodeInput encoderInput
  rw [rawParseCodec_correct]
  exact rawEncode_correct F P u

 theorem rawInverseInput_correct {n : ℕ} (F : Family n) (P : Parameters n) (x : List Bit) :
    rawInverseInput (inverseInput F P x) = bitCode (inverseList F P x) := by
  unfold rawInverseInput inverseInput
  rw [rawParseCodec_correct]
  exact rawInverse_correct F P x


end EditGV897.Main


set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev RawOp := (Bool × Bool) × (ℕ × Bool)
abbrev rawOpEncoding := encPair (encPair encBool encBool) (encPair encUnary encBool)

def rawLegalOps (L : ℕ) : List RawOp :=
  (List.range (L+1)).flatMap (fun k => [((false,false),(k,false)),((false,false),(k,true))]) ++
  (List.range L).map (fun k => ((false,true),(k,false))) ++
  (List.range L).map (fun k => ((true,false),(k,false)))

def rawSymbolicStep (n : ℕ) (s : List RawEquation) (op : RawOp) : List RawEquation :=
  let k := op.2.1
  if op.1.1 then s.take k ++ ((s.drop k).take 1).map (fun e => (e.1,!e.2)) ++ s.drop (k+1)
  else if op.1.2 then s.take k ++ s.drop (k+1)
  else s.take k ++ [(List.replicate n false,op.2.2)] ++ s.drop k

def rawSymbolicPaths (n : ℕ) : ℕ → List RawEquation → List (List RawEquation)
  | 0,s => [s]
  | r+1,s => s :: (rawLegalOps s.length).flatMap (fun op => rawSymbolicPaths n r (rawSymbolicStep n s op))

def rawStart (n : ℕ) : List RawEquation := (List.range n).map (fun i => (rawUnit n i,false))

def rawCanonicalFamily (t n : ℕ) : List RawAffine :=
  ((rawSymbolicPaths n (2*t) (rawStart n)).filter (fun s => s.length == n)).map
    (fun s => (s.map Prod.fst,s.map Prod.snd))

 theorem rawLegalOps_polytime : ComputableTidilyInPolyTime rawLegalOps encUnary (encList rawOpEncoding) := by
  unfold rawLegalOps
  fun_prop

set_option maxHeartbeats 1600000 in
theorem rawSymbolicStep_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawEquation) × RawOp => rawSymbolicStep p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList rawEquationEncoding)) rawOpEncoding) (encList rawEquationEncoding) := by
  unfold rawSymbolicStep
  fun_prop

 theorem rawStart_polytime : ComputableTidilyInPolyTime rawStart encUnary (encList rawEquationEncoding) := by
  unfold rawStart
  apply mapWithInput (encB := rawEquationEncoding) range
  exact (rawUnit_polytime.comp ((fst encUnary encUnary).prod (snd encUnary encUnary))).prod (const false)

theorem rawSymbolicPaths_polytime (r : ℕ) : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawEquation => rawSymbolicPaths p.1 r p.2)
    (encPair encUnary (encList rawEquationEncoding)) (encList (encList rawEquationEncoding)) := by
  induction r with
  | zero => exact cons' (snd _ _) (const [])
  | succ r ih =>
    let en := encPair encUnary (encList rawEquationEncoding)
    have hn := fst encUnary (encList rawEquationEncoding)
    have hs := snd encUnary (encList rawEquationEncoding)
    have hops := rawLegalOps_polytime.comp ((length_list rawEquationEncoding).comp hs)
    have hbody : ComputableTidilyInPolyTime
        (fun p : (ℕ × List RawEquation) × RawOp => rawSymbolicPaths p.1.1 r
          (rawSymbolicStep p.1.1 p.1.2 p.2))
        (encPair en rawOpEncoding) (encList (encList rawEquationEncoding)) := by
      simpa only [Function.comp_def] using ih.comp
        (((fst en rawOpEncoding).fst').prod rawSymbolicStep_polytime)
    have hall := flatMapWithInput (encB := encList rawEquationEncoding)
      (f := fun (p : ℕ × List RawEquation) (op : RawOp) =>
        rawSymbolicPaths p.1 r (rawSymbolicStep p.1 p.2 op)) hops hbody
    exact cons' hs hall

 theorem rawCanonicalFamily_polytime (t : ℕ) : ComputableTidilyInPolyTime
    (rawCanonicalFamily t) encUnary (encList rawAffineEncoding) := by
  unfold rawCanonicalFamily
  have hpaths := (rawSymbolicPaths_polytime (2*t)).comp ((id' (encIn := encUnary)).prod rawStart_polytime)
  have hfiltered : ComputableTidilyInPolyTime
      (fun n => (rawSymbolicPaths n (2*t) (rawStart n)).filter (fun s => s.length == n))
      encUnary (encList (encList rawEquationEncoding)) := by
    apply filterWithInput hpaths
    exact unary_beq ((length_list rawEquationEncoding).comp (snd _ _)) (fst _ _)
  have hmat := map (fst encBits encBool)
  have hoff := listToBits.comp (map (snd encBits encBool))
  exact (map (hmat.prod hoff)).comp hfiltered

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

def rawOp : PositionedOp → RawOp
  | .insert k a => ((false,false),(k,bitBool a))
  | .delete k => ((false,true),(k,false))
  | .toggle k => ((true,false),(k,false))

 theorem rawLegalOps_correct (L : ℕ) : rawLegalOps L = (legalOps L).map rawOp := by
  simp [rawLegalOps,legalOps,rawOp,List.map_flatMap,List.flatMap_map,Function.comp_def]

 theorem rawSymbolicStep_correct {n : ℕ} (s : List (Equation n)) (op : PositionedOp) :
    rawSymbolicStep n (s.map rawEquation) (rawOp op) = (symbolicStep s op).map rawEquation := by
  cases op with
  | insert k a =>
    simp [rawSymbolicStep,rawOp,symbolicStep,rawEquation,wordCode_zero]
  | delete k => simp [rawSymbolicStep,rawOp,symbolicStep]
  | toggle k =>
    simp only [rawSymbolicStep,rawOp,if_true,symbolicStep,← List.map_take,← List.map_drop,List.map_append,List.map_map,Function.comp_def]
    congr 2
    apply List.map_congr_left
    intro e he
    simp [rawEquation]

 theorem rawSymbolicPaths_correct {n : ℕ} (r : ℕ) (s : List (Equation n)) :
    rawSymbolicPaths n r (s.map rawEquation) =
      (symbolicPaths r s).map (fun p => p.map rawEquation) := by
  induction r generalizing s with
  | zero => simp [rawSymbolicPaths,symbolicPaths]
  | succ r ih =>
    simp only [rawSymbolicPaths,symbolicPaths,List.length_map,rawLegalOps_correct,
      List.map_cons,List.map_flatMap,List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro op hop
    rw [rawSymbolicStep_correct,ih]

 theorem rawStart_correct (n : ℕ) : rawStart n =
    (List.ofFn (fun i : Fin n => (unitWord n i.val,(0 : Bit)))).map rawEquation := by
  apply List.ext_getElem
  · simp [rawStart]
  · intro i hi hj
    simp [rawStart,rawEquation,rawUnit_word]

 theorem rawAffine_script {n : ℕ} (s : List (Equation n)) (hlen : s.length = n) :
    rawAffine (⟨(fun i => (s[i.val]?.getD ((0,0) : Equation n)).1),
      (fun i => (s[i.val]?.getD ((0,0) : Equation n)).2)⟩ : Affine n) =
      ((s.map rawEquation).map Prod.fst,(s.map rawEquation).map Prod.snd) := by
  apply Prod.ext
  · simp only [rawAffine,List.map_map,Function.comp_def]
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      have hsi : i < s.length := by simpa using hj
      simp [List.getElem?_eq_getElem hsi,rawEquation]
  · simp only [rawAffine,List.map_map,Function.comp_def]
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      have hsi : i < s.length := by simpa using hj
      simp [wordCode,bitCode,wordList,DeletionHash.MixedEdit.letters,
        List.getElem?_eq_getElem hsi,rawEquation,bitBool]

 theorem rawCanonicalFamily_correct (t n : ℕ) :
    rawCanonicalFamily t n = (canonicalFamily t n).map rawAffine := by
  unfold rawCanonicalFamily canonicalFamily
  rw [rawStart_correct,rawSymbolicPaths_correct]
  simp only [List.filter_map,List.map_map,Function.comp_def,List.length_map]
  apply List.map_congr_left
  intro s hs
  have hlen : s.length = n := by
    have h := (List.mem_filter.mp hs).2
    simpa only [beq_iff_eq] using h
  simpa only [List.map_map,Function.comp_def] using (rawAffine_script s hlen).symm

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawBitStep (y : List Bool) (op : RawOp) : List Bool :=
  let k := op.2.1
  if op.1.1 then y.take k ++ ((y.drop k).take 1).map Bool.not ++ y.drop (k+1)
  else if op.1.2 then y.take k ++ y.drop (k+1)
  else y.take k ++ [op.2.2] ++ y.drop k

def rawCandidates : ℕ → List Bool → List (List Bool)
  | 0,y => [y]
  | t+1,y => y :: (rawLegalOps y.length).flatMap (fun op => rawCandidates t (rawBitStep y op))

def rawSyndrome (G : List (List Bool)) (x : List Bool) : List Bool := G.map (fun h => rawDot h x)

def rawDecodable (n : ℕ) (P : List (List Bool) × List Bool) (x : List Bool) : Bool :=
  x.length == n && rawSyndrome P.1 (rawPad n x) == P.2

def rawDecode (t n : ℕ) (P : List (List Bool) × List Bool) (y : List Bool) : List Bool :=
  if n+t < y.length then [] else
    ((rawCandidates t y).find? (rawDecodable n P)).elim []
      (fun x => rawInverse ((n,rawCanonicalFamily t n),P) x)

 theorem rawBitStep_polytime : ComputableTidilyInPolyTime
    (fun p : List Bool × RawOp => rawBitStep p.1 p.2)
    (encPair encBits rawOpEncoding) encBits := by
  unfold rawBitStep
  fun_prop

 theorem rawCandidates_polytime (t : ℕ) : ComputableTidilyInPolyTime (rawCandidates t)
    encBits (encList encBits) := by
  induction t with
  | zero => exact cons' id' (const [])
  | succ t ih =>
    have hops := rawLegalOps_polytime.comp length_bits
    have hf := ih.comp rawBitStep_polytime
    have hall := flatMapWithInput (encB := encBits)
      (f := fun (y : List Bool) (op : RawOp) => rawCandidates t (rawBitStep y op)) hops hf
    exact cons' id' hall

 theorem rawSyndrome_polytime : ComputableTidilyInPolyTime
    (fun p : List (List Bool) × List Bool => rawSyndrome p.1 p.2)
    (encPair (encList encBits) encBits) encBits := by
  unfold rawSyndrome
  apply mapToBitsWithInput (fst (encList encBits) encBits)
  exact rawDot_polytime.comp ((snd _ _).prod ((fst _ _).snd'))

 theorem rawDecodable_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × (List (List Bool) × List Bool)) × List Bool => rawDecodable p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary rawParametersEncoding) encBits) encBool := by
  unfold rawDecodable
  have hP := fst (encPair encUnary rawParametersEncoding) encBits
  have hx := snd (encPair encUnary rawParametersEncoding) encBits
  have hlen := unary_beq (length_bits_comp hx) hP.fst'
  have hpad := rawPad_polytime.comp (hP.fst'.prod hx)
  have hsyn := rawSyndrome_polytime.comp (hP.snd'.fst'.prod hpad)
  have htest := beq hsyn hP.snd'.snd'
  have hand : ComputableTidilyInPolyTime (fun p : Bool × Bool => p.1 && p.2)
      (encPair encBool encBool) encBool := of_finite _
  simpa only [Function.comp_def] using hand.comp (hlen.prod htest)

set_option maxHeartbeats 1600000 in
theorem rawDecode_polytime (t : ℕ) : ComputableTidilyInPolyTime
    (fun p : (ℕ × (List (List Bool) × List Bool)) × List Bool => rawDecode t p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary rawParametersEncoding) encBits) encBits := by
  unfold rawDecode
  let en := encPair (encPair encUnary rawParametersEncoding) encBits
  have hP := fst (encPair encUnary rawParametersEncoding) encBits
  have hy := snd (encPair encUnary rawParametersEncoding) encBits
  have hlist := (rawCandidates_polytime t).comp hy
  have hfound : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List (List Bool) × List Bool)) × List Bool =>
        (rawCandidates t p.2).find? (rawDecodable p.1.1 p.1.2)) en (encOption encBits) := by
    apply findWithInput hlist
    simpa only [Function.comp_def] using rawDecodable_polytime.comp
      (((fst en encBits).fst').prod (snd en encBits))
  have hdecoded : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List (List Bool) × List Bool)) × List Bool =>
        ((rawCandidates t p.2).find? (rawDecodable p.1.1 p.1.2)).elim []
          (fun x => rawInverse ((p.1.1,rawCanonicalFamily t p.1.1),p.1.2) x)) en encBits := by
    apply optionElimWithInput hfound (const [])
    have ho := fst en encBits
    have hx := snd en encBits
    have hn := ho.fst'.fst'
    have hp := ho.fst'.snd'
    have hF := (rawCanonicalFamily_polytime t).comp hn
    simpa only [Function.comp_def] using rawInverse_polytime.comp (((hn.prod hF).prod hp).prod hx)
  have hsum := unary_add.comp (hP.fst'.prod (const (encMid := encUnary) t))
  have htest := unary_lt.comp (hsum.prod (length_bits_comp hy))
  simpa only [Function.comp_def,decide_eq_true_eq] using htest.cond (const []) hdecoded

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawBitStep_correct (y : List Bit) (op : PositionedOp) :
    rawBitStep (bitCode y) (rawOp op) = bitCode (bitStep y op) := by
  cases op with
  | insert k a => simp [rawBitStep,rawOp,bitStep,bitCode,bitBool]
  | delete k => simp [rawBitStep,rawOp,bitStep,bitCode]
  | toggle k =>
    simp only [rawBitStep,rawOp,if_true,bitStep,bitCode,← List.map_take,← List.map_drop,
      List.map_append,List.map_map,Function.comp_def]
    congr 2
    apply List.map_congr_left
    intro a ha
    rcases bit_zero_or_one a with rfl | rfl <;> decide

 theorem rawCandidates_correct (t : ℕ) (y : List Bit) :
    rawCandidates t (bitCode y) = (candidates t y).map bitCode := by
  induction t generalizing y with
  | zero => simp [rawCandidates,candidates]
  | succ t ih =>
    simp only [rawCandidates,candidates,bitCode,List.length_map,rawLegalOps_correct,
      List.map_cons,List.map_flatMap,List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro op hop
    change rawCandidates t (rawBitStep (bitCode y) (rawOp op)) = _
    rw [rawBitStep_correct,ih]

 theorem rawSyndrome_correct {n : ℕ} (G : Rows n) (x : Word n) :
    rawSyndrome (G.map wordCode) (wordCode x) = bitCode (syndrome G x) := by
  simp [rawSyndrome,syndrome,bitCode,List.map_map,Function.comp_def,rawDot_words,bitBool]

 theorem bitCode_eq_iff (a b : List Bit) : bitCode a = bitCode b ↔ a=b :=
  List.map_inj_right bitBool_injective

 theorem rawDecodable_correct {n : ℕ} (P : Parameters n) (x : List Bit) :
    rawDecodable n (P.rows.map wordCode,bitCode P.beta) (bitCode x) =
      (x.length == n && decide (syndrome P.rows (listWord n x) = P.beta)) := by
  unfold rawDecodable
  rw [rawPad_prefix,rawSyndrome_correct]
  have hl : (bitCode x).length = x.length := by simp [bitCode]
  rw [hl]
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq,bitCode_eq_iff]

 theorem rawDecode_correct {n : ℕ} (t : ℕ) (P : Parameters n) (y : List Bit) :
    rawDecode t n (P.rows.map wordCode,bitCode P.beta) (bitCode y) =
      bitCode ((decodeList t P y).getD []) := by
  unfold rawDecode decodeList
  have hl : (bitCode y).length = y.length := by simp [bitCode]
  rw [hl]
  split
  · simp [bitCode]
  · rw [rawCandidates_correct,List.find?_map]
    have hp : (rawDecodable n (P.rows.map wordCode,bitCode P.beta) ∘ bitCode) =
        (fun x : List Bit => x.length == n && decide (syndrome P.rows (listWord n x) = P.beta)) := by
      funext x
      exact rawDecodable_correct P x
    rw [hp,rawCanonicalFamily_correct]
    cases hf : (candidates t y).find? (fun x => x.length == n && decide
      (syndrome P.rows (listWord n x) = P.beta)) with
    | none => simp [bitCode]
    | some x =>
      simp only [Option.map_some,Option.elim_some,Option.getD_some]
      exact rawInverse_correct (canonicalFamily t n) P x

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawFamilyCode (F : List RawAffine) : List Bool :=
  rawUnary F.length ++ F.flatMap (fun f => f.1.flatten ++ f.2)

def rawAugment (t : ℕ) (w : List Bool) : List Bool :=
  let n := readUnary w
  rawUnary n ++ rawFamilyCode (rawCanonicalFamily t n) ++ dropHeader w

def rawMainEncode (t : ℕ) (w : List Bool) : List Bool := rawEncodeInput (rawAugment t w)

def rawMainDecode (t : ℕ) (w : List Bool) : List Bool :=
  let D := rawParseCodec (rawAugment t w)
  rawDecode t D.1.1.1 D.1.2 D.2

 theorem rawFamilyCode_polytime : ComputableTidilyInPolyTime rawFamilyCode
    (encList rawAffineEncoding) encBits := by
  have hheader := rawUnary_polytime.comp (length_list rawAffineEncoding)
  have hbody : ComputableTidilyInPolyTime (fun f : RawAffine => f.1.flatten ++ f.2)
      rawAffineEncoding encBits := by
    exact bitsAppend (bitsFlatten (fst (encList encBits) encBits)) (snd (encList encBits) encBits)
  have hbits := (map hbody).comp (id' (encIn := encList rawAffineEncoding))
  exact bitsAppend hheader (bitsFlatten hbits)

 theorem rawAugment_polytime (t : ℕ) : ComputableTidilyInPolyTime (rawAugment t) encBits encBits := by
  have hn := readUnary_polytime
  have hF := (rawCanonicalFamily_polytime t).comp hn
  exact bitsAppend (bitsAppend (rawUnary_polytime.comp hn) (rawFamilyCode_polytime.comp hF)) dropHeader_polytime

 theorem rawMainEncode_polytime (t : ℕ) : ComputableTidilyInPolyTime (rawMainEncode t) encBits encBits :=
  rawEncodeInput_polytime.comp (rawAugment_polytime t)

set_option maxHeartbeats 1600000 in
theorem rawMainDecode_polytime (t : ℕ) : ComputableTidilyInPolyTime (rawMainDecode t) encBits encBits := by
  unfold rawMainDecode
  have hD := rawParseCodec_polytime.comp (rawAugment_polytime t)
  simpa only [Function.comp_def] using
    (rawDecode_polytime t).comp ((hD.fst'.fst'.fst'.prod hD.fst'.snd').prod hD.snd')

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawFamilyCode_correct {n : ℕ} (F : Family n) :
    rawFamilyCode (F.map rawAffine) = familyCode F := by
  simp [rawFamilyCode,rawUnary,rawAffine,familyCode,List.flatMap_map,Function.comp_def,unary]

 theorem rawAugment_correct (t n : ℕ) (tail : List Bool) :
    rawAugment t (unary n ++ tail) = unary n ++ familyCode (canonicalFamily t n) ++ tail := by
  unfold rawAugment
  rw [readUnary_prefix,dropHeader_prefix]
  dsimp only
  rw [rawCanonicalFamily_correct,rawFamilyCode_correct]
  rfl

 theorem rawAugment_codec (t n : ℕ) (P : Parameters n) (x : List Bool) :
    rawAugment t (unary n ++ parametersCode P ++ frame x) =
      familyRowsInput (canonicalFamily t n) P.rows ++ frame (bitCode P.beta) ++ frame x := by
  rw [List.append_assoc,rawAugment_correct]
  simp only [parametersCode,familyRowsInput,List.append_assoc]

 theorem rawMainEncode_correct (t n : ℕ) (P : Parameters n) (u : Word (messageLength P)) :
    rawMainEncode t (editEncoderInput P u) = wordCode (encodeWord (canonicalFamily t n) P u) := by
  unfold rawMainEncode editEncoderInput
  rw [rawAugment_codec]
  exact rawEncodeInput_correct (canonicalFamily t n) P u

 theorem rawMainDecode_correct (t n : ℕ) (P : Parameters n) (y : List Bit) :
    rawMainDecode t (editDecoderInput P y) = bitCode ((decodeList t P y).getD []) := by
  unfold rawMainDecode editDecoderInput
  rw [rawAugment_codec,rawParseCodec_correct]
  exact rawDecode_correct t P y

end EditGV897.Main

namespace EditGV897.Main
open EditGV897.Runtime

 theorem codec_input_runtime (t : ℕ) :
    ∃ (encoder decoder : Program) (Ae de Ad dd : ℕ), 0 < Ae ∧ 0 < Ad ∧
      ∀ (n : ℕ) (P : Parameters n),
        (∀ u : Word (messageLength P),
          Runs encoder (editEncoderInput P u) (wordCode (encodeWord (canonicalFamily t n) P u))
            (polyBudget Ae de (editEncoderInput P u).length)) ∧
        (∀ y : List Bit,
          Runs decoder (editDecoderInput P y) (bitCode ((decodeList t P y).getD []))
            (polyBudget Ad dd (editDecoderInput P y).length)) := by
  obtain ⟨encoder,Ae,de,he,hev⟩ := binary_program_realization _ _ _ (rawMainEncode_polytime t).computableInPolyTime
  obtain ⟨decoder,Ad,dd,hd,hdv⟩ := binary_program_realization _ _ _ (rawMainDecode_polytime t).computableInPolyTime
  refine ⟨encoder,decoder,Ae,de,Ad,dd,he,hd,?_⟩
  intro n P
  constructor
  · intro u
    simpa only [Turing.MultiTapeTM.encBits_apply,rawMainEncode_correct] using (hev (editEncoderInput P u)).1
  · intro y
    simpa only [Turing.MultiTapeTM.encBits_apply,rawMainDecode_correct] using (hdv (editDecoderInput P y)).1

end EditGV897.Main
open EditGV897.Main
theorem solution (t : ℕ) :
    ∃ (encoder decoder : Program) (Ae de Ad dd : ℕ), 0 < Ae ∧ 0 < Ad ∧
      ∀ (n : ℕ) (P : Parameters n),
        (∀ u : Word (messageLength P),
          Runs encoder (editEncoderInput P u) (wordCode (encodeWord (canonicalFamily t n) P u))
            (polyBudget Ae de (editEncoderInput P u).length)) ∧
        (∀ y : List Bit,
          Runs decoder (editDecoderInput P y) (bitCode ((decodeList t P y).getD []))
            (polyBudget Ad dd (editDecoderInput P y).length)) := EditGV897.Main.codec_input_runtime t