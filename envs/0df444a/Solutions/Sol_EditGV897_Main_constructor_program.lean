-- Prove2me | solution 1 for EditGV897.Main.constructor_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:08.854169+00:00
-- url     : https://prove2.me/submissions/49f6b8c9-7f82-4ea2-ae7b-c00d4370f767

import Definitions.Def_EditGV897_Main_Codec
import Theorems.Thm_EditGV897_Main_binary_program_realization
import Theorems.Thm_EditGV897_Main_witness_count_correct
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
namespace EditGV897.Main
 theorem Runs.mono {P : Program} {input output : List Bool} {s t : ℕ}
    (h : Runs P input output s) (hst : s ≤ t) : Runs P input output t := by
  obtain ⟨k, hk, c, hc, hhalt, hout⟩ := h
  exact ⟨k, hk.trans hst, c, hc, hhalt, hout⟩

theorem witnessCount_correct {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := witness_count_correct n F G E
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

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev rawSuffixEncoding := encPair (encPair encUnary (encList rawAffineEncoding))
  (encPair (encList encBits) encUnary)
abbrev rawPrefixEncoding := encPair (encPair encUnary (encList rawAffineEncoding))
  (encPair (encList encBits) encBits)

def rawPad (n : ℕ) (w : List Bool) : List Bool :=
  (List.range n).map (fun i => w[i]?.getD false)

theorem rawPad_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List Bool => rawPad p.1 p.2) (encPair encUnary encBits) encBits := by
  unfold rawPad
  apply mapToBitsWithInput (range.comp (fst _ _))
  have ho := fst (encPair encUnary encBits) encUnary
  have hi := snd (encPair encUnary encBits) encUnary
  simpa only [List.getD_eq_getElem?_getD] using bitsGetDWithInput ho.snd' hi false

def rawZeroSuffix (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (j : ℕ) : ℕ :=
  (F.map (fun f => rawContribution n f G ((rawFixed n f).drop j))).sum

def rawZeroPrefix (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (p : List Bool) : ℕ :=
  (F.map (fun f => rawContribution n f G
    ((rawFixed n f).drop p.length ++ [rawPull n f (rawPad n p)]))).sum

def rawTwiceExpectation (n : ℕ) (F : List RawAffine) (G : List (List Bool)) (p : List Bool) : ℕ :=
  (rawWitness n F G [] + 2 * rawZeroPrefix n F G p) - rawZeroSuffix n F G p.length

set_option maxHeartbeats 1600000 in
theorem rawZeroSuffix_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × ℕ) =>
      rawZeroSuffix p.1.1 p.1.2 p.2.1 p.2.2) rawSuffixEncoding encNat := by
  unfold rawZeroSuffix
  apply binary_sum.comp
  have hF := (fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encUnary)).snd'
  apply mapWithInput (encB := encNat) hF
  have ho := fst rawSuffixEncoding rawAffineEncoding
  have hf := snd rawSuffixEncoding rawAffineEncoding
  have hnf := ho.fst'.fst'.prod hf
  have hfixed := rawFixed_polytime.comp hnf
  have hE := listDropWithInput hfixed ho.snd'.snd'
  exact rawContribution_polytime.comp (hnf.prod (ho.snd'.fst'.prod hE))

set_option maxHeartbeats 1600000 in
theorem rawZeroPrefix_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × List Bool) =>
      rawZeroPrefix p.1.1 p.1.2 p.2.1 p.2.2) rawPrefixEncoding encNat := by
  unfold rawZeroPrefix
  apply binary_sum.comp
  have hF := (fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encBits)).snd'
  apply mapWithInput (encB := encNat) hF
  have ho := fst rawPrefixEncoding rawAffineEncoding
  have hf := snd rawPrefixEncoding rawAffineEncoding
  have hnf := ho.fst'.fst'.prod hf
  have hp := ho.snd'.snd'
  have hfixed := rawFixed_polytime.comp hnf
  have htail := listDropWithInput hfixed (length_bits_comp hp)
  have hpad := rawPad_polytime.comp (ho.fst'.fst'.prod hp)
  have hpull := rawPull_polytime.comp (hnf.prod hpad)
  have hsingle := cons' hpull (const [])
  exact rawContribution_polytime.comp (hnf.prod
    (ho.snd'.fst'.prod (listAppend' htail hsingle)))

set_option maxHeartbeats 1600000 in
theorem rawTwiceExpectation_polytime : ComputableTidilyInPolyTime
    (fun p : (ℕ × List RawAffine) × (List (List Bool) × List Bool) =>
      rawTwiceExpectation p.1.1 p.1.2 p.2.1 p.2.2) rawPrefixEncoding encNat := by
  unfold rawTwiceExpectation
  have hnf := fst (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encBits)
  have hgp := snd (encPair encUnary (encList rawAffineEncoding))
    (encPair (encList encBits) encBits)
  have hw := rawWitness_polytime.comp (hnf.prod (hgp.fst'.prod
    (const (encMid := encList rawEquationEncoding) [])))
  have hs := rawZeroSuffix_polytime.comp (hnf.prod (hgp.fst'.prod (length_bits_comp hgp.snd')))
  have ht := binary_mul.comp ((const (encMid := encNat) 2).prod rawZeroPrefix_polytime)
  exact binary_sub.comp ((binary_add.comp (hw.prod ht)).prod hs)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

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

 theorem rawZeroSuffix_equations {n : ℕ} (F : Family n) (G : Rows n) (j : ℕ) :
    rawZeroSuffix n (F.map rawAffine) (G.map wordCode) j = zeroSuffixCount F G j := by
  unfold rawZeroSuffix zeroSuffixCount
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro f hf
  rw [rawFixed_equations, ← List.map_drop, rawContribution_equations]

 theorem rawZeroPrefix_equations {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawZeroPrefix n (F.map rawAffine) (G.map wordCode) (bitCode p) = zeroPrefixCount F G p := by
  unfold rawZeroPrefix zeroPrefixCount
  simp only [List.map_map, Function.comp_def, bitCode, List.length_map]
  congr 1
  apply List.map_congr_left
  intro f hf
  change rawContribution n (rawAffine f) (G.map wordCode)
    ((rawFixed n (rawAffine f)).drop p.length ++ [rawPull n (rawAffine f) (rawPad n (bitCode p))]) = _
  rw [rawFixed_equations, ← List.map_drop, rawPad_prefix, rawPull_equation,
    ← List.map_singleton, ← List.map_append, rawContribution_equations]

 theorem witnessCount_le_empty {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E ≤ witnessCount F G [] := by
  rw [witnessCount_correct, witnessCount_correct]
  have he : affineSet ([] : List (Equation n)) = Finset.univ := by
    ext x
    simp [affineSet]
  rw [he]
  unfold witnessSum
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

 theorem zeroSuffixCount_le_witness {n : ℕ} (F : Family n) (G : Rows n) (j : ℕ) :
    zeroSuffixCount F G j ≤ witnessCount F G [] := by
  unfold zeroSuffixCount witnessCount
  apply List.sum_le_sum
  intro f hf
  simpa [witnessCount] using witnessCount_le_empty [f] G ((fixedEquations f).drop j)

 theorem rawTwiceExpectation_eq {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    (rawTwiceExpectation n (F.map rawAffine) (G.map wordCode) (bitCode p) : ℤ) =
      twiceExpectation F G p := by
  unfold rawTwiceExpectation
  rw [rawZeroSuffix_equations, rawZeroPrefix_equations]
  have hp : (bitCode p).length = p.length := by simp [bitCode]
  rw [hp]
  have hw : rawWitness n (F.map rawAffine) (G.map wordCode) [] = witnessCount F G [] :=
    rawWitness_equations F G []
  rw [hw, Int.natCast_sub (by have h := zeroSuffixCount_le_witness F G p.length; omega)]
  unfold twiceExpectation
  push_cast
  ring

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

abbrev RawRowData := (ℕ × List RawAffine) × List (List Bool)
abbrev rawRowEncoding := encPair (encPair encUnary (encList rawAffineEncoding)) (encList encBits)

def rawGreedyStep (D : RawRowData) (p : List Bool) : List Bool :=
  let a := rawTwiceExpectation D.1.1 D.1.2 D.2 (p ++ [false])
  let b := rawTwiceExpectation D.1.1 D.1.2 D.2 (p ++ [true])
  p ++ [if a ≤ b then false else true]

def rawChooseRow (D : RawRowData) : List Bool := (rawGreedyStep D)^[D.1.1] []

set_option maxHeartbeats 1600000 in
theorem rawGreedyStep_polytime : ComputableTidilyInPolyTime
    (fun p : RawRowData × List Bool => rawGreedyStep p.1 p.2)
    (encPair rawRowEncoding encBits) encBits := by
  unfold rawGreedyStep
  have hd := fst rawRowEncoding encBits
  have hp := snd rawRowEncoding encBits
  have hfalse := bitsAppend hp (const [false])
  have htrue := bitsAppend hp (const [true])
  have ha := rawTwiceExpectation_polytime.comp (hd.fst'.prod (hd.snd'.prod hfalse))
  have hb := rawTwiceExpectation_polytime.comp (hd.fst'.prod (hd.snd'.prod htrue))
  have hc := binary_le.comp (ha.prod hb)
  have hbit := hc.cond (const (encMid := encBool) false) (const (encMid := encBool) true)
  have hs := bitsCons hbit (const [])
  simpa only [Function.comp_def, decide_eq_true_eq] using bitsAppend hp hs

 theorem rawChooseRow_polytime : ComputableTidilyInPolyTime rawChooseRow rawRowEncoding encBits := by
  unfold rawChooseRow
  apply iterateWithInput_of_bounded_growth ((fst _ _).fst') (const []) rawGreedyStep_polytime
    (growth := fun _ => 1)
  refine ⟨.const 1, ?_⟩
  intro D p
  simp [rawGreedyStep]

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawGreedyStep_correct {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) :
    rawGreedyStep ((n,F.map rawAffine),G.map wordCode) (bitCode p) =
      bitCode (p ++ [if twiceExpectation F G (p++[0]) ≤ twiceExpectation F G (p++[1]) then 0 else 1]) := by
  have h0 : bitCode p ++ [false] = bitCode (p++[0]) := by simp [bitCode]
  have h1 : bitCode p ++ [true] = bitCode (p++[1]) := by simp [bitCode]
  have hc : rawTwiceExpectation n (F.map rawAffine) (G.map wordCode) (bitCode (p++[0])) ≤
        rawTwiceExpectation n (F.map rawAffine) (G.map wordCode) (bitCode (p++[1])) ↔
      twiceExpectation F G (p++[0]) ≤ twiceExpectation F G (p++[1]) := by
    rw [← rawTwiceExpectation_eq F G (p++[0]), ← rawTwiceExpectation_eq F G (p++[1])]
    omega
  dsimp only [rawGreedyStep]
  rw [h0,h1]
  simp only [hc]
  split_ifs <;> simp [bitCode]

 theorem rawGreedy_iterate {n : ℕ} (F : Family n) (G : Rows n) (k : ℕ) (p : List Bit) :
    (rawGreedyStep ((n,F.map rawAffine),G.map wordCode))^[k] (bitCode p) =
      bitCode (chooseRowPrefix F G k p) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, rawGreedyStep_correct, ih]
    rfl

 theorem greedyPrefix_length {n : ℕ} (F : Family n) (G : Rows n) (k : ℕ) (p : List Bit) :
    (chooseRowPrefix F G k p).length = p.length+k := by
  induction k generalizing p with
  | zero => simp [chooseRowPrefix]
  | succ k ih =>
    dsimp only [chooseRowPrefix]
    rw [ih]
    simp
    omega

 theorem rawChooseRow_correct {n : ℕ} (F : Family n) (G : Rows n) :
    rawChooseRow ((n,F.map rawAffine),G.map wordCode) = wordCode (chooseRow F G) := by
  have hh := rawGreedy_iterate F G n []
  change _ = bitCode (wordList (listWord n (chooseRowPrefix F G n [])))
  rw [wordList_listWord _ (by simpa using greedyPrefix_length F G n [])]
  exact hh

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawSyndromeValue (D : RawRowData) (β : List Bool) : ℕ :=
  rawWitness D.1.1 D.1.2 D.2 (D.2.zip β)

def rawSyndromeStep (D : RawRowData) (best β : List Bool) : List Bool :=
  if rawSyndromeValue D β < rawSyndromeValue D best then β else best

/-- Guard the exhaustive search by its polynomial-size certificate. -/
def rawSyndromeBits (D : RawRowData) : ℕ :=
  if 2^D.2.length ≤ 4*D.1.2.length then D.2.length else 0

def rawSyndromeCandidates (D : RawRowData) : List (List Bool) :=
  (Cslib.BitString.enumList (rawSyndromeBits D)).map List.reverse

def rawChooseSyndrome (D : RawRowData) : List Bool :=
  (rawSyndromeCandidates D).foldl (rawSyndromeStep D) (List.replicate D.2.length false)

set_option maxHeartbeats 1600000 in
theorem rawSyndromeValue_polytime : ComputableTidilyInPolyTime
    (fun p : RawRowData × List Bool => rawSyndromeValue p.1 p.2)
    (encPair rawRowEncoding encBits) encNat := by
  unfold rawSyndromeValue
  have hd := fst rawRowEncoding encBits
  have hb := snd rawRowEncoding encBits
  have hG := hd.snd'
  have hz := (zip encBits encBool).comp (hG.prod (bitsToList.comp hb))
  simpa only [Function.comp_def] using rawWitness_polytime.comp (hd.fst'.prod (hG.prod hz))

set_option maxHeartbeats 1600000 in
theorem rawSyndromeStep_polytime : ComputableTidilyInPolyTime
    (fun p : (RawRowData × List Bool) × List Bool => rawSyndromeStep p.1.1 p.1.2 p.2)
    (encPair (encPair rawRowEncoding encBits) encBits) encBits := by
  unfold rawSyndromeStep
  have hp := fst (encPair rawRowEncoding encBits) encBits
  have hb := hp.snd'
  have hx := snd (encPair rawRowEncoding encBits) encBits
  have hv := rawSyndromeValue_polytime.comp (hp.fst'.prod hx)
  have hbest := rawSyndromeValue_polytime.comp hp
  have hc := binary_lt.comp (hv.prod hbest)
  simpa only [Function.comp_def, decide_eq_true_eq] using hc.cond hx hb

 theorem rawSyndromeBits_polytime : ComputableTidilyInPolyTime rawSyndromeBits
    rawRowEncoding encUnary := by
  unfold rawSyndromeBits
  have hb := (length_list encBits).comp (snd (encPair encUnary (encList rawAffineEncoding)) (encList encBits))
  have hM := (length_list rawAffineEncoding).comp
    ((fst (encPair encUnary (encList rawAffineEncoding)) (encList encBits)).snd')
  have hpow := binary_two_pow.comp hb
  have hfour := binary_mul.comp ((const (encMid := encNat) 4).prod (unary_to_binary.comp hM))
  simpa only [Function.comp_def, decide_eq_true_eq] using (binary_le.comp (hpow.prod hfour)).cond hb (const 0)

theorem rawSyndromeBits_le (D : RawRowData) : rawSyndromeBits D ≤ D.2.length := by
  unfold rawSyndromeBits
  split <;> omega

 theorem rawSyndromeBits_pow_le (D : RawRowData) : 2^(rawSyndromeBits D) ≤ 4*D.1.2.length+1 := by
  unfold rawSyndromeBits
  split <;> omega

 theorem rawRowData_lengths (D : RawRowData) :
    D.1.2.length ≤ (rawRowEncoding D).length ∧ D.2.length ≤ (rawRowEncoding D).length := by
  have hF := SizedListEncoding.length_le (encA := rawAffineEncoding)
    (encL := encList rawAffineEncoding) D.1.2
  have hG := SizedListEncoding.length_le (encA := encBits) (encL := encList encBits) D.2
  simp only [rawRowEncoding, length_encPair] at *
  omega

 theorem rawSyndromeCandidates_polytime : ComputableTidilyInPolyTime rawSyndromeCandidates
    rawRowEncoding (encList encBits) := by
  have henum := bitsEnumList rawSyndromeBits_polytime
    (size := fun L => 16*(L+1)^2) (by fun_prop) (fun D => ?_)
  · exact (map bitsReverse).comp henum
  · have hM := (rawRowData_lengths D).1
    have hb := (rawRowData_lengths D).2
    have hcount := rawSyndromeBits_le D
    have hpow := rawSyndromeBits_pow_le D
    nlinarith

 theorem rawSyndromeCandidates_length (D : RawRowData) (β : List Bool)
    (hβ : β ∈ rawSyndromeCandidates D) : β.length ≤ D.2.length := by
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hβ
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
  simpa using rawSyndromeBits_le D

set_option maxHeartbeats 1600000 in
theorem rawChooseSyndrome_polytime : ComputableTidilyInPolyTime rawChooseSyndrome
    rawRowEncoding encBits := by
  have hb := (length_list encBits).comp
    (snd (encPair encUnary (encList rawAffineEncoding)) (encList encBits))
  apply foldlWith_of_bounded_growth (encA := encBits) (encL := encList encBits)
    id' rawSyndromeCandidates_polytime ((bitsReplicate false).comp hb)
    rawSyndromeStep_polytime hb.polyBounded
  intro D best β hβ
  have hl := rawSyndromeCandidates_length D β hβ
  dsimp only [rawSyndromeStep]
  split <;> simp_all <;> omega

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem checkRows_pow_le {M : ℕ} (hM : 0 < M) : 2^(checkRows M) ≤ 4*M := by
  have hx : 1 < 2*M := by omega
  have hpos := Nat.clog_pos (by decide : 1 < 2) hx
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hx
  have he : checkRows M = (Nat.clog 2 (2*M)).pred+1 := by
    unfold checkRows
    exact (Nat.succ_pred_eq_of_pos hpos).symm
  rw [he,pow_succ]
  omega

 theorem rawEnumList_words (b : ℕ) :
    (Cslib.BitString.enumList b).map List.reverse = (allBitLists b).map bitCode := by
  induction b with
  | zero => simp [allBitLists,bitCode]
  | succ b ih =>
    rw [Cslib.BitString.enumList_succ, List.map_flatMap]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append]
    rw [← List.flatMap_map List.reverse (fun w : List Bool => [w ++ [false],w ++ [true]])
      (Cslib.BitString.enumList b), ih]
    simp [allBitLists, List.flatMap_map, List.map_flatMap, bitCode, Function.comp_def]

 theorem rawSyndromeValue_correct {n : ℕ} (F : Family n) (G : Rows n) (β : List Bit) :
    rawSyndromeValue ((n,F.map rawAffine),G.map wordCode) (bitCode β) =
      witnessCount F G (cosetEquations G β) := by
  unfold rawSyndromeValue
  have hz : (G.map wordCode).zip (bitCode β) = (G.zip β).map rawEquation := by
    simp [bitCode, rawEquation, List.zip_map, List.map_map, Function.comp_def, bitBool]
  rw [hz]
  exact rawWitness_equations F G (G.zip β)

 theorem rawSyndromeStep_correct {n : ℕ} (F : Family n) (G : Rows n) (best β : List Bit) :
    rawSyndromeStep ((n,F.map rawAffine),G.map wordCode) (bitCode best) (bitCode β) =
      bitCode (if witnessCount F G (cosetEquations G β) < witnessCount F G (cosetEquations G best)
        then β else best) := by
  unfold rawSyndromeStep
  rw [rawSyndromeValue_correct,rawSyndromeValue_correct]
  split <;> rfl

 theorem rawSyndrome_fold {n : ℕ} (F : Family n) (G : Rows n) (L : List (List Bit)) (best : List Bit) :
    (L.map bitCode).foldl (rawSyndromeStep ((n,F.map rawAffine),G.map wordCode)) (bitCode best) =
      bitCode (L.foldl (fun best β =>
        if witnessCount F G (cosetEquations G β) < witnessCount F G (cosetEquations G best)
        then β else best) best) := by
  induction L generalizing best with
  | nil => rfl
  | cons β L ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [rawSyndromeStep_correct,ih]

 theorem rawChooseSyndrome_correct {n : ℕ} (F : Family n) (G : Rows n)
    (hF : 0 < F.length) (hG : G.length = checkRows F.length) :
    rawChooseSyndrome ((n,F.map rawAffine),G.map wordCode) = bitCode (chooseSyndrome F G) := by
  have hb : rawSyndromeBits ((n,F.map rawAffine),G.map wordCode) = G.length := by
    dsimp only [rawSyndromeBits]
    simp only [List.length_map]
    rw [if_pos (by rw [hG]; exact checkRows_pow_le hF)]
  unfold rawChooseSyndrome rawSyndromeCandidates
  rw [hb,rawEnumList_words]
  have hzero : List.replicate (G.map wordCode).length false = bitCode (List.replicate G.length 0) := by
    simp [bitCode]
  rw [hzero,rawSyndrome_fold]
  rfl

end EditGV897.Main

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

def rawRank (n : ℕ) (G : List (List Bool)) : ℕ :=
  (rawSummary (rawEliminate n (G.map (fun row => (row,false))))).1

def rawCompletionRow (n : ℕ) (G : List (List Bool)) : List Bool :=
  ((List.range n).find? (fun k => rawRank n (G++[rawUnit n k]) == G.length+1)).elim
    (List.replicate n false) (rawUnit n)

def rawCheckRows (M : ℕ) : ℕ := (2*M-1).size

def rawBuildRowsStep (n : ℕ) (F : List RawAffine) (G : List (List Bool)) : List (List Bool) :=
  G ++ [if rawWitness n F G [] = 0 then rawCompletionRow n G else rawChooseRow ((n,F),G)]

def rawChooseMatrix (n : ℕ) (F : List RawAffine) : List (List Bool) :=
  (rawBuildRowsStep n F)^[rawCheckRows F.length] []

 theorem rawRank_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List (List Bool) => rawRank p.1 p.2)
    (encPair encUnary (encList encBits)) encUnary := by
  unfold rawRank
  have hn := fst encUnary (encList encBits)
  have hG := snd encUnary (encList encBits)
  have hrows : ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) => p.2.map (fun row => (row,false)))
      (encPair encUnary (encList encBits)) (encList rawEquationEncoding) := by
    apply mapWithInput hG
    exact (snd _ _).prod (const false)
  simpa only [Function.comp_def] using (rawSummary_polytime.comp
    (rawEliminate_polytime.comp (hn.prod hrows))).fst'

set_option maxHeartbeats 1600000 in
theorem rawCompletionRow_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List (List Bool) => rawCompletionRow p.1 p.2)
    (encPair encUnary (encList encBits)) encBits := by
  unfold rawCompletionRow
  let en := encPair encUnary (encList encBits)
  have hn := fst encUnary (encList encBits)
  have hG := snd encUnary (encList encBits)
  have hfind : ComputableTidilyInPolyTime
      (fun p : ℕ × List (List Bool) => (List.range p.1).find?
        (fun k => rawRank p.1 (p.2++[rawUnit p.1 k]) == p.2.length+1))
      en (encOption encUnary) := by
    apply findWithInput (range.comp hn)
    have ho := fst en encUnary
    have hk := snd en encUnary
    have hu := rawUnit_polytime.comp (ho.fst'.prod hk)
    have hlist := listAppend' ho.snd' (cons' hu (const []))
    have hr := rawRank_polytime.comp (ho.fst'.prod hlist)
    have hb := unary_add.comp (((length_list encBits).comp ho.snd').prod (const (encMid := encUnary) 1))
    exact unary_beq hr hb
  apply optionElimWithInput hfind ((bitsReplicate false).comp hn)
  exact rawUnit_polytime.comp ((fst en encUnary).fst'.prod (snd en encUnary))

 theorem rawCheckRows_polytime : ComputableTidilyInPolyTime rawCheckRows encUnary encUnary := by
  unfold rawCheckRows
  have ht := unary_mul.comp ((const (encMid := encUnary) 2).prod id')
  have hp := unary_sub.comp (ht.prod (const (encMid := encUnary) 1))
  exact ComputableInPolyTime.binary_size.tidy.comp (unary_to_binary.comp hp)

set_option maxHeartbeats 1600000 in
theorem rawBuildRowsStep_polytime : ComputableTidilyInPolyTime
    (fun p : RawRowData => rawBuildRowsStep p.1.1 p.1.2 p.2)
    rawRowEncoding (encList encBits) := by
  unfold rawBuildRowsStep
  have hnf := fst (encPair encUnary (encList rawAffineEncoding)) (encList encBits)
  have hG := snd (encPair encUnary (encList rawAffineEncoding)) (encList encBits)
  have hw := rawWitness_polytime.comp (hnf.prod (hG.prod (const (encMid := encList rawEquationEncoding) [])))
  have hc := decide_eq' hw (const (encMid := encNat) 0)
  have hcompletion := rawCompletionRow_polytime.comp (hnf.fst'.prod hG)
  have hrow := hc.cond hcompletion rawChooseRow_polytime
  simpa only [Function.comp_def,decide_eq_true_eq] using listAppend' hG (cons' hrow (const []))

 theorem rawGreedyStep_length (D : RawRowData) (p : List Bool) :
    (rawGreedyStep D p).length = p.length+1 := by simp [rawGreedyStep]

 theorem rawGreedyIterate_length (D : RawRowData) (k : ℕ) (p : List Bool) :
    ((rawGreedyStep D)^[k] p).length = p.length+k := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply,ih,rawGreedyStep_length]
    omega

 theorem rawCompletionRow_length (n : ℕ) (G : List (List Bool)) :
    (rawCompletionRow n G).length = n := by
  unfold rawCompletionRow
  cases (List.range n).find? (fun k => rawRank n (G++[rawUnit n k]) == G.length+1) <;> simp [rawUnit]

 theorem rawBuildRowsStep_growth (n : ℕ) (F : List RawAffine) (G : List (List Bool)) :
    (encList encBits (rawBuildRowsStep n F G)).length ≤
      (encList encBits G).length + (2*n+1) := by
  unfold rawBuildRowsStep
  split
  · simp [encList_append,encList_cons,length_frame,rawCompletionRow_length]
  · have hlen : (rawChooseRow ((n,F),G)).length = n := by
      simpa only [rawChooseRow,List.length_nil,Nat.zero_add] using
        rawGreedyIterate_length ((n,F),G) n []
    simp [encList_append,encList_cons,length_frame,hlen]

 theorem rawChooseMatrix_polytime : ComputableTidilyInPolyTime
    (fun p : ℕ × List RawAffine => rawChooseMatrix p.1 p.2)
    (encPair encUnary (encList rawAffineEncoding)) (encList encBits) := by
  have hn := fst encUnary (encList rawAffineEncoding)
  have hF := snd encUnary (encList rawAffineEncoding)
  have hcount := rawCheckRows_polytime.comp ((length_list rawAffineEncoding).comp hF)
  have hg := unary_add.comp ((unary_mul.comp ((const (encMid := encUnary) 2).prod hn)).prod
    (const (encMid := encUnary) 1))
  exact iterateWithInput_of_bounded_growth hcount (const []) rawBuildRowsStep_polytime
    ⟨hg.polyBounded,fun x state => rawBuildRowsStep_growth x.1 x.2 state⟩

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem rawRank_correct {n : ℕ} (G : Rows n) : rawRank n (G.map wordCode) = rowRank G := by
  have hrows : (G.map wordCode).map (fun row => (row,false)) =
      (G.map (fun h => (h,(0 : Bit)))).map rawEquation := by
    simp [List.map_map,rawEquation,Function.comp_def]
  unfold rawRank rawEliminate
  rw [hrows,rawGaussian_summary n (0,(0,_)),rawGaussian_equations n 0 _ (by omega)]
  simp [rawPivotCount_equations,rowRank]

 theorem wordCode_zero (n : ℕ) : wordCode (0 : Word n) = List.replicate n false := by
  simp [wordCode,bitCode,wordList,DeletionHash.MixedEdit.letters]
  exact List.ofFn_const n false

 theorem rawCompletionRow_correct {n : ℕ} (G : Rows n) :
    rawCompletionRow n (G.map wordCode) = wordCode (completionRow G) := by
  have hpred : (fun k => rawRank n (G.map wordCode ++ [rawUnit n k]) == (G.map wordCode).length+1) =
      (fun k => rowRank (G++[unitWord n k]) == G.length+1) := by
    funext k
    rw [rawUnit_word,← List.map_singleton,← List.map_append,rawRank_correct,List.length_map]
  unfold rawCompletionRow completionRow
  rw [hpred]
  cases hf : (List.range n).find? (fun k => rowRank (G++[unitWord n k]) == G.length+1) <;>
    simp [hf,rawUnit_word,wordCode_zero]

 theorem rawCheckRows_correct (M : ℕ) : rawCheckRows M = checkRows M := by
  by_cases hM : M=0
  · simp [rawCheckRows,checkRows,hM]
  have hpos : 0 < 2*M := by omega
  have hs := Nat.lt_size_self (2*M-1)
  have hc := Nat.le_pow_clog (by decide : 1 < 2) (2*M)
  apply Nat.le_antisymm
  · apply Nat.size_le.mpr
    change 2*M-1 < 2^(Nat.clog 2 (2*M))
    omega
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    change 2*M ≤ 2^((2*M-1).size)
    omega

 theorem rawBuildRowsStep_correct {n : ℕ} (F : Family n) (G : Rows n) :
    rawBuildRowsStep n (F.map rawAffine) (G.map wordCode) =
      (G++[if witnessCount F G [] = 0 then completionRow G else chooseRow F G]).map wordCode := by
  have hw := rawWitness_equations F G []
  unfold rawBuildRowsStep
  rw [show rawWitness n (F.map rawAffine) (G.map wordCode) [] = witnessCount F G [] from hw]
  split <;> simp_all [rawCompletionRow_correct,rawChooseRow_correct]

 theorem rawBuildRows_correct {n : ℕ} (F : Family n) (k : ℕ) (G : Rows n) :
    (rawBuildRowsStep n (F.map rawAffine))^[k] (G.map wordCode) = (buildRows F k G).map wordCode := by
  induction k generalizing G with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,rawBuildRowsStep_correct,ih]
    rfl

 theorem rawChooseMatrix_correct {n : ℕ} (F : Family n) :
    rawChooseMatrix n (F.map rawAffine) = (chooseMatrix F).map wordCode := by
  unfold rawChooseMatrix chooseMatrix
  rw [List.length_map,rawCheckRows_correct]
  exact rawBuildRows_correct F _ []

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

def rawFrame (w : List Bool) : List Bool := List.replicate w.length true ++ false :: w

def rawNaturalCode (n : ℕ) : List Bool := false :: rawFrame n.bits.reverse

def rawEvaluateInput (w : List Bool) : ℕ :=
  let D := rawParseExpectation w
  rawTwiceExpectation D.1.1 D.1.2 D.2.1 D.2.2

def rawBuildRowInput (w : List Bool) : List Bool :=
  let D := rawParseFamilyRows w
  rawChooseRow (D.1, D.2.1)

 theorem rawFrame_polytime : ComputableTidilyInPolyTime rawFrame encBits encBits := by
  exact bitsAppend ((bitsReplicate true).comp length_bits) (bitsCons (const false) id')

 theorem rawNaturalCode_polytime : ComputableTidilyInPolyTime rawNaturalCode encNat encBits := by
  exact bitsCons (const false) (rawFrame_polytime.comp (bitsReverse.comp (encode encNat)))

set_option maxHeartbeats 1600000 in
theorem rawEvaluateInput_polytime : ComputableTidilyInPolyTime
    (fun w => rawNaturalCode (rawEvaluateInput w)) encBits encBits := by
  exact rawNaturalCode_polytime.comp (rawTwiceExpectation_polytime.comp rawParseExpectation_polytime)

 theorem rawBuildRowInput_polytime : ComputableTidilyInPolyTime rawBuildRowInput encBits encBits := by
  exact rawChooseRow_polytime.comp
    (rawParseFamilyRows_polytime.fst'.prod rawParseFamilyRows_polytime.snd'.fst')

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Runtime
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableTidilyInPolyTime

abbrev rawParametersEncoding := encPair (encList encBits) encBits

def rawSetup (t n : ℕ) : List (List Bool) × List Bool :=
  let F := rawCanonicalFamily t n
  let G := rawChooseMatrix n F
  (G,rawChooseSyndrome ((n,F),G))

def rawUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

def rawParametersCode (P : List (List Bool) × List Bool) : List Bool :=
  rawUnary P.1.length ++ P.1.flatten ++ rawFrame P.2

def rawConstructor (t : ℕ) (w : List Bool) : List Bool :=
  rawParametersCode (rawSetup t (readUnary w))

 theorem rawSetup_polytime (t : ℕ) : ComputableTidilyInPolyTime (rawSetup t)
    encUnary rawParametersEncoding := by
  unfold rawSetup
  have hnf := (id' (encIn := encUnary)).prod (rawCanonicalFamily_polytime t)
  have hG := rawChooseMatrix_polytime.comp hnf
  exact hG.prod (rawChooseSyndrome_polytime.comp (hnf.prod hG))

 theorem rawUnary_polytime : ComputableTidilyInPolyTime rawUnary encUnary encBits :=
  bitsAppend (bitsReplicate true) (const [false])

 theorem rawParametersCode_polytime : ComputableTidilyInPolyTime rawParametersCode
    rawParametersEncoding encBits := by
  have hrows := fst (encList encBits) encBits
  have hbeta := snd (encList encBits) encBits
  have hheader := rawUnary_polytime.comp ((length_list encBits).comp hrows)
  exact bitsAppend (bitsAppend hheader (bitsFlatten hrows)) (rawFrame_polytime.comp hbeta)

 theorem rawConstructor_polytime (t : ℕ) : ComputableTidilyInPolyTime (rawConstructor t)
    encBits encBits := by
  exact rawParametersCode_polytime.comp ((rawSetup_polytime t).comp readUnary_polytime)

end EditGV897.Runtime

set_option backward.isDefEq.respectTransparency false

namespace EditGV897.Main
open EditGV897.Runtime

 theorem runtimeBuildRows_length {n : ℕ} (F : Family n) (k : ℕ) (G : Rows n) :
    (buildRows F k G).length = G.length+k := by
  induction k generalizing G with
  | zero => simp [buildRows]
  | succ k ih =>
    simp only [buildRows]
    rw [ih]
    simp
    omega

 theorem runtimeChooseMatrix_length {n : ℕ} (F : Family n) :
    (chooseMatrix F).length = checkRows F.length := by
  simpa only [chooseMatrix,List.length_nil,Nat.zero_add] using runtimeBuildRows_length F (checkRows F.length) []

 theorem runtimeCanonical_pos (t n : ℕ) : 0 < (canonicalFamily t n).length := by
  let s := List.ofFn (fun i : Fin n => (unitWord n i.val,(0 : Bit)))
  have hm : s ∈ symbolicPaths (2*t) s := by cases 2*t <;> simp [symbolicPaths]
  have hfilter : s ∈ (symbolicPaths (2*t) s).filter (fun s => s.length == n) := by
    simp [hm,s]
  have hnon : canonicalFamily t n ≠ [] := by
    have hex : ∃ f, f ∈ canonicalFamily t n := ⟨_,List.mem_map.mpr ⟨s,hfilter,rfl⟩⟩
    rintro h
    obtain ⟨f,hf⟩ := hex
    simpa [h] using hf
  exact List.length_pos_iff.mpr hnon

 theorem rawSetup_correct (t n : ℕ) : rawSetup t n =
    ((setup t n).rows.map wordCode,bitCode (setup t n).beta) := by
  dsimp only [rawSetup,setup]
  rw [rawCanonicalFamily_correct,rawChooseMatrix_correct]
  rw [rawChooseSyndrome_correct _ _ (runtimeCanonical_pos t n) (runtimeChooseMatrix_length _)]

 theorem rawParametersCode_correct {n : ℕ} (P : Parameters n) :
    rawParametersCode (P.rows.map wordCode,bitCode P.beta) = parametersCode P := by
  simp [rawParametersCode,rawUnary,rawFrame,parametersCode,rowCode,frame,unary,List.flatMap]

 theorem rawConstructor_correct (t n : ℕ) : rawConstructor t (unary n) = parametersCode (setup t n) := by
  unfold rawConstructor
  have hn : readUnary (unary n) = n := by simpa only [List.append_nil] using readUnary_prefix n []
  rw [hn,rawSetup_correct,rawParametersCode_correct]

end EditGV897.Main

namespace EditGV897.Main
open EditGV897.Runtime

 theorem constructor_runtime (t : ℕ) :
    ∃ (constructor : Program) (A d : ℕ), 0 < A ∧ ∀ n : ℕ,
      (parametersCode (setup t n)).length ≤ polyBudget A d n ∧
      Runs constructor (unary n) (parametersCode (setup t n)) (polyBudget A d n) := by
  obtain ⟨P,c,d,hc,hr⟩ := binary_program_realization _ _ _ (rawConstructor_polytime t).computableInPolyTime
  refine ⟨P,c*2^d,d,Nat.mul_pos hc (by positivity),?_⟩
  intro n
  have hrun := (hr (unary n)).1
  have hlen := (hr (unary n)).2
  simp only [Turing.MultiTapeTM.encBits_apply,rawConstructor_correct] at hrun hlen
  have hb : polyBudget c d (unary n).length ≤ polyBudget (c*2^d) d n := by
    have he : (unary n).length+1 = n+2 := by simp [unary]
    unfold polyBudget
    rw [he]
    calc
      c*(n+2)^d ≤ c*(2*(n+1))^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = c*2^d*(n+1)^d := by rw [mul_pow]; ring
  exact ⟨hlen.trans hb,hrun.mono hb⟩

end EditGV897.Main
open EditGV897.Main
theorem solution (t : ℕ) :
    ∃ (constructor : Program) (A d : ℕ), 0 < A ∧ ∀ n : ℕ,
      (parametersCode (setup t n)).length ≤ polyBudget A d n ∧
      Runs constructor (unary n) (parametersCode (setup t n)) (polyBudget A d n) := EditGV897.Main.constructor_runtime t