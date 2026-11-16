-- Prove2me | solution 1 for F3SubsetSum.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-15T11:34:17.787196+00:00
-- url     : https://prove2.me/submissions/a94e17ef-39a3-4052-b06c-be45ea44dfb5

import Mathlib
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_QutritCircuit
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

-- Source: Solutions.L2.Gates

set_option maxHeartbeats 1000000
namespace F3Tools
open F3SubsetSum

/-- A reversible arithmetic gate, carrying its classical action and its exact quantum action. -/
structure Reversible (W : ℕ) where
  gates : List (Gate W)
  forward : QBasis W → QBasis W
  backward : QBasis W → QBasis W
  left_inv : Function.LeftInverse backward forward
  right_inv : Function.RightInverse backward forward
  action : ∀ ψ, gates.foldl (fun φ g => applyGate g φ) ψ = ψ ∘ backward

noncomputable def Reversible.identity (W : ℕ) : Reversible W where
  gates := []
  forward := id
  backward := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  action := fun _ => rfl

noncomputable def Reversible.then {W : ℕ} (A B : Reversible W) : Reversible W where
  gates := A.gates ++ B.gates
  forward := B.forward ∘ A.forward
  backward := A.backward ∘ B.backward
  left_inv y := by
    change A.backward (B.backward (B.forward (A.forward y))) = y
    rw [B.left_inv, A.left_inv]
  right_inv y := by
    change B.forward (A.forward (A.backward (B.backward y))) = y
    rw [A.right_inv, B.right_inv]
  action ψ := by rw [List.foldl_append, B.action, A.action]; rfl

theorem Reversible.basis {W : ℕ} (A : Reversible W) (y : QBasis W) :
    A.gates.foldl (fun φ g => applyGate g φ) (basisKet y) = basisKet (A.forward y) := by
  rw [A.action]
  funext z
  simp only [Function.comp_def, basisKet]
  congr 1
  exact propext ⟨fun h => by rw [← h, A.right_inv], fun h => by rw [h, A.left_inv]⟩

noncomputable def shift {W : ℕ} (i : Fin W) : Reversible W where
  gates := [.x i]
  forward y := Function.update y i (y i + 1)
  backward y := Function.update y i (y i - 1)
  left_inv y := by funext j; by_cases h : j = i <;> simp [h]
  right_inv y := by funext j; by_cases h : j = i <;> simp [h]
  action ψ := rfl

noncomputable def add {W : ℕ} (i j : Fin W) (hij : i ≠ j) : Reversible W where
  gates := [.csum i j hij]
  forward y := Function.update y j (y j + y i)
  backward y := Function.update y j (y j - y i)
  left_inv y := by funext k; by_cases h : k = j <;> simp [h, hij]
  right_inv y := by funext k; by_cases h : k = j <;> simp [h, hij]
  action ψ := rfl

noncomputable def mulAdd {W : ℕ} (i j k : Fin W) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Reversible W where
  gates := [.ccmul i j k hij hik hjk]
  forward y := Function.update y k (y k + y i * y j)
  backward y := Function.update y k (y k - y i * y j)
  left_inv y := by funext l; by_cases h : l = k <;> simp [h, hik, hjk]
  right_inv y := by funext l; by_cases h : l = k <;> simp [h, hik, hjk]
  action ψ := rfl

noncomputable def Reversible.inverse {W : ℕ} (A : Reversible W)
    (gs : List (Gate W))
    (hgs : ∀ ψ, gs.foldl (fun φ g => applyGate g φ) ψ = ψ ∘ A.forward) : Reversible W where
  gates := gs
  forward := A.backward
  backward := A.forward
  left_inv := A.right_inv
  right_inv := A.left_inv
  action := hgs

noncomputable def subtract {W : ℕ} (i j : Fin W) (hij : i ≠ j) : Reversible W :=
  (add i j hij).inverse [.csumInv i j hij] (fun _ => rfl)

noncomputable def mulSubtract {W : ℕ} (i j k : Fin W)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : Reversible W :=
  (mulAdd i j k hij hik hjk).inverse [.ccmulInv i j k hij hik hjk] (fun _ => rfl)

noncomputable def unshift {W : ℕ} (i : Fin W) : Reversible W :=
  (shift i).inverse [.xInv i] (fun _ => rfl)

end F3Tools

-- Source: Solutions.L2.Arithmetic

set_option maxHeartbeats 2000000
namespace F3Tools
open F3SubsetSum

/-- Raw arithmetic instructions. Indices are natural numbers for serialization. -/
abbrev Raw := ℕ × ℕ × ℕ × ℕ

/-- Every well-formed instruction is a gate on distinct wires. -/
def Valid (W : ℕ) (g : Raw) : Prop :=
  g.2.2.2 < W ∧ (g.1 = 0 ∨
    g.2.1 < W ∧ g.2.1 ≠ g.2.2.2 ∧ (g.1 = 1 ∨ g.1 = 2 ∨
      g.2.2.1 < W ∧ g.2.2.1 ≠ g.2.2.2 ∧ g.2.1 ≠ g.2.2.1 ∧ g.1 = 3))

instance (W : ℕ) (g : Raw) : Decidable (Valid W g) := inferInstanceAs (Decidable (_ ∧ _))

noncomputable def rawRev (W : ℕ) (g : Raw) : Reversible W :=
  if hk : g.2.2.2 < W then
    if g.1 = 0 then shift ⟨g.2.2.2,hk⟩
    else if hi : g.2.1 < W ∧ g.2.1 ≠ g.2.2.2 then
      if g.1 = 1 then add ⟨g.2.1,hi.1⟩ ⟨g.2.2.2,hk⟩ (fun h => hi.2 (congrArg Fin.val h))
      else if g.1 = 2 then subtract ⟨g.2.1,hi.1⟩ ⟨g.2.2.2,hk⟩ (fun h => hi.2 (congrArg Fin.val h))
      else if hj : g.2.2.1 < W ∧ g.2.2.1 ≠ g.2.2.2 ∧ g.2.1 ≠ g.2.2.1 ∧ g.1 = 3 then
        mulAdd ⟨g.2.1,hi.1⟩ ⟨g.2.2.1,hj.1⟩ ⟨g.2.2.2,hk⟩
          (fun h => hj.2.2.1 (congrArg Fin.val h))
          (fun h => hi.2 (congrArg Fin.val h)) (fun h => hj.2.1 (congrArg Fin.val h))
      else Reversible.identity W
    else Reversible.identity W
  else Reversible.identity W

def rawValue (g : Raw) (y : ℕ → ZMod 3) : ZMod 3 :=
  if g.1 = 0 then 1 else if g.1 = 1 then y g.2.1
  else if g.1 = 2 then -y g.2.1 else y g.2.1 * y g.2.2.1

def rawStep (g : Raw) (y : ℕ → ZMod 3) : ℕ → ZMod 3 :=
  Function.update y g.2.2.2 (y g.2.2.2 + rawValue g y)

noncomputable def rawCircuit (W : ℕ) : List Raw → Reversible W
  | [] => Reversible.identity W
  | g :: gs => (rawRev W g).then (rawCircuit W gs)

/-- Infinite register storage agrees with the actual circuit on every physical wire. -/
theorem rawRev_forward (W : ℕ) (g : Raw) (hv : Valid W g) (y : ℕ → ZMod 3) :
    (rawRev W g).forward (fun i => y i.val) = fun i => rawStep g y i.val := by
  rcases hv with ⟨hk,hv⟩
  unfold rawRev
  rw [dif_pos hk]
  rcases hv with h0 | ⟨hi,hik,hs⟩
  · rw [if_pos h0]
    funext i
    simp [shift,rawStep,rawValue,h0,Function.update_apply,Fin.ext_iff]
  · by_cases h0 : g.1 = 0
    · rw [if_pos h0]
      funext i
      simp [shift,rawStep,rawValue,h0,Function.update_apply,Fin.ext_iff]
    rw [if_neg h0,dif_pos ⟨hi,hik⟩]
    rcases hs with h1 | h2 | ⟨hj,hjk,hij,h3⟩
    · rw [if_pos h1]
      funext i
      simp [add,rawStep,rawValue,h0,h1,Function.update_apply,Fin.ext_iff]
    · have h1 : g.1 ≠ 1 := by omega
      rw [if_neg h1,if_pos h2]
      funext i
      simp [subtract,Reversible.inverse,add,rawStep,rawValue,h0,h1,h2,Function.update_apply,Fin.ext_iff]
      split_ifs <;> ring
    · have h1 : g.1 ≠ 1 := by omega
      have h2 : g.1 ≠ 2 := by omega
      rw [if_neg h1,if_neg h2,dif_pos ⟨hj,hjk,hij,h3⟩]
      funext i
      simp [mulAdd,rawStep,rawValue,h0,h1,h2,Function.update_apply,Fin.ext_iff]

end F3Tools

-- Source: Solutions.L2.Expressions

set_option maxHeartbeats 2000000
namespace F3Tools

inductive Expr where
  | zero
  | one
  | input (i : ℕ)
  | plus (a b : Expr)
  | times (a b : Expr)
  | minus (a : Expr)
  deriving Inhabited

def Expr.eval (y : ℕ → ZMod 3) : Expr → ZMod 3
  | .zero => 0
  | .one => 1
  | .input i => y i
  | .plus a b => a.eval y + b.eval y
  | .times a b => a.eval y * b.eval y
  | .minus a => -a.eval y

abbrev Token := ℕ × ℕ

def Expr.code : Expr → List Token
  | .zero => [(0,0)]
  | .one => [(0,1)]
  | .input i => [(1,i)]
  | .plus a b => a.code ++ b.code ++ [(2,0)]
  | .times a b => a.code ++ b.code ++ [(3,0)]
  | .minus a => a.code ++ [(4,0)]

def valueStep (y : ℕ → ZMod 3) (s : List (ZMod 3)) (t : Token) : List (ZMod 3) :=
  if t.1 = 0 then (t.2 : ZMod 3) :: s
  else if t.1 = 1 then y t.2 :: s
  else if t.1 = 2 then (s.getD 1 0 + s.getD 0 0) :: s.drop 2
  else if t.1 = 3 then (s.getD 1 0 * s.getD 0 0) :: s.drop 2
  else (-s.getD 0 0) :: s.drop 1

theorem Expr.code_eval (e : Expr) (y : ℕ → ZMod 3) (s : List (ZMod 3)) :
    e.code.foldl (valueStep y) s = e.eval y :: s := by
  induction e generalizing s with
  | zero => simp [Expr.code,Expr.eval,valueStep]
  | one => simp [Expr.code,Expr.eval,valueStep]
  | input i => simp [Expr.code,Expr.eval,valueStep]
  | plus a b ha hb => simp [Expr.code,Expr.eval,List.foldl_append,ha,hb,valueStep]
  | times a b ha hb => simp [Expr.code,Expr.eval,List.foldl_append,ha,hb,valueStep]
  | minus a ha => simp [Expr.code,Expr.eval,List.foldl_append,ha,valueStep]

def Expr.sum (xs : List Expr) : Expr := xs.foldr Expr.plus Expr.zero
def Expr.product (xs : List Expr) : Expr := xs.foldr Expr.times Expr.one

theorem Expr.eval_sum (y : ℕ → ZMod 3) (xs : List Expr) :
    (Expr.sum xs).eval y = (xs.map (Expr.eval y)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp_all [Expr.sum,Expr.eval]

theorem Expr.eval_product (y : ℕ → ZMod 3) (xs : List Expr) :
    (Expr.product xs).eval y = (xs.map (Expr.eval y)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp_all [Expr.product,Expr.eval]

def Expr.isZero (a : Expr) : Expr := .plus .one (.minus (.times a a))
def Expr.choose (a b c : Expr) : Expr := .plus (.times a b) (.times (.plus .one (.minus a)) c)

theorem Expr.eval_isZero (y : ℕ → ZMod 3) (e : Expr) :
    e.isZero.eval y = if e.eval y = 0 then 1 else 0 := by
  change 1 + -(e.eval y * e.eval y) = _
  generalize e.eval y = z
  fin_cases z <;> decide

theorem Expr.eval_choose (y : ℕ → ZMod 3) (a b c : Expr) (h : a.eval y = 0 ∨ a.eval y = 1) :
    (a.choose b c).eval y = if a.eval y = 1 then b.eval y else c.eval y := by
  rcases h with h | h <;> simp [Expr.choose,Expr.eval,h]

end F3Tools

-- Source: Solutions.L2.Search

set_option maxHeartbeats 2000000
namespace F3Search
open F3Tools F3SubsetSum

/-- Enumerate all bitstrings, in a fixed order. -/
def bits : ℕ → List (List Bool)
  | 0 => [[]]
  | m+1 => (bits m).map (false :: ·) ++ (bits m).map (true :: ·)

theorem bits_length (m : ℕ) : (bits m).length = 2^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [bits,ih,pow_succ,Nat.mul_two]

theorem mem_bits {m : ℕ} (s : List Bool) (hs : s.length = m) : s ∈ bits m := by
  induction m generalizing s with
  | zero => have : s = [] := List.eq_nil_of_length_eq_zero hs; simp [this,bits]
  | succ m ih =>
    cases s with
    | nil => simp at hs
    | cons b s =>
      have ht : s.length = m := by simpa using hs
      have hm := ih s ht
      cases b <;> simp [bits,hm]

def set (m : ℕ) (s : List Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => s.getD i.val false)

def sumExpr (n m row : ℕ) (s : List Bool) : Expr :=
  Expr.sum ((List.range m).map (fun i => if s.getD i false then Expr.input (n*i+row) else Expr.zero))

def goodExpr (n m : ℕ) (s : List Bool) : Expr :=
  if s.any id then Expr.product ((List.range n).map (fun j => (sumExpr n m j s).isZero)) else Expr.zero

def searchExpr (n m i : ℕ) : List (List Bool) → Expr
  | [] => .zero
  | s :: ss => (goodExpr n m s).choose
      (if s.getD i false then .one else .zero) (searchExpr n m i ss)

noncomputable def first (n m : ℕ) (h : Fin m → Fin n → ZMod 3) (ss : List (List Bool)) : Finset (Fin m) :=
  open Classical in
  match ss.find? (fun s => decide (IsZeroSubsetSum h (set m s))) with
  | some s => set m s
  | none => ∅

/-- Every finite subset occurs in the enumeration. -/
theorem set_complete (m : ℕ) (S : Finset (Fin m)) :
    ∃ s ∈ bits m, set m s = S := by
  let s := List.ofFn (fun i : Fin m => decide (i ∈ S))
  refine ⟨s,mem_bits s (by simp [s]),?_⟩
  ext i
  simp [set,s,List.getD_eq_getElem _ _ (show i.val < s.length by simpa [s] using i.isLt)]

def registers {n m : ℕ} (h : Fin m → Fin n → ZMod 3) : ℕ → ZMod 3 := fun w =>
  if hw : w < n*m then h ⟨w/n,Nat.div_lt_of_lt_mul hw⟩
    ⟨w%n,Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hw))⟩ else 0

theorem registers_entry {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (i : Fin m) (j : Fin n) :
    registers h (n*i.val+j.val) = h i j := by
  have hn : 0 < n := by have := j.isLt; omega
  have hw : n*i.val+j.val < n*m := by nlinarith [i.isLt,j.isLt]
  have hd : (n*i.val+j.val)/n = i.val := by
    simp only [Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hm : (n*i.val+j.val)%n = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  simp only [registers,dif_pos hw]
  apply congrArg₂ h <;> apply Fin.ext
  · exact hd
  · exact hm

theorem eval_sumExpr {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (s : List Bool) (j : Fin n) :
    (sumExpr n m j.val s).eval (registers h) = ∑ i ∈ set m s, h i j := by
  rw [sumExpr,Expr.eval_sum,List.map_map]
  simp only [Function.comp_def]
  have he : (List.range m).map (fun i =>
      (if s.getD i false then Expr.input (n*i+j.val) else Expr.zero).eval (registers h)) =
      List.ofFn (fun i : Fin m => if s.getD i.val false then h i j else 0) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      split_ifs
      · exact registers_entry h ⟨i,by simpa using hi⟩ j
      · rfl
  rw [he,List.sum_ofFn]
  simp [set,Finset.sum_filter]

theorem any_iff_nonempty (m : ℕ) (s : List Bool) (hlen : s.length = m) :
    s.any id = true ↔ (set m s).Nonempty := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨b,hb,hb'⟩
    obtain ⟨i,hi,he⟩ := List.getElem_of_mem hb
    refine ⟨⟨i,by omega⟩,?_⟩
    simp only [set,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [List.getD_eq_getElem s false hi,he]
    exact hb'
  · rintro ⟨i,hi⟩
    have ht : i.val < s.length := by simpa [hlen] using i.isLt
    simp only [set,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    rw [List.getD_eq_getElem s false ht] at hi
    exact ⟨s[i.val],List.getElem_mem ht,hi⟩

theorem prod_indicator {α : Type} (xs : List α) (P : α → Prop) [DecidablePred P] :
    (xs.map (fun x => if P x then (1 : ZMod 3) else 0)).prod =
      if ∀ x ∈ xs, P x then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.prod_cons,ih,List.mem_cons,forall_eq_or_imp]
    split_ifs <;> simp_all

open Classical in
theorem eval_goodExpr {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (s : List Bool)
    (hlen : s.length = m) :
    (goodExpr n m s).eval (registers h) = if IsZeroSubsetSum h (set m s) then 1 else 0 := by
  have hz : (∀ j ∈ List.range n, (sumExpr n m j s).eval (registers h) = 0) ↔
      ∑ i ∈ set m s, h i = 0 := by
    constructor
    · intro hh
      funext j
      simpa only [Finset.sum_apply,Pi.zero_apply] using
        (eval_sumExpr h s j).symm.trans (hh j.val (List.mem_range.mpr j.isLt))
    · intro hh j hj
      have := congrFun hh (⟨j,List.mem_range.mp hj⟩ : Fin n)
      rw [eval_sumExpr h s ⟨j,List.mem_range.mp hj⟩]
      simpa only [Finset.sum_apply,Pi.zero_apply] using this
  unfold goodExpr
  by_cases ha : s.any id = true
  · rw [if_pos ha,Expr.eval_product,List.map_map]
    simp only [Function.comp_def,Expr.eval_isZero]
    rw [prod_indicator]
    simp only [hz,IsZeroSubsetSum,(any_iff_nonempty m s hlen).mp ha,true_and]
  · rw [if_neg ha]
    have hn := not_iff_not.mpr (any_iff_nonempty m s hlen) |>.mp ha
    simp [Expr.eval,IsZeroSubsetSum,hn]

open Classical in
theorem first_cons {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (s : List Bool) (ss : List (List Bool)) :
    first n m h (s::ss) = if IsZeroSubsetSum h (set m s) then set m s else first n m h ss := by
  unfold first
  rw [List.find?_cons]
  split_ifs with hg <;> simp [hg]

open Classical in
theorem eval_searchExpr {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (ss : List (List Bool))
    (hlen : ∀ s ∈ ss, s.length = m) (i : Fin m) :
    (searchExpr n m i.val ss).eval (registers h) =
      if i ∈ first n m h ss then 1 else 0 := by
  induction ss with
  | nil => simp [searchExpr,Expr.eval,first]
  | cons s ss ih =>
    have he := eval_goodExpr h s (hlen s (by simp))
    have ht := ih (fun s hs => hlen s (by simp [hs]))
    simp only [searchExpr,Expr.choose,Expr.eval,he]
    by_cases hg : IsZeroSubsetSum h (set m s)
    · rw [first_cons,if_pos hg]
      simp only [if_pos hg,one_mul,add_neg_cancel,zero_mul,add_zero]
      simp only [set,Finset.mem_filter,Finset.mem_univ,true_and]
      split_ifs <;> rfl
    · rw [first_cons,if_neg hg]
      simp only [if_neg hg,zero_mul,neg_zero,add_zero,zero_add,one_mul]
      exact ht

open Classical in
theorem first_correct {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (hh : HasZeroSubsetSum h) :
    IsZeroSubsetSum h (first n m h (bits m)) := by
  obtain ⟨S,hS⟩ := hh
  obtain ⟨s,hs,he⟩ := set_complete m S
  have hex : ((bits m).find? (fun s => decide (IsZeroSubsetSum h (set m s)))).isSome := by
    by_contra hn
    have hn' : (bits m).find? (fun s => decide (IsZeroSubsetSum h (set m s))) = none := by
      cases hx : (bits m).find? (fun s => decide (IsZeroSubsetSum h (set m s))) <;> simp_all
    have hc := List.find?_eq_none.mp hn' s hs
    simp [he,hS] at hc
  unfold first
  cases hx : (bits m).find? (fun s => decide (IsZeroSubsetSum h (set m s))) with
  | none => simp [hx] at hex
  | some s =>
    have hp : decide (IsZeroSubsetSum h (set m s)) = true := List.find?_some (p := fun s => decide (IsZeroSubsetSum h (set m s))) hx
    exact of_decide_eq_true hp

end F3Search

-- Source: Solutions.L2.Compiler

set_option maxHeartbeats 2000000
namespace F3Tools
open F3SubsetSum

def rawRun (gs : List Raw) (y : ℕ → ZMod 3) := gs.foldl (fun y g => rawStep g y) y

def source (I : ℕ) (s : List ℕ) (k : ℕ) := s.getD k I

def tokenGates (I p : ℕ) (s : List ℕ) (t : Token) : List Raw :=
  if t.1 = 0 then List.replicate (t.2 % 3) (0,0,0,p+1)
  else if t.1 = 1 then [(1,(if t.2 < I then t.2 else I),0,p+1)]
  else if t.1 = 2 then [(1,source I s 1,0,p+1),(1,source I s 0,0,p+1)]
  else if t.1 = 3 then [(1,source I s 1,0,p),(3,p,source I s 0,p+1)]
  else [(2,source I s 0,0,p+1)]

def tokenStack (p : ℕ) (s : List ℕ) (t : Token) : List ℕ :=
  (p+1) :: (if t.1 = 0 ∨ t.1 = 1 then s else s.drop (if t.1 = 2 ∨ t.1 = 3 then 2 else 1))

def compileStep (I : ℕ) (s : (List Raw × ℕ) × List ℕ) (t : Token) : (List Raw × ℕ) × List ℕ :=
  ((s.1.1 ++ tokenGates I s.1.2 s.2 t,s.1.2+2),tokenStack s.1.2 s.2 t)

def compile (I base : ℕ) (code : List Token) : (List Raw × ℕ) × List ℕ :=
  code.foldl (compileStep I) (([],base),[])

def tokenResult (I : ℕ) (s : List ℕ) (t : Token) (y : ℕ → ZMod 3) : ZMod 3 :=
  if t.1 = 0 then t.2
  else if t.1 = 1 then y (if t.2 < I then t.2 else I)
  else if t.1 = 2 then y (source I s 1) + y (source I s 0)
  else if t.1 = 3 then y (source I s 1) * y (source I s 0)
  else -y (source I s 0)

theorem source_lt (I p : ℕ) (s : List ℕ) (hI : I < p) (hs : ∀ a ∈ s, a < p) (k : ℕ) :
    source I s k < p := by
  unfold source
  by_cases hk : k < s.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact hs _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hI

theorem tokenGates_valid (I p : ℕ) (s : List ℕ) (t : Token)
    (hI : I < p) (hs : ∀ a ∈ s, a < p) : ∀ g ∈ tokenGates I p s t, Valid (p+2) g := by
  have h0 := source_lt I p s hI hs 0
  have h1 := source_lt I p s hI hs 1
  have hv : (if t.2 < I then t.2 else I) < p := by split_ifs <;> omega
  unfold tokenGates
  split_ifs
  · intro g hg
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hg
    simp [Valid]
  all_goals intro g hg; simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  all_goals rcases hg with rfl | rfl <;> simp [Valid] <;> omega

theorem tokenGates_result (I p : ℕ) (s : List ℕ) (t : Token) (y : ℕ → ZMod 3)
    (hI : I < p) (hs : ∀ a ∈ s, a < p) (hz : ∀ k, p  ≤  k → y k = 0) :
    rawRun (tokenGates I p s t) y (p+1) = tokenResult I s t y := by
  have h0 := source_lt I p s hI hs 0
  have h1 := source_lt I p s hI hs 1
  have hv : (if t.2 < I then t.2 else I) < p := by split_ifs <;> omega
  have hp := hz p (by omega)
  have hp1 := hz (p+1) (by omega)
  by_cases a : t.1 = 0
  · have hm : t.2 % 3 < 3 := Nat.mod_lt _ (by decide)
    have castmod : ((t.2 % 3 : ℕ) : ZMod 3) = t.2 := by simp
    simp only [tokenGates,tokenResult,if_pos a]
    interval_cases hh : t.2 % 3 <;>
      simp [rawRun,rawStep,rawValue,hp1,hh] at ⊢ castmod <;> exact castmod
  by_cases b : t.1 = 1
  · simp [tokenGates,tokenResult,a,b,rawRun,rawStep,rawValue,hp1]
  by_cases c : t.1 = 2
  · simp [tokenGates,tokenResult,a,b,c,rawRun,rawStep,rawValue,hp1,
      Function.update_apply,show source I s 0 ≠ p+1 by omega]
  by_cases d : t.1 = 3
  · simp [tokenGates,tokenResult,a,b,c,d,rawRun,rawStep,rawValue,hp,hp1,
      Function.update_apply,show p+1 ≠ p by omega,show source I s 0 ≠ p by omega]
  · simp [tokenGates,tokenResult,a,b,c,d,rawRun,rawStep,rawValue,hp1]


theorem rawRun_preserve (gs : List Raw) (y : ℕ → ZMod 3) (k : ℕ)
    (h : ∀ g ∈ gs, k ≠ g.2.2.2) : rawRun gs y k = y k := by
  induction gs generalizing y with
  | nil => rfl
  | cons g gs ih =>
    change rawRun gs (rawStep g y) k = y k
    rw [ih _ (fun g hg => h g (List.mem_cons_of_mem _ hg))]
    simp [rawStep,Function.update_apply,h g (by simp)]

theorem tokenGates_targets (I p : ℕ) (s : List ℕ) (t : Token) :
    ∀ g ∈ tokenGates I p s t, g.2.2.2 = p ∨ g.2.2.2 = p+1 := by
  unfold tokenGates
  split_ifs
  · intro g hg
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hg
    simp
  all_goals intro g hg; simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  all_goals rcases hg with rfl | rfl <;> simp

theorem tokenGates_preserve (I p : ℕ) (s : List ℕ) (t : Token) (y : ℕ → ZMod 3)
    (k : ℕ) (hk : k < p ∨ p+2  ≤  k) : rawRun (tokenGates I p s t) y k = y k := by
  apply rawRun_preserve
  intro g hg
  have := tokenGates_targets I p s t g hg
  omega

theorem tokenStack_lt (I p : ℕ) (s : List ℕ) (t : Token) (hs : ∀ a ∈ s, a < p) :
    ∀ a ∈ tokenStack p s t, a < p+2 := by
  intro a ha
  simp only [tokenStack,List.mem_cons] at ha
  rcases ha with rfl | ha
  · omega
  · split_ifs at ha
    · have := hs a ha; omega
    · have := hs a (List.mem_of_mem_drop ha); omega
    · have := hs a (List.mem_of_mem_drop ha); omega

theorem rawCircuit_forward (W : ℕ) (gs : List Raw) (hv : ∀ g ∈ gs, Valid W g)
    (y : ℕ → ZMod 3) :
    (rawCircuit W gs).forward (fun i => y i.val) = fun i => rawRun gs y i.val := by
  induction gs generalizing y with
  | nil => rfl
  | cons g gs ih =>
    change (rawCircuit W gs).forward ((rawRev W g).forward (fun i => y i.val)) = _
    rw [rawRev_forward W g (hv _ (by simp)) y,ih (fun g hg => hv g (by simp [hg]))]
    rfl

end F3Tools

-- Source: Solutions.L2.Execution

set_option maxHeartbeats 3000000
namespace F3Tools

/-- Invariant for the arithmetic stack compiler. -/
structure StoreInv (I base p : ℕ) (s : List ℕ) (v : List (ZMod 3))
    (orig y : ℕ → ZMod 3) : Prop where
  base_pos : I < base
  growing : base  ≤  p
  indices : ∀ a ∈ s, a < p
  original : ∀ a, a < base → y a = orig a
  zero_origin : orig I = 0
  unused : ∀ a, p  ≤  a → y a = 0
  values : s.map y = v

theorem source_value (I : ℕ) (s : List ℕ) (y : ℕ → ZMod 3) (hy : y I = 0) (k : ℕ) :
    y (source I s k) = (s.map y).getD k 0 := by
  unfold source
  by_cases hk : k < s.length
  · rw [List.getD_eq_getElem s I hk,List.getD_eq_getElem (s.map y) 0 (by simpa using hk)]
    simp only [List.getElem_map]
  · rw [List.getD_eq_default s I (by omega),List.getD_eq_default (s.map y) 0 (by simpa using Nat.le_of_not_gt hk)]
    exact hy

theorem tokenResult_value (I base p : ℕ) (s : List ℕ) (v : List (ZMod 3))
    (orig y : ℕ → ZMod 3) (h : StoreInv I base p s v orig y) (t : Token)
    (ht : t.1 ≠ 1 ∨ t.2 < I) :
    tokenResult I s t y = (valueStep orig v t).headD 0 := by
  have hy : y I = 0 := by rw [h.original _ h.base_pos,h.zero_origin]
  have hs (k : ℕ) := source_value I s y hy k
  simp only [h.values] at hs
  unfold tokenResult valueStep
  by_cases h0 : t.1 = 0
  · simp [h0]
  by_cases h1 : t.1 = 1
  · have hi : t.2 < I := ht.resolve_left (not_not_intro h1)
    simp [h0,h1,hi,h.original t.2 (lt_trans hi h.base_pos)]
  by_cases h2 : t.1 = 2
  · simp [h0,h1,h2,hs]
  by_cases h3 : t.1 = 3
  · simp [h0,h1,h2,h3,hs]
  · simp [h0,h1,h2,h3,hs]

theorem token_preserves_inv (I base p : ℕ) (s : List ℕ) (v : List (ZMod 3))
    (orig y : ℕ → ZMod 3) (h : StoreInv I base p s v orig y) (t : Token)
    (ht : t.1 ≠ 1 ∨ t.2 < I) :
    StoreInv I base (p+2) (tokenStack p s t) (valueStep orig v t) orig
      (rawRun (tokenGates I p s t) y) := by
  have hbase := h.growing
  have hip : I < p := lt_of_lt_of_le h.base_pos h.growing
  have hp : ∀ a ∈ s, rawRun (tokenGates I p s t) y a = y a := by
    intro a ha
    exact tokenGates_preserve I p s t y a (Or.inl (h.indices a ha))
  have hv : rawRun (tokenGates I p s t) y (p+1) = (valueStep orig v t).headD 0 :=
    (tokenGates_result I p s t y hip h.indices h.unused).trans (tokenResult_value I base p s v orig y h t ht)
  refine ⟨h.base_pos,by omega,tokenStack_lt I p s t h.indices,?_,h.zero_origin,?_,?_⟩
  · intro a ha
    rw [tokenGates_preserve I p s t y a (Or.inl (by omega)),h.original a ha]
  · intro a ha
    rw [tokenGates_preserve I p s t y a (Or.inr ha),h.unused a (by omega)]
  · have hm : s.map (rawRun (tokenGates I p s t) y) = v := by
      rw [← h.values]
      exact List.map_congr_left hp
    simp only [tokenStack,List.map_cons,hv]
    unfold valueStep at ⊢ hv
    split_ifs <;> simp_all [List.map_drop]

theorem Valid.mono {W W' : ℕ} {g : Raw} (h : Valid W g) (hW : W  ≤  W') : Valid W' g := by
  rcases h with ⟨hk,hg⟩
  refine ⟨by omega,?_⟩
  rcases hg with h0 | ⟨hi,hik,h⟩
  · exact Or.inl h0
  · refine Or.inr ⟨by omega,hik,?_⟩
    rcases h with h1 | h2 | ⟨hj,hjk,hij,h3⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨by omega,hjk,hij,h3⟩)

theorem tokenGates_length (I p : ℕ) (s : List ℕ) (t : Token) :
    (tokenGates I p s t).length  ≤  2 := by
  unfold tokenGates
  split_ifs <;> simp <;> omega

@[simp] theorem rawRun_append (gs hs : List Raw) (y : ℕ → ZMod 3) :
    rawRun (gs++hs) y = rawRun hs (rawRun gs y) := List.foldl_append

/-- End-to-end correctness, validity, and resource bounds for the stack compiler. -/
theorem compile_correct (I base : ℕ) (code : List Token)
    (hc : ∀ t ∈ code, t.1 ≠ 1 ∨ t.2 < I)
    (state : (List Raw × ℕ) × List ℕ) (v : List (ZMod 3)) (orig : ℕ → ZMod 3)
    (hi : StoreInv I base state.1.2 state.2 v orig (rawRun state.1.1 orig))
    (hg : ∀ g ∈ state.1.1, Valid state.1.2 g) :
    let result := code.foldl (compileStep I) state
    StoreInv I base result.1.2 result.2 (code.foldl (valueStep orig) v) orig (rawRun result.1.1 orig) ∧
      (∀ g ∈ result.1.1, Valid result.1.2 g) ∧
      result.1.2 = state.1.2+2*code.length ∧
      result.1.1.length  ≤  state.1.1.length+2*code.length := by
  induction code generalizing state v with
  | nil => exact ⟨hi,hg,by simp,by simp⟩
  | cons t ts ih =>
    have htc := hc t (by simp)
    have htail : ∀ t ∈ ts, t.1 ≠ 1 ∨ t.2 < I := fun t ht => hc t (by simp [ht])
    have hI : I < state.1.2 := lt_of_lt_of_le hi.base_pos hi.growing
    have hnew : StoreInv I base (compileStep I state t).1.2 (compileStep I state t).2
        (valueStep orig v t) orig (rawRun (compileStep I state t).1.1 orig) := by
      simpa only [compileStep,rawRun_append] using token_preserves_inv I base state.1.2 state.2 v
        orig (rawRun state.1.1 orig) hi t htc
    have hvalid : ∀ g ∈ (compileStep I state t).1.1, Valid (compileStep I state t).1.2 g := by
      intro g hg'
      simp only [compileStep,List.mem_append] at hg'
      rcases hg' with hold | hnew
      · exact (hg g hold).mono (by dsimp [compileStep]; omega)
      · exact tokenGates_valid I state.1.2 state.2 t hI hi.indices g hnew
    obtain ⟨hinv,hgates,hp,hlen⟩ := ih htail (compileStep I state t) (valueStep orig v t) hnew hvalid
    refine ⟨hinv,hgates,?_,?_⟩
    · change (ts.foldl (compileStep I) (compileStep I state t)).1.2 = state.1.2+2*(ts.length+1)
      rw [hp]
      change state.1.2+2+2*ts.length = state.1.2+2*(ts.length+1)
      omega
    · change (ts.foldl (compileStep I) (compileStep I state t)).1.1.length  ≤  state.1.1.length+2*(ts.length+1)
      have hl : (compileStep I state t).1.1.length = state.1.1.length+(tokenGates I state.1.2 state.2 t).length := by
        simp only [compileStep,List.length_append]
      rw [hl] at hlen
      have := tokenGates_length I state.1.2 state.2 t
      omega

end F3Tools

-- Source: Solutions.L2.SearchCode

set_option maxHeartbeats 3000000
namespace F3Tools

def Expr.Bounded (I : ℕ) : Expr → Prop
  | .zero | .one => True
  | .input i => i < I
  | .plus a b | .times a b => a.Bounded I ∧ b.Bounded I
  | .minus a => a.Bounded I

theorem Expr.bounded_code (I : ℕ) (e : Expr) (h : e.Bounded I) :
    ∀ t ∈ e.code, t.1 ≠ 1 ∨ t.2 < I := by
  induction e with
  | zero => simp [Expr.code]
  | one => simp [Expr.code]
  | input i => simpa [Expr.code,Expr.Bounded] using h
  | plus a b ha hb =>
    simp only [Expr.code,List.mem_append,List.mem_singleton,forall_eq_or_imp]
    intro t ht
    rcases ht with (ht | ht) | rfl
    · exact ha h.1 t ht
    · exact hb h.2 t ht
    · simp
  | times a b ha hb =>
    simp only [Expr.code,List.mem_append,List.mem_singleton,forall_eq_or_imp]
    intro t ht
    rcases ht with (ht | ht) | rfl
    · exact ha h.1 t ht
    · exact hb h.2 t ht
    · simp
  | minus a ha =>
    simp only [Expr.code,List.mem_append,List.mem_singleton,forall_eq_or_imp]
    intro t ht
    rcases ht with ht | rfl
    · exact ha h t ht
    · simp

theorem Expr.sum_bounded (I : ℕ) (es : List Expr) (h : ∀ e ∈ es, e.Bounded I) :
    (Expr.sum es).Bounded I := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun e he => h e (by simp [he]))⟩

theorem Expr.product_bounded (I : ℕ) (es : List Expr) (h : ∀ e ∈ es, e.Bounded I) :
    (Expr.product es).Bounded I := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun e he => h e (by simp [he]))⟩

theorem Expr.list_code_eval (es : List Expr) (y : ℕ → ZMod 3) (s : List (ZMod 3)) :
    (es.flatMap Expr.code).foldl (valueStep y) s = es.reverse.map (Expr.eval y) ++ s := by
  induction es generalizing s with
  | nil => rfl
  | cons a es ih => simp [List.foldl_append,Expr.code_eval,ih,List.reverse_cons,List.append_assoc]

theorem Expr.code_numbers (I M : ℕ) (e : Expr) (h : e.Bounded I) (hI : I  ≤  M) (hM : 4  ≤  M) :
    ∀ t ∈ e.code, t.1  ≤  M ∧ t.2  ≤  M := by
  induction e with
  | zero => simp [Expr.code] <;> omega
  | one => simp [Expr.code] <;> omega
  | input i => simp [Expr.code]; dsimp [Expr.Bounded] at h; omega
  | plus a b ha hb =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ha h.1 t ht
    · exact hb h.2 t ht
    · simp <;> omega
  | times a b ha hb =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with (ht | ht) | rfl
    · exact ha h.1 t ht
    · exact hb h.2 t ht
    · simp <;> omega
  | minus a ha =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact ha h t ht
    · simp <;> omega

end F3Tools

namespace F3Search
open F3Tools

theorem sumExpr_bounded (n m j : ℕ) (s : List Bool) (hj : j < n) :
    (sumExpr n m j s).Bounded (n*m) := by
  apply Expr.sum_bounded
  intro e he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
  have hi' := List.mem_range.mp hi
  split_ifs
  · dsimp [Expr.Bounded]
    nlinarith
  · trivial

theorem goodExpr_bounded (n m : ℕ) (s : List Bool) : (goodExpr n m s).Bounded (n*m) := by
  unfold goodExpr
  split_ifs
  · apply Expr.product_bounded
    intro e he
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hs := sumExpr_bounded n m j s (List.mem_range.mp hj)
    exact ⟨trivial,hs,hs⟩
  · trivial

theorem searchExpr_bounded (n m i : ℕ) (ss : List (List Bool)) :
    (searchExpr n m i ss).Bounded (n*m) := by
  induction ss with
  | nil => trivial
  | cons s ss ih =>
    have hg := goodExpr_bounded n m s
    change (_ ∧ _) ∧ ((_ ∧ _) ∧ _)
    refine ⟨⟨hg,?_⟩,⟨⟨trivial,hg⟩,ih⟩⟩
    split_ifs <;> trivial

def outputExprs (n m : ℕ) : List Expr :=
  (List.range m).reverse.map (fun i => searchExpr n m i (bits m))

def code (n m : ℕ) : List Token := (outputExprs n m).flatMap Expr.code

theorem code_bounded (n m : ℕ) : ∀ t ∈ code n m, t.1 ≠ 1 ∨ t.2 < n*m := by
  intro t ht
  obtain ⟨e,he,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  exact Expr.bounded_code _ _ (searchExpr_bounded n m i (bits m)) t ht

theorem bits_member_length {m : ℕ} (s : List Bool) (hs : s ∈ bits m) : s.length = m := by
  induction m generalizing s with
  | zero => simpa [bits] using hs
  | succ m ih =>
    simp only [bits,List.mem_append,List.mem_map] at hs
    rcases hs with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩ <;> simp [ih t ht]

open Classical in
theorem code_eval (n m : ℕ) (h : Fin m → Fin n → ZMod 3) :
    (code n m).foldl (valueStep (registers h)) [] =
      List.ofFn (fun i : Fin m => if i ∈ first n m h (bits m) then (1 : ZMod 3) else 0) := by
  rw [code,Expr.list_code_eval]
  simp only [outputExprs,← List.map_reverse,List.reverse_reverse,List.map_map,List.append_nil]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact eval_searchExpr h (bits m) (fun s hs => bits_member_length s hs) ⟨i,by simpa using hi⟩

theorem code_numbers (n m M : ℕ) (hI : n*m  ≤  M) (hM : 4  ≤  M) :
    ∀ t ∈ code n m, t.1  ≤  M ∧ t.2  ≤  M := by
  intro t ht
  obtain ⟨e,he,ht⟩ := List.mem_flatMap.mp ht
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  exact Expr.code_numbers (n*m) M _ (searchExpr_bounded n m i (bits m)) hI hM t ht

end F3Search

-- Source: Solutions.L2.Circuit

set_option maxHeartbeats 4000000
namespace F3Tools
open F3SubsetSum

theorem compile_stack_lower (I base : ℕ) (code : List Token)
    (state : (List Raw × ℕ) × List ℕ) (hp : base  ≤  state.1.2)
    (hs : ∀ a ∈ state.2, base  ≤  a) :
    ∀ a ∈ (code.foldl (compileStep I) state).2, base  ≤  a := by
  induction code generalizing state with
  | nil => exact hs
  | cons t ts ih =>
    apply ih (compileStep I state t) (by dsimp [compileStep]; omega)
    intro a ha
    simp only [compileStep,tokenStack,List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · split_ifs at ha
      · exact hs a ha
      · exact hs a (List.mem_of_mem_drop ha)
      · exact hs a (List.mem_of_mem_drop ha)

def copyBlock (start : ℕ) : List ℕ → List Raw
  | [] => []
  | a::as => (1,a,0,start) :: copyBlock (start+1) as

theorem copyBlock_targets (start : ℕ) (as : List ℕ) :
    ∀ g ∈ copyBlock start as, start  ≤  g.2.2.2 ∧ g.2.2.2 < start+as.length := by
  induction as generalizing start with
  | nil => simp [copyBlock]
  | cons a as ih =>
    intro g hg
    simp only [copyBlock,List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp
    · have := ih (start+1) g hg
      simp only [List.length_cons]
      omega

theorem copyBlock_high (start base : ℕ) (as : List ℕ) (hb : start+as.length  ≤  base)
    (y : ℕ → ZMod 3) (k : ℕ) (hk : base  ≤  k) : rawRun (copyBlock start as) y k = y k := by
  apply rawRun_preserve
  intro g hg
  have := copyBlock_targets start as g hg
  omega

theorem copyBlock_valid (start base W : ℕ) (as : List ℕ)
    (hb : start+as.length  ≤  base) (hw : base  ≤  W)
    (ha : ∀ a ∈ as, base  ≤  a ∧ a < W) : ∀ g ∈ copyBlock start as, Valid W g := by
  induction as generalizing start with
  | nil => simp [copyBlock]
  | cons a as ih =>
    intro g hg
    have hfirst := ha a (by simp)
    simp only [copyBlock,List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp only [Valid,or_false]
      exact ⟨by simp only [List.length_cons] at hb; omega,Or.inr ⟨hfirst.2,by simp only [List.length_cons] at hb; omega,Or.inl trivial⟩⟩
    · exact ih (start+1) (by simp only [List.length_cons] at hb; omega) (fun a h => ha a (by simp [h])) g hg

theorem copyBlock_value (start base : ℕ) (as : List ℕ) (hb : start+as.length  ≤  base)
    (ha : ∀ a ∈ as, base  ≤  a) (y : ℕ → ZMod 3) (i : ℕ) (hi : i < as.length) :
    rawRun (copyBlock start as) y (start+i) = y (as.getD i 0)+y (start+i) := by
  induction as generalizing start y i with
  | nil => simp at hi
  | cons a as ih =>
    have hbase := ha a (by simp)
    have hb' : start+1+as.length  ≤  base := by simp only [List.length_cons] at hb; omega
    have htail : ∀ a ∈ as, base  ≤  a := fun a h => ha a (by simp [h])
    change rawRun (copyBlock (start+1) as) (rawStep (1,a,0,start) y) (start+i) = _
    cases i with
    | zero =>
      have hpres : rawRun (copyBlock (start+1) as) (rawStep (1,a,0,start) y) start =
          rawStep (1,a,0,start) y start := by
        apply rawRun_preserve
        intro g hg
        have := copyBlock_targets (start+1) as g hg
        omega
      simpa [rawStep,rawValue,add_comm] using hpres
    | succ i =>
      have hi' : i < as.length := by simpa using hi
      have heq : start+(i+1) = start+1+i := by omega
      rw [show start+Nat.succ i = start+1+i by omega,ih (start+1) hb' htail (rawStep (1,a,0,start) y) i hi']
      rw [List.getD_cons_succ]
      have hg : base  ≤  as.getD i 0 := by
        rw [List.getD_eq_getElem _ _ hi']
        exact htail _ (List.getElem_mem hi')
      simp only [rawStep,rawValue,show (1:ℕ) ≠ 0 by decide,if_false,if_true,
        Function.update_apply,show as.getD i 0 ≠ start by omega,
        show start+1+i ≠ start by omega,heq]


end F3Tools

namespace F3Search
open F3Tools F3SubsetSum

def base (n m : ℕ) := n*m+m+1
def compiled (n m : ℕ) := compile (n*m) (base n m) (code n m)
def gates (n m : ℕ) : List Raw := (compiled n m).1.1 ++ copyBlock (n*m) (compiled n m).2
noncomputable def circuit (n m : ℕ) : Circuit :=
  ⟨(compiled n m).1.2,(rawCircuit (compiled n m).1.2 (gates n m)).gates⟩

theorem compile_invariant (n m : ℕ) (h : Fin m → Fin n → ZMod 3) :
    StoreInv (n*m) (base n m) (compiled n m).1.2 (compiled n m).2
      (List.ofFn (fun i : Fin m => if i ∈ first n m h (bits m) then (1 : ZMod 3) else 0))
      (registers h) (rawRun (compiled n m).1.1 (registers h)) ∧
    (∀ g ∈ (compiled n m).1.1,Valid (compiled n m).1.2 g) := by
  have hi : StoreInv (n*m) (base n m) (base n m) [] [] (registers h) (registers h) := by
    refine ⟨by dsimp [base]; omega,le_rfl,by simp,fun _ _ => rfl,?_,?_,rfl⟩
    · simp [registers]
    · intro a ha
      simp [registers,show ¬a<n*m by dsimp [base] at ha; omega]
  have hc := compile_correct (n*m) (base n m) (code n m) (code_bounded n m)
    (([],base n m),[]) [] (registers h) hi (by simp)
  exact ⟨by simpa only [compiled,compile,code_eval] using hc.1,hc.2.1⟩

theorem compiled_shape (n m : ℕ) :
    (compiled n m).2.length = m ∧ base n m  ≤  (compiled n m).1.2 ∧
    (∀ a ∈ (compiled n m).2, base n m  ≤  a ∧ a < (compiled n m).1.2) := by
  have hc := (compile_invariant n m (fun _ _ => 0)).1
  have hl := congrArg List.length hc.values
  simp only [List.length_map,List.length_ofFn] at hl
  refine ⟨hl,hc.growing,fun a ha => ⟨?_,hc.indices a ha⟩⟩
  exact compile_stack_lower (n*m) (base n m) (code n m) (([],base n m),[]) le_rfl (by simp) a ha

theorem gates_valid (n m : ℕ) : ∀ g ∈ gates n m, Valid (compiled n m).1.2 g := by
  have hs := compiled_shape n m
  intro g hg
  rcases List.mem_append.mp hg with hpre | hpost
  · exact (compile_invariant n m (fun _ _ => 0)).2 g hpre
  · exact copyBlock_valid (n*m) (base n m) (compiled n m).1.2 (compiled n m).2
      (by rw [hs.1]; dsimp [base]; omega) hs.2.1 hs.2.2 g hpost

def finalRegisters (n m : ℕ) (h : Fin m → Fin n → ZMod 3) := rawRun (gates n m) (registers h)

theorem final_value (n m : ℕ) (h : Fin m → Fin n → ZMod 3) (i : Fin m) :
    finalRegisters n m h (n*m+i.val) = if i ∈ first n m h (bits m) then 1 else 0 := by
  have hs := compiled_shape n m
  have hc := (compile_invariant n m h).1
  have hi : i.val < (compiled n m).2.length := by rw [hs.1]; exact i.isLt
  unfold finalRegisters gates
  rw [rawRun_append,copyBlock_value (n*m) (base n m) (compiled n m).2
    (by rw [hs.1]; dsimp [base]; omega) (fun a ha => (hs.2.2 a ha).1) _ i.val hi]
  rw [hc.original (n*m+i.val) (by dsimp [base]; have := i.isLt; omega)]
  have hz : registers h (n*m+i.val) = 0 := by simp [registers]
  rw [hz,add_zero,List.getD_eq_getElem _ _ hi]
  have hv : ((compiled n m).2.map (rawRun (compiled n m).1.1 (registers h))).getD i.val 0 =
      if i ∈ first n m h (bits m) then (1 : ZMod 3) else 0 := by
    rw [hc.values]
    simp [List.getD_eq_getElem _ _ (show i.val < (List.ofFn (fun i : Fin m =>
      if i ∈ first n m h (bits m) then (1:ZMod 3) else 0)).length by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)] at hv
  simpa only [List.getElem_map] using hv

noncomputable def finalBasis (n m : ℕ) (h : Fin m → Fin n → ZMod 3) : QBasis (circuit n m).wires :=
  fun i => finalRegisters n m h i.val

theorem circuit_basis (n m : ℕ) (h : Fin m → Fin n → ZMod 3) :
    (circuit n m).run (basisKet (inputBasis n m (circuit n m).wires h)) = basisKet (finalBasis n m h) := by
  change (rawCircuit (compiled n m).1.2 (gates n m)).gates.foldl
    (fun φ g => applyGate g φ) (basisKet (fun i => registers h i.val)) = _
  rw [Reversible.basis,rawCircuit_forward _ _ (gates_valid n m)]
  rfl

open Classical in
theorem output_correct (n m : ℕ) (h : Fin m → Fin n → ZMod 3) :
    outSet n m (finalBasis n m h) = first n m h (bits m) := by
  have hs := (compiled_shape n m).2.1
  ext i
  have hi : n*m+i.val < (circuit n m).wires := by
    change n*m+i.val < (compiled n m).1.2
    dsimp [base] at hs
    have := i.isLt
    omega
  simp only [outSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hw,hv⟩
    change finalRegisters n m h (n*m+i.val) ≠ 0 at hv
    rw [final_value] at hv
    split_ifs at hv with hm
    · exact hm
    · exact False.elim (hv rfl)
  · intro hm
    refine ⟨hi,?_⟩
    change finalRegisters n m h (n*m+i.val) ≠ 0
    rw [final_value,if_pos hm]
    decide

open Classical in
theorem success_bound (n m : ℕ) : probSolvable n m  ≤  successProb n m (circuit n m) := by
  unfold probSolvable successProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Nat.cast_one,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro h hh
  by_cases hp : HasZeroSubsetSum h
  · rw [if_pos hp]
    have hsol := first_correct h hp
    have hout := output_correct n m h
    have hrun := circuit_basis n m h
    have hsum := Finset.single_le_sum (s := Finset.univ)
      (f := fun y : QBasis (circuit n m).wires =>
        if IsZeroSubsetSum h (outSet n m y) then
          Complex.normSq ((circuit n m).run (basisKet (inputBasis n m (circuit n m).wires h)) y) else 0)
      (fun y _ => by split_ifs; exact Complex.normSq_nonneg _; exact le_rfl) (Finset.mem_univ (finalBasis n m h))
    simpa [hout,hrun,hsol,basisKet] using hsum
  · rw [if_neg hp]
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl

end F3Search

-- Source: Solutions.T31.Interface

set_option maxHeartbeats 2000000
namespace F3Reduction
open F3SubsetSum F3Tools

/-- Matrix, noisy word, secret target, and zero scratch, in that order. -/
def decoderBasis (n m W : ℕ) (A : Matrix (Fin n) (Fin m) (ZMod 3))
    (b : Fin m → ZMod 3) (r : Fin n → ZMod 3) : QBasis W := fun w =>
  if hA : w.val < n*m then inputBasis n m W (fun i j => A j i) w
  else if hb : w.val < n*m+m then b ⟨w.val-n*m,by omega⟩
  else if hr : w.val < n*m+m+n then r ⟨w.val-(n*m+m),by omega⟩
  else 0

/-- Exact coherent subtraction, with zero scratch restored, on every target value. -/
def CleanDecoder (Dec : DecoderFn 3) (n m : ℕ) (R : Circuit) : Prop :=
  n*m+m+n  ≤  R.wires ∧ ∀ A b r,
    R.run (basisKet (decoderBasis n m R.wires A b r)) =
      basisKet (decoderBasis n m R.wires A b (fun j => r j - Dec n m A (fun i => b i-1) j))

def mapGate {W V : ℕ} (f : Fin W ↪ Fin V) : Gate W → Gate V
  | .x i => .x (f i)
  | .xInv i => .xInv (f i)
  | .csum i j h => .csum (f i) (f j) (fun he => h (f.injective he))
  | .csumInv i j h => .csumInv (f i) (f j) (fun he => h (f.injective he))
  | .ccmul i j k h₁ h₂ h₃ => .ccmul (f i) (f j) (f k)
      (fun he => h₁ (f.injective he)) (fun he => h₂ (f.injective he)) (fun he => h₃ (f.injective he))
  | .ccmulInv i j k h₁ h₂ h₃ => .ccmulInv (f i) (f j) (f k)
      (fun he => h₁ (f.injective he)) (fun he => h₂ (f.injective he)) (fun he => h₃ (f.injective he))
  | .fourier i => .fourier (f i)
  | .fourierInv i => .fourierInv (f i)
  | .p i => .p (f i)
  | .pInv i => .pInv (f i)
  | .u i => .u (f i)
  | .uInv i => .uInv (f i)

def single (W tag i : ℕ) : List (Gate W) :=
  if hi : i < W then
    [if tag = 0 then .fourier ⟨i,hi⟩ else if tag = 1 then .p ⟨i,hi⟩ else .uInv ⟨i,hi⟩]
  else []

/-- The column transformation from subset sum to signed sum. -/
def transform (n m tag : ℕ) : List Raw :=
  (List.range (m-1)).flatMap (fun i =>
    (List.range n).map (fun j => (tag,n*i+j,0,n*(m-1)+j)))

/-- Populate each not-state using a fresh uniform secret. -/
def notStates (n m : ℕ) : List Raw :=
  (List.range m).flatMap (fun i =>
    (List.range n).map (fun j => (3,n*i+j,n*m+m+j,n*m+i)))

/-- The output set records nonzero entries, so subtracting the anchor gives the
relative-sign subset directly. The anchor remains nonzero on every signed solution. -/
def postprocess (n m : ℕ) : List Raw :=
  (List.range (m-1)).map (fun i => (2,n*m+(m-1),0,n*m+i))

/-- Quantum preparation, coherent erasure and tensor U-inverse on the decoder's wires. -/
noncomputable abbrev coreCircuit (n m : ℕ) (R : Circuit) : Circuit :=
  ⟨R.wires,
    (List.range n).flatMap (fun j => single R.wires 0 (n*m+m+j)) ++
    (List.range m).flatMap (fun i => single R.wires 1 (n*m+i)) ++
    (notStates n m).flatMap (fun g => (rawRev R.wires g).gates) ++
    R.gates ++
    (List.range m).flatMap (fun i => single R.wires 2 (n*m+i))⟩

/-- One concrete circuit, shared by the quantum proof and the uniform generator. -/
noncomputable abbrev wrap (n m : ℕ) (R : Circuit) : Circuit :=
  ⟨R.wires,if m = 0 then [] else
    (transform n m 2).flatMap (fun g => (rawRev R.wires g).gates) ++
    (coreCircuit n m R).gates ++
    (postprocess n m).flatMap (fun g => (rawRev R.wires g).gates)⟩

/-- Compiler contract, including the exact unary generator input and polynomial resources. -/
def Compiled (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn 3)
    (G : Turing.TM2ComputableAux Bool Bool) (R : ℕ → ℕ → ℕ → Circuit) (C : ℝ) : Prop :=
  0 < C ∧ ∀ n m T, ComputesWithin M Dec n m T →
    CleanDecoder Dec n m (R n m T) ∧
    HMBinPacking.OutputsWithin G (unaryD n++unaryD m++unary T) (encodeCircuit (R n m T))
      ⌊C * ((n+m+T+1 : ℕ) : ℝ)^C⌋₊ ∧
    ((R n m T).gates.length : ℝ)  ≤  C*((n+m+T+1 : ℕ) : ℝ)^C ∧
    ((R n m T).wires : ℝ)  ≤  C*((n+m+T+1 : ℕ) : ℝ)^C

/-- The existing theorem follows from the three local proof obligations. -/
theorem root_from_dependencies
    (compiler : ∀ M Dec, ∃ G R C, Compiled M Dec G R C)
    (quantum : ∀ Dec n m R, CleanDecoder Dec n m R →
      1-2*avgError Dec n m-(3:ℝ)^n*(2/3:ℝ)^m  ≤  successProb n m (wrap n m R))
    (assembly : ∀ M Dec G R C, Compiled M Dec G R C →
      ∃ G' C', 0 < C' ∧ ∀ n m T, ComputesWithin M Dec n m T →
        HMBinPacking.OutputsWithin G' (unaryD n++unaryD m++unary T)
          (encodeCircuit (wrap n m (R n m T))) ⌊C'*((n+m+T+1:ℕ):ℝ)^C'⌋₊ ∧
        n*m+m  ≤  (wrap n m (R n m T)).wires ∧
        ((wrap n m (R n m T)).gates.length : ℝ)  ≤  C'*((n+m+T+1:ℕ):ℝ)^C' ∧
        ((wrap n m (R n m T)).wires : ℝ)  ≤  C'*((n+m+T+1:ℕ):ℝ)^C')
    (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn 3) :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → ℕ → Circuit) (C : ℝ), 0 < C ∧
      ∀ n m T : ℕ, ComputesWithin M Dec n m T →
        HMBinPacking.OutputsWithin G (unaryD n ++ unaryD m ++ unary T) (encodeCircuit (circ n m T))
            ⌊C * ((n + m + T + 1 : ℕ) : ℝ) ^ C⌋₊ ∧
          n * m + m  ≤  (circ n m T).wires ∧
          ((circ n m T).gates.length : ℝ)  ≤  C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          ((circ n m T).wires : ℝ)  ≤  C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          1 - 2 * avgError Dec n m - (3 : ℝ) ^ n * (2 / 3 : ℝ) ^ m  ≤ 
            successProb n m (circ n m T) := by
  obtain ⟨G,R,C,hc⟩ := compiler M Dec
  obtain ⟨G',C',hp,ha⟩ := assembly M Dec G R C hc
  refine ⟨G',fun n m T => wrap n m (R n m T),C',hp,?_⟩
  intro n m T ht
  obtain ⟨ho,hw,hg,hs⟩ := ha n m T ht
  exact ⟨ho,hw,hg,hs,quantum Dec n m (R n m T) ((hc.2 n m T ht).1)⟩

end F3Reduction

-- Source: Solutions.T31.Qutrit

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum

lemma omega_root : IsPrimitiveRoot omega 3 := Complex.isPrimitiveRoot_exp 3 (by decide)
lemma omega_cube : omega^3 = 1 := omega_root.pow_eq_one
lemma omega_ne_one : omega ≠ 1 := omega_root.ne_one (by decide)
lemma omega_ne_zero : omega ≠ 0 := omega_root.ne_zero (by decide)

lemma omega_quadratic : omega^2+omega+1 = 0 := by
  have h : (omega-1)*(omega^2+omega+1) = 0 := by
    calc
      _ = omega^3-1 := by ring
      _ = 0 := by rw [omega_cube]; ring
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr omega_ne_one)

lemma omega_square : omega^2 = -omega-1 := by linear_combination omega_quadratic

lemma omega_four : omega^4 = omega := by rw [show (4:ℕ) = 3+1 by decide,pow_add,omega_cube]; simp

lemma omega_normSq : Complex.normSq omega = 1 := by
  have hn := omega_root.norm'_eq_one (by decide)
  rw [Complex.normSq_eq_norm_sq,hn]
  norm_num

lemma omega_conj : star omega = omega^2 := by
  apply mul_left_cancel₀ omega_ne_zero
  change omega * (starRingEnd ℂ) omega = omega*omega^2
  rw [Complex.mul_conj,omega_normSq]
  rw [show omega*omega^2 = omega^3 by ring,omega_cube]
  rfl

@[simp] lemma zadd_0_0 : (0 : ZMod 3) + 0 = 0 := by decide
@[simp] lemma zadd_0_1 : (0 : ZMod 3) + 1 = 1 := by decide
@[simp] lemma zadd_0_2 : (0 : ZMod 3) + 2 = 2 := by decide
@[simp] lemma zadd_1_0 : (1 : ZMod 3) + 0 = 1 := by decide
@[simp] lemma zadd_1_1 : (1 : ZMod 3) + 1 = 2 := by decide
@[simp] lemma zadd_1_2 : (1 : ZMod 3) + 2 = 0 := by decide
@[simp] lemma zadd_2_0 : (2 : ZMod 3) + 0 = 2 := by decide
@[simp] lemma zadd_2_1 : (2 : ZMod 3) + 1 = 0 := by decide
@[simp] lemma zadd_2_2 : (2 : ZMod 3) + 2 = 1 := by decide
@[simp] lemma zsub_0_0 : (0 : ZMod 3) - 0 = 0 := by decide
@[simp] lemma zsub_0_1 : (0 : ZMod 3) - 1 = 2 := by decide
@[simp] lemma zsub_0_2 : (0 : ZMod 3) - 2 = 1 := by decide
@[simp] lemma zsub_1_0 : (1 : ZMod 3) - 0 = 1 := by decide
@[simp] lemma zsub_1_1 : (1 : ZMod 3) - 1 = 0 := by decide
@[simp] lemma zsub_1_2 : (1 : ZMod 3) - 2 = 2 := by decide
@[simp] lemma zsub_2_0 : (2 : ZMod 3) - 0 = 2 := by decide
@[simp] lemma zsub_2_1 : (2 : ZMod 3) - 1 = 1 := by decide
@[simp] lemma zsub_2_2 : (2 : ZMod 3) - 2 = 0 := by decide
@[simp] lemma zmul_0_0 : (0 : ZMod 3) * 0 = 0 := by decide
@[simp] lemma zmul_0_1 : (0 : ZMod 3) * 1 = 0 := by decide
@[simp] lemma zmul_0_2 : (0 : ZMod 3) * 2 = 0 := by decide
@[simp] lemma zmul_1_0 : (1 : ZMod 3) * 0 = 0 := by decide
@[simp] lemma zmul_1_1 : (1 : ZMod 3) * 1 = 1 := by decide
@[simp] lemma zmul_1_2 : (1 : ZMod 3) * 2 = 2 := by decide
@[simp] lemma zmul_2_0 : (2 : ZMod 3) * 0 = 0 := by decide
@[simp] lemma zmul_2_1 : (2 : ZMod 3) * 1 = 2 := by decide
@[simp] lemma zmul_2_2 : (2 : ZMod 3) * 2 = 1 := by decide
@[simp] lemma zneg_0 : -(0 : ZMod 3) = 0 := by decide
@[simp] lemma zneg_1 : -(1 : ZMod 3) = 2 := by decide
@[simp] lemma zneg_2 : -(2 : ZMod 3) = 1 := by decide
@[simp] lemma zne_0_1 : (0 : ZMod 3) ≠ 1 := by decide
@[simp] lemma zne_0_2 : (0 : ZMod 3) ≠ 2 := by decide
@[simp] lemma zne_1_2 : (1 : ZMod 3) ≠ 2 := by decide
@[simp] lemma zne_1_0 : (1 : ZMod 3) ≠ 0 := by decide
@[simp] lemma zne_2_0 : (2 : ZMod 3) ≠ 0 := by decide
@[simp] lemma zne_2_1 : (2 : ZMod 3) ≠ 1 := by decide

lemma omega_five : omega^5 = omega^2 := by rw [show (5:ℕ) = 3+2 by decide,pow_add,omega_cube]; simp

lemma omega_six : omega^6 = 1 := by rw [show (6:ℕ) = 3*2 by decide,pow_mul,omega_cube]; norm_num

noncomputable def phase (a : ZMod 3) : ℂ := omega^a.val

@[simp] lemma phase_zero : phase 0 = 1 := rfl
@[simp] lemma phase_one : phase 1 = omega := by simp [phase,ZMod.val]
@[simp] lemma phase_two : phase 2 = omega^2 := by simp [phase,ZMod.val]

lemma cases_three (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have h : ∀ a : ZMod 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  exact h a

lemma phase_add (a b : ZMod 3) : phase (a+b) = phase a*phase b := by
  rcases cases_three a with rfl | rfl | rfl <;> rcases cases_three b with rfl | rfl | rfl
  all_goals simp only [zero_add,add_zero,phase_zero,phase_one,phase_two,
    show (1+1:ZMod 3) = 2 by decide,show (1+2:ZMod 3) = 0 by decide,
    show (2+1:ZMod 3) = 0 by decide,show (2+2:ZMod 3) = 1 by decide]
  all_goals ring_nf <;> simp [omega_cube,omega_four]

lemma phase_neg (a : ZMod 3) : phase (-a) = star (phase a) := by
  rcases cases_three a with rfl | rfl | rfl
  all_goals simp [show -(1:ZMod 3) = 2 by decide,show -(2:ZMod 3) = 1 by decide,
    omega_conj,star_pow,phase_zero,phase_one,phase_two]
  simpa only [← pow_mul] using omega_four.symm

lemma phase_normSq (a : ZMod 3) : Complex.normSq (phase a) = 1 := by
  simp [phase,map_pow,omega_normSq]

lemma sum_three (f : ZMod 3 → ℂ) : ∑ a : ZMod 3, f a = f 0+f 1+f 2 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0,1,2} := by decide
  rw [hu]
  norm_num [Finset.sum_insert,Finset.sum_singleton,show (0:ZMod 3) ≠ 1 by decide,
    show (0:ZMod 3) ≠ 2 by decide,show (1:ZMod 3) ≠ 2 by decide]
  ring

lemma phase_sum (a : ZMod 3) : ∑ b : ZMod 3, phase (a*b) = if a = 0 then 3 else 0 := by
  rw [sum_three]
  rcases cases_three a with rfl | rfl | rfl
  all_goals simp only [zero_mul,mul_zero,one_mul,mul_one,phase_zero,phase_one,phase_two,
    show (2*2:ZMod 3) = 1 by decide,show (1:ZMod 3) ≠ 0 by decide,
    show (2:ZMod 3) ≠ 0 by decide,ite_true,ite_false]
  · norm_num
  all_goals linear_combination omega_quadratic

end F3Reduction

-- Source: Solutions.T31.Energy

set_option maxHeartbeats 1000000
namespace F3Reduction
open scoped BigOperators

noncomputable def energy {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (v i)

noncomputable def mass {ι : Type} [Fintype ι] (P : ι → Prop) (v : ι → ℂ) : ℝ := by
  classical
  exact ∑ i, if P i then Complex.normSq (v i) else 0

lemma energy_nonneg {ι : Type} [Fintype ι] (v : ι → ℂ) : 0  ≤  energy v :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

lemma mass_nonneg {ι : Type} [Fintype ι] (P : ι → Prop) (v : ι → ℂ) : 0  ≤  mass P v := by
  classical
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact Complex.normSq_nonneg _
  · exact le_rfl

lemma mass_le_energy {ι : Type} [Fintype ι] (P : ι → Prop) (v : ι → ℂ) : mass P v  ≤  energy v := by
  classical
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · exact le_rfl
  · exact Complex.normSq_nonneg _

lemma mass_complement {ι : Type} [Fintype ι] (P : ι → Prop) (v : ι → ℂ) :
    mass P v+mass (fun i => ¬P i) v = energy v := by
  classical
  rw [mass,mass,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : P i <;> simp [h]

/-- An ideal component supported on valid outcomes can be removed when bounding failure. -/
lemma success_of_ideal {ι κ : Type} [Fintype ι] [Fintype κ]
    (T : (ι → ℂ) → (κ → ℂ))
    (hadd : ∀ u v, T (u+v) = T u+T v)
    (hiso : ∀ u, energy (T u) = energy u)
    (P : κ → Prop) (ideal err : ι → ℂ)
    (hsupport : ∀ i, ¬P i → T ideal i = 0)
    (hnorm : energy (ideal+err) = 1) :
    1-energy err  ≤  mass P (T (ideal+err)) := by
  classical
  have hf : mass (fun i => ¬P i) (T (ideal+err)) = mass (fun i => ¬P i) (T err) := by
    unfold mass
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : P i
    · simp [hp]
    · simp [hp,hadd,hsupport i hp]
  have htotal := mass_complement P (T (ideal+err))
  have hle := mass_le_energy (fun i => ¬P i) (T err)
  rw [hiso,hnorm] at htotal
  rw [hf] at htotal
  rw [hiso] at hle
  linarith

noncomputable def ip {ι : Type} [Fintype ι] (u v : ι → ℂ) : ℂ := ∑ i, star (u i)*v i

lemma ip_self {ι : Type} [Fintype ι] (v : ι → ℂ) : ip v v = (energy v : ℂ) := by
  simp only [ip,energy,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact Complex.normSq_eq_conj_mul_self.symm

noncomputable def matApply {ι κ : Type} [Fintype ι] (M : κ → ι → ℂ) (v : ι → ℂ) : κ → ℂ :=
  fun j => ∑ i, M j i*v i

lemma matApply_add {ι κ : Type} [Fintype ι] (M : κ → ι → ℂ) (u v : ι → ℂ) :
    matApply M (u+v) = matApply M u+matApply M v := by
  funext j
  simp [matApply,mul_add,Finset.sum_add_distrib]

lemma matApply_ip {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℂ) (u v : ι → ℂ) :
    ip (matApply M u) (matApply M v) =
      ∑ a, ∑ b, star (u a)*v b*(∑ j, star (M j a)*M j b) := by
  simp only [ip,matApply,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro j hj
  ring

open Classical in
lemma matApply_isometry {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : κ → ι → ℂ)
    (hM : ∀ a b, ∑ j, star (M j a)*M j b = if a = b then 1 else 0)
    (v : ι → ℂ) : energy (matApply M v) = energy v := by
  classical
  have h := matApply_ip M v v
  simp only [hM] at h
  have he : ip (matApply M v) (matApply M v) = ip v v := by
    simpa [ip] using h
  rw [ip_self,ip_self] at he
  exact_mod_cast he

end F3Reduction

-- Source: Solutions.T31.Matrices

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum

lemma sqrt_cast_sq (r : ℝ) (hr : 0  ≤  r) : (Real.sqrt r : ℂ)^2 = r := by
  norm_cast
  exact Real.sq_sqrt hr

lemma sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 2)

lemma sqrt3_ne : (Real.sqrt 3 : ℂ) ≠ 0 := by
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ) < 3)

noncomputable def trine (a b : ZMod 3) : ℂ :=
  if b = 0 then 0 else phase (a*b)/(Real.sqrt 2 : ℂ)

noncomputable def notState (a b : ZMod 3) : ℂ :=
  if b = a+1 then 1/(Real.sqrt 2 : ℂ) else if b = a-1 then -1/(Real.sqrt 2 : ℂ) else 0

lemma fourier_orthogonal (a b : ZMod 3) :
    ∑ j : ZMod 3, star (fourierMat j a)*fourierMat j b = if a = b then 1 else 0 := by
  rcases cases_three a with rfl | rfl | rfl <;> rcases cases_three b with rfl | rfl | rfl
  all_goals rw [sum_three]
  all_goals norm_num [fourierMat,ZMod.val,Fin.mul_def,omega_conj,star_div,star_pow]
  all_goals field_simp [sqrt3_ne]
  all_goals try rw [sqrt_cast_sq 3 (by norm_num)]
  all_goals try ring_nf
  all_goals try simp only [omega_cube,omega_four,omega_six]
  all_goals norm_num [omega_five]
  all_goals linear_combination omega_quadratic

lemma p_orthogonal (a b : ZMod 3) :
    ∑ j : ZMod 3, star (pMat j a)*pMat j b = if a = b then 1 else 0 := by
  rcases cases_three a with rfl | rfl | rfl <;> rcases cases_three b with rfl | rfl | rfl
  all_goals rw [sum_three]
  all_goals norm_num [pMat,star_div]
  all_goals try field_simp [sqrt2_ne]
  all_goals try rw [sqrt_cast_sq 2 (by norm_num)]
  all_goals norm_num
  all_goals ring

lemma uMat_phase (b a : ZMod 3) : uMat b a =
    if a = 0 then 1/(Real.sqrt 3 : ℂ)
    else if a = 1 then (phase (-(b-1))-phase (-(b+1)))/3
    else (phase (b-1)-phase (b+1))/3 := rfl

lemma u_orthogonal (a b : ZMod 3) :
    ∑ j : ZMod 3, star (uMat j a)*uMat j b = if a = b then 1 else 0 := by
  rcases cases_three a with rfl | rfl | rfl <;> rcases cases_three b with rfl | rfl | rfl
  all_goals rw [sum_three]
  all_goals simp [uMat_phase,omega_conj,star_div,star_pow]
  all_goals try field_simp [sqrt3_ne]
  all_goals try rw [sqrt_cast_sq 3 (by norm_num)]
  all_goals try ring_nf
  all_goals try norm_num [omega_cube,omega_four,omega_five,omega_six,omega_square]
  all_goals ring

lemma u_trine (a b : ZMod 3) :
    matApply uMat (trine a) b = notState a b := by
  rcases cases_three a with rfl | rfl | rfl <;> rcases cases_three b with rfl | rfl | rfl
  all_goals simp only [matApply,sum_three]
  all_goals simp [uMat_phase,trine,notState]
  all_goals try field_simp [sqrt2_ne,sqrt3_ne]
  all_goals try ring_nf
  all_goals try norm_num [omega_cube,omega_four,omega_five,omega_six,omega_square]
  all_goals ring

lemma adjoint_orthogonal (M : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hM : ∀ a b, ∑ j, star (M j a)*M j b = if a = b then 1 else 0) :
    ∀ a b, ∑ j, star (M.conjTranspose j a)*M.conjTranspose j b = if a = b then 1 else 0 := by
  have hl : M.conjTranspose*M = 1 := by
    ext a b
    simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using hM a b
  have hr : M*M.conjTranspose = 1 := mul_eq_one_comm.mp hl
  intro a b
  have he := congrFun (congrFun hr a) b
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,mul_comm] using he

lemma adjoint_cancel (M : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hM : ∀ a b, ∑ j, star (M j a)*M j b = if a = b then 1 else 0) (v : ZMod 3 → ℂ) :
    matApply M.conjTranspose (matApply M v) = v := by
  funext a
  simp only [matApply,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [Matrix.conjTranspose_apply,← mul_assoc,← Finset.sum_mul]
  change (∑ b, (∑ j, star (M j a)*M j b)*v b) = v a
  simp only [hM]
  simp

lemma uInv_not (a b : ZMod 3) : matApply uMat.conjTranspose (notState a) b = trine a b := by
  have hu : notState a = matApply uMat (trine a) := funext (fun b => (u_trine a b).symm)
  rw [hu,adjoint_cancel uMat u_orthogonal]

end F3Reduction

-- Source: Solutions.T31.Wire

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum

abbrev Rest (W : ℕ) (i : Fin W) := {j : Fin W // j ≠ i} → ZMod 3

def splitWire {W : ℕ} (i : Fin W) : QBasis W ≃ ZMod 3 × Rest W i := Equiv.funSplitAt i (ZMod 3)

lemma splitWire_at {W : ℕ} (i : Fin W) (a : ZMod 3) (r : Rest W i) :
    (splitWire i).symm (a,r) i = a := by
  have h := congrArg Prod.fst ((splitWire i).apply_symm_apply (a,r))
  exact h

lemma splitWire_update {W : ℕ} (i : Fin W) (a b : ZMod 3) (r : Rest W i) :
    Function.update ((splitWire i).symm (a,r)) i b = (splitWire i).symm (b,r) := by
  apply (splitWire i).injective
  rw [(splitWire i).apply_symm_apply]
  apply Prod.ext
  · change Function.update ((splitWire i).symm (a,r)) i b i = _
    simp [splitWire_at]
  · funext j
    change Function.update ((splitWire i).symm (a,r)) i b j.val = r j
    rw [Function.update_of_ne j.property]
    exact congrFun (congrArg Prod.snd ((splitWire i).apply_symm_apply (a,r))) j

lemma energy_splitWire {W : ℕ} (i : Fin W) (ψ : Ket W) :
    energy ψ = ∑ r : Rest W i, ∑ a : ZMod 3, Complex.normSq (ψ ((splitWire i).symm (a,r))) := by
  unfold energy
  have h := Fintype.sum_equiv (splitWire i)
    (fun y => Complex.normSq (ψ y))
    (fun p => Complex.normSq (ψ ((splitWire i).symm p))) (fun _ => by simp)
  rw [h,Fintype.sum_prod_type,Finset.sum_comm]

open Classical in
lemma single_isometry {W : ℕ} (i : Fin W) (M : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hM : ∀ a b, ∑ j, star (M j a)*M j b = if a = b then 1 else 0) (ψ : Ket W) :
    energy (applySingle M i ψ) = energy ψ := by
  rw [energy_splitWire i,energy_splitWire i]
  apply Finset.sum_congr rfl
  intro r hr
  have hpoint (a : ZMod 3) :
      applySingle M i ψ ((splitWire i).symm (a,r)) =
        matApply M (fun b => ψ ((splitWire i).symm (b,r))) a := by
    simp only [applySingle,splitWire_at,splitWire_update,matApply]
  simp_rw [hpoint]
  apply matApply_isometry M
  intro a b
  by_cases h : a = b
  · simpa only [if_pos h] using hM a b
  · simpa only [if_neg h] using hM a b

lemma applySingle_add {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (i : Fin W) (ψ φ : Ket W) :
    applySingle M i (ψ+φ) = applySingle M i ψ+applySingle M i φ := by
  funext y
  simp [applySingle,mul_add,Finset.sum_add_distrib]

lemma applySingle_smul {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (i : Fin W) (c : ℂ) (ψ : Ket W) :
    applySingle M i (c • ψ) = c • applySingle M i ψ := by
  funext y
  simp only [applySingle,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma applyGate_add {W : ℕ} (g : Gate W) (ψ φ : Ket W) :
    applyGate g (ψ+φ) = applyGate g ψ+applyGate g φ := by
  cases g <;> first | rfl | apply applySingle_add

lemma applyGate_smul {W : ℕ} (g : Gate W) (c : ℂ) (ψ : Ket W) :
    applyGate g (c • ψ) = c • applyGate g ψ := by
  cases g <;> first | rfl | apply applySingle_smul

noncomputable def gateLinear {W : ℕ} (g : Gate W) : Ket W →ₗ[ℂ] Ket W where
  toFun := applyGate g
  map_add' := applyGate_add g
  map_smul' := applyGate_smul g

noncomputable def circuitLinear (C : Circuit) : Ket C.wires →ₗ[ℂ] Ket C.wires :=
  C.gates.foldl (fun T g => (gateLinear g).comp T) LinearMap.id

lemma circuitLinear_apply (C : Circuit) (ψ : Ket C.wires) : circuitLinear C ψ = C.run ψ := by
  unfold circuitLinear Circuit.run
  generalize C.gates = gs
  have h : ∀ (T : Ket C.wires →ₗ[ℂ] Ket C.wires),
      (gs.foldl (fun T g => (gateLinear g).comp T) T) ψ =
        gs.foldl (fun φ g => applyGate g φ) (T ψ) := by
    induction gs with
    | nil => intro T; rfl
    | cons g gs ih => intro T; exact ih _
  exact h _

lemma run_add (C : Circuit) (ψ φ : Ket C.wires) : C.run (ψ+φ) = C.run ψ+C.run φ := by
  rw [← circuitLinear_apply,← circuitLinear_apply,← circuitLinear_apply]
  exact (circuitLinear C).map_add ψ φ

lemma run_sum {ι : Type} (C : Circuit) (s : Finset ι) (ψ : ι → Ket C.wires) :
    C.run (∑ a ∈ s, ψ a) = ∑ a ∈ s, C.run (ψ a) := by
  simp_rw [← circuitLinear_apply]
  exact map_sum (circuitLinear C) _ _

end F3Reduction

-- Source: Solutions.T31.Unitary

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum F3Tools

lemma permutation_energy {ι : Type} [Fintype ι] (e : ι ≃ ι) (v : ι → ℂ) :
    energy (v ∘ e) = energy v := by
  unfold energy
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma reversible_energy {W : ℕ} (A : Reversible W) (ψ : Ket W) :
    energy (A.gates.foldl (fun φ g => applyGate g φ) ψ) = energy ψ := by
  rw [A.action]
  exact permutation_energy ⟨A.backward,A.forward,A.right_inv,A.left_inv⟩ ψ

lemma gate_energy {W : ℕ} (g : Gate W) (ψ : Ket W) : energy (applyGate g ψ) = energy ψ := by
  cases g with
  | x i => exact reversible_energy (shift i) ψ
  | xInv i => exact reversible_energy (unshift i) ψ
  | csum i j hij => exact reversible_energy (add i j hij) ψ
  | csumInv i j hij => exact reversible_energy (subtract i j hij) ψ
  | ccmul i j k hij hik hjk => exact reversible_energy (mulAdd i j k hij hik hjk) ψ
  | ccmulInv i j k hij hik hjk => exact reversible_energy (mulSubtract i j k hij hik hjk) ψ
  | fourier i => exact single_isometry i fourierMat fourier_orthogonal ψ
  | fourierInv i => exact single_isometry i fourierMat.conjTranspose (adjoint_orthogonal _ fourier_orthogonal) ψ
  | p i => exact single_isometry i pMat p_orthogonal ψ
  | pInv i => exact single_isometry i pMat.conjTranspose (adjoint_orthogonal _ p_orthogonal) ψ
  | u i => exact single_isometry i uMat u_orthogonal ψ
  | uInv i => exact single_isometry i uMat.conjTranspose (adjoint_orthogonal _ u_orthogonal) ψ

lemma run_energy (C : Circuit) (ψ : Ket C.wires) : energy (C.run ψ) = energy ψ := by
  unfold Circuit.run
  generalize C.gates = gs
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih => exact (ih (applyGate g ψ)).trans (gate_energy g ψ)

lemma basis_energy {W : ℕ} (y : QBasis W) : energy (basisKet y) = 1 := by
  classical
  simp [energy,basisKet]

end F3Reduction

-- Source: Solutions.T31.Inverse

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum

def inverseGate {W : ℕ} : Gate W → Gate W
  | .x i => .xInv i
  | .xInv i => .x i
  | .csum i j h => .csumInv i j h
  | .csumInv i j h => .csum i j h
  | .ccmul i j k h₁ h₂ h₃ => .ccmulInv i j k h₁ h₂ h₃
  | .ccmulInv i j k h₁ h₂ h₃ => .ccmul i j k h₁ h₂ h₃
  | .fourier i => .fourierInv i
  | .fourierInv i => .fourier i
  | .p i => .pInv i
  | .pInv i => .p i
  | .u i => .uInv i
  | .uInv i => .u i

lemma inverseGate_involution {W : ℕ} (g : Gate W) : inverseGate (inverseGate g) = g := by
  cases g <;> rfl

lemma single_comp {W : ℕ} (M N : Matrix (ZMod 3) (ZMod 3) ℂ) (i : Fin W) (ψ : Ket W) :
    applySingle M i (applySingle N i ψ) = applySingle (M*N) i ψ := by
  funext y
  simp only [applySingle,Function.update_self,Function.update_idem,Finset.mul_sum,
    Matrix.mul_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma single_identity {W : ℕ} (i : Fin W) (ψ : Ket W) : applySingle 1 i ψ = ψ := by
  funext y
  simp [applySingle,Matrix.one_apply]

lemma matrix_adjoint_mul (M : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hM : ∀ a b, ∑ j, star (M j a)*M j b = if a = b then 1 else 0) :
    M.conjTranspose*M = 1 := by
  ext a b
  simpa [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using hM a b

lemma single_adjoint_cancel {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ)
    (hM : ∀ a b, ∑ j, star (M j a)*M j b = if a = b then 1 else 0)
    (i : Fin W) (ψ : Ket W) :
    applySingle M.conjTranspose i (applySingle M i ψ) = ψ := by
  rw [single_comp,matrix_adjoint_mul M hM,single_identity]

lemma gate_inverse_left {W : ℕ} (g : Gate W) (ψ : Ket W) :
    applyGate (inverseGate g) (applyGate g ψ) = ψ := by
  cases g with
  | x i => funext y; simp [inverseGate,applyGate]
  | xInv i => funext y; simp [inverseGate,applyGate]
  | csum i j h => funext y; simp [inverseGate,applyGate,h]
  | csumInv i j h => funext y; simp [inverseGate,applyGate,h]
  | ccmul i j k h₁ h₂ h₃ => funext y; simp [inverseGate,applyGate,h₂,h₃]
  | ccmulInv i j k h₁ h₂ h₃ => funext y; simp [inverseGate,applyGate,h₂,h₃]
  | fourier i => exact single_adjoint_cancel fourierMat fourier_orthogonal i ψ
  | fourierInv i =>
    simpa only [inverseGate,applyGate,Matrix.conjTranspose_conjTranspose] using
      single_adjoint_cancel fourierMat.conjTranspose (adjoint_orthogonal _ fourier_orthogonal) i ψ
  | p i => exact single_adjoint_cancel pMat p_orthogonal i ψ
  | pInv i =>
    simpa only [inverseGate,applyGate,Matrix.conjTranspose_conjTranspose] using
      single_adjoint_cancel pMat.conjTranspose (adjoint_orthogonal _ p_orthogonal) i ψ
  | u i => exact single_adjoint_cancel uMat u_orthogonal i ψ
  | uInv i =>
    simpa only [inverseGate,applyGate,Matrix.conjTranspose_conjTranspose] using
      single_adjoint_cancel uMat.conjTranspose (adjoint_orthogonal _ u_orthogonal) i ψ

lemma gate_inverse_right {W : ℕ} (g : Gate W) (ψ : Ket W) :
    applyGate g (applyGate (inverseGate g) ψ) = ψ := by
  simpa only [inverseGate_involution] using gate_inverse_left (inverseGate g) ψ

noncomputable abbrev inverseCircuit (C : Circuit) : Circuit :=
  ⟨C.wires,C.gates.reverse.map inverseGate⟩

lemma inverse_run {W : ℕ} (gs : List (Gate W)) (ψ : Ket W) :
    (gs.reverse.map inverseGate).foldl (fun φ g => applyGate g φ)
      (gs.foldl (fun φ g => applyGate g φ) ψ) = ψ := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.reverse_cons,List.map_append,List.map_cons,List.map_nil,List.foldl_append,
      List.foldl_cons,List.foldl_nil]
    rw [ih,gate_inverse_left]

lemma inverseCircuit_run (C : Circuit) (ψ : Ket C.wires) : (inverseCircuit C).run (C.run ψ) = ψ := by
  exact inverse_run C.gates ψ

end F3Reduction

-- Source: Solutions.T31.BasisAction

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

def sameOutside {W : ℕ} (i : Fin W) (y z : QBasis W) : Prop := ∀ j, j ≠ i → y j = z j

lemma update_basis_eq {W : ℕ} (i : Fin W) (y z : QBasis W) (a : ZMod 3) :
    Function.update z i a = y ↔ a = y i ∧ sameOutside i y z := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · have hi := congrFun h i
      simpa only [Function.update_self] using hi
    · intro j hj
      have hh := congrFun h j
      simpa only [Function.update_of_ne hj] using hh.symm
  · rintro ⟨ha,hout⟩
    funext j
    by_cases hj : j = i
    · subst j; simp [ha]
    · simp only [Function.update_of_ne hj]
      exact (hout j hj).symm

lemma basis_update_eq {W : ℕ} (i : Fin W) (y z : QBasis W) (a : ZMod 3) :
    z = Function.update y i a ↔ a = z i ∧ sameOutside i y z := by
  rw [eq_comm,update_basis_eq]
  constructor
  · rintro ⟨h,hout⟩
    exact ⟨h,fun j hj => (hout j hj).symm⟩
  · rintro ⟨h,hout⟩
    exact ⟨h,fun j hj => (hout j hj).symm⟩

lemma applySingle_basis {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (i : Fin W) (y : QBasis W) :
    applySingle M i (basisKet y) =
      ∑ a : ZMod 3, M a (y i) • basisKet (Function.update y i a) := by
  funext z
  simp only [applySingle,basisKet,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    update_basis_eq,basis_update_eq,mul_ite,mul_one,mul_zero]
  by_cases h : sameOutside i y z <;> simp [h]

lemma gate_basis {W : ℕ} (g : Gate W) (y : QBasis W) :
    applyGate g (basisKet y) =
      ∑ z : QBasis W, applyGate g (basisKet y) z • basisKet z := by
  funext z
  simp [basisKet]

/-- Reconstruct a finite state from its computational-basis amplitudes. -/
lemma basis_expansion {W : ℕ} (ψ : Ket W) : ψ = ∑ y : QBasis W, ψ y • basisKet y := by
  funext y
  simp [basisKet]

lemma run_basis_expansion (C : Circuit) (ψ : Ket C.wires) :
    C.run ψ = ∑ y : QBasis C.wires, ψ y • C.run (basisKet y) := by
  conv_lhs => rw [basis_expansion ψ]
  rw [run_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← circuitLinear_apply,← circuitLinear_apply]
  exact (circuitLinear C).map_smul _ _

end F3Reduction

-- Source: Solutions.T31.Bennett

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum F3Tools

noncomputable abbrev reversibleCircuit {W : ℕ} (A : Reversible W) : Circuit := ⟨W,A.gates⟩

lemma inverse_reversible_basis {W : ℕ} (A : Reversible W) (y : QBasis W) :
    (inverseCircuit (reversibleCircuit A)).run (basisKet y) = basisKet (A.backward y) := by
  have h := inverseCircuit_run (reversibleCircuit A) (basisKet (A.backward y))
  change (inverseCircuit (reversibleCircuit A)).run
    (A.gates.foldl (fun φ g => applyGate g φ) (basisKet (A.backward y))) = _ at h
  rw [A.basis,A.right_inv] at h
  exact h

noncomputable abbrev bennettCircuit {W : ℕ} (A : Reversible W) (k j : Fin W) (hkj : k ≠ j) : Circuit :=
  ⟨W,A.gates++[.csumInv k j hkj]++(inverseCircuit (reversibleCircuit A)).gates⟩

/-- Compute, copy the answer into an arbitrary target, and uncompute all scratch. -/
lemma bennett_basis {W : ℕ} (A : Reversible W) (k j : Fin W) (hkj : k ≠ j)
    (hreadonly : ∀ z v, A.backward (Function.update z j v) = Function.update (A.backward z) j v)
    (y : QBasis W) (hj : A.forward y j = y j) :
    (bennettCircuit A k j hkj).run (basisKet y) =
      basisKet (Function.update y j (y j-A.forward y k)) := by
  unfold bennettCircuit Circuit.run
  rw [List.foldl_append,List.foldl_append,A.basis]
  change (inverseCircuit (reversibleCircuit A)).run
    (applyGate (.csumInv k j hkj) (basisKet (A.forward y))) = _
  have hcopy := (subtract k j hkj).basis (A.forward y)
  change applyGate (.csumInv k j hkj) (basisKet (A.forward y)) =
    basisKet (Function.update (A.forward y) j (A.forward y j-A.forward y k)) at hcopy
  rw [hcopy,inverse_reversible_basis,hreadonly,A.left_inv,hj]

lemma backward_readonly {W : ℕ} (A : Reversible W) (j : Fin W)
    (hforward : ∀ z v, A.forward (Function.update z j v) = Function.update (A.forward z) j v) :
    ∀ z v, A.backward (Function.update z j v) = Function.update (A.backward z) j v := by
  intro z v
  apply A.left_inv.injective
  rw [A.right_inv,hforward,A.right_inv]

def NoTouch (j : ℕ) (g : Raw) : Prop :=
  g.2.2.2 ≠ j ∧ (g.1 = 0 ∨ (g.2.1 ≠ j ∧ (g.1 = 1 ∨ g.1 = 2 ∨ g.2.2.1 ≠ j)))

lemma rawValue_update (j : ℕ) (g : Raw) (h : NoTouch j g) (y : ℕ → ZMod 3) (v : ZMod 3) :
    rawValue g (Function.update y j v) = rawValue g y := by
  unfold rawValue
  rcases h.2 with h0 | ⟨hi,hg⟩
  · simp [h0]
  · by_cases h0 : g.1 = 0
    · simp [h0]
    rcases hg with h1 | h2 | hj
    · simp [h1,Function.update_of_ne hi]
    · simp [h2,Function.update_of_ne hi]
    · simp [Function.update_of_ne hi,Function.update_of_ne hj]

lemma rawStep_update (j : ℕ) (g : Raw) (h : NoTouch j g) (y : ℕ → ZMod 3) (v : ZMod 3) :
    rawStep g (Function.update y j v) = Function.update (rawStep g y) j v := by
  unfold rawStep
  rw [rawValue_update j g h,Function.update_of_ne h.1]
  funext a
  by_cases ha : a = j
  · subst a
    simp [Function.update_apply,Ne.symm h.1]
  · by_cases hk : a = g.2.2.2 <;> simp [Function.update_apply,ha,hk,h.1]

lemma rawRun_update (j : ℕ) (gs : List Raw) (h : ∀ g ∈ gs, NoTouch j g)
    (y : ℕ → ZMod 3) (v : ZMod 3) :
    rawRun gs (Function.update y j v) = Function.update (rawRun gs y) j v := by
  induction gs generalizing y with
  | nil => rfl
  | cons g gs ih =>
    change rawRun gs (rawStep g (Function.update y j v)) = _
    rw [rawStep_update j g (h g (by simp)) y v,ih (fun g hg => h g (by simp [hg]))]
    rfl

end F3Reduction

-- Source: Solutions.T31.DAG

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction

abbrev CompileState := (List Raw × ℕ) × List ℕ

def one (p : ℕ) (e : Expr) : CompileState := compile p (p+1) e.code

def result (p : ℕ) (e : Expr) : ℕ := source p (one p e).2 0

lemma one_inv (p : ℕ) (e : Expr) (he : e.Bounded p) (y : ℕ → ZMod 3)
    (hz : ∀ a, p  ≤  a → y a = 0) :
    StoreInv p (p+1) (one p e).1.2 (one p e).2 [e.eval y] y (rawRun (one p e).1.1 y) ∧
      (∀ g ∈ (one p e).1.1, Valid (one p e).1.2 g) ∧
      (one p e).1.2 = p+1+2*e.code.length ∧ (one p e).1.1.length  ≤  2*e.code.length := by
  have hi : StoreInv p (p+1) (p+1) [] [] y y :=
    ⟨by omega,le_rfl,by simp,fun _ _ => rfl,hz p le_rfl,fun a ha => hz a (by omega),rfl⟩
  have hc := compile_correct p (p+1) e.code (e.bounded_code p he) (([],p+1),[]) [] y hi (by simp)
  simpa only [one,compile,Expr.code_eval,List.length_nil,zero_add] using hc

lemma one_value (p : ℕ) (e : Expr) (he : e.Bounded p) (y : ℕ → ZMod 3)
    (hz : ∀ a, p  ≤  a → y a = 0) : rawRun (one p e).1.1 y (result p e) = e.eval y := by
  have hc := (one_inv p e he y hz).1
  have hr : rawRun (one p e).1.1 y p = 0 := by rw [hc.original p (by omega),hz p le_rfl]
  have hs := source_value p (one p e).2 (rawRun (one p e).1.1 y) hr 0
  simpa only [result,hc.values,List.getD_cons_zero] using hs

lemma one_shape (p : ℕ) (e : Expr) (he : e.Bounded p) :
    p < result p e ∧ result p e < (one p e).1.2 := by
  have hc := (one_inv p e he (fun _ => 0) (by simp)).1
  have hl := congrArg List.length hc.values
  simp only [List.length_map,List.length_cons,List.length_nil] at hl
  have hm : result p e ∈ (one p e).2 := by
    unfold result source
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  have hlo := compile_stack_lower p (p+1) e.code (([],p+1),[]) le_rfl (by simp)
    (result p e) hm
  exact ⟨by omega,hc.indices _ hm⟩

lemma source_ne (I j : ℕ) (s : List ℕ) (hj : j < I) (hs : ∀ a ∈ s, I < a) (k : ℕ) :
    source I s k ≠ j := by
  unfold source
  by_cases hk : k < s.length
  · rw [List.getD_eq_getElem _ _ hk]
    have := hs _ (List.getElem_mem hk)
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

lemma tokenGates_noTouch (I p j : ℕ) (s : List ℕ) (t : Token)
    (hj : j < I) (hp : I < p) (hs : ∀ a ∈ s, I < a) (ht : t.1 ≠ 1 ∨ t.2 ≠ j) :
    ∀ g ∈ tokenGates I p s t, NoTouch j g := by
  have h0 := source_ne I j s hj hs 0
  have h1 := source_ne I j s hj hs 1
  unfold tokenGates
  split_ifs
  · intro g hg
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hg
    simp [NoTouch]; omega
  all_goals intro g hg; simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  all_goals rcases hg with rfl | rfl <;> simp [NoTouch,h0,h1] <;> simp_all <;> omega

lemma compile_noTouch (I base j : ℕ) (code : List Token)
    (ht : ∀ t ∈ code, t.1 ≠ 1 ∨ t.2 ≠ j) (hj : j < I)
    (state : CompileState) (hp : I < state.1.2) (hs : ∀ a ∈ state.2, I < a)
    (hg : ∀ g ∈ state.1.1, NoTouch j g) :
    ∀ g ∈ (code.foldl (compileStep I) state).1.1, NoTouch j g := by
  induction code generalizing state with
  | nil => exact hg
  | cons t ts ih =>
    apply ih (fun t ht' => ht t (by simp [ht'])) (compileStep I state t) (by dsimp [compileStep]; omega)
    · intro a ha
      simp only [compileStep,tokenStack,List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · split_ifs at ha
        · exact hs a ha
        · exact hs a (List.mem_of_mem_drop ha)
        · exact hs a (List.mem_of_mem_drop ha)
    · intro g hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact hg g hold
      · exact tokenGates_noTouch I state.1.2 j state.2 t hj hp hs (ht t (by simp)) g hnew

lemma one_noTouch (p j : ℕ) (e : Expr) (hj : j < p)
    (he : ∀ t ∈ e.code, t.1 ≠ 1 ∨ t.2 ≠ j) :
    ∀ g ∈ (one p e).1.1, NoTouch j g :=
  compile_noTouch p (p+1) j e.code he hj (([],p+1),[]) (by change p < p+1; omega) (by simp) (by simp)

end F3MachineCompiler

-- Source: Solutions.T31.Batch

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Tools
lemma Expr.bounded_mono {I J : ℕ} (e : Expr) (h : e.Bounded I) (hIJ : I  ≤  J) : e.Bounded J := by
  induction e with
  | zero | one => trivial
  | input i => exact lt_of_lt_of_le h hIJ
  | plus a b ha hb | times a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | minus a ha => exact ha h

lemma Expr.eval_congr_bounded {I : ℕ} (e : Expr) (h : e.Bounded I)
    (y z : ℕ → ZMod 3) (hyz : ∀ i, i < I → y i = z i) : e.eval y = e.eval z := by
  induction e with
  | zero | one => rfl
  | input i => exact hyz i h
  | plus a b ha hb => exact congrArg₂ (·+·) (ha h.1) (hb h.2)
  | times a b ha hb => exact congrArg₂ (·*·) (ha h.1) (hb h.2)
  | minus a ha => exact congrArg Neg.neg (ha h)
end F3Tools

namespace F3MachineCompiler
open F3Tools

def batch (p : ℕ) : List Expr → CompileState
  | [] => (([],p),[])
  | e::es =>
    let q := one p e
    let r := batch q.1.2 es
    ((q.1.1++r.1.1,r.1.2),result p e::r.2)

structure BatchSpec (p : ℕ) (es : List Expr) (r : CompileState) (y : ℕ → ZMod 3) : Prop where
  monotone : p  ≤  r.1.2
  valid : ∀ g ∈ r.1.1, Valid r.1.2 g
  preserve : ∀ k, k < p → rawRun r.1.1 y k = y k
  unused : ∀ k, r.1.2  ≤  k → rawRun r.1.1 y k = 0
  values : r.2.map (rawRun r.1.1 y) = es.map (Expr.eval y)
  indices : ∀ k ∈ r.2, p < k ∧ k < r.1.2

lemma batch_correct (p : ℕ) (es : List Expr) (he : ∀ e ∈ es, e.Bounded p)
    (y : ℕ → ZMod 3) (hz : ∀ a, p  ≤  a → y a = 0) : BatchSpec p es (batch p es) y := by
  induction es generalizing p y with
  | nil => exact ⟨le_rfl,by simp [batch],fun _ _ => rfl,hz,rfl,by simp [batch]⟩
  | cons e es ih =>
    have hb := he e (by simp)
    have ho := one_inv p e hb y hz
    have hp : p  ≤  (one p e).1.2 := le_trans (by omega : p  ≤  p+1) ho.1.growing
    have htail : ∀ a ∈ es, a.Bounded p := fun a ha => he a (by simp [ha])
    have hr := ih (one p e).1.2 (fun a ha => a.bounded_mono (htail a ha) hp)
      (rawRun (one p e).1.1 y) ho.1.unused
    refine ⟨le_trans hp hr.monotone,?_,?_,?_,?_,?_⟩
    · intro g hg
      change g ∈ (one p e).1.1++(batch (one p e).1.2 es).1.1 at hg
      rcases List.mem_append.mp hg with hq | hr'
      · exact (ho.2.1 g hq).mono hr.monotone
      · exact hr.valid g hr'
    · intro k hk
      change rawRun ((one p e).1.1++(batch (one p e).1.2 es).1.1) y k = y k
      rw [rawRun_append,hr.preserve k (lt_of_lt_of_le hk hp),ho.1.original k (by omega)]
    · intro k hk
      change rawRun ((one p e).1.1++(batch (one p e).1.2 es).1.1) y k = 0
      rw [rawRun_append]
      exact hr.unused k hk
    · change (result p e::(batch (one p e).1.2 es).2).map
          (rawRun ((one p e).1.1++(batch (one p e).1.2 es).1.1) y) = _
      rw [rawRun_append,List.map_cons,List.map_cons]
      have hs := one_shape p e hb
      rw [hr.preserve _ hs.2,one_value p e hb y hz,hr.values]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact a.eval_congr_bounded (htail a ha) _ _ (fun i hi => ho.1.original i (by omega))
    · intro k hk
      change k ∈ result p e::(batch (one p e).1.2 es).2 at hk
      rcases List.mem_cons.mp hk with rfl | hk
      · have hs := one_shape p e hb
        exact ⟨hs.1,lt_of_lt_of_le hs.2 hr.monotone⟩
      · have hs := hr.indices k hk
        exact ⟨lt_of_le_of_lt hp hs.1,hs.2⟩

lemma batch_noTouch (p j : ℕ) (es : List Expr) (hj : j < p)
    (he : ∀ e ∈ es, ∀ t ∈ e.code, t.1 ≠ 1 ∨ t.2 ≠ j)
    (hb : ∀ e ∈ es, e.Bounded p) : ∀ g ∈ (batch p es).1.1, F3Reduction.NoTouch j g := by
  induction es generalizing p with
  | nil => simp [batch]
  | cons e es ih =>
    intro g hg
    change g ∈ (one p e).1.1++(batch (one p e).1.2 es).1.1 at hg
    rcases List.mem_append.mp hg with hq | hr
    · exact one_noTouch p j e hj (he e (by simp)) g hq
    · have ho := (one_inv p e (hb e (by simp)) (fun _ => 0) (by simp)).1
      have hp : p  ≤  (one p e).1.2 := le_trans (by omega : p  ≤  p+1) ho.growing
      exact ih (one p e).1.2 (lt_of_lt_of_le hj hp) (fun a ha => he a (by simp [ha]))
        (fun a ha => a.bounded_mono (hb a (by simp [ha])) hp) g hr

end F3MachineCompiler

-- Source: Solutions.T31.BooleanMachine
/-! Boolean-stack normalization adapted from the accepted QMCBoolSim proof:
https://prove2.me/theorems/e2e45b22-7503-4b55-8d3b-2e418548371f
Submission 25584ed5-3e1b-4b35-84d4-3c1e9810c92e. Public Prove2me contribution, Apache 2.0. -/
open scoped BigOperators

namespace QMCBoolSim
open Turing Function OAI.MetricKMedian.Binary

section Sim
variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Boolean statements over the extended state. -/
abbrev St (K Λ σ : Type) := TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)

/-- Push the first `n` bits of `g v`, so that bit `0` ends on top. -/
def pushAt (k : K) (g : σ × Option Bool → List Bool) : ℕ → St K Λ σ → St K Λ σ
  | 0, q => q
  | n + 1, q => .push k (fun v => (g v).getD n false) (pushAt k g n q)

theorem pushAt_spec (k : K) (g : σ × Option Bool → List Bool) (n : ℕ) (q : St K Λ σ)
    (v : σ × Option Bool) (s : K → List Bool) (hn : n  ≤  (g v).length) :
    TM2.stepAux (pushAt k g n q) v s = TM2.stepAux q v (update s k ((g v).take n ++ s k)) := by
  induction n generalizing s with
  | zero => simp [pushAt]
  | succ n ih =>
      simp only [pushAt, TM2.stepAux]
      rw [ih _ (by omega)]
      have hlt : n < (g v).length := by omega
      simp only [update_self, update_idem]
      congr 2
      rw [List.getD_eq_getElem _ _ hlt, List.take_succ_eq_append_getElem hlt]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Read `n` bits from `k`, remembering them in the control flow. -/
def readTree (k : K) : ℕ → (List Bool → St K Λ σ) → St K Λ σ → St K Λ σ
  | 0, cont, _ => cont []
  | n + 1, cont, e =>
      .pop k (fun v x => (v.1, x))
        (.branch (fun v => v.2.isSome)
          (.branch (fun v => v.2 == some true)
            (readTree k n (fun l => cont (true :: l)) e)
            (readTree k n (fun l => cont (false :: l)) e))
          e)

theorem readTree_spec (k : K) (l : List Bool) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (rest : List Bool) (hs : s k = l ++ rest) :
    ∃ b', TM2.stepAux (readTree k l.length cont e) (v, b) s
      = TM2.stepAux (cont l) (v, b') (update s k rest) := by
  induction l generalizing cont b s with
  | nil =>
      refine ⟨b, ?_⟩
      have : update s k rest = s := by
        have : rest = s k := by simpa using hs.symm
        rw [this]; simp
      rw [this]; rfl
  | cons x l ih =>
      have hs' : s k = x :: (l ++ rest) := by simpa using hs
      cases x with
      | true =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (true :: l)) (some true)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb
      | false =>
          obtain ⟨b', hb⟩ := ih (fun l => cont (false :: l)) (some false)
            (update s k (l ++ rest)) (by simp)
          refine ⟨b', ?_⟩
          simp only [update_idem] at hb
          simpa [List.length_cons, readTree, TM2.stepAux, hs'] using hb

theorem readTree_empty (k : K) (n : ℕ) (cont : List Bool → St K Λ σ) (e : St K Λ σ)
    (v : σ) (b : Option Bool) (s : K → List Bool) (hs : s k = []) :
    TM2.stepAux (readTree k (n + 1) cont e) (v, b) s = TM2.stepAux e (v, none) s := by
  have : update s k [] = s := by rw [← hs]; simp
  simp [readTree, TM2.stepAux, hs, this]

/-- The symbols pushed by a statement. -/
def syms : TM2.Stmt Γ Λ σ → Set (Σ k, Γ k)
  | .push k f q => Set.range (fun v => (⟨k, f v⟩ : Σ k, Γ k)) ∪ syms q
  | .peek _ _ q => syms q
  | .pop _ _ q => syms q
  | .load _ q => syms q
  | .branch _ q r => syms q ∪ syms r
  | .goto _ => ∅
  | .halt => ∅

theorem syms_finite [Finite σ] (q : TM2.Stmt Γ Λ σ) : (syms q).Finite := by
  induction q with
  | push k f q ih => exact (Set.finite_range _).union ih
  | peek k f q ih => exact ih
  | pop k f q ih => exact ih
  | load f q ih => exact ih
  | branch f q r ihq ihr => exact ihq.union ihr
  | goto f => exact Set.finite_empty
  | halt => exact Set.finite_empty

variable (w : K → ℕ) (c : ∀ k, Γ k → List Bool) (d : ∀ k, List Bool → Option (Γ k))

/-- Translate a statement to Boolean stacks. -/
def tr : TM2.Stmt Γ Λ σ → St K Λ σ
  | .push k f q => pushAt k (fun v => c k (f v.1)) (w k) (tr q)
  | .peek k f q =>
      readTree k (w k)
        (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none)) (tr q)))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .pop k f q =>
      readTree k (w k)
        (fun l => .load (fun v => (f v.1 (d k l), none)) (tr q))
        (.load (fun v => (f v.1 none, none)) (tr q))
  | .load f q => .load (fun v => (f v.1, none)) (tr q)
  | .branch f q r => .branch (fun v => f v.1) (tr q) (tr r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

/-- Encode the stacks. -/
def enc (s : ∀ k, List (Γ k)) : K → List Bool := fun k => (s k).flatMap (c k)

/-- Encode a configuration. -/
def ecfg (a : TM2.Cfg Γ Λ σ) : TM2.Cfg (fun _ : K => Bool) Λ (σ × Option Bool) :=
  ⟨a.l, (a.var, none), enc c a.stk⟩

theorem enc_update (s : ∀ k, List (Γ k)) (k : K) (t : List (Γ k)) :
    enc c (update s k t) = update (enc c s) k (t.flatMap (c k)) := by
  funext j
  by_cases h : j = k
  · subst h; simp [enc]
  · simp [enc, update_of_ne h]

variable (T : Set (Σ k, Γ k))

theorem inv_update {s : ∀ k, List (Γ k)} (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T)
    {k : K} {t : List (Γ k)} (ht : ∀ x ∈ t, (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    ∀ j x, x ∈ update s k t j → (⟨j, x⟩ : Σ k, Γ k) ∈ T := by
  intro j x hx
  by_cases h : j = k
  · subst h
    simp only [update_self] at hx
    exact ht x hx
  · rw [update_of_ne h] at hx
    exact hs j x hx

variable (hw : ∀ k, 0 < w k)
  (hlen : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → (c k x).length = w k)
  (hd : ∀ k x, (⟨k, x⟩ : Σ k, Γ k) ∈ T → d k (c k x) = some x)

include hw hlen hd in
theorem tr_spec (q : TM2.Stmt Γ Λ σ) (hq : syms q ⊆ T) (v : σ) (s : ∀ k, List (Γ k))
    (hs : ∀ k x, x ∈ s k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    TM2.stepAux (tr w c d q) (v, none) (enc c s) = ecfg c (TM2.stepAux q v s) ∧
      (∀ k x, x ∈ (TM2.stepAux q v s).stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) := by
  induction q generalizing v s with
  | push k f q ih =>
      have hfv : (⟨k, f v⟩ : Σ k, Γ k) ∈ T := hq (Or.inl ⟨v, rfl⟩)
      have hs' := inv_update T hs (k := k) (t := f v :: s k) (by
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hfv
        · exact hs k x hx)
      have ih' := ih (fun _ hx => hq (Or.inr hx)) v _ hs'
      simp only [tr, TM2.stepAux]
      refine ⟨?_, ih'.2⟩
      rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hfv]), ← ih'.1, enc_update]
      congr 2
      rw [List.take_of_length_le (by simp [hlen k _ hfv])]
      simp [enc]
  | peek k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have ih' := ih hq' (f v none) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have ih' := ih hq' (f v (some x)) s hs
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => pushAt k (fun _ => l) (w k) (.load (fun v => (f v.1 (d k l), none))
              (tr w c d q)))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          simp only [List.head?_cons]
          rw [hb]
          rw [pushAt_spec _ _ _ _ _ _ (by simp [hlen k _ hx]),
            List.take_of_length_le (by simp [hlen k _ hx])]
          simp only [TM2.stepAux, hd k x hx, update_idem, update_self]
          have : update (enc c s) k (c k x ++ t.flatMap (c k)) = enc c s := by
            have : c k x ++ t.flatMap (c k) = enc c s k := by simp [enc, hsk]
            rw [this]; simp
          rw [this]
          exact ih'.1
  | pop k f q ih =>
      have hq' : syms q ⊆ T := hq
      simp only [tr, TM2.stepAux]
      cases hsk : s k with
      | nil =>
          have hup : update s k [] = s := by rw [← hsk]; simp
          have ih' := ih hq' (f v none) s hs
          simp only [List.tail_nil, List.head?_nil, hup]
          refine ⟨?_, ih'.2⟩
          obtain ⟨n, hn⟩ : ∃ n, w k = n + 1 := Nat.exists_eq_succ_of_ne_zero (hw k).ne'
          rw [hn, readTree_empty _ _ _ _ _ _ _ (by simp [enc, hsk])]
          simpa [TM2.stepAux] using ih'.1
      | cons x t =>
          have hx : (⟨k, x⟩ : Σ k, Γ k) ∈ T := hs k x (by simp [hsk])
          have hs' := inv_update T hs (k := k) (t := t) (by
            intro y hy
            exact hs k y (by simp [hsk, hy]))
          have ih' := ih hq' (f v (some x)) _ hs'
          simp only [List.tail_cons, List.head?_cons]
          refine ⟨?_, ih'.2⟩
          obtain ⟨b', hb⟩ := readTree_spec (Λ := Λ) k (c k x)
            (fun l => .load (fun v => (f v.1 (d k l), none)) (tr w c d q))
            (.load (fun v => (f v.1 none, none)) (tr w c d q)) v none (enc c s)
            (t.flatMap (c k)) (by simp [enc, hsk])
          rw [hlen k x hx] at hb
          rw [hb]
          simp only [TM2.stepAux, hd k x hx]
          rw [← enc_update]
          exact ih'.1
  | load f q ih =>
      have ih' := ih hq (f v) s hs
      simp only [tr, TM2.stepAux]
      exact ih'
  | branch f q r ihq ihr =>
      have hq' : syms q ⊆ T := fun _ hx => hq (Or.inl hx)
      have hr' : syms r ⊆ T := fun _ hx => hq (Or.inr hx)
      simp only [tr, TM2.stepAux]
      cases hf : f v with
      | false => simpa using ihr hr' v s hs
      | true => simpa using ihq hq' v s hs
  | goto f =>
      exact ⟨rfl, hs⟩
  | halt =>
      exact ⟨rfl, hs⟩

include hw hlen hd in
theorem sim_trace (m : Λ → TM2.Stmt Γ Λ σ) (hm : ∀ l, syms (m l) ⊆ T)
    {n : ℕ} {a b : TM2.Cfg Γ Λ σ} (h : Trace (TM2.step m) n a b)
    (ha : ∀ k x, x ∈ a.stk k → (⟨k, x⟩ : Σ k, Γ k) ∈ T) :
    Trace (TM2.step (fun l => tr w c d (m l))) n (ecfg c a) (ecfg c b) := by
  induction h with
  | refl => exact Trace.refl _
  | @cons n a b e hab _ ih =>
      rcases a with ⟨l, v, s⟩
      cases l with
      | none => cases hab
      | some l =>
          have hb : b = TM2.stepAux (m l) v s := (Option.some.inj hab).symm
          subst b
          have hspec := tr_spec w c d T hw hlen hd (m l) (hm l) v s ha
          refine Trace.cons ?_ (ih hspec.2)
          exact congrArg some hspec.1

end Sim

theorem exists_block (A : Type) (S : Set A) (hS : S.Finite) :
    ∃ (w : ℕ) (c : A → List Bool), 0 < w ∧ (∀ x ∈ S, (c x).length = w) ∧ Set.InjOn c S := by
  classical
  haveI : Finite S := hS
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let i : A → ℕ := fun x => if h : x ∈ S then (e ⟨x, h⟩).val else 0
  refine ⟨n + 1, fun x => List.ofFn (fun j : Fin (n + 1) => decide (j.val = i x)),
    Nat.succ_pos _, fun x _ => by simp, ?_⟩
  intro x hx y hy hxy
  have hxy' := List.ofFn_injective hxy
  have hix : i x < n + 1 := by
    have : i x = (e ⟨x, hx⟩).val := by simp [i, hx]
    have := (e ⟨x, hx⟩).isLt
    omega
  have h1 := congrFun hxy' ⟨i x, hix⟩
  simp only [decide_true] at h1
  have h2 : i x = i y := by simpa using h1.symm
  have h3 : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
    apply Fin.ext
    simpa [i, hx, hy] using h2
  simpa using e.injective h3

/-- The Boolean machine simulating a bundled machine. -/
abbrev simMachine (tm : FinTM2) (w : tm.K → ℕ) (c : ∀ k, tm.Γ k → List Bool)
    (d : ∀ k, List Bool → Option (tm.Γ k)) : Machine :=
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  { K := tm.K
    input := tm.k₀
    output := tm.k₁
    Label := tm.Λ
    main := tm.main
    State := tm.σ × Option Bool
    initial := (tm.initialState, none)
    code := fun l => tr w c d (tm.m l) }

theorem simulate (tm : FinTM2) (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool) :
    ∃ (M : Machine) (τ : Bool ≃ Bool), ∀ (s t : List Bool) (n : ℕ),
      TM2OutputsInTime tm (s.map e₀.symm) (some (t.map e₁.symm)) n →
        Nonempty (TM2OutputsInTime M.tm s (some (t.map τ)) n) := by
  classical
  letI := tm.kDecidableEq
  letI := tm.kFin
  letI := tm.ΛFin
  letI := tm.σFin
  let T : Set (Σ k, tm.Γ k) :=
    (⋃ l, syms (tm.m l)) ∪ Set.range (fun x : tm.Γ tm.k₀ => (⟨tm.k₀, x⟩ : Σ k, tm.Γ k))
  haveI : Finite (tm.Γ tm.k₀) := Finite.of_equiv Bool e₀.symm
  have hT : T.Finite :=
    (Set.finite_iUnion fun l => syms_finite (tm.m l)).union (Set.finite_range _)
  have key : ∀ k, ∃ (w : ℕ) (c : tm.Γ k → List Bool), 0 < w ∧
      (∀ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (c x).length = w) ∧
      (∀ x y, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T → c x = c y → x = y) ∧
      (∀ h : k = tm.k₀, ∀ x, c x = [e₀ (h ▸ x)]) ∧
      (k ≠ tm.k₀ → ∀ h : k = tm.k₁, ∀ x, c x = [e₁ (h ▸ x)]) := by
    intro k
    by_cases h0 : k = tm.k₀
    · subst h0
      refine ⟨1, fun x => [e₀ x], one_pos, fun _ _ => rfl, ?_, fun _ _ => rfl, fun h => absurd rfl h⟩
      intro x y _ _ hxy
      exact e₀.injective (by simpa using hxy)
    · by_cases h1 : k = tm.k₁
      · subst h1
        refine ⟨1, fun x => [e₁ x], one_pos, fun _ _ => rfl, ?_, fun h => absurd h h0,
          fun _ _ _ => rfl⟩
        intro x y _ _ hxy
        exact e₁.injective (by simpa using hxy)
      · have hS : {x : tm.Γ k | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T}.Finite :=
          hT.preimage (f := fun x : tm.Γ k => (⟨k, x⟩ : Σ k, tm.Γ k))
            (sigma_mk_injective.injOn)
        obtain ⟨w, c, hw, hl, hi⟩ := exists_block _ _ hS
        exact ⟨w, c, hw, hl, fun x y hx hy h => hi hx hy h, fun h => absurd h h0,
          fun _ h => absurd h h1⟩
  choose w c hw hlen hinj hc0 hc1 using key
  let d : ∀ k, List Bool → Option (tm.Γ k) := fun k l =>
    if h : ∃ x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T ∧ c k x = l then some h.choose else none
  have hd : ∀ k x, (⟨k, x⟩ : Σ k, tm.Γ k) ∈ T → d k (c k x) = some x := by
    intro k x hx
    have h : ∃ y, (⟨k, y⟩ : Σ k, tm.Γ k) ∈ T ∧ c k y = c k x := ⟨x, hx, rfl⟩
    have hspec := h.choose_spec
    simp only [d, dif_pos h]
    exact congrArg some (hinj k _ _ hspec.1 hx hspec.2)
  have hc0' : ∀ x, c tm.k₀ x = [e₀ x] := fun x => hc0 tm.k₀ rfl x
  obtain ⟨τ, hτ⟩ : ∃ τ : Bool ≃ Bool, ∀ x, c tm.k₁ x = [τ (e₁ x)] := by
    by_cases h : tm.k₁ = tm.k₀
    · have aux : ∀ k (_ : k = tm.k₀) (e : tm.Γ k ≃ Bool),
          ∃ τ : Bool ≃ Bool, ∀ x, c k x = [τ (e x)] := by
        intro k hk e
        subst hk
        exact ⟨e.symm.trans e₀, fun x => by simp [hc0']⟩
      exact aux _ h e₁
    · exact ⟨Equiv.refl _, fun x => hc1 tm.k₁ h rfl x⟩
  have hin : ∀ s : List Bool, (s.map e₀.symm).flatMap (c tm.k₀) = s := by
    intro s
    induction s with
    | nil => rfl
    | cons b s ih => simpa [hc0'] using ih
  have hout : ∀ t : List Bool, (t.map e₁.symm).flatMap (c tm.k₁) = t.map τ := by
    intro t
    induction t with
    | nil => rfl
    | cons b t ih => simpa [hτ] using ih
  refine ⟨simMachine tm w c d, τ, ?_⟩
  intro s t n h
  have htr : Trace (TM2.step tm.m) h.steps _ _ := Trace.of_iterate (f := tm.step) h.evals_in_steps
  have hsim := sim_trace w c d T hw hlen hd tm.m
    (fun l x hx => Or.inl (Set.mem_iUnion.2 ⟨l, hx⟩)) htr (by
      intro k x hx
      by_cases hk : k = tm.k₀
      · subst hk
        exact Or.inr ⟨_, rfl⟩
      · simp [initList, hk] at hx)
  have hinit : ecfg c (initList tm (s.map e₀.symm)) = (simMachine tm w c d).initialCfg s := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₀
    · subst hk
      simpa [enc, initList, Machine.initialCfg] using hin s
    · simp [enc, initList, Machine.initialCfg, hk]
  have hhalt : ecfg c (haltList tm (t.map e₁.symm)) = (simMachine tm w c d).finalCfg (t.map τ) := by
    refine congrArg (TM2.Cfg.mk _ _) ?_
    funext k
    by_cases hk : k = tm.k₁
    · subst hk
      simpa [enc, haltList, Machine.finalCfg] using hout t
    · simp [enc, haltList, Machine.finalCfg, hk]
  rw [hinit, hhalt] at hsim
  exact ⟨⟨⟨_, hsim.iterate_eq⟩, h.steps_le_m⟩⟩

/-- A letterwise transducer. -/
def mapT (τ : Bool → Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((), [τ b])
  finish _ := []

theorem mapT_run (τ : Bool → Bool) (xs : List Bool) : (mapT τ).run () xs = xs.map τ := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change τ b :: (mapT τ).run () xs = τ b :: xs.map τ; rw [ih]

end QMCBoolSim

-- Source: Solutions.T31.SymbolicTM

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

abbrev BinaryMachine := OAI.MetricKMedian.Binary.Machine

noncomputable def literal (v : ZMod 3) : Expr :=
  if v = 0 then .zero else if v = 1 then .one else .plus .one .one

lemma literal_eval (v : ZMod 3) (y : ℕ → ZMod 3) : (literal v).eval y = v := by
  rcases F3Reduction.cases_three v with rfl | rfl | rfl <;> norm_num [literal,Expr.eval]

noncomputable def select {α : Type} [Fintype α] (v : α → Expr) (f : α → ZMod 3) : Expr :=
  Expr.sum ((Finset.univ.toList : List α).map (fun a => .times (v a) (literal (f a))))

lemma select_eval {α : Type} [Fintype α] (v : α → Expr) (f : α → ZMod 3)
    (y : ℕ → ZMod 3) :
    (select v f).eval y = ∑ a, (v a).eval y*f a := by
  simp [select,Expr.eval_sum,List.map_map,Expr.eval,literal_eval,Finset.sum_toList]

lemma select_onehot {α : Type} [Fintype α] (v : α → Expr) (f : α → ZMod 3)
    (y : ℕ → ZMod 3) (a : α) (hv : ∀ b, (v b).eval y = if b = a then 1 else 0) :
    (select v f).eval y = f a := by
  rw [select_eval]
  simp [hv]

def symbol : Option Bool → ZMod 3
  | none => 0
  | some false => 1
  | some true => 2

lemma symbol_injective : Function.Injective symbol := by
  decide

def cell (L : List Bool) (i : ℕ) : ZMod 3 := symbol L[i]?

lemma cell_head (L : List Bool) : cell L 0 = symbol L.head? := by cases L <;> rfl
lemma cell_nil (i : ℕ) : cell [] i = 0 := by simp [cell,symbol]
lemma cell_cons_zero (b : Bool) (L : List Bool) : cell (b::L) 0 = symbol (some b) := rfl
lemma cell_cons_succ (b : Bool) (L : List Bool) (i : ℕ) : cell (b::L) (i+1) = cell L i := by
  simp [cell]
lemma cell_tail (L : List Bool) (i : ℕ) : cell L.tail i = cell L (i+1) := by
  cases L <;> simp [cell,symbol]
lemma cell_beyond (L : List Bool) (i : ℕ) (hi : L.length  ≤  i) : cell L i = 0 := by
  simp [cell,List.getElem?_eq_none hi,symbol]

structure Symbolic (M : BinaryMachine) (N : ℕ) where
  label : Option M.Label → Expr
  state : M.State → Expr
  stack : M.K → Fin N → Expr

def Represents {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) : Prop :=
  (∀ l, (S.label l).eval y = if l = c.l then 1 else 0) ∧
  (∀ s, (S.state s).eval y = if s = c.var then 1 else 0) ∧
  (∀ k i, (S.stack k i).eval y = cell (c.stk k) i.val)

noncomputable def stateTable {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (f : M.State → ZMod 3) := select S.state f

lemma stateTable_eval {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (f : M.State → ZMod 3) :
    (stateTable S f).eval y = f c.var := select_onehot _ _ _ _ h.2.1

noncomputable def headSelector {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (k : M.K) (hN : 0 < N) (p : M.State × Option Bool) : Expr :=
  .times (S.state p.1) (.isZero (.plus (S.stack k ⟨0,hN⟩) (.minus (literal (symbol p.2)))))

lemma headSelector_eval {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (k : M.K) (hN : 0 < N)
    (p : M.State × Option Bool) :
    (headSelector S k hN p).eval y = if p = (c.var,(c.stk k).head?) then 1 else 0 := by
  change (S.state p.1).eval y * (Expr.isZero (.plus (S.stack k ⟨0,hN⟩)
    (.minus (literal (symbol p.2))))).eval y = _
  rw [Expr.eval_isZero]
  simp only [Expr.eval,literal_eval,h.2.1,h.2.2,cell_head]
  have he : (symbol (c.stk k).head? + -symbol p.2 = 0) ↔ (c.stk k).head? = p.2 := by
    rw [← sub_eq_add_neg,sub_eq_zero,symbol_injective.eq_iff]
  simp only [he]
  by_cases hs : p.1 = c.var <;> by_cases hb : p.2 = (c.stk k).head? <;>
    simp [hs,hb,Prod.ext_iff,eq_comm]

noncomputable def headTable {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (k : M.K) (hN : 0 < N) (f : M.State → Option Bool → ZMod 3) : Expr :=
  select (headSelector S k hN) (fun p => f p.1 p.2)

lemma headTable_eval {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (k : M.K) (hN : 0 < N)
    (f : M.State → Option Bool → ZMod 3) :
    (headTable S k hN f).eval y = f c.var (c.stk k).head? :=
  select_onehot (headSelector S k hN) (fun p => f p.1 p.2) y (c.var,(c.stk k).head?)
    (fun p => by
      have h := headSelector_eval S c y h k hN p
      by_cases hp : p = (c.var,(c.stk k).head?) <;>
        simpa only [if_pos,if_neg,hp] using h)

end F3MachineCompiler

namespace F3MachineCompiler
open F3Tools
open Classical

noncomputable def symLoad {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (f : M.State → M.State) : Symbolic M N :=
  { S with state := fun s => stateTable S (fun a => if f a = s then 1 else 0) }

lemma symLoad_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (f : M.State → M.State) :
    Represents (symLoad S f) {c with var := f c.var} y := by
  refine ⟨h.1,?_,h.2.2⟩
  intro s
  rw [symLoad,stateTable_eval S c y h]
  simp [eq_comm]

noncomputable def symRead {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (k : M.K) (hN : 0 < N) (f : M.State → Option Bool → M.State) : Symbolic M N :=
  { S with state := fun s => headTable S k hN (fun a b => if f a b = s then 1 else 0) }

lemma symRead_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (k : M.K) (hN : 0 < N)
    (f : M.State → Option Bool → M.State) :
    Represents (symRead S k hN f) {c with var := f c.var (c.stk k).head?} y := by
  refine ⟨h.1,?_,h.2.2⟩
  intro s
  rw [symRead,headTable_eval S c y h]
  simp [eq_comm]

noncomputable def symPush {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (k : M.K) (f : M.State → Bool) : Symbolic M N :=
  { S with stack := fun j i =>
      if j = k then if hi : i.val = 0 then stateTable S (fun a => symbol (some (f a)))
        else S.stack j ⟨i.val-1,by have := i.isLt; omega⟩
      else S.stack j i }

lemma symPush_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (k : M.K) (f : M.State → Bool) :
    Represents (symPush S k f) {c with stk := Function.update c.stk k (f c.var::c.stk k)} y := by
  refine ⟨h.1,h.2.1,?_⟩
  intro j i
  by_cases hj : j = k
  · subst j
    simp only [symPush,ite_true,Function.update_self]
    by_cases hi : i.val = 0
    · simp only [dif_pos hi,hi,cell_cons_zero]
      exact stateTable_eval S c y h _
    · rw [dif_neg hi,h.2.2]
      have he : i.val = (i.val-1)+1 := by omega
      conv_rhs => rw [he,cell_cons_succ]
  · simp only [symPush,if_neg hj,Function.update_of_ne hj]
    exact h.2.2 j i

noncomputable def symDrop {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (k : M.K) : Symbolic M N :=
  { S with stack := fun j i => if j = k then
      if hi : i.val+1 < N then S.stack j ⟨i.val+1,hi⟩ else .zero
    else S.stack j i }

lemma symDrop_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (k : M.K) (hk : (c.stk k).length  ≤  N) :
    Represents (symDrop S k) {c with stk := Function.update c.stk k (c.stk k).tail} y := by
  refine ⟨h.1,h.2.1,?_⟩
  intro j i
  by_cases hj : j = k
  · subst j
    simp only [symDrop,ite_true,Function.update_self,cell_tail]
    split_ifs with hi
    · exact h.2.2 _ _
    · simp only [Expr.eval]
      exact (cell_beyond (c.stk k) (i.val+1) (by omega)).symm
  · simp only [symDrop,if_neg hj,Function.update_of_ne hj]
    exact h.2.2 j i

noncomputable def symGoto {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (f : M.State → M.Label) : Symbolic M N :=
  { S with label := fun l => stateTable S (fun a => if some (f a) = l then 1 else 0) }

lemma symGoto_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (f : M.State → M.Label) :
    Represents (symGoto S f) {c with l := some (f c.var)} y := by
  refine ⟨?_,h.2.1,h.2.2⟩
  intro l
  rw [symGoto,stateTable_eval S c y h]
  simp [eq_comm]

noncomputable def symHalt {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) : Symbolic M N :=
  { S with label := fun l => literal (if l = none then 1 else 0) }

lemma symHalt_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) :
    Represents (symHalt S) {c with l := none} y := by
  exact ⟨fun l => literal_eval _ y,h.2.1,h.2.2⟩

noncomputable def symChoose {M : BinaryMachine} {N : ℕ} (a : Expr)
    (S T : Symbolic M N) : Symbolic M N where
  label l := a.choose (S.label l) (T.label l)
  state s := a.choose (S.state s) (T.state s)
  stack k i := a.choose (S.stack k i) (T.stack k i)

lemma symChoose_rep {M : BinaryMachine} {N : ℕ} (S T : Symbolic M N) (c d : M.Cfg)
    (y : ℕ → ZMod 3) (hs : Represents S c y) (ht : Represents T d y)
    (a : Expr) (b : Bool) (ha : a.eval y = if b then 1 else 0) :
    Represents (symChoose a S T) (if b then c else d) y := by
  cases b <;> simp only [Bool.false_eq_true,if_false,if_true] at ha ⊢
  · constructor
    · intro l; simpa [symChoose,Expr.choose,Expr.eval,ha] using ht.1 l
    · constructor
      · intro s; simpa [symChoose,Expr.choose,Expr.eval,ha] using ht.2.1 s
      · intro k i; simpa [symChoose,Expr.choose,Expr.eval,ha] using ht.2.2 k i
  · constructor
    · intro l; simpa [symChoose,Expr.choose,Expr.eval,ha] using hs.1 l
    · constructor
      · intro s; simpa [symChoose,Expr.choose,Expr.eval,ha] using hs.2.1 s
      · intro k i; simpa [symChoose,Expr.choose,Expr.eval,ha] using hs.2.2 k i

end F3MachineCompiler

-- Source: Solutions.T31.TMStep

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools Turing
open Classical

variable {M : BinaryMachine}
abbrev Statement (M : BinaryMachine) := TM2.Stmt (fun _ : M.K => Bool) M.Label M.State

def growth : Statement M → ℕ
  | .push _ _ q => growth q+1
  | .peek _ _ q => growth q
  | .pop _ _ q => growth q
  | .load _ q => growth q
  | .branch _ q r => max (growth q) (growth r)
  | .goto _ => 0
  | .halt => 0

def Fits (c : M.Cfg) (B : ℕ) : Prop := ∀ k, (c.stk k).length  ≤  B

lemma fits_push (c : M.Cfg) (B : ℕ) (hc : Fits c B) (k : M.K) (f : M.State → Bool) :
    Fits {c with stk := Function.update c.stk k (f c.var::c.stk k)} (B+1) := by
  intro j
  by_cases hj : j = k <;> simp [Function.update_apply,hj,List.length_cons]
  · exact hc k
  · exact le_trans (hc j) (by omega)

lemma fits_drop (c : M.Cfg) (B : ℕ) (hc : Fits c B) (k : M.K) :
    Fits {c with stk := Function.update c.stk k (c.stk k).tail} B := by
  intro j
  by_cases hj : j = k <;> simp [Function.update_apply,hj,List.length_tail]
  · have := hc k; omega
  · exact hc j

lemma stepAux_fits (q : Statement M) (c : M.Cfg) (B : ℕ) (hc : Fits c B) :
    Fits (TM2.stepAux q c.var c.stk) (B+growth q) := by
  induction q generalizing c B with
  | push k f q ih =>
    have h := ih {c with stk := Function.update c.stk k (f c.var::c.stk k)} (B+1)
      (fits_push c B hc k f)
    simpa only [TM2.stepAux,growth,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  | peek k f q ih => exact ih {c with var := f c.var (c.stk k).head?} B hc
  | pop k f q ih =>
    exact ih {c with var := f c.var (c.stk k).head?,stk := Function.update c.stk k (c.stk k).tail}
      B (fits_drop c B hc k)
  | load f q ih => exact ih {c with var := f c.var} B hc
  | branch f q r ihq ihr =>
    intro k
    simp only [TM2.stepAux,growth]
    cases hf : f c.var
    · simpa only [Bool.cond_false] using
        (le_trans (ihr c B hc k) (Nat.add_le_add_left (Nat.le_max_right _ _) B))
    · simpa only [Bool.cond_true] using
        (le_trans (ihq c B hc k) (Nat.add_le_add_left (Nat.le_max_left _ _) B))
  | goto f => simpa [TM2.stepAux,growth,Fits] using hc
  | halt => simpa [TM2.stepAux,growth,Fits] using hc

noncomputable def symbolicAux {N : ℕ} (hN : 0 < N) : Statement M → Symbolic M N → Symbolic M N
  | .push k f q, S => symbolicAux hN q (symPush S k f)
  | .peek k f q, S => symbolicAux hN q (symRead S k hN f)
  | .pop k f q, S => symbolicAux hN q (symDrop (symRead S k hN f) k)
  | .load f q, S => symbolicAux hN q (symLoad S f)
  | .branch f q r, S => symChoose (stateTable S (fun a => if f a then 1 else 0))
      (symbolicAux hN q S) (symbolicAux hN r S)
  | .goto f, S => symGoto S f
  | .halt, S => symHalt S

lemma symbolicAux_rep {N : ℕ} (hN : 0 < N) (q : Statement M) (S : Symbolic M N)
    (c : M.Cfg) (y : ℕ → ZMod 3) (h : Represents S c y)
    (B : ℕ) (hc : Fits c B) (hr : B+growth q  ≤  N) :
    Represents (symbolicAux hN q S) (TM2.stepAux q c.var c.stk) y := by
  induction q generalizing S c B with
  | push k f q ih =>
    exact ih (symPush S k f) {c with stk := Function.update c.stk k (f c.var::c.stk k)}
      (symPush_rep S c y h k f) (B+1) (fits_push c B hc k f) (by simpa [growth,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using hr)
  | peek k f q ih =>
    exact ih (symRead S k hN f) {c with var := f c.var (c.stk k).head?}
      (symRead_rep S c y h k hN f) B hc hr
  | pop k f q ih =>
    exact ih (symDrop (symRead S k hN f) k)
      {c with var := f c.var (c.stk k).head?,stk := Function.update c.stk k (c.stk k).tail}
      (symDrop_rep _ _ y (symRead_rep S c y h k hN f) k (le_trans (hc k) (by dsimp only [growth] at hr; omega)))
      B (fits_drop c B hc k) hr
  | load f q ih =>
    exact ih (symLoad S f) {c with var := f c.var} (symLoad_rep S c y h f) B hc hr
  | branch f q r ihq ihr =>
    have hq : B+growth q  ≤  N := le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) B) hr
    have hr' : B+growth r  ≤  N := le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) B) hr
    have hrep := symChoose_rep (symbolicAux hN q S) (symbolicAux hN r S)
      (TM2.stepAux q c.var c.stk) (TM2.stepAux r c.var c.stk) y
      (ihq S c h B hc hq) (ihr S c h B hc hr')
      (stateTable S (fun a => if f a then 1 else 0)) (f c.var)
      (stateTable_eval S c y h _)
    cases hf : f c.var <;> simpa [symbolicAux,TM2.stepAux,hf] using hrep
  | goto f => exact symGoto_rep S c y h f
  | halt => exact symHalt_rep S c y h

end F3MachineCompiler

namespace F3MachineCompiler
open F3Tools Turing
open Classical

noncomputable def blend {α : Type} [Fintype α] (v f : α → Expr) : Expr :=
  Expr.sum (Finset.univ.toList.map (fun a => .times (v a) (f a)))

lemma blend_eval {α : Type} [Fintype α] (v f : α → Expr) (y : ℕ → ZMod 3) :
    (blend v f).eval y = ∑ a, (v a).eval y*(f a).eval y := by
  simp [blend,Expr.eval_sum,List.map_map,Expr.eval]

lemma blend_onehot {α : Type} [Fintype α] (v f : α → Expr) (y : ℕ → ZMod 3)
    (a : α) (hv : ∀ b, (v b).eval y = if b = a then 1 else 0) :
    (blend v f).eval y = (f a).eval y := by
  rw [blend_eval]
  simp [hv]

noncomputable def combine {M : BinaryMachine} {N : ℕ} {α : Type} [Fintype α]
    (v : α → Expr) (S : α → Symbolic M N) : Symbolic M N where
  label l := blend v (fun a => (S a).label l)
  state s := blend v (fun a => (S a).state s)
  stack k i := blend v (fun a => (S a).stack k i)

lemma combine_rep {M : BinaryMachine} {N : ℕ} {α : Type} [Fintype α]
    (v : α → Expr) (S : α → Symbolic M N) (y : ℕ → ZMod 3) (a : α)
    (hv : ∀ b, (v b).eval y = if b = a then 1 else 0) (c : M.Cfg)
    (hc : Represents (S a) c y) : Represents (combine v S) c y := by
  constructor
  · intro l
    exact (blend_onehot v (fun a => (S a).label l) y a hv).trans (hc.1 l)
  · constructor
    · intro s
      exact (blend_onehot v (fun a => (S a).state s) y a hv).trans (hc.2.1 s)
    · intro k i
      exact (blend_onehot v (fun a => (S a).stack k i) y a hv).trans (hc.2.2 k i)

noncomputable def symbolicStep {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (S : Symbolic M N) :
    Symbolic M N := combine S.label (fun l => match l with
      | none => S
      | some l => symbolicAux hN (M.code l) S)

def totalStep (M : BinaryMachine) (c : M.Cfg) : M.Cfg := (M.step c).getD c

lemma totalStep_eq (M : BinaryMachine) (c : M.Cfg) :
    totalStep M c = match c.l with
      | none => c
      | some l => TM2.stepAux (M.code l) c.var c.stk := by
  obtain ⟨l,v,S⟩ := c
  cases l <;> rfl

def machineGrowth (M : BinaryMachine) : ℕ := ∑ l, growth (M.code l)

lemma growth_le_machineGrowth (M : BinaryMachine) (l : M.Label) :
    growth (M.code l)  ≤  machineGrowth M := by
  unfold machineGrowth
  exact Finset.single_le_sum (f := fun l => growth (M.code l)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

lemma totalStep_fits (M : BinaryMachine) (c : M.Cfg) (B : ℕ) (hc : Fits c B) :
    Fits (totalStep M c) (B+machineGrowth M) := by
  cases hl : c.l with
  | none =>
    have he : totalStep M c = c := by simp [totalStep_eq,hl]
    rw [he]
    intro k
    exact le_trans (hc k) (Nat.le_add_right _ _)
  | some l =>
    have he : totalStep M c = TM2.stepAux (M.code l) c.var c.stk := by
      simp [totalStep_eq,hl]
    rw [he]
    intro k
    exact le_trans (stepAux_fits (M.code l) c B hc k)
      (Nat.add_le_add_left (growth_le_machineGrowth M l) B)

lemma symbolicStep_rep {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (S : Symbolic M N)
    (c : M.Cfg) (y : ℕ → ZMod 3) (h : Represents S c y) (B : ℕ)
    (hc : Fits c B) (hr : B+machineGrowth M  ≤  N) :
    Represents (symbolicStep hN S) (totalStep M c) y := by
  unfold symbolicStep
  apply combine_rep S.label _ y c.l (fun l => by
    have hh := h.1 l
    by_cases hl : l = c.l <;> simpa only [if_pos,if_neg,hl] using hh)
  cases hl : c.l with
  | none => simpa [totalStep_eq,hl] using h
  | some l =>
    simpa [totalStep_eq,hl] using
      symbolicAux_rep hN (M.code l) S c y h B hc
        (le_trans (Nat.add_le_add_left (growth_le_machineGrowth M l) B) hr)

end F3MachineCompiler

-- Source: Solutions.T31.Clock

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open Turing OAI.MetricKMedian.Binary

lemma trace_total_iterate {α : Type} {f : α → Option α} {n : ℕ} {a b : α}
    (h : Trace f n a b) : (fun x => (f x).getD x)^[n] a = b := by
  induction h with
  | refl a => rfl
  | @cons n a b c hab hbc ih =>
    rw [Function.iterate_succ_apply]
    simpa only [hab,Option.getD_some] using ih

lemma iterate_of_fixed {α : Type} (f : α → α) (b : α) (h : f b = b) (n : ℕ) : f^[n] b = b := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply,h,ih]

lemma clock_outputs (M : BinaryMachine) (s t : List Bool) (T : ℕ)
    (h : TM2OutputsInTime M.tm s (some t) T) :
    (totalStep M)^[T] (M.initialCfg s) = M.finalCfg t := by
  have ht : Trace M.step h.steps (M.initialCfg s) (M.finalCfg t) := Trace.of_inTime h
  have hi := trace_total_iterate ht
  change (totalStep M)^[h.steps] (M.initialCfg s) = M.finalCfg t at hi
  have hf : totalStep M (M.finalCfg t) = M.finalCfg t := by simp [totalStep_eq,Machine.finalCfg]
  rw [← Nat.sub_add_cancel h.steps_le_m,Function.iterate_add_apply,hi]
  exact iterate_of_fixed (totalStep M) (M.finalCfg t) hf _

lemma clock_fits (M : BinaryMachine) (s : List Bool) (t : ℕ) :
    Fits ((totalStep M)^[t] (M.initialCfg s)) (s.length+t*machineGrowth M) := by
  induction t with
  | zero =>
    intro k
    simp only [Function.iterate_zero,Function.id_def,Machine.initialCfg,Nat.zero_mul,Nat.add_zero]
    split_ifs <;> simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    have h := totalStep_fits M _ _ ih
    simpa only [Nat.succ_mul,Nat.add_assoc] using h

end F3MachineCompiler

-- Source: Solutions.T31.Coordinates

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

abbrev Coordinate (M : BinaryMachine) (N : ℕ) := Option M.Label ⊕ (M.State ⊕ (M.K × Fin N))
def dimension (M : BinaryMachine) (N : ℕ) := Fintype.card (Option M.Label)+
  (Fintype.card M.State+Fintype.card M.K*N)

noncomputable def coordinates (M : BinaryMachine) (N : ℕ) : Coordinate M N ≃ Fin (dimension M N) :=
  (Equiv.sumCongr (Fintype.equivFin (Option M.Label))
    ((Equiv.sumCongr (Fintype.equivFin M.State)
      ((Equiv.prodCongr (Fintype.equivFin M.K) (Equiv.refl (Fin N))).trans finProdFinEquiv)).trans
        finSumFinEquiv)).trans finSumFinEquiv

def Symbolic.get {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) : Coordinate M N → Expr
  | .inl l => S.label l
  | .inr (.inl s) => S.state s
  | .inr (.inr (k,i)) => S.stack k i

def Symbolic.of {M : BinaryMachine} {N : ℕ} (v : Coordinate M N → Expr) : Symbolic M N where
  label l := v (.inl l)
  state s := v (.inr (.inl s))
  stack k i := v (.inr (.inr (k,i)))

lemma Symbolic.get_of {M : BinaryMachine} {N : ℕ} (v : Coordinate M N → Expr) :
    (Symbolic.of v).get = v := by funext i; rcases i with _|(_|⟨_,_⟩) <;> rfl

noncomputable def configurationValue {M : BinaryMachine} {N : ℕ} (c : M.Cfg) : Coordinate M N → ZMod 3
  | .inl l => if l = c.l then 1 else 0
  | .inr (.inl s) => if s = c.var then 1 else 0
  | .inr (.inr (k,i)) => cell (c.stk k) i.val

lemma represents_iff {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg) (y : ℕ → ZMod 3) :
    Represents S c y ↔ ∀ i, (S.get i).eval y = configurationValue c i := by
  constructor
  · intro h i
    rcases i with l|(s|⟨k,i⟩)
    · exact h.1 l
    · exact h.2.1 s
    · exact h.2.2 k i
  · intro h
    exact ⟨fun l => h (.inl l),fun s => h (.inr (.inl s)),fun k i => h (.inr (.inr (k,i)))⟩

noncomputable def expressionList {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) : List Expr :=
  List.ofFn (fun i : Fin (dimension M N) => S.get ((coordinates M N).symm i))

noncomputable def store {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N) : CompileState :=
  batch p (expressionList S)

noncomputable def stored {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N) : Symbolic M N :=
  Symbolic.of (fun i => .input ((store p S).2.getD (coordinates M N i).val 0))

lemma batch_component (p : ℕ) (es : List Expr) (he : ∀ e ∈ es, e.Bounded p)
    (y : ℕ → ZMod 3) (hz : ∀ a, p  ≤  a → y a = 0) (i : ℕ) (hi : i < es.length) :
    rawRun (batch p es).1.1 y ((batch p es).2.getD i 0) = (es.getD i .zero).eval y := by
  have hs := batch_correct p es he y hz
  have hl := congrArg List.length hs.values
  simp only [List.length_map] at hl
  have hleft : i < (batch p es).2.length := by omega
  have hh := congrArg (fun l : List (ZMod 3) => l.getD i 0) hs.values
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hleft),
    List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi)] at hh
  simp only [List.getElem_map] at hh
  simpa only [List.getD_eq_getElem _ _ hleft,List.getD_eq_getElem _ _ hi] using hh

lemma stored_rep {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (hs : Represents S c y) (hb : ∀ e ∈ expressionList S, e.Bounded p)
    (hz : ∀ a, p  ≤  a → y a = 0) :
    Represents (stored p S) c (rawRun (store p S).1.1 y) := by
  rw [represents_iff]
  intro i
  simp only [stored,Symbolic.get_of,Expr.eval]
  have hi : (coordinates M N i).val < (expressionList S).length := by
    simp only [expressionList,List.length_ofFn]; exact (coordinates M N i).isLt
  have h := batch_component p (expressionList S) hb y hz (coordinates M N i).val hi
  have he : (expressionList S).getD (coordinates M N i).val .zero = S.get i := by
    rw [List.getD_eq_getElem _ _ hi]
    simp [expressionList,List.getElem_ofFn]
  rw [he] at h
  exact h.trans ((represents_iff S c y).mp hs i)

end F3MachineCompiler

-- Source: Solutions.T31.Inputs

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

def Inputs (P : ℕ → Prop) : Expr → Prop
  | .zero | .one => True
  | .input i => P i
  | .plus a b | .times a b => Inputs P a ∧ Inputs P b
  | .minus a => Inputs P a

lemma inputs_bounded (p : ℕ) (e : Expr) (h : Inputs (fun i => i < p) e) : e.Bounded p := by
  induction e with
  | zero | one => trivial
  | input i => exact h
  | plus a b ha hb | times a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | minus a ha => exact ha h

lemma inputs_code (P : ℕ → Prop) (e : Expr) (he : Inputs P e) :
    ∀ t ∈ e.code, t.1 ≠ 1 ∨ P t.2 := by
  induction e with
  | zero | one => simp [Expr.code]
  | input i => simpa [Expr.code,Inputs] using he
  | plus a b ha hb | times a b ha hb =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with (ht|ht)|rfl
    · exact ha he.1 t ht
    · exact hb he.2 t ht
    · simp
  | minus a ha =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with ht|rfl
    · exact ha he t ht
    · simp

lemma inputs_sum (P : ℕ → Prop) (xs : List Expr) (h : ∀ e ∈ xs, Inputs P e) :
    Inputs P (Expr.sum xs) := by
  induction xs with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun a ha => h a (by simp [ha]))⟩

lemma inputs_literal (P : ℕ → Prop) (v : ZMod 3) : Inputs P (literal v) := by
  unfold literal
  split_ifs <;> trivial

lemma inputs_select {α : Type} [Fintype α] (P : ℕ → Prop) (v : α → Expr) (f : α → ZMod 3)
    (h : ∀ a, Inputs P (v a)) : Inputs P (select v f) := by
  apply inputs_sum
  intro e he
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
  exact ⟨h a,inputs_literal P _⟩

lemma inputs_blend {α : Type} [Fintype α] (P : ℕ → Prop) (v f : α → Expr)
    (hv : ∀ a, Inputs P (v a)) (hf : ∀ a, Inputs P (f a)) : Inputs P (blend v f) := by
  apply inputs_sum
  intro e he
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
  exact ⟨hv a,hf a⟩

lemma inputs_choose (P : ℕ → Prop) (a b c : Expr)
    (ha : Inputs P a) (hb : Inputs P b) (hc : Inputs P c) : Inputs P (a.choose b c) :=
  ⟨⟨ha,hb⟩,⟨⟨trivial,ha⟩,hc⟩⟩

lemma inputs_isZero (P : ℕ → Prop) (e : Expr) (h : Inputs P e) : Inputs P e.isZero :=
  ⟨trivial,⟨h,h⟩⟩

def Safe {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N) : Prop :=
  (∀ l, Inputs P (S.label l)) ∧ (∀ s, Inputs P (S.state s)) ∧ (∀ k i, Inputs P (S.stack k i))

lemma safe_get {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N) (h : Safe P S)
    (i : Coordinate M N) : Inputs P (S.get i) := by
  rcases i with l|(s|⟨k,i⟩)
  · exact h.1 l
  · exact h.2.1 s
  · exact h.2.2 k i

lemma safe_expressionList {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) : ∀ e ∈ expressionList S, Inputs P e := by
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact safe_get P S h _

lemma inputs_stateTable {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (f : M.State → ZMod 3) : Inputs P (stateTable S f) := inputs_select P _ _ h.2.1

lemma inputs_headTable {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (k : M.K) (hN : 0 < N) (f : M.State → Option Bool → ZMod 3) :
    Inputs P (headTable S k hN f) := by
  apply inputs_select
  intro a
  exact ⟨h.2.1 a.1,inputs_isZero P _ ⟨h.2.2 _ _,inputs_literal P _⟩⟩

lemma safe_symLoad {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (f : M.State → M.State) : Safe P (symLoad S f) :=
  ⟨h.1,fun _ => inputs_stateTable P S h _,h.2.2⟩

lemma safe_symRead {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (k : M.K) (hN : 0 < N) (f : M.State → Option Bool → M.State) :
    Safe P (symRead S k hN f) := ⟨h.1,fun s => inputs_headTable P S h k hN (fun a b => if f a b = s then 1 else 0),h.2.2⟩

lemma safe_symPush {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (k : M.K) (f : M.State → Bool) : Safe P (symPush S k f) := by
  refine ⟨h.1,h.2.1,?_⟩
  intro j i
  unfold symPush
  dsimp only
  split_ifs
  · exact inputs_stateTable P S h _
  · exact h.2.2 _ _
  · exact h.2.2 _ _

lemma safe_symDrop {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (k : M.K) : Safe P (symDrop S k) := by
  refine ⟨h.1,h.2.1,?_⟩
  intro j i
  unfold symDrop
  dsimp only
  split_ifs
  · exact h.2.2 _ _
  · trivial
  · exact h.2.2 _ _

lemma safe_symGoto {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) (f : M.State → M.Label) : Safe P (symGoto S f) :=
  ⟨fun _ => inputs_stateTable P S h _,h.2.1,h.2.2⟩

lemma safe_symHalt {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (h : Safe P S) : Safe P (symHalt S) := ⟨fun _ => inputs_literal P _,h.2.1,h.2.2⟩

lemma safe_symChoose {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S T : Symbolic M N)
    (hs : Safe P S) (ht : Safe P T) (a : Expr) (ha : Inputs P a) : Safe P (symChoose a S T) :=
  ⟨fun l => inputs_choose P _ _ _ ha (hs.1 l) (ht.1 l),
    fun s => inputs_choose P _ _ _ ha (hs.2.1 s) (ht.2.1 s),
    fun k i => inputs_choose P _ _ _ ha (hs.2.2 k i) (ht.2.2 k i)⟩

lemma safe_symbolicAux {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (hN : 0 < N)
    (q : Statement M) (S : Symbolic M N) (h : Safe P S) : Safe P (symbolicAux hN q S) := by
  induction q generalizing S with
  | push k f q ih => exact ih _ (safe_symPush P S h k f)
  | peek k f q ih => exact ih _ (safe_symRead P S h k hN f)
  | pop k f q ih => exact ih _ (safe_symDrop P _ (safe_symRead P S h k hN f) k)
  | load f q ih => exact ih _ (safe_symLoad P S h f)
  | branch f q r ihq ihr =>
    exact safe_symChoose P _ _ (ihq S h) (ihr S h) _ (inputs_stateTable P S h _)
  | goto f => exact safe_symGoto P S h f
  | halt => exact safe_symHalt P S h

lemma safe_combine {M : BinaryMachine} {N : ℕ} {α : Type} [Fintype α]
    (P : ℕ → Prop) (v : α → Expr) (S : α → Symbolic M N) (hv : ∀ a, Inputs P (v a))
    (hs : ∀ a, Safe P (S a)) : Safe P (combine v S) :=
  ⟨fun l => inputs_blend P v _ hv (fun a => (hs a).1 l),
    fun s => inputs_blend P v _ hv (fun a => (hs a).2.1 s),
    fun k i => inputs_blend P v _ hv (fun a => (hs a).2.2 k i)⟩

lemma safe_symbolicStep {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (hN : 0 < N)
    (S : Symbolic M N) (h : Safe P S) : Safe P (symbolicStep hN S) := by
  apply safe_combine P S.label _ h.1
  intro a
  cases a with
  | none => exact h
  | some a => exact safe_symbolicAux P hN (M.code a) S h

end F3MachineCompiler

-- Source: Solutions.L3.Base

namespace L3

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

section
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem foldl_env (f : α → β → γ → β) (x : α) (l : List γ) (b : β) :
    l.foldl (fun (p : α × β) a => (p.1, f p.1 p.2 a)) (x, b) = (x, l.foldl (f x) b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact ih _

theorem fold_size (f : α → β → γ → β) (G : Polynomial ℕ)
    (hG : ∀ x b a, (enc (f x b a)).length  ≤  (enc b).length + G.eval ((enc x).length + (enc a).length))
    (x : α) (M : ℕ) (pre : List γ) (hpre : ∀ a ∈ pre, (enc a).length  ≤  M) (acc : β) :
    (enc (pre.foldl (f x) acc)).length  ≤  (enc acc).length + pre.length * G.eval ((enc x).length + M) := by
  induction pre generalizing acc with
  | nil => simp
  | cons a pre ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (fun a' ha' => hpre a' (List.mem_cons_of_mem _ ha')) (f x acc a)
    have h2 := hG x acc a
    have h3 := polynomial_eval_mono G (show (enc x).length + (enc a).length  ≤  (enc x).length + M by
      have := hpre a (List.mem_cons_self); omega)
    nlinarith

theorem Poly.list_foldl [Inhabited γ] {f : α → β → γ → β} {as : α → List γ} {b0 : α → β}
    (hf : Poly (fun y : (α × β) × γ => f y.1.1 y.1.2 y.2)) (has : Poly as) (hb0 : Poly b0)
    (G : Polynomial ℕ)
    (hG : ∀ x b a, (enc (f x b a)).length  ≤  (enc b).length + G.eval ((enc x).length + (enc a).length)) :
    Poly (fun x => (as x).foldl (f x) (b0 x)) := by
  have hop : Poly (fun y : (α × β) × γ => (y.1.1, f y.1.1 y.1.2 y.2)) :=
    Poly.pair (Poly.comp Poly.fst Poly.fst) hf
  let P : PolyProgram (encodePair (encodePair enc enc) enc) (encodePair enc enc)
      (fun y : (α × β) × γ => (y.1.1, f y.1.1 y.1.2 y.2)) := hop.program
  let FP := PolyProgram.listFold (ea := (enc : γ → List Bool)) (eb := encodePair (enc : α → List Bool) (enc : β → List Bool))
    P default (X + X * G) (by
      intro as' b' pre suf hsplit
      obtain ⟨x, acc⟩ := b'
      rw [foldl_env]
      have hpre : ∀ a ∈ pre, (enc a).length  ≤  (encodeList enc as').length := by
        intro a ha
        exact EncodedList.member_length _ as' a (by rw [hsplit]; exact List.mem_append_left _ ha)
      have hs := fold_size f G hG x _ pre hpre acc
      have hlen : pre.length  ≤  (encodeList enc as').length := by
        have h1 := EncodedList.length_le (enc : γ → List Bool) as'
        have h2 : pre.length  ≤  as'.length := by rw [hsplit, List.length_append]; omega
        omega
      simp only [encodePair_length, eval_add, eval_X, eval_mul]
      set L := 2 * (encodeList enc as').length + 1 + (2 * (enc x).length + 1 + (enc acc).length)
      have hG' := polynomial_eval_mono G (show (enc x).length + (encodeList enc as').length  ≤  L by omega)
      have hm : pre.length * G.eval ((enc x).length + (encodeList enc as').length)  ≤  L * G.eval L :=
        Nat.mul_le_mul (by omega) hG'
      change 2 * (enc x).length + 1 + (enc (pre.foldl (f x) acc)).length  ≤  L + L * G.eval L
      omega)
  have hFP : Poly (fun z : List γ × (α × β) =>
      z.1.foldl (fun b a => (fun y : (α × β) × γ => (y.1.1, f y.1.1 y.1.2 y.2)) (b, a)) z.2) := ⟨FP⟩
  have hin : Poly (fun x => (as x, (x, b0 x))) := by fun_prop
  have h := Poly.comp Poly.snd (Poly.comp hFP hin)
  simp only [foldl_env] at h
  exact h

end

section Arith
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem Poly.nat_mod : Poly (fun x : ℕ × ℕ => x.1 % x.2) := ⟨PolyProgram.natMod⟩
@[fun_prop] theorem Poly.nat_div : Poly (fun x : ℕ × ℕ => x.1 / x.2) := ⟨PolyProgram.natDiv⟩
@[fun_prop] theorem Poly.nat_mod_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x % g x) := Poly.comp Poly.nat_mod (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_div_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) := Poly.comp Poly.nat_div (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_add_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_mul_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.nat_mul (Poly.pair hf hg)
@[fun_prop] theorem Poly.nat_sub_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)
@[fun_prop] theorem Poly.bool_and_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) := Poly.comp Poly.bool_and (Poly.pair hf hg)
@[fun_prop] theorem Poly.bool_or_comp {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x || g x) := Poly.comp Poly.bool_or (Poly.pair hf hg)
@[fun_prop] theorem Poly.bool_not_comp {f : α → Bool} (hf : Poly f) :
    Poly (fun x => !f x) := Poly.comp Poly.bool_not hf
@[fun_prop] theorem Poly.nat_beq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x == g x) := by
  have h := Poly.nat_eq_comp hf hg
  have he : (fun x => decide (f x = g x)) = (fun x => f x == g x) := by
    funext x; cases h : (f x == g x) <;> simp_all
  rwa [he] at h

theorem list_all_eq_findIdx {γ : Type} (l : List γ) (p : γ → Bool) :
    l.all p = (l.findIdx (fun b => !p b) == l.length) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.all_cons, List.findIdx_cons, List.length_cons]
    cases h : p a <;> simp [ih]

@[fun_prop] theorem Poly.list_all [Inhabited β] {p : α → β → Bool} {as : α → List β}
    (hp : Poly (fun x : α × β => p x.1 x.2)) (ha : Poly as) : Poly (fun x => (as x).all (p x)) := by
  have h : Poly (fun x => ((as x).findIdx (fun b => !p x b) == (as x).length)) := by fun_prop
  simpa only [← list_all_eq_findIdx] using h

@[fun_prop] theorem Poly.list_take [Inhabited β] : Poly (fun x : List β × ℕ => x.1.take x.2) :=
  ⟨PolyProgram.listTake enc default⟩
@[fun_prop] theorem Poly.list_drop [Inhabited β] : Poly (fun x : List β × ℕ => x.1.drop x.2) :=
  ⟨PolyProgram.listDrop enc default⟩
@[fun_prop] theorem Poly.list_take_comp [Inhabited β] {l : α → List β} {k : α → ℕ} (hl : Poly l) (hk : Poly k) :
    Poly (fun x => (l x).take (k x)) := Poly.comp Poly.list_take (Poly.pair hl hk)
@[fun_prop] theorem Poly.list_drop_comp [Inhabited β] {l : α → List β} {k : α → ℕ} (hl : Poly l) (hk : Poly k) :
    Poly (fun x => (l x).drop (k x)) := Poly.comp Poly.list_drop (Poly.pair hl hk)
@[fun_prop] theorem Poly.list_append_comp [Inhabited β] {l l' : α → List β} (hl : Poly l) (hl' : Poly l') :
    Poly (fun x => l x ++ l' x) := Poly.comp Poly.list_append (Poly.pair hl hl')
@[fun_prop] theorem Poly.list_length_comp [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => (l x).length) := Poly.comp Poly.list_length hl
@[fun_prop] theorem Poly.list_range_length [Inhabited β] {l : α → List β} (hl : Poly l) :
    Poly (fun x => List.range (l x).length) :=
  Poly.comp (f := fun xs : List β => List.range xs.length) Poly.list_indices hl
@[fun_prop] theorem Poly.list_zip_comp [Inhabited β] {γ : Type} [Coding γ] [Inhabited γ]
    {l : α → List β} {l' : α → List γ} (hl : Poly l) (hl' : Poly l') :
    Poly (fun x => (l x).zip (l' x)) := Poly.comp Poly.list_zip (Poly.pair hl hl')
@[fun_prop] theorem Poly.list_cons_comp {a : α → β} {l : α → List β} (ha : Poly a) (hl : Poly l) :
    Poly (fun x => a x :: l x) := Poly.comp Poly.list_cons (Poly.pair ha hl)

@[fun_prop] theorem Poly.list_getD_fn (d : β) {l : α → List β} {i : α → ℕ} (hl : Poly l) (hi : Poly i) :
    Poly (fun x => (l x).getD (i x) d) := by
  simp only [List.getD_eq_getElem?_getD]
  exact Poly.list_getD_comp d hl hi

theorem getD_var {γ : Type} [Inhabited γ] (l : List γ) (i : ℕ) (d : γ) :
    l.getD i d = if i < l.length then l.getD i default else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default _ _ (by omega)]

@[fun_prop] theorem Poly.list_getD_var [Inhabited β] {l : α → List β} {i : α → ℕ} {d : α → β}
    (hl : Poly l) (hi : Poly i) (hd : Poly d) : Poly (fun x => (l x).getD (i x) (d x)) := by
  simp only [getD_var (l _) (i _) (d _)]
  fun_prop

@[fun_prop] theorem Poly.nat_min_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => min (f x) (g x)) := by
  have : (fun x => min (f x) (g x)) = (fun x => if f x  ≤  g x then f x else g x) := by
    funext x; split_ifs with h <;> omega
  rw [this]; fun_prop

@[fun_prop] theorem Poly.nat_max_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => max (f x) (g x)) := by
  have : (fun x => max (f x) (g x)) = (fun x => if f x  ≤  g x then g x else f x) := by
    funext x; split_ifs with h <;> omega
  rw [this]; fun_prop

/-- `List.range k` for a number `k` given in binary is *not* polynomial; we provide it when the
number is bounded by the length of a list in the input. -/
theorem range_eq_take (k : ℕ) (l : List β) (h : k  ≤  l.length) :
    List.range k = (List.range l.length).take k := by
  rw [List.take_range, Nat.min_eq_left h]

end Arith

end L3





/-! # Machines with explicit (non-polynomial) running times -/

namespace L3

open OAI.MetricKMedian.Binary Polynomial

/-- A machine computing `f` from `ea`-codes to `eb`-codes within `T a` steps. -/
structure Timed {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) (T : α → ℕ) where
  machine : Machine
  run : ∀ a, ∃ t, t  ≤  T a ∧ Trace machine.step t (machine.initialCfg (ea a)) (machine.finalCfg (eb (f a)))

namespace Timed

variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}

noncomputable def ofPoly {f : α → β} (P : PolyProgram ea eb f) :
    Timed ea eb f (fun a => P.time.eval (ea a).length) where
  machine := P.machine
  run a := by
    have hp := P.outputs a
    exact ⟨hp.steps, hp.steps_le_m, Trace.of_iterate hp.evals_in_steps⟩

noncomputable def comp {f : α → β} {g : β → γ} {T1 : α → ℕ} {T2 : β → ℕ}
    (P : Timed ea eb f T1) (Q : Timed eb ec g T2) :
    Timed ea ec (fun a => g (f a)) (fun a => T1 a + 2 * (eb (f a)).length + 2 + T2 (f a)) where
  machine := Compose.machine P.machine Q.machine
  run a := by
    obtain ⟨t1, h1, tr1⟩ := P.run a
    obtain ⟨t2, h2, tr2⟩ := Q.run (f a)
    exact ⟨_, by omega, Compose.run P.machine Q.machine tr1 tr2⟩

noncomputable def mono {f : α → β} {T T' : α → ℕ} (P : Timed ea eb f T) (h : ∀ a, T a  ≤  T' a) :
    Timed ea eb f T' where
  machine := P.machine
  run a := by
    obtain ⟨t, ht, tr⟩ := P.run a
    exact ⟨t, ht.trans (h a), tr⟩

noncomputable def congr {f f' : α → β} {T : α → ℕ} (P : Timed ea eb f T) (h : ∀ a, f a = f' a) :
    Timed ea eb f' T where
  machine := P.machine
  run a := by rw [← h a]; exact P.run a

/-- Loops with explicit iteration counts and sizes. -/
noncomputable def loop {body : α → β ⊕ α} (P : PolyProgram ea (encodeLoop ea eb) body) (g : α → β)
    (N S : α → ℕ) (h : ∀ a, BoundedRun ea body (S a) (N a) a (g a)) :
    Timed ea eb g (fun a => N a * P.passTime (S a)) where
  machine := Loop.machine P.machine
  run a := by
    obtain ⟨t, ht, tr⟩ := P.run_loop (h a)
    exact ⟨t, ht, tr⟩

end Timed

end L3


-- Source: Solutions.L3.Prepare

set_option maxHeartbeats 1000000

namespace L3
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial F3SubsetSum

def inputN (w : List Bool) : ℕ := w.findIdx (! ·)
def inputM (w : List Bool) : ℕ := w.length - inputN w - 1

def base (n m : ℕ) : ℕ := (m + n - 1) / n
def exponent (d n m : ℕ) : ℕ := d * ((n * n + m - 1) / m)
def clock (d n m : ℕ) : ℕ := base n m ^ exponent d n m

def large (K : ℕ) (w : List Bool) : Bool := decide (K * inputN w  ≤  inputM w)
def bases (w : List Bool) : List Bool :=
  ((List.range (w ++ [true]).length).take (base (inputN w) (inputM w))).map (fun _ => true)

abbrev Payload := (Bool × List Bool) × List Bool
abbrev PowerState := Payload × (ℕ × List Bool)

def powerBody (s : PowerState) : (Payload × List Bool) ⊕ PowerState :=
  if s.2.1 == 0 then .inl (s.1,s.2.2)
  else .inr (s.1,(s.2.1-1,s.1.2.flatMap (fun _ => s.2.2)))

def copies (bs xs : List Bool) : List Bool := bs.flatMap (fun _ => xs)
def powerList (bs : List Bool) : ℕ → List Bool → List Bool
  | 0, xs => xs
  | k+1, xs => powerList bs k (copies bs xs)

def powerResult (s : PowerState) : Payload × List Bool :=
  (s.1,powerList s.1.2 s.2.1 s.2.2)

def powerSize (s : PowerState) : ℕ :=
  2 * (enc s.1).length + 3 + 2 * s.2.1.size +
    max 1 (s.1.2.length ^ s.2.1) * (enc s.2.2).length

def start (K d : ℕ) (w : List Bool) : PowerState :=
  (((large K w,w),bases w),
    (if large K w then exponent d (inputN w) (inputM w) else 0,
     if large K w then [true] else []))

def finish (s : Payload × List Bool) : List Bool :=
  if s.1.1.1 then true :: (s.1.1.2 ++ [false] ++ s.2) else false :: s.1.1.2

@[fun_prop] theorem inputN_poly : Poly inputN := by
  unfold inputN
  fun_prop

@[fun_prop] theorem inputM_poly : Poly inputM := by
  unfold inputM
  fun_prop

@[fun_prop] theorem large_poly (K : ℕ) : Poly (large K) := by
  unfold large
  fun_prop

@[fun_prop] theorem bases_poly : Poly bases := by
  unfold bases base
  fun_prop

@[fun_prop] theorem start_poly (K d : ℕ) : Poly (start K d) := by
  unfold start exponent
  fun_prop

@[fun_prop] theorem finish_poly : Poly finish := by
  unfold finish
  fun_prop

noncomputable def powerProgram : PolyProgram enc (encodeLoop enc enc) powerBody := by
  have hp : Poly (fun s : PowerState => s.2.1 == 0) := by fun_prop
  have hd : Poly (fun s : PowerState => (s.1,s.2.2)) := by fun_prop
  have hc : Poly (fun s : PowerState => (s.1,(s.2.1-1,s.1.2.flatMap (fun _ => s.2.2)))) := by
    fun_prop
  exact (PolyProgram.ite hp.program
    (hc.program.comp (PolyProgram.injectRight enc enc))
    (hd.program.comp (PolyProgram.injectLeft enc enc))).congr _ (fun _ => rfl)

theorem enc_bool_length (xs : List Bool) : (enc xs).length = 3 * xs.length :=
  BooleanLists.length xs

theorem enc_pair_length {α β : Type} [Coding α] [Coding β] (x : α × β) :
    (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length :=
  encodePair_length _ _ _

theorem enc_nat_length (n : ℕ) : (enc n).length = n.size := Nat.size_eq_bits_len n

theorem copies_length (bs xs : List Bool) : (copies bs xs).length = bs.length * xs.length := by
  simp [copies,List.length_flatMap,List.sum_const_nat]

theorem powerList_length (bs : List Bool) (k : ℕ) (xs : List Bool) :
    (powerList bs k xs).length = bs.length ^ k * xs.length := by
  induction k generalizing xs with
  | zero => simp [powerList]
  | succ k ih => simp only [powerList,ih,copies_length,pow_succ]; ring

theorem powerList_true (bs : List Bool) (k : ℕ) :
    powerList bs k [true] = List.replicate (bs.length ^ k) true := by
  have h : ∀ k xs, (∀ x ∈ xs, x = true) → ∀ x ∈ powerList bs k xs, x = true := by
    intro k
    induction k with
    | zero => intro xs hx; exact hx
    | succ k ih =>
      intro xs hx
      apply ih
      intro x hm
      simp only [copies,List.mem_flatMap] at hm
      obtain ⟨_,_,hm⟩ := hm
      exact hx x hm
  apply List.eq_replicate_iff.mpr
  exact ⟨by simp [powerList_length],h k [true] (by simp)⟩

theorem powerRun (p : Payload) (k : ℕ) (xs : List Bool) (S : ℕ)
    (hS : 2 * (enc p).length + 3 + 2 * k.size +
      max 1 (p.2.length ^ k) * (enc xs).length  ≤  S) :
    BoundedRun enc powerBody S (k+1) (p,(k,xs)) (p,powerList p.2 k xs) := by
  induction k generalizing xs with
  | zero =>
    apply BoundedRun.stop
    · simp only [enc_pair_length,enc_nat_length,Nat.size_zero,pow_zero,max_self,one_mul] at hS ⊢
      omega
    · simp [powerBody,powerList]
  | succ k ih =>
    apply BoundedRun.step (a' := (p,(k,copies p.2 xs)))
    · change (enc (p,(k+1,xs))).length  ≤  S
      simp only [enc_pair_length,enc_nat_length] at hS ⊢
      have hpow : 1  ≤  max 1 (p.2.length^(k+1)) := le_max_left _ _
      nlinarith
    · simp [powerBody,copies]
    · apply ih
      have hk : k.size  ≤  (k+1).size := Nat.size_le_size (Nat.le_succ k)
      have hlen : (enc (copies p.2 xs)).length = p.2.length * (enc xs).length := by
        simp only [enc_bool_length,copies_length]; ring
      have hprod : max 1 (p.2.length^k) * p.2.length  ≤  max 1 (p.2.length^(k+1)) := by
        by_cases hb : p.2.length = 0
        · simp [hb]
        · have hb1 : 1  ≤  p.2.length := by omega
          have hk1 : 1  ≤  p.2.length^k := one_le_pow₀ hb1
          have hk2 : 1  ≤  p.2.length^(k+1) := one_le_pow₀ hb1
          rw [max_eq_right hk1,max_eq_right hk2,pow_succ]
      change 2*(enc p).length+3+2*k.size+
        max 1 (p.2.length^k)*(enc (copies p.2 xs)).length  ≤  S
      rw [hlen]
      nlinarith

noncomputable def powerTimed : Timed enc enc powerResult
    (fun s => (s.2.1+1) * powerProgram.passTime (powerSize s)) :=
  Timed.loop powerProgram powerResult (fun s => s.2.1+1) powerSize
    (fun s => powerRun s.1 s.2.1 s.2.2 _ le_rfl)

noncomputable def prepare (K d : ℕ) :=
  (((Timed.ofPoly BooleanLists.packProgram).comp (Timed.ofPoly (start_poly K d).program)).comp
    powerTimed).comp ((Timed.ofPoly finish_poly.program).comp (Timed.ofPoly BooleanLists.unpackProgram))

end L3

namespace L3
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial F3SubsetSum

theorem inputN_word (n m : ℕ) : inputN (unaryD n ++ unary m) = n := by
  induction n with
  | zero => simp [inputN,unaryD,unary,List.findIdx_cons]
  | succ n ih =>
    simpa [inputN,unaryD,unary,List.replicate_succ,List.findIdx_cons,List.cons_append] using
      congrArg Nat.succ ih

theorem inputM_word (n m : ℕ) : inputM (unaryD n ++ unary m) = m := by
  unfold inputM
  rw [inputN_word]
  simp [unaryD,unary,List.length_append]

theorem base_bound (n m : ℕ) : base n m  ≤  n+m+1 := by
  unfold base
  exact (Nat.div_le_self _ _).trans (by omega)

theorem bases_length_word (n m : ℕ) :
    (bases (unaryD n ++ unary m)).length = base n m := by
  unfold bases
  rw [inputN_word,inputM_word]
  simp only [List.length_map,List.length_take,List.length_range,List.length_append,
    List.length_singleton,unaryD,unary,List.length_replicate]
  apply min_eq_left
  have := base_bound n m
  omega

theorem large_word (K n m : ℕ) :
    large K (unaryD n ++ unary m) = decide (K*n  ≤  m) := by
  simp [large,inputN_word,inputM_word]

theorem powerList_nil (bs : List Bool) (k : ℕ) : powerList bs k [] = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hnil : copies bs [] = [] := by
      simp only [copies]
      induction bs <;> simp_all
    simp only [powerList,hnil,ih]

theorem result_word (K d n m : ℕ) :
    finish (powerResult (start K d (unaryD n ++ unary m))) =
      if K*n  ≤  m then
        true :: (unaryD n ++ unaryD m ++ unary (clock d n m))
      else false :: (unaryD n ++ unary m) := by
  by_cases h : K*n  ≤  m
  · simp only [start,large_word,inputN_word,inputM_word]
    simp only [h,decide_true,if_true]
    simp only [powerResult,finish,powerList_true,bases_length_word,clock,if_true]
    simp [unaryD,unary,List.append_assoc]
  · simp only [start,large_word,inputN_word,inputM_word]
    simp [h,powerResult,finish,powerList]

theorem powerSize_result (s : PowerState) :
    (enc (powerResult s)).length  ≤  powerSize s := by
  unfold powerResult powerSize
  simp only [enc_pair_length,enc_bool_length,powerList_length]
  have hh : s.1.2.length^s.2.1  ≤  max 1 (s.1.2.length^s.2.1) := le_max_right _ _
  nlinarith

theorem exponent_bound (d n m : ℕ) :
    exponent d n m + 1  ≤  (d+1)*(n+m+1)^2 := by
  have h := Nat.div_le_self (n*n+m-1) m
  have he : (n*n+m-1)/m  ≤  n*n+m := h.trans (Nat.sub_le _ _)
  have hd := Nat.mul_le_mul_left d he
  have hn : n*n+m+1  ≤  (n+m+1)^2 := by nlinarith
  have hb : ∀ u : ℕ, d*u+1  ≤  (d+1)*(u+1) := by intro u; nlinarith
  unfold exponent
  exact (Nat.add_le_add_right hd 1).trans ((hb _).trans (Nat.mul_le_mul_left (d+1) hn))

theorem start_size_word (K d n m : ℕ) :
    powerSize (start K d (unaryD n ++ unary m))  ≤  
      (start_poly K d).program.sizeBound.eval (3*(n+m+1)) + 3*(if K*n  ≤  m then clock d n m else 0)+4 := by
  set w := unaryD n ++ unary m
  have hs := (start_poly K d).program.length_bound w
  have hw : (enc w).length = 3*(n+m+1) := by simp [enc_bool_length,w,unaryD,unary,Nat.add_assoc]
  rw [hw] at hs
  unfold powerSize
  have hparts : 2*(enc (start K d w).1).length + 3 + 2*(start K d w).2.1.size  ≤  
      (enc (start K d w)).length + 1 := by
    simp only [enc_pair_length,enc_nat_length]
    omega
  have hpow : max 1 ((start K d w).1.2.length^(start K d w).2.1) *
      (enc (start K d w).2.2).length  ≤  3*(if K*n  ≤  m then clock d n m else 0)+3 := by
    simp only [start]
    rw [show large K w = decide (K*n  ≤  m) from large_word K n m,
      show inputN w = n from inputN_word n m,
      show inputM w = m from inputM_word n m]
    by_cases h : K*n  ≤  m
    · simp only [if_pos h] at ⊢
      simp only [h,decide_true,ite_true,enc_bool_length,List.length_singleton,
        show (bases w).length = base n m from bases_length_word n m]
      change max 1 (clock d n m)*3  ≤  _
      have : max 1 (clock d n m)  ≤  clock d n m+1 := max_le (by omega) (by omega)
      omega
    · simp [h,enc_bool_length]
  exact le_trans (Nat.add_le_add_left hpow _) (by omega)

noncomputable def loopTime : Polynomial ℕ :=
  powerProgram.time + 2*powerProgram.sizeBound+3

theorem loopTime_eq (S : ℕ) : powerProgram.passTime S = loopTime.eval S := by
  simp [loopTime,PolyProgram.passTime]

noncomputable def RStart (K d : ℕ) : Polynomial ℕ :=
  (start_poly K d).program.sizeBound.comp (3*X)

noncomputable def RSize (K d : ℕ) : Polynomial ℕ := RStart K d + 3*X+4

noncomputable def RPrepare (K d : ℕ) : Polynomial ℕ :=
  BooleanLists.packProgram.time +
  2*(3*X)+2+(start_poly K d).program.time.comp (3*X)+
  2*RStart K d+2+
  C (d+1)*(X+1)^2 * loopTime.comp (RSize K d)+
  2*RSize K d+2+
  finish_poly.program.time.comp (RSize K d)+
  2*finish_poly.program.sizeBound.comp (RSize K d)+2+
  BooleanLists.unpackProgram.time.comp (finish_poly.program.sizeBound.comp (RSize K d))

end L3

namespace L3
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial F3SubsetSum

def budget (K d n m : ℕ) : ℕ := n+m+(if K*n  ≤  m then clock d n m else 0)+1

theorem prepare_run (K d n m : ℕ) :
    ∃ t  ≤  (RPrepare K d).eval (budget K d n m),
      Trace (prepare K d).machine.step t
        ((prepare K d).machine.initialCfg (unaryD n ++ unary m))
        ((prepare K d).machine.finalCfg
          (if K*n  ≤  m then true :: (unaryD n ++ unaryD m ++ unary (clock d n m))
            else false :: (unaryD n ++ unary m))) := by
  set w := unaryD n ++ unary m
  set s := start K d w
  set r := powerResult s
  set Z := budget K d n m
  obtain ⟨t,ht,tr⟩ := (prepare K d).run w
  refine ⟨t,?_,?_⟩
  · have hw : w.length = n+m+1 := by simp [w,unaryD,unary,Nat.add_assoc]
    have hZ : n+m+1  ≤  Z := by unfold Z budget; omega
    have hwe : (enc w).length  ≤  3*Z := by rw [enc_bool_length,hw]; omega
    have hs : (enc s).length  ≤  (RStart K d).eval Z := by
      have h := (start_poly K d).program.length_bound w
      exact h.trans (by
        simp only [RStart,eval_comp,eval_mul,eval_ofNat,eval_X]
        exact polynomial_eval_mono _ hwe)
    have hsize : powerSize s  ≤  (RSize K d).eval Z := by
      have h := start_size_word K d n m
      change powerSize s  ≤  _ at h
      have hmono := polynomial_eval_mono (start_poly K d).program.sizeBound
        (Nat.mul_le_mul_left 3 hZ)
      have hclock : (if K*n  ≤  m then clock d n m else 0)  ≤  Z := by unfold Z budget; omega
      simp only [RSize,RStart,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X] at ⊢
      omega
    have hr : (enc r).length  ≤  (RSize K d).eval Z := (powerSize_result s).trans hsize
    have hfin : (enc (finish r)).length  ≤  finish_poly.program.sizeBound.eval ((RSize K d).eval Z) :=
      (finish_poly.program.length_bound r).trans (polynomial_eval_mono _ hr)
    have hk : s.2.1+1  ≤  (d+1)*(Z+1)^2 := by
      have he := exponent_bound d n m
      have hm : (d+1)*(n+m+1)^2  ≤  (d+1)*(Z+1)^2 := by gcongr; omega
      change (if large K w then exponent d (inputN w) (inputM w) else 0)+1  ≤  _
      rw [show inputN w = n from inputN_word n m,show inputM w = m from inputM_word n m]
      split_ifs
      · omega
      · nlinarith
    have hloop : (s.2.1+1)*powerProgram.passTime (powerSize s)  ≤  
        (d+1)*(Z+1)^2 * loopTime.eval ((RSize K d).eval Z) := by
      rw [loopTime_eq]
      exact Nat.mul_le_mul hk (polynomial_eval_mono _ hsize)
    have hpt := polynomial_eval_mono BooleanLists.packProgram.time (hw ▸ hZ)
    have hst := polynomial_eval_mono (start_poly K d).program.time hwe
    have hft := polynomial_eval_mono finish_poly.program.time hr
    have hut := polynomial_eval_mono BooleanLists.unpackProgram.time hfin
    change t  ≤  
      BooleanLists.packProgram.time.eval w.length + 2*(enc w).length + 2 +
        (start_poly K d).program.time.eval (enc w).length +
        2*(enc s).length + 2 +
        (s.2.1+1)*powerProgram.passTime (powerSize s) +
        2*(enc r).length + 2 +
        (finish_poly.program.time.eval (enc r).length +
          2*(enc (finish r)).length + 2 +
          BooleanLists.unpackProgram.time.eval (enc (finish r)).length) at ht
    simp only [RPrepare,eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_ofNat,eval_pow,
      eval_one]
    omega
  · change Trace _ t _ ((prepare K d).machine.finalCfg (finish (powerResult (start K d w)))) at tr
    rw [show w=unaryD n++unary m from rfl,result_word] at tr
    exact tr

end L3

-- Source: Solutions.L2.GenerateCode

set_option maxHeartbeats 3000000
namespace F3Generate
open F3Tools F3Search OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

/-- Fold lists by appending a block on either side of the accumulator. -/
theorem Poly.fold_blocks {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    [Inhabited β] [Inhabited γ] (pre post : α → γ → List β) (as : α → List γ) (init : α → List β)
    (hp : Poly (fun x : α × γ => pre x.1 x.2))
    (hq : Poly (fun x : α × γ => post x.1 x.2)) (ha : Poly as) (hi : Poly init) :
    Poly (fun x => (as x).foldl (fun acc a => pre x a ++ acc ++ post x a) (init x)) := by
  apply L3.Poly.list_foldl (by fun_prop) ha hi
    (hp.program.sizeBound.comp (2*X+1)+hq.program.sizeBound.comp (2*X+1))
  intro x acc a
  have hpre := hp.program.length_bound (x,a)
  have hpost := hq.program.length_bound (x,a)
  dsimp only [Prod.fst,Prod.snd] at hpre hpost
  have he : (enc (x,a)).length  ≤  2*((enc x).length+(enc a).length)+1 := by
    rw [L3.enc_pair_length]; dsimp only [Prod.fst,Prod.snd]; omega
  have hp' := polynomial_eval_mono hp.program.sizeBound he
  have hq' := polynomial_eval_mono hq.program.sizeBound he
  change (encodeList enc (pre x a ++ acc ++ post x a)).length  ≤  _
  simp only [EncodedList.append,List.length_append,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X,eval_one]
  change (enc (pre x a)).length+(enc acc).length+(enc (post x a)).length  ≤  _
  omega

abbrev Env := List Bool

def nr (w : Env) := (List.range w.length).take (L3.inputN w)
def mr (w : Env) := (List.range w.length).take (L3.inputM w)

def sumCode (w : Env) (j : ℕ) (s : List Bool) : List Token :=
  (mr w).reverse.foldl (fun acc i =>
    [(if s.getD i false then 1 else 0,if s.getD i false then L3.inputN w*i+j else 0)] ++ acc ++ [(2,0)]) [(0,0)]

def goodCode (w : Env) (s : List Bool) : List Token :=
  if s.any id then (nr w).reverse.foldl (fun acc j =>
    [(0,1)] ++ sumCode w j s ++ sumCode w j s ++ [(3,0),(4,0),(2,0)] ++ acc ++ [(3,0)]) [(0,1)]
  else [(0,0)]

def searchPrefix (w : Env) (i : ℕ) (s : List Bool) : List Token :=
  goodCode w s ++ [(0,if s.getD i false then 1 else 0),(3,0),(0,1)] ++
    goodCode w s ++ [(4,0),(2,0)]

def searchCode (w : Env) (ss : List (List Bool)) (i : ℕ) : List Token :=
  ss.reverse.foldl (fun acc s => searchPrefix w i s ++ acc ++ [(3,0),(2,0)]) [(0,0)]

def outputCode (w : Env) (ss : List (List Bool)) : List Token :=
  (mr w).reverse.flatMap (searchCode w ss)

@[fun_prop] theorem nr_poly : Poly nr := by unfold nr; fun_prop
@[fun_prop] theorem mr_poly : Poly mr := by unfold mr; fun_prop

@[fun_prop] theorem reverse_poly {α : Type} [Coding α] [Inhabited α] : Poly (List.reverse : List α → List α) :=
  ⟨PolyProgram.listReverse enc default⟩

@[fun_prop] theorem sumCode_poly : Poly (fun x : (Env × ℕ) × List Bool => sumCode x.1.1 x.1.2 x.2) := by
  unfold sumCode
  apply Poly.fold_blocks <;> fun_prop

@[fun_prop] theorem sumCode_comp {α : Type} [Coding α] {f : α → Env} {g : α → ℕ}
    {h : α → List Bool} (hf : Poly f) (hg : Poly g) (hh : Poly h) :
    Poly (fun x => sumCode (f x) (g x) (h x)) :=
  Poly.comp sumCode_poly (Poly.pair (Poly.pair hf hg) hh)

@[fun_prop] theorem goodCode_poly : Poly (fun x : Env × List Bool => goodCode x.1 x.2) := by
  unfold goodCode
  have he : ∀ xs : List Bool, xs.any id = !(xs.all (fun b => !b)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons b xs ih => cases b <;> simp [ih]
  have hany : Poly (fun x : Env × List Bool => x.2.any id) := by
    simp_rw [he]
    fun_prop
  apply Poly.ite hany
  · apply Poly.fold_blocks <;> fun_prop
  · fun_prop

@[fun_prop] theorem searchCode_poly : Poly (fun x : (Env × List (List Bool)) × ℕ => searchCode x.1.1 x.1.2 x.2) := by
  unfold searchCode searchPrefix
  apply Poly.fold_blocks <;> fun_prop

@[fun_prop] theorem outputCode_poly : Poly (fun x : Env × List (List Bool) => outputCode x.1 x.2) := by
  unfold outputCode
  fun_prop

end F3Generate

-- Source: Solutions.T31.ExprMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

instance exprCoding : Coding Expr := ⟨fun e => enc e.code⟩

theorem Poly.same_output_encoding {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {f : α → β} {g : α → γ} (hf : Poly f) (h : ∀ a, enc (f a) = enc (g a)) : Poly g := by
  let P := hf.program
  refine ⟨⟨P.machine,P.time,?_⟩⟩
  intro a
  rw [← h a]
  exact P.outputs a

@[fun_prop] theorem exprCode_poly : Poly (Expr.code : Expr → List Token) :=
  Poly.same_output_encoding (Poly.identity (α := Expr)) (fun _ => rfl)

@[fun_prop] theorem exprCode_comp {α : Type} [Coding α] {f : α → Expr} (hf : Poly f) :
    Poly (fun x => (f x).code) := Poly.comp exprCode_poly hf

@[fun_prop] theorem exprInput_poly : Poly (Expr.input : ℕ → Expr) := by
  have h : Poly (fun i : ℕ => [(1,i)] : ℕ → List Token) := by fun_prop
  exact Poly.same_output_encoding h (fun _ => rfl)

@[fun_prop] theorem exprPlus_poly : Poly (fun x : Expr × Expr => Expr.plus x.1 x.2) := by
  have h : Poly (fun x : Expr × Expr => x.1.code++x.2.code++[(2,0)] : Expr × Expr → List Token) := by fun_prop
  exact Poly.same_output_encoding h (fun _ => rfl)

@[fun_prop] theorem exprTimes_poly : Poly (fun x : Expr × Expr => Expr.times x.1 x.2) := by
  have h : Poly (fun x : Expr × Expr => x.1.code++x.2.code++[(3,0)] : Expr × Expr → List Token) := by fun_prop
  exact Poly.same_output_encoding h (fun _ => rfl)

@[fun_prop] theorem exprMinus_poly : Poly (Expr.minus : Expr → Expr) := by
  have h : Poly (fun x : Expr => x.code++[(4,0)] : Expr → List Token) := by fun_prop
  exact Poly.same_output_encoding h (fun _ => rfl)

@[fun_prop] theorem exprInput_comp {α : Type} [Coding α] {f : α → ℕ} (hf : Poly f) :
    Poly (fun x => Expr.input (f x)) := Poly.comp exprInput_poly hf
@[fun_prop] theorem exprPlus_comp {α : Type} [Coding α] {f g : α → Expr} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => Expr.plus (f x) (g x)) := Poly.comp exprPlus_poly (Poly.pair hf hg)
@[fun_prop] theorem exprTimes_comp {α : Type} [Coding α] {f g : α → Expr} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => Expr.times (f x) (g x)) := Poly.comp exprTimes_poly (Poly.pair hf hg)
@[fun_prop] theorem exprMinus_comp {α : Type} [Coding α] {f : α → Expr} (hf : Poly f) :
    Poly (fun x => Expr.minus (f x)) := Poly.comp exprMinus_poly hf

@[fun_prop] theorem exprIsZero_poly : Poly (Expr.isZero : Expr → Expr) := by
  unfold Expr.isZero
  fun_prop
@[fun_prop] theorem exprIsZero_comp {α : Type} [Coding α] {f : α → Expr} (hf : Poly f) :
    Poly (fun x => (f x).isZero) := Poly.comp exprIsZero_poly hf
@[fun_prop] theorem exprChoose_poly : Poly (fun x : (Expr × Expr) × Expr => x.1.1.choose x.1.2 x.2) := by
  unfold Expr.choose
  fun_prop
@[fun_prop] theorem exprChoose_comp {α : Type} [Coding α] {a b c : α → Expr}
    (ha : Poly a) (hb : Poly b) (hc : Poly c) : Poly (fun x => (a x).choose (b x) (c x)) :=
  Poly.comp exprChoose_poly (Poly.pair (Poly.pair ha hb) hc)

lemma exprPlus_encoding_length (a b : Expr) :
    (enc (Expr.plus a b)).length = (enc a).length+(enc b).length+(enc ([(2,0)] : List Token)).length := by
  change (OAI.MetricKMedian.Binary.encodeList enc (a.code++b.code++[(2,0)])).length = _
  simp only [EncodedList.append,List.length_append]
  rfl

@[fun_prop] theorem exprSum_poly : Poly (Expr.sum : List Expr → Expr) := by
  have h : Poly (fun xs : List Expr => xs.reverse.foldl (fun acc e => Expr.plus e acc) Expr.zero) := by
    apply L3.Poly.list_foldl (α := List Expr) (β := Expr) (γ := Expr) (by fun_prop) (by fun_prop) (by fun_prop)
      (X+C (enc ([(2,0)] : List Token)).length)
    intro xs acc a
    rw [exprPlus_encoding_length]
    simp only [eval_add,eval_X,eval_C]
    omega
  change Poly (fun xs : List Expr => xs.foldr Expr.plus Expr.zero)
  simpa only [List.foldl_reverse] using h

@[fun_prop] theorem exprSum_comp {α : Type} [Coding α] {f : α → List Expr} (hf : Poly f) :
    Poly (fun x => Expr.sum (f x)) := Poly.comp exprSum_poly hf

end F3MachineCompiler

-- Source: Solutions.T31.Simulation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools Turing
open Classical

lemma stored_index {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N)
    (hb : Safe (fun i => i < p) S) (i : Coordinate M N) :
    p < (store p S).2.getD (coordinates M N i).val 0 ∧
      (store p S).2.getD (coordinates M N i).val 0 < (store p S).1.2 := by
  have hbound : ∀ e ∈ expressionList S, e.Bounded p :=
    fun e he => inputs_bounded p e (safe_expressionList _ S hb e he)
  have hs := batch_correct p (expressionList S) hbound (fun _ => 0) (by simp)
  have hl := congrArg List.length hs.values
  simp only [List.length_map] at hl
  have hi : (coordinates M N i).val < (store p S).2.length := by
    change _ < (batch p (expressionList S)).2.length
    rw [hl]
    simpa only [expressionList,List.length_ofFn] using (coordinates M N i).isLt
  apply hs.indices
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

lemma safe_stored {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N)
    (hb : Safe (fun i => i < p) S) : Safe (fun i => i < (store p S).1.2) (stored p S) := by
  refine ⟨fun l => ?_,fun s => ?_,fun k i => ?_⟩
  all_goals exact (stored_index p S hb _).2

structure Simulation (M : BinaryMachine) (N : ℕ) where
  gates : List Raw
  pointer : ℕ
  registers : Symbolic M N

def Simulates {M : BinaryMachine} {N : ℕ} (S : Simulation M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) : Prop :=
  (∀ g ∈ S.gates, Valid S.pointer g) ∧
  (∀ i, S.pointer  ≤  i → rawRun S.gates y i = 0) ∧
  Represents S.registers c (rawRun S.gates y) ∧ Safe (fun i => i < S.pointer) S.registers

noncomputable def emit {M : BinaryMachine} {N : ℕ} (F : Symbolic M N → Symbolic M N)
    (S : Simulation M N) : Simulation M N :=
  let R := F S.registers
  let B := store S.pointer R
  ⟨S.gates++B.1.1,B.1.2,stored S.pointer R⟩

lemma emit_correct {M : BinaryMachine} {N : ℕ} (S : Simulation M N) (c d : M.Cfg)
    (y : ℕ → ZMod 3) (h : Simulates S c y) (F : Symbolic M N → Symbolic M N)
    (hrep : Represents (F S.registers) d (rawRun S.gates y))
    (hsafe : Safe (fun i => i < S.pointer) (F S.registers)) : Simulates (emit F S) d y := by
  have hbound : ∀ e ∈ expressionList (F S.registers), e.Bounded S.pointer :=
    fun e he => inputs_bounded _ e (safe_expressionList _ _ hsafe e he)
  have hs := batch_correct S.pointer (expressionList (F S.registers)) hbound (rawRun S.gates y) h.2.1
  refine ⟨?_,?_,?_,safe_stored S.pointer (F S.registers) hsafe⟩
  · intro g hg
    rcases List.mem_append.mp hg with hold | hnew
    · exact (h.1 g hold).mono hs.monotone
    · exact hs.valid g hnew
  · intro i hi
    change rawRun (S.gates++(store S.pointer (F S.registers)).1.1) y i = 0
    rw [rawRun_append]
    exact hs.unused i hi
  · change Represents (stored S.pointer (F S.registers)) d
      (rawRun (S.gates++(store S.pointer (F S.registers)).1.1) y)
    rw [rawRun_append]
    exact stored_rep S.pointer _ d _ hrep hbound h.2.1

noncomputable def simulateStep {M : BinaryMachine} {N : ℕ} (hN : 0 < N) :
    Simulation M N → Simulation M N := emit (symbolicStep hN)

lemma simulateStep_correct {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (S : Simulation M N)
    (c : M.Cfg) (y : ℕ → ZMod 3) (h : Simulates S c y) (B : ℕ)
    (hc : Fits c B) (hcap : B+machineGrowth M  ≤  N) :
    Simulates (simulateStep hN S) (totalStep M c) y := by
  apply emit_correct S c _ y h
  · exact symbolicStep_rep hN S.registers c _ h.2.2.1 B hc hcap
  · exact safe_symbolicStep _ hN S.registers h.2.2.2

lemma simulation_clock {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (s : List Bool)
    (S : Simulation M N) (y : ℕ → ZMod 3) (h : Simulates S (M.initialCfg s) y)
    (T : ℕ) (hcap : s.length+T*machineGrowth M  ≤  N) :
    Simulates ((simulateStep hN)^[T] S) ((totalStep M)^[T] (M.initialCfg s)) y := by
  induction T with
  | zero => exact h
  | succ T ih =>
    have hc : s.length+T*machineGrowth M  ≤  N := by
      rw [Nat.succ_mul] at hcap
      omega
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply' (f := totalStep M)]
    exact simulateStep_correct hN _ _ y (ih hc) _ (clock_fits M s T)
      (by simpa only [Nat.succ_mul,Nat.add_assoc] using hcap)

end F3MachineCompiler

-- Source: Solutions.T31.ExpressionSize

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

lemma sum_code_length (xs : List Expr) :
    (Expr.sum xs).code.length = 1+xs.length+(xs.map (fun e => e.code.length)).sum := by
  induction xs with
  | nil => rfl
  | cons e es ih =>
    simp only [Expr.sum,List.foldr_cons,Expr.code,List.length_append,List.length_singleton,
      List.length_cons,List.map_cons,List.sum_cons]
    change e.code.length+(Expr.sum es).code.length+1 = _
    rw [ih]
    omega

lemma code_lengths_bound (xs : List Expr) (B : ℕ) (h : ∀ e ∈ xs, e.code.length  ≤  B) :
    (xs.map (fun e => e.code.length)).sum  ≤  xs.length*B := by
  induction xs with
  | nil => simp
  | cons e es ih =>
    have he := h e (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma sum_size (xs : List Expr) (B : ℕ) (h : ∀ e ∈ xs, e.code.length  ≤  B) :
    (Expr.sum xs).code.length  ≤  1+xs.length*(B+1) := by
  rw [sum_code_length]
  have hl := code_lengths_bound xs B h
  nlinarith

lemma literal_size (v : ZMod 3) : (literal v).code.length  ≤  3 := by
  unfold literal
  split_ifs <;> simp [Expr.code]

lemma select_size {α : Type} [Fintype α] (v : α → Expr) (f : α → ZMod 3) (B : ℕ)
    (h : ∀ a, (v a).code.length  ≤  B) :
    (select v f).code.length  ≤  1+Fintype.card α*(B+5) := by
  have hs := sum_size (Finset.univ.toList.map (fun a => Expr.times (v a) (literal (f a)))) (B+4) (by
    intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    have h1 := h a
    have h2 := literal_size (f a)
    simp only [Expr.code,List.length_append,List.length_singleton]
    omega)
  simpa only [select,List.length_map,Finset.length_toList,Finset.card_univ,Nat.add_assoc] using hs

lemma blend_size {α : Type} [Fintype α] (v f : α → Expr) (B D : ℕ)
    (hv : ∀ a, (v a).code.length  ≤  B) (hf : ∀ a, (f a).code.length  ≤  D) :
    (blend v f).code.length  ≤  1+Fintype.card α*(B+D+2) := by
  have hs := sum_size (Finset.univ.toList.map (fun a => Expr.times (v a) (f a))) (B+D+1) (by
    intro e he
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
    have h1 := hv a
    have h2 := hf a
    simp only [Expr.code,List.length_append,List.length_singleton]
    omega)
  simpa only [blend,List.length_map,Finset.length_toList,Finset.card_univ,Nat.add_assoc] using hs

lemma isZero_size (e : Expr) : e.isZero.code.length = 2*e.code.length+4 := by
  simp [Expr.isZero,Expr.code,List.length_append]
  omega

lemma choose_size (a b c : Expr) : (a.choose b c).code.length = 2*a.code.length+b.code.length+c.code.length+6 := by
  simp [Expr.choose,Expr.code,List.length_append]
  omega

def Size {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) : Prop :=
  (∀ l, (S.label l).code.length  ≤  B) ∧ (∀ s, (S.state s).code.length  ≤  B) ∧
    (∀ k i, (S.stack k i).code.length  ≤  B)

lemma size_mono {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) {B D : ℕ}
    (h : Size S B) (hBD : B  ≤  D) : Size S D :=
  ⟨fun l => le_trans (h.1 l) hBD,fun s => le_trans (h.2.1 s) hBD,
    fun k i => le_trans (h.2.2 k i) hBD⟩

lemma stateTable_size {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (f : M.State → ZMod 3) :
    (stateTable S f).code.length  ≤  (5*Fintype.card M.State+1)*(B+1) := by
  have hs := select_size S.state f B h.2.1
  change (select S.state f).code.length  ≤  _
  nlinarith

lemma headTable_size {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (k : M.K) (hN : 0 < N) (f : M.State → Option Bool → ZMod 3) :
    (headTable S k hN f).code.length  ≤  (60*Fintype.card M.State+1)*(B+1) := by
  have hh (a : M.State × Option Bool) : (headSelector S k hN a).code.length  ≤  3*B+15 := by
    have hs := h.2.1 a.1
    have ht := h.2.2 k ⟨0,hN⟩
    have hl := literal_size (symbol a.2)
    simp only [headSelector,Expr.code,List.length_append,List.length_singleton,isZero_size]
    omega
  have hs := select_size (headSelector S k hN) (fun a => f a.1 a.2) (3*B+15) hh
  change (select (headSelector S k hN) (fun a => f a.1 a.2)).code.length  ≤  _
  simp only [Fintype.card_prod,Fintype.card_option,Fintype.card_bool] at hs
  nlinarith

lemma size_stored {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N) : Size (stored p S) 1 :=
  ⟨by intros; exact le_rfl,by intros; exact le_rfl,by intros; exact le_rfl⟩

end F3MachineCompiler

-- Source: Solutions.T31.StepSize

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

def tableFactor (M : BinaryMachine) : ℕ := 5*Fintype.card M.State+1
def readFactor (M : BinaryMachine) : ℕ := 60*Fintype.card M.State+1

lemma factor_dominates (C B : ℕ) (hC : 1  ≤  C) : B  ≤  C*(B+1) := by nlinarith

lemma size_symLoad {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (f : M.State → M.State) : Size (symLoad S f) (tableFactor M*(B+1)) := by
  have hd := factor_dominates (tableFactor M) B (by dsimp [tableFactor]; omega)
  exact ⟨fun l => le_trans (h.1 l) hd,fun s => stateTable_size S B h _,
    fun k i => le_trans (h.2.2 k i) hd⟩

lemma size_symRead {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (k : M.K) (hN : 0 < N) (f : M.State → Option Bool → M.State) :
    Size (symRead S k hN f) (readFactor M*(B+1)) := by
  have hd := factor_dominates (readFactor M) B (by dsimp [readFactor]; omega)
  exact ⟨fun l => le_trans (h.1 l) hd,
    fun s => headTable_size S B h k hN (fun a b => if f a b = s then 1 else 0),
    fun k i => le_trans (h.2.2 k i) hd⟩

lemma size_symPush {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (k : M.K) (f : M.State → Bool) : Size (symPush S k f) (tableFactor M*(B+1)) := by
  have hd := factor_dominates (tableFactor M) B (by dsimp [tableFactor]; omega)
  refine ⟨fun l => le_trans (h.1 l) hd,fun s => le_trans (h.2.1 s) hd,?_⟩
  intro j i
  unfold symPush
  dsimp only
  split_ifs
  · exact stateTable_size S B h _
  · exact le_trans (h.2.2 _ _) hd
  · exact le_trans (h.2.2 _ _) hd

lemma size_symDrop {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (k : M.K) : Size (symDrop S k) (B+1) := by
  refine ⟨fun l => le_trans (h.1 l) (by omega),fun s => le_trans (h.2.1 s) (by omega),?_⟩
  intro j i
  unfold symDrop
  dsimp only
  split_ifs
  · exact le_trans (h.2.2 _ _) (by omega)
  · simp [Expr.code]
  · exact le_trans (h.2.2 _ _) (by omega)

lemma size_symGoto {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (f : M.State → M.Label) : Size (symGoto S f) (tableFactor M*(B+1)) := by
  have hd := factor_dominates (tableFactor M) B (by dsimp [tableFactor]; omega)
  exact ⟨fun l => stateTable_size S B h _,fun s => le_trans (h.2.1 s) hd,
    fun k i => le_trans (h.2.2 k i) hd⟩

lemma size_symHalt {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B) :
    Size (symHalt S) (3*(B+1)) :=
  ⟨fun l => le_trans (literal_size _) (by omega),fun s => le_trans (h.2.1 s) (by omega),
    fun k i => le_trans (h.2.2 k i) (by omega)⟩

lemma size_symChoose {M : BinaryMachine} {N : ℕ} (S T : Symbolic M N) (A B D : ℕ)
    (hS : Size S B) (hT : Size T D) (a : Expr) (ha : a.code.length  ≤  A) :
    Size (symChoose a S T) (2*A+B+D+6) := by
  refine ⟨fun l => ?_,fun s => ?_,fun k i => ?_⟩
  all_goals simp only [symChoose,choose_size]
  · have hs := hS.1 l; have ht := hT.1 l; omega
  · have hs := hS.2.1 s; have ht := hT.2.1 s; omega
  · have hs := hS.2.2 k i; have ht := hT.2.2 k i; omega

lemma size_combine {M : BinaryMachine} {N : ℕ} {α : Type} [Fintype α]
    (v : α → Expr) (S : α → Symbolic M N) (A B : ℕ)
    (hv : ∀ a, (v a).code.length  ≤  A) (hS : ∀ a, Size (S a) B) :
    Size (combine v S) (1+Fintype.card α*(A+B+2)) :=
  ⟨fun l => blend_size v _ A B hv (fun a => (hS a).1 l),
    fun s => blend_size v _ A B hv (fun a => (hS a).2.1 s),
    fun k i => blend_size v _ A B hv (fun a => (hS a).2.2 k i)⟩

end F3MachineCompiler

namespace F3MachineCompiler
open F3Tools
open Classical

def auxFactor (M : BinaryMachine) : Statement M → ℕ
  | .push _ _ q => auxFactor M q*(tableFactor M+1)
  | .peek _ _ q => auxFactor M q*(readFactor M+1)
  | .pop _ _ q => auxFactor M q*(readFactor M+2)
  | .load _ q => auxFactor M q*(tableFactor M+1)
  | .branch _ q r => 2*tableFactor M+auxFactor M q+auxFactor M r+6
  | .goto _ => tableFactor M
  | .halt => 3

lemma auxFactor_pos (M : BinaryMachine) (q : Statement M) : 0 < auxFactor M q := by
  induction q <;> simp only [auxFactor]
  all_goals first | positivity | simp [tableFactor]

lemma symbolicAux_size {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (q : Statement M)
    (S : Symbolic M N) (B : ℕ) (h : Size S B) :
    Size (symbolicAux hN q S) (auxFactor M q*(B+1)) := by
  induction q generalizing S B with
  | push k f q ih =>
    have hq := ih _ _ (size_symPush S B h k f)
    apply size_mono _ hq
    change auxFactor M q*(tableFactor M*(B+1)+1)  ≤  auxFactor M q*(tableFactor M+1)*(B+1)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  | peek k f q ih =>
    have hq := ih _ _ (size_symRead S B h k hN f)
    apply size_mono _ hq
    change auxFactor M q*(readFactor M*(B+1)+1)  ≤  auxFactor M q*(readFactor M+1)*(B+1)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  | pop k f q ih =>
    have hq := ih _ _ (size_symDrop _ _ (size_symRead S B h k hN f) k)
    apply size_mono _ hq
    change auxFactor M q*(readFactor M*(B+1)+1+1)  ≤  auxFactor M q*(readFactor M+2)*(B+1)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  | load f q ih =>
    have hq := ih _ _ (size_symLoad S B h f)
    apply size_mono _ hq
    change auxFactor M q*(tableFactor M*(B+1)+1)  ≤  auxFactor M q*(tableFactor M+1)*(B+1)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  | branch f q r ihq ihr =>
    have hh := size_symChoose _ _ (tableFactor M*(B+1)) (auxFactor M q*(B+1))
      (auxFactor M r*(B+1)) (ihq S B h) (ihr S B h)
      (stateTable S (fun a => if f a then 1 else 0)) (stateTable_size S B h _)
    apply size_mono _ hh
    change _  ≤  (2*tableFactor M+auxFactor M q+auxFactor M r+6)*(B+1)
    nlinarith
  | goto f => exact size_symGoto S B h f
  | halt => exact size_symHalt S B h

def machineFactor (M : BinaryMachine) : ℕ := (∑ l, auxFactor M (M.code l))+1

def stepFactor (M : BinaryMachine) : ℕ := 1+Fintype.card (Option M.Label)*(machineFactor M+3)

lemma auxFactor_le_machineFactor (M : BinaryMachine) (l : M.Label) :
    auxFactor M (M.code l)  ≤  machineFactor M := by
  have h := Finset.single_le_sum (f := fun l => auxFactor M (M.code l))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
  dsimp only [machineFactor]
  omega

lemma symbolicStep_size {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (S : Symbolic M N)
    (B : ℕ) (h : Size S B) : Size (symbolicStep hN S) (stepFactor M*(B+1)) := by
  have hbranches : ∀ l : Option M.Label,
      Size (match l with | none => S | some l => symbolicAux hN (M.code l) S)
        (machineFactor M*(B+1)) := by
    intro l
    cases l with
    | none => exact size_mono S h (factor_dominates _ B (by dsimp [machineFactor]; omega))
    | some l =>
      exact size_mono _ (symbolicAux_size hN (M.code l) S B h)
        (Nat.mul_le_mul_right _ (auxFactor_le_machineFactor M l))
  have hs := size_combine S.label _ B (machineFactor M*(B+1)) h.1 hbranches
  apply size_mono _ hs
  dsimp only [stepFactor]
  nlinarith

end F3MachineCompiler

-- Source: Solutions.T31.ResourceBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

lemma batch_resources (p : ℕ) (es : List Expr) (he : ∀ e ∈ es, e.Bounded p) :
    (batch p es).1.2 = p+es.length+2*(es.map (fun e => e.code.length)).sum ∧
      (batch p es).1.1.length  ≤  2*(es.map (fun e => e.code.length)).sum := by
  induction es generalizing p with
  | nil => simp [batch]
  | cons e es ih =>
    have ho := one_inv p e (he e (by simp)) (fun _ => 0) (by simp)
    have hp : p  ≤  (one p e).1.2 := le_trans (by omega : p  ≤  p+1) ho.1.growing
    have ht := ih (one p e).1.2 (fun a ha => a.bounded_mono (he a (by simp [ha])) hp)
    constructor
    · change (batch (one p e).1.2 es).1.2 = _
      rw [ht.1,ho.2.2.1]
      simp only [List.length_cons,List.map_cons,List.sum_cons]
      omega
    · change ((one p e).1.1++(batch (one p e).1.2 es).1.1).length  ≤  _
      rw [List.length_append]
      have hq := ho.2.2.2
      have hr := ht.2
      simp only [List.map_cons,List.sum_cons]
      omega

lemma batch_size_bound (p : ℕ) (es : List Expr) (he : ∀ e ∈ es, e.Bounded p)
    (B : ℕ) (hB : ∀ e ∈ es, e.code.length  ≤  B) :
    (batch p es).1.2  ≤  p+es.length*(2*B+1) ∧ (batch p es).1.1.length  ≤  es.length*(2*B) := by
  have hr := batch_resources p es he
  have hs := code_lengths_bound es B hB
  constructor <;> nlinarith [hr.1,hr.2]

lemma size_get {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (B : ℕ) (h : Size S B)
    (i : Coordinate M N) : (S.get i).code.length  ≤  B := by
  rcases i with l|(s|⟨k,i⟩)
  · exact h.1 l
  · exact h.2.1 s
  · exact h.2.2 k i

lemma store_size_bound {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N)
    (he : Safe (fun i => i < p) S) (B : ℕ) (hB : Size S B) :
    (store p S).1.2  ≤  p+dimension M N*(2*B+1) ∧
      (store p S).1.1.length  ≤  dimension M N*(2*B) := by
  have hr := batch_size_bound p (expressionList S)
    (fun e he' => inputs_bounded p e (safe_expressionList _ S he e he')) B (by
      intro e he'
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he'
      exact size_get S B hB _)
  simpa only [store,expressionList,List.length_ofFn] using hr

lemma simulateStep_size {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (S : Simulation M N) :
    Size (simulateStep hN S).registers 1 := size_stored _ _

lemma simulateStep_resources {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (S : Simulation M N)
    (he : Safe (fun i => i < S.pointer) S.registers) (hB : Size S.registers 3) :
    (simulateStep hN S).pointer  ≤  S.pointer+dimension M N*(8*stepFactor M+1) ∧
      (simulateStep hN S).gates.length  ≤  S.gates.length+dimension M N*(8*stepFactor M) := by
  have hs := store_size_bound S.pointer (symbolicStep hN S.registers)
    (safe_symbolicStep _ hN _ he) (stepFactor M*(3+1)) (symbolicStep_size hN _ 3 hB)
  constructor
  · change (store S.pointer (symbolicStep hN S.registers)).1.2  ≤  _
    convert hs.1 using 1 <;> ring
  · change (S.gates++(store S.pointer (symbolicStep hN S.registers)).1.1).length  ≤  _
    rw [List.length_append]
    have hr : 2*(stepFactor M*(3+1)) = 8*stepFactor M := by ring
    rw [hr] at hs
    exact Nat.add_le_add_left hs.2 _

end F3MachineCompiler

-- Source: Solutions.T31.InputEncoding

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

noncomputable def initialSymbolic (M : BinaryMachine) (N : ℕ) : Symbolic M N where
  label l := literal (if l = some M.main then 1 else 0)
  state s := literal (if s = M.initial then 1 else 0)
  stack _ _ := .zero

lemma initialSymbolic_rep (M : BinaryMachine) (N : ℕ) (y : ℕ → ZMod 3) :
    Represents (initialSymbolic M N) (M.initialCfg []) y := by
  refine ⟨fun l => literal_eval _ y,fun s => literal_eval _ y,?_⟩
  intro k i
  simp [initialSymbolic,OAI.MetricKMedian.Binary.Machine.initialCfg,cell_nil,Expr.eval]

lemma initialSymbolic_safe (M : BinaryMachine) (N : ℕ) (P : ℕ → Prop) : Safe P (initialSymbolic M N) :=
  ⟨fun _ => inputs_literal P _,fun _ => inputs_literal P _,by intros; trivial⟩

noncomputable def conditionalPush {M : BinaryMachine} {N : ℕ} (e : Expr) (b : Bool)
    (S : Symbolic M N) : Symbolic M N := symChoose e (symPush S M.input (fun _ => b)) S

lemma conditionalPush_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (e : Expr) (b test : Bool)
    (he : e.eval y = if test then 1 else 0) :
    Represents (conditionalPush e b S)
      (if test then {c with stk := Function.update c.stk M.input (b::c.stk M.input)} else c) y :=
  symChoose_rep _ _ _ _ y (symPush_rep S c y h M.input (fun _ => b)) h e test he

lemma conditionalPush_safe {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (P : ℕ → Prop)
    (h : Safe P S) (e : Expr) (he : Inputs P e) (b : Bool) : Safe P (conditionalPush e b S) :=
  safe_symChoose P _ S (safe_symPush P S h M.input (fun _ => b)) h e he

noncomputable def fillTrit {M : BinaryMachine} {N : ℕ} (e : Expr) (S : Symbolic M N) : Symbolic M N :=
  let S₀ := symPush S M.input (fun _ => false)
  let S₁ := conditionalPush (.plus .one (.minus e.isZero)) true S₀
  conditionalPush (.isZero (.plus e (.minus (literal 2)))) true S₁

lemma fillTrit_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (e : Expr) (v : ZMod 3) (he : e.eval y = v) :
    Represents (fillTrit e S)
      {c with stk := Function.update c.stk M.input (unaryD v.val++c.stk M.input)} y := by
  let c₀ : M.Cfg := {c with stk := Function.update c.stk M.input (false::c.stk M.input)}
  have h₀ := symPush_rep S c y h M.input (fun _ => false)
  have htest₁ : (Expr.plus .one (.minus e.isZero)).eval y = if decide (v ≠ 0) then 1 else 0 := by
    rw [Expr.eval,Expr.eval,Expr.eval,Expr.eval_isZero,he]
    by_cases hv : v = 0 <;> simp [hv]
  have h₁ := conditionalPush_rep _ c₀ y h₀ (.plus .one (.minus e.isZero)) true (decide (v ≠ 0)) htest₁
  have htest₂ : (Expr.isZero (.plus e (.minus (literal 2)))).eval y = if decide (v = 2) then 1 else 0 := by
    rw [Expr.eval_isZero]
    simp only [Expr.eval,literal_eval,he]
    simp only [← sub_eq_add_neg,sub_eq_zero,decide_eq_true_eq]
  have h₂ := conditionalPush_rep _ _ y h₁ (.isZero (.plus e (.minus (literal 2)))) true
    (decide (v = 2)) htest₂
  change Represents (fillTrit e S) _ y at h₂
  convert h₂ using 1
  have hv2 : (2 : ZMod 3).val = 2 := by decide
  rcases F3Reduction.cases_three v with rfl | rfl | rfl <;>
    simp [c₀,unaryD,unary,Function.update_self,Function.update_idem,ZMod.val_zero,ZMod.val_one,hv2]

lemma fillTrit_safe {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (P : ℕ → Prop)
    (h : Safe P S) (e : Expr) (he : Inputs P e) : Safe P (fillTrit e S) := by
  apply conditionalPush_safe
  · apply conditionalPush_safe
    · exact safe_symPush P S h M.input (fun _ => false)
    · exact ⟨trivial,inputs_isZero P e he⟩
  · exact inputs_isZero P _ ⟨he,inputs_literal P 2⟩

end F3MachineCompiler

-- Source: Solutions.T31.Emission

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

def Prefix {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Simulation M N) (y : ℕ → ZMod 3) : Prop :=
  ∀ i, i < p → rawRun S.gates y i = y i

lemma emit_monotone {M : BinaryMachine} {N : ℕ} (S : Simulation M N)
    (F : Symbolic M N → Symbolic M N) (h : Safe (fun i => i < S.pointer) (F S.registers)) :
    S.pointer  ≤  (emit F S).pointer := by
  have hr := batch_correct S.pointer (expressionList (F S.registers))
    (fun e he => inputs_bounded _ e (safe_expressionList _ _ h e he)) (fun _ => 0) (by simp)
  exact hr.monotone

lemma emit_prefix {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Simulation M N) (y : ℕ → ZMod 3)
    (hp : p  ≤  S.pointer) (hpre : Prefix p S y)
    (hz : ∀ i, S.pointer  ≤  i → rawRun S.gates y i = 0)
    (F : Symbolic M N → Symbolic M N) (h : Safe (fun i => i < S.pointer) (F S.registers)) :
    Prefix p (emit F S) y := by
  have hr := batch_correct S.pointer (expressionList (F S.registers))
    (fun e he => inputs_bounded _ e (safe_expressionList _ _ h e he)) (rawRun S.gates y) hz
  intro i hi
  change rawRun (S.gates++(store S.pointer (F S.registers)).1.1) y i = y i
  rw [rawRun_append]
  exact (hr.preserve i (lt_of_lt_of_le hi hp)).trans (hpre i hi)

noncomputable def initialSimulation (M : BinaryMachine) (N p : ℕ) : Simulation M N :=
  ⟨[],p,initialSymbolic M N⟩

lemma initialSimulation_correct (M : BinaryMachine) (N p : ℕ) (y : ℕ → ZMod 3)
    (hz : ∀ i, p  ≤  i → y i = 0) : Simulates (initialSimulation M N p) (M.initialCfg []) y :=
  ⟨by simp [initialSimulation],hz,initialSymbolic_rep M N y,initialSymbolic_safe M N _⟩

lemma inputs_of_bounded (p : ℕ) (e : Expr) (h : e.Bounded p) : Inputs (fun i => i < p) e := by
  induction e with
  | zero | one => trivial
  | input i => exact h
  | plus a b ha hb | times a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | minus a ha => exact ha h

noncomputable def prepare (es : List Expr) {M : BinaryMachine} {N : ℕ} (S : Simulation M N) : Simulation M N :=
  es.foldr (fun e acc => emit (fillTrit e) acc) S

noncomputable def encodedExprs (es : List Expr) (y : ℕ → ZMod 3) : List Bool :=
  es.flatMap (fun e => unaryD (e.eval y).val)

lemma prepare_correct {M : BinaryMachine} {N : ℕ} (p : ℕ) (es : List Expr)
    (S : Simulation M N) (s : List Bool) (y : ℕ → ZMod 3)
    (h : Simulates S (M.initialCfg s) y) (hp : p  ≤  S.pointer) (hpre : Prefix p S y)
    (he : ∀ e ∈ es, Inputs (fun i => i < p) e) :
    Simulates (prepare es S) (M.initialCfg (encodedExprs es y++s)) y ∧
      p  ≤  (prepare es S).pointer ∧ Prefix p (prepare es S) y := by
  induction es with
  | nil => simpa [prepare,encodedExprs] using And.intro h (And.intro hp hpre)
  | cons e es ih =>
    obtain ⟨ht,hptr,hpref⟩ := ih (fun a ha => he a (by simp [ha]))
    let S' := prepare es S
    have hb : e.Bounded p := inputs_bounded p e (he e (by simp))
    have heval : e.eval (rawRun S'.gates y) = e.eval y :=
      e.eval_congr_bounded hb _ _ hpref
    have hesafe : Inputs (fun i => i < S'.pointer) e := by
      have hbounded := e.bounded_mono hb hptr
      exact inputs_of_bounded S'.pointer e hbounded
    have hsafe := fillTrit_safe S'.registers _ ht.2.2.2 e hesafe
    have hrep := fillTrit_rep S'.registers (M.initialCfg (encodedExprs es y++s))
      (rawRun S'.gates y) ht.2.2.1 e (e.eval y) heval
    have hrep' : Represents (fillTrit e S'.registers)
        (M.initialCfg (unaryD (e.eval y).val++(encodedExprs es y++s))) (rawRun S'.gates y) := by
      convert hrep using 1
      refine OAI.MetricKMedian.Binary.cfg_ext ?_ ?_ ?_
      · rfl
      · rfl
      · funext k
        by_cases hk : k = M.input <;>
          simp [OAI.MetricKMedian.Binary.Machine.initialCfg,Function.update_apply,hk]
    have hout := emit_correct S' _ _ y ht (fillTrit e) hrep' hsafe
    refine ⟨?_,le_trans hptr (emit_monotone S' (fillTrit e) hsafe),
      emit_prefix p S' y hptr hpref ht.2.1 (fillTrit e) hsafe⟩
    simpa only [S',prepare,List.foldr_cons,encodedExprs,List.flatMap_cons,List.append_assoc] using hout

noncomputable def prepareBits (bits : List Bool) {M : BinaryMachine} {N : ℕ}
    (S : Simulation M N) : Simulation M N :=
  bits.foldr (fun b acc => emit (fun R => symPush R M.input (fun _ => b)) acc) S

lemma prepareBits_correct {M : BinaryMachine} {N : ℕ} (p : ℕ) (bits : List Bool)
    (S : Simulation M N) (s : List Bool) (y : ℕ → ZMod 3)
    (h : Simulates S (M.initialCfg s) y) (hp : p  ≤  S.pointer) (hpre : Prefix p S y) :
    Simulates (prepareBits bits S) (M.initialCfg (bits++s)) y ∧
      p  ≤  (prepareBits bits S).pointer ∧ Prefix p (prepareBits bits S) y := by
  induction bits with
  | nil => simpa [prepareBits] using And.intro h (And.intro hp hpre)
  | cons b bits ih =>
    obtain ⟨ht,hptr,hpref⟩ := ih
    let S' := prepareBits bits S
    have hsafe := safe_symPush _ S'.registers ht.2.2.2 M.input (fun _ => b)
    have hrep := symPush_rep S'.registers (M.initialCfg (bits++s)) (rawRun S'.gates y)
      ht.2.2.1 M.input (fun _ => b)
    have hrep' : Represents (symPush S'.registers M.input (fun _ => b))
        (M.initialCfg (b::(bits++s))) (rawRun S'.gates y) := by
      convert hrep using 1
      refine OAI.MetricKMedian.Binary.cfg_ext ?_ ?_ ?_
      · rfl
      · rfl
      · funext k
        by_cases hk : k = M.input <;>
          simp [OAI.MetricKMedian.Binary.Machine.initialCfg,hk]
    have hout := emit_correct S' _ _ y ht (fun R => symPush R M.input (fun _ => b)) hrep' hsafe
    refine ⟨?_,le_trans hptr (emit_monotone S' (fun R => symPush R M.input (fun _ => b)) hsafe),
      emit_prefix p S' y hptr hpref ht.2.1 (fun R => symPush R M.input (fun _ => b)) hsafe⟩
    simpa only [S',prepareBits,List.foldr_cons,List.cons_append] using hout

end F3MachineCompiler

-- Source: Solutions.T31.InputProgram

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

def inputExprs (n m : ℕ) : List Expr :=
  (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => Expr.input (n*i.val+j.val))) ++
  (List.finRange m).map (fun i => .plus (.input (n*m+i.val)) (.minus .one))

lemma inputExprs_bounded (n m p : ℕ) (hp : n*m+m  ≤  p) :
    ∀ e ∈ inputExprs n m, Inputs (fun i => i < p) e := by
  intro e he
  rcases List.mem_append.mp he with hA|hb
  · obtain ⟨i,_,he⟩ := List.mem_flatMap.mp hA
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    have hi := i.isLt
    have hj := j.isLt
    change n*i.val+j.val < p
    nlinarith
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    exact ⟨by have := i.isLt; change n*m+i.val < p; omega,trivial⟩

lemma encoded_inputExprs {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 3))
    (b : Fin m → ZMod 3) (y : ℕ → ZMod 3)
    (hA : ∀ i j, y (n*i.val+j.val) = A j i) (hb : ∀ i, y (n*m+i.val) = b i) :
    encodedExprs (inputExprs n m) y =
      (List.finRange m).flatMap (fun i => (List.finRange n).flatMap (fun j => unaryD (A j i).val)) ++
      (List.finRange m).flatMap (fun i => unaryD (b i-1).val) := by
  simp only [encodedExprs,inputExprs,List.flatMap_append,List.flatMap_assoc,List.flatMap_map,
    Function.comp_apply,Expr.eval,hA,hb,sub_eq_add_neg]

noncomputable def inputProgram (M : BinaryMachine) (N p n m : ℕ) : Simulation M N :=
  prepareBits (unaryD n++unaryD m) (prepare (inputExprs n m) (initialSimulation M N p))

lemma inputProgram_correct (M : BinaryMachine) (N p n m : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod 3)) (b : Fin m → ZMod 3) (y : ℕ → ZMod 3)
    (hp : n*m+m  ≤  p) (hz : ∀ i, p  ≤  i → y i = 0)
    (hA : ∀ i j, y (n*i.val+j.val) = A j i) (hb : ∀ i, y (n*m+i.val) = b i) :
    Simulates (inputProgram M N p n m) (M.initialCfg (encodeInstance A (fun i => b i-1))) y ∧
      p  ≤  (inputProgram M N p n m).pointer ∧ Prefix p (inputProgram M N p n m) y := by
  have hs := initialSimulation_correct M N p y hz
  have hpre : Prefix p (initialSimulation M N p) y := fun _ _ => rfl
  obtain ⟨hd,hdp,hdpre⟩ := prepare_correct p (inputExprs n m) (initialSimulation M N p) [] y
    hs le_rfl hpre (inputExprs_bounded n m p hp)
  obtain ⟨hr,hrp,hrpre⟩ := prepareBits_correct p (unaryD n++unaryD m)
    (prepare (inputExprs n m) (initialSimulation M N p)) (encodedExprs (inputExprs n m) y++[]) y hd hdp hdpre
  refine ⟨?_,hrp,hrpre⟩
  simpa only [inputProgram,encodeInstance,encoded_inputExprs A b y hA hb,List.append_nil,List.append_assoc] using hr

end F3MachineCompiler

-- Source: Solutions.T31.OutputEncoding

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

noncomputable def equalsTrue (τ : Bool ≃ Bool) (e : Expr) : Expr :=
  .isZero (.plus e (.minus (literal (symbol (some (τ true))))))

lemma equalsTrue_eval (τ : Bool ≃ Bool) (e : Expr) (y : ℕ → ZMod 3) :
    (equalsTrue τ e).eval y = if e.eval y = symbol (some (τ true)) then 1 else 0 := by
  rw [equalsTrue,Expr.eval_isZero]
  simp only [Expr.eval,literal_eval,← sub_eq_add_neg,sub_eq_zero]

lemma equalsTrue_symbol (τ : Bool ≃ Bool) (b : Bool) :
    (symbol (some (τ b)) = symbol (some (τ true))) ↔ b = true := by
  simp only [symbol_injective.eq_iff,Option.some.injEq,τ.injective.eq_iff]

noncomputable def headMask {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) : Expr := equalsTrue τ (S.stack M.output ⟨0,by omega⟩)
noncomputable def nextMask {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) : Expr := equalsTrue τ (S.stack M.output ⟨1,by omega⟩)
noncomputable def twoMask {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) : Expr := .times (headMask τ hN S) (nextMask τ hN S)
noncomputable def parsedTrit {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) : Expr := .plus (headMask τ hN S) (twoMask τ hN S)

noncomputable def conditionalDrop {M : BinaryMachine} {N : ℕ} (e : Expr)
    (S : Symbolic M N) : Symbolic M N := symChoose e (symDrop S M.output) S

lemma conditionalDrop_rep {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (c : M.Cfg)
    (y : ℕ → ZMod 3) (h : Represents S c y) (hk : (c.stk M.output).length  ≤  N)
    (e : Expr) (test : Bool) (he : e.eval y = if test then 1 else 0) :
    Represents (conditionalDrop e S)
      (if test then {c with stk := Function.update c.stk M.output (c.stk M.output).tail} else c) y :=
  symChoose_rep _ _ _ _ y (symDrop_rep S c y h M.output hk) h e test he

noncomputable def consumeTrit {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) : Symbolic M N :=
  let S₀ := symDrop S M.output
  let S₁ := conditionalDrop (headMask τ hN S) S₀
  conditionalDrop (twoMask τ hN S) S₁

lemma canonical_masks {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (c : M.Cfg) (y : ℕ → ZMod 3) (h : Represents S c y)
    (v : ZMod 3) (tail : List Bool) (hw : c.stk M.output = (unaryD v.val++tail).map τ) :
    (headMask τ hN S).eval y = (if v = 0 then 0 else 1) ∧
      (twoMask τ hN S).eval y = (if v = 2 then 1 else 0) := by
  have h₀ : (S.stack M.output ⟨0,by omega⟩).eval y = cell ((unaryD v.val++tail).map τ) 0 := by
    rw [h.2.2,hw]
  have h₁ : (S.stack M.output ⟨1,by omega⟩).eval y = cell ((unaryD v.val++tail).map τ) 1 := by
    rw [h.2.2,hw]
  have hv2 : (2 : ZMod 3).val = 2 := by decide
  simp only [headMask,nextMask,twoMask,Expr.eval,equalsTrue_eval,h₀,h₁]
  rcases F3Reduction.cases_three v with rfl | rfl | rfl <;>
    simp [unaryD,unary,ZMod.val_zero,ZMod.val_one,hv2,cell,equalsTrue_symbol]

lemma parsedTrit_eval {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (c : M.Cfg) (y : ℕ → ZMod 3) (h : Represents S c y)
    (v : ZMod 3) (tail : List Bool) (hw : c.stk M.output = (unaryD v.val++tail).map τ) :
    (parsedTrit τ hN S).eval y = v := by
  obtain ⟨h₀,h₁⟩ := canonical_masks τ hN S c y h v tail hw
  simp only [parsedTrit,Expr.eval,h₀,h₁]
  rcases F3Reduction.cases_three v with rfl | rfl | rfl <;> simp

lemma consumeTrit_rep {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (c : M.Cfg) (y : ℕ → ZMod 3) (h : Represents S c y)
    (hk : (c.stk M.output).length  ≤  N) (v : ZMod 3) (tail : List Bool)
    (hw : c.stk M.output = (unaryD v.val++tail).map τ) :
    Represents (consumeTrit τ hN S)
      {c with stk := Function.update c.stk M.output (tail.map τ)} y := by
  obtain ⟨hm₁,hm₂⟩ := canonical_masks τ hN S c y h v tail hw
  have ht₁ : (headMask τ hN S).eval y = if decide (v ≠ 0) then 1 else 0 := by
    rw [hm₁]
    by_cases hv : v = 0 <;> simp [hv]
  have ht₂ : (twoMask τ hN S).eval y = if decide (v = 2) then 1 else 0 := by
    simpa only [decide_eq_true_eq] using hm₂
  let c₀ : M.Cfg := {c with stk := Function.update c.stk M.output (c.stk M.output).tail}
  have h₀ := symDrop_rep S c y h M.output hk
  have hk₀ : (c₀.stk M.output).length  ≤  N := by
    dsimp only [c₀]
    rw [Function.update_self,List.length_tail]
    omega
  have h₁ := conditionalDrop_rep (symDrop S M.output) c₀ y h₀ hk₀
    (headMask τ hN S) (decide (v ≠ 0)) ht₁
  let c₁ : M.Cfg := if decide (v ≠ 0) then
    {c₀ with stk := Function.update c₀.stk M.output (c₀.stk M.output).tail} else c₀
  have hk₁ : (c₁.stk M.output).length  ≤  N := by
    dsimp only [c₁]
    split_ifs
    · dsimp only
      rw [Function.update_self,List.length_tail]; omega
    · exact hk₀
  have h₂ := conditionalDrop_rep _ c₁ y h₁ hk₁ (twoMask τ hN S) (decide (v = 2)) ht₂
  change Represents (consumeTrit τ hN S) _ y at h₂
  convert h₂ using 1
  have hv2 : (2 : ZMod 3).val = 2 := by decide
  refine OAI.MetricKMedian.Binary.cfg_ext ?_ ?_ ?_
  · dsimp [c₁,c₀]; split_ifs <;> rfl
  · dsimp [c₁,c₀]; split_ifs <;> rfl
  · funext k
    by_cases hko : k = M.output
    · subst k
      rcases F3Reduction.cases_three v with rfl | rfl | rfl <;>
        simp [c₁,c₀,hw,unaryD,unary,ZMod.val_zero,ZMod.val_one,hv2]
    · dsimp only [c₁,c₀]
      split_ifs <;> simp [Function.update_apply,hko]

lemma equalsTrue_inputs (P : ℕ → Prop) (τ : Bool ≃ Bool) (e : Expr) (he : Inputs P e) :
    Inputs P (equalsTrue τ e) := inputs_isZero P _ ⟨he,inputs_literal P _⟩

lemma headMask_inputs {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (τ : Bool ≃ Bool)
    (hN : 2  ≤  N) (S : Symbolic M N) (hs : Safe P S) : Inputs P (headMask τ hN S) :=
  equalsTrue_inputs P τ _ (hs.2.2 _ _)
lemma twoMask_inputs {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (τ : Bool ≃ Bool)
    (hN : 2  ≤  N) (S : Symbolic M N) (hs : Safe P S) : Inputs P (twoMask τ hN S) :=
  ⟨headMask_inputs P τ hN S hs,equalsTrue_inputs P τ _ (hs.2.2 _ _)⟩
lemma parsedTrit_inputs {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (τ : Bool ≃ Bool)
    (hN : 2  ≤  N) (S : Symbolic M N) (hs : Safe P S) : Inputs P (parsedTrit τ hN S) :=
  ⟨headMask_inputs P τ hN S hs,twoMask_inputs P τ hN S hs⟩

lemma conditionalDrop_safe {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (S : Symbolic M N)
    (hs : Safe P S) (e : Expr) (he : Inputs P e) : Safe P (conditionalDrop e S) :=
  safe_symChoose P _ S (safe_symDrop P S hs M.output) hs e he

lemma consumeTrit_safe {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (τ : Bool ≃ Bool)
    (hN : 2  ≤  N) (S : Symbolic M N) (hs : Safe P S) : Safe P (consumeTrit τ hN S) := by
  apply conditionalDrop_safe
  · apply conditionalDrop_safe
    · exact safe_symDrop P S hs M.output
    · exact headMask_inputs P τ hN S hs
  · exact twoMask_inputs P τ hN S hs

end F3MachineCompiler

-- Source: Solutions.T31.DecoderSimulation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum Turing
open Classical

lemma flatMap_length_bound {α β : Type} (xs : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ xs, (f a).length  ≤  B) : (xs.flatMap f).length  ≤  xs.length*B := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma unaryD_trit_length (v : ZMod 3) : (unaryD v.val).length  ≤  3 := by
  have hv := ZMod.val_lt v
  simp only [unaryD,unary,List.length_append,List.length_replicate,List.length_singleton]
  omega

lemma instance_length_bound {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 3)) (b : Fin m → ZMod 3) :
    (encodeInstance A b).length  ≤  n+m+2+3*(n*m+m) := by
  have hA := flatMap_length_bound (List.finRange m)
    (fun i => (List.finRange n).flatMap (fun j => unaryD (A j i).val)) (n*3) (by
      intro i hi
      simpa only [List.length_finRange] using
        flatMap_length_bound (List.finRange n) (fun j => unaryD (A j i).val) 3
          (fun j _ => unaryD_trit_length _))
  have hb := flatMap_length_bound (List.finRange m) (fun i => unaryD (b i).val) 3
    (fun i _ => unaryD_trit_length _)
  simp only [List.length_finRange] at hA hb
  dsimp only [unaryD,unary] at hA hb
  simp only [encodeInstance,List.length_append,unaryD,unary,List.length_replicate,List.length_singleton]
  nlinarith

def capacity (M : BinaryMachine) (n m T : ℕ) := 4*(n+m+1)^2+T*machineGrowth M+3

def reserve (n m : ℕ) := n*m+m+n+1

lemma capacity_ge_two (M : BinaryMachine) (n m T : ℕ) : 2  ≤  capacity M n m T := by
  dsimp only [capacity]
  omega

lemma capacity_fits (M : BinaryMachine) {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 3))
    (b : Fin m → ZMod 3) (T : ℕ) :
    (encodeInstance A b).length+T*machineGrowth M  ≤  capacity M n m T := by
  have hlen := instance_length_bound A b
  dsimp only [capacity]
  nlinarith [sq_nonneg (n : ℤ),sq_nonneg (m : ℤ)]

noncomputable def decoderSimulation (M : BinaryMachine) (n m T : ℕ) : Simulation M (capacity M n m T) :=
  (simulateStep (show 0 < capacity M n m T from lt_of_lt_of_le (by decide) (capacity_ge_two M n m T)))^[T]
    (inputProgram M (capacity M n m T) (reserve n m) n m)

lemma decoderSimulation_correct (M : BinaryMachine) (n m T : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod 3)) (b : Fin m → ZMod 3) (y : ℕ → ZMod 3)
    (hz : ∀ i, reserve n m  ≤  i → y i = 0)
    (hA : ∀ i j, y (n*i.val+j.val) = A j i) (hb : ∀ i, y (n*m+i.val) = b i) :
    Simulates (decoderSimulation M n m T)
      ((totalStep M)^[T] (M.initialCfg (encodeInstance A (fun i => b i-1)))) y := by
  have hi := (inputProgram_correct M (capacity M n m T) (reserve n m) n m A b y
    (by dsimp [reserve]; omega) hz hA hb).1
  exact simulation_clock _ _ _ y hi T (capacity_fits M A (fun i => b i-1) T)

lemma boolean_decoder (M : TM2ComputableAux Bool Bool) (Dec : DecoderFn 3) :
    ∃ (B : BinaryMachine) (τ : Bool ≃ Bool), ∀ n m T, ComputesWithin M Dec n m T →
      ∀ A b, Nonempty (TM2OutputsInTime B.tm (encodeInstance A b)
        (some ((encodeSecret (Dec n m A b)).map τ)) T) := by
  obtain ⟨B,τ,hB⟩ := QMCBoolSim.simulate M.tm M.inputAlphabet M.outputAlphabet
  refine ⟨B,τ,?_⟩
  intro n m T h A b
  obtain ⟨hr⟩ := h A b
  exact hB _ _ _ hr

end F3MachineCompiler

-- Source: Solutions.T31.Untouched

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3Reduction F3SubsetSum
open Classical

lemma inputs_mono (P Q : ℕ → Prop) (e : Expr) (h : Inputs P e) (hpq : ∀ i, P i → Q i) :
    Inputs Q e := by
  induction e with
  | zero | one => trivial
  | input i => exact hpq i h
  | plus a b ha hb | times a b ha hb => exact ⟨ha h.1,hb h.2⟩
  | minus a ha => exact ha h

structure Untouched {M : BinaryMachine} {N : ℕ} (j : ℕ) (S : Simulation M N) : Prop where
  below : j < S.pointer
  gates : ∀ g ∈ S.gates, NoTouch j g
  registers : Safe (fun i => i ≠ j) S.registers
  bounded : Safe (fun i => i < S.pointer) S.registers

lemma emit_untouched {M : BinaryMachine} {N : ℕ} (j : ℕ) (S : Simulation M N) (h : Untouched j S)
    (F : Symbolic M N → Symbolic M N)
    (hf : Safe (fun i => i ≠ j) (F S.registers))
    (hb : Safe (fun i => i < S.pointer) (F S.registers)) : Untouched j (emit F S) := by
  have hp := emit_monotone S F hb
  refine ⟨lt_of_lt_of_le h.below hp,?_,?_,safe_stored _ _ hb⟩
  · intro g hg
    rcases List.mem_append.mp hg with hold|hnew
    · exact h.gates g hold
    · exact batch_noTouch S.pointer j (expressionList (F S.registers)) h.below
        (fun e he => inputs_code _ e (safe_expressionList _ _ hf e he))
        (fun e he => inputs_bounded _ e (safe_expressionList _ _ hb e he)) g hnew
  · refine ⟨fun l => ?_,fun s => ?_,fun k i => ?_⟩
    · exact ne_of_gt (lt_trans h.below (stored_index S.pointer (F S.registers) hb (.inl l)).1)
    · exact ne_of_gt (lt_trans h.below (stored_index S.pointer (F S.registers) hb (.inr (.inl s))).1)
    · exact ne_of_gt (lt_trans h.below (stored_index S.pointer (F S.registers) hb (.inr (.inr (k,i)))).1)

lemma initial_untouched (M : BinaryMachine) (N p j : ℕ) (hj : j < p) :
    Untouched j (initialSimulation M N p) :=
  ⟨hj,by simp [initialSimulation],initialSymbolic_safe M N _,initialSymbolic_safe M N _⟩

lemma simulateStep_untouched {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (j : ℕ)
    (S : Simulation M N) (h : Untouched j S) : Untouched j (simulateStep hN S) :=
  emit_untouched j S h (symbolicStep hN) (safe_symbolicStep _ hN _ h.registers)
    (safe_symbolicStep _ hN _ h.bounded)

lemma iterate_untouched {M : BinaryMachine} {N : ℕ} (hN : 0 < N) (j : ℕ)
    (S : Simulation M N) (h : Untouched j S) (T : ℕ) : Untouched j ((simulateStep hN)^[T] S) := by
  induction T with
  | zero => exact h
  | succ T ih => rw [Function.iterate_succ_apply']; exact simulateStep_untouched hN j _ ih

lemma prepare_untouched {M : BinaryMachine} {N : ℕ} (p j : ℕ) (es : List Expr)
    (S : Simulation M N) (h : Untouched j S) (hp : p  ≤  S.pointer)
    (he : ∀ e ∈ es, Inputs (fun i => i < p) e) (he' : ∀ e ∈ es, Inputs (fun i => i ≠ j) e) :
    Untouched j (prepare es S) ∧ p  ≤  (prepare es S).pointer := by
  induction es with
  | nil => exact ⟨h,hp⟩
  | cons e es ih =>
    obtain ⟨ht,hptr⟩ := ih (fun a ha => he a (by simp [ha])) (fun a ha => he' a (by simp [ha]))
    let S' := prepare es S
    have hsafe := fillTrit_safe S'.registers _ ht.registers e (he' e (by simp))
    have hbound := fillTrit_safe S'.registers _ ht.bounded e
      (inputs_mono _ _ e (he e (by simp)) (fun i hi => lt_of_lt_of_le hi hptr))
    exact ⟨emit_untouched j S' ht (fillTrit e) hsafe hbound,
      le_trans hptr (emit_monotone S' (fillTrit e) hbound)⟩

lemma prepareBits_untouched {M : BinaryMachine} {N : ℕ} (p j : ℕ) (bits : List Bool)
    (S : Simulation M N) (h : Untouched j S) (hp : p  ≤  S.pointer) :
    Untouched j (prepareBits bits S) ∧ p  ≤  (prepareBits bits S).pointer := by
  induction bits with
  | nil => exact ⟨h,hp⟩
  | cons b bits ih =>
    obtain ⟨ht,hptr⟩ := ih
    let S' := prepareBits bits S
    let F : Symbolic M N → Symbolic M N := fun R => symPush R M.input (fun _ => b)
    have hsafe := safe_symPush _ S'.registers ht.registers M.input (fun _ => b)
    have hbound := safe_symPush _ S'.registers ht.bounded M.input (fun _ => b)
    exact ⟨emit_untouched j S' ht F hsafe hbound,le_trans hptr (emit_monotone S' F hbound)⟩

lemma inputProgram_untouched (M : BinaryMachine) (N n m j : ℕ)
    (hj : n*m+m  ≤  j) (hj' : j < reserve n m) :
    Untouched j (inputProgram M N (reserve n m) n m) := by
  have he := inputExprs_bounded n m (n*m+m) le_rfl
  obtain ⟨hd,hdp⟩ := prepare_untouched (reserve n m) j (inputExprs n m)
    (initialSimulation M N (reserve n m)) (initial_untouched M N _ j hj') le_rfl
    (fun e he' => inputs_mono _ _ e (he e he') (fun i hi => by dsimp [reserve]; omega))
    (fun e he' => inputs_mono _ _ e (he e he') (fun i hi => by omega))
  exact (prepareBits_untouched (reserve n m) j (unaryD n++unaryD m) _ hd hdp).1

lemma decoderSimulation_untouched (M : BinaryMachine) (n m T j : ℕ)
    (hj : n*m+m  ≤  j) (hj' : j < reserve n m) :
    Untouched j (decoderSimulation M n m T) :=
  iterate_untouched _ j _ (inputProgram_untouched M _ n m j hj hj') T

end F3MachineCompiler

-- Source: Solutions.T31.OutputProgram

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

def encodeValues (vs : List (ZMod 3)) : List Bool := vs.flatMap (fun v => unaryD v.val)

lemma encodeValues_append (vs ws : List (ZMod 3)) :
    encodeValues (vs++ws) = encodeValues vs++encodeValues ws := List.flatMap_append

noncomputable def consumeStep {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N) :
    Simulation M N → Simulation M N := emit (consumeTrit τ hN)

lemma consumeStep_correct {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Simulation M N) (y : ℕ → ZMod 3) (v : ZMod 3) (tail : List Bool)
    (h : Simulates S (M.finalCfg ((unaryD v.val++tail).map τ)) y)
    (hk : ((unaryD v.val++tail).map τ).length  ≤  N) :
    Simulates (consumeStep τ hN S) (M.finalCfg (tail.map τ)) y := by
  have hword : (M.finalCfg ((unaryD v.val++tail).map τ)).stk M.output =
      (unaryD v.val++tail).map τ := by simp [OAI.MetricKMedian.Binary.Machine.finalCfg]
  have hr := consumeTrit_rep τ hN S.registers (M.finalCfg ((unaryD v.val++tail).map τ))
    (rawRun S.gates y) h.2.2.1 (by simpa only [hword] using hk) v tail hword
  have hr' : Represents (consumeTrit τ hN S.registers) (M.finalCfg (tail.map τ)) (rawRun S.gates y) := by
    convert hr using 1
    refine OAI.MetricKMedian.Binary.cfg_ext ?_ ?_ ?_
    · rfl
    · rfl
    · funext k
      by_cases hk : k = M.output <;>
        simp [OAI.MetricKMedian.Binary.Machine.finalCfg,Function.update_apply,hk]
  exact emit_correct S _ _ y h (consumeTrit τ hN) hr' (consumeTrit_safe _ τ hN _ h.2.2.2)

lemma consumePrefix_correct {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (pre : List (ZMod 3)) (tail : List Bool) (S : Simulation M N) (y : ℕ → ZMod 3)
    (h : Simulates S (M.finalCfg ((encodeValues pre++tail).map τ)) y)
    (hk : ((encodeValues pre++tail).map τ).length  ≤  N) :
    Simulates ((consumeStep τ hN)^[pre.length] S) (M.finalCfg (tail.map τ)) y := by
  induction pre generalizing S with
  | nil => simpa only [encodeValues,List.flatMap_nil,List.nil_append,List.length_nil,Function.iterate_zero,
      Function.id_def] using h
  | cons v vs ih =>
    have hinit : Simulates S (M.finalCfg ((unaryD v.val++(encodeValues vs++tail)).map τ)) y := by
      simpa only [encodeValues,List.flatMap_cons,List.append_assoc] using h
    have hlen : ((unaryD v.val++(encodeValues vs++tail)).map τ).length  ≤  N := by
      simpa only [encodeValues,List.flatMap_cons,List.append_assoc] using hk
    have hr := consumeStep_correct τ hN S y v _ hinit hlen
    have hk' : ((encodeValues vs++tail).map τ).length  ≤  N := by
      simp only [List.length_map,List.length_append] at hlen ⊢
      omega
    have ht := ih (consumeStep τ hN S) hr hk'
    simpa only [List.length_cons,Function.iterate_succ_apply] using ht

lemma consumeStep_untouched {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (j : ℕ) (S : Simulation M N) (h : Untouched j S) : Untouched j (consumeStep τ hN S) :=
  emit_untouched j S h (consumeTrit τ hN) (consumeTrit_safe _ τ hN _ h.registers)
    (consumeTrit_safe _ τ hN _ h.bounded)

lemma consumeClock_untouched {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (j : ℕ) (S : Simulation M N) (h : Untouched j S) (t : ℕ) :
    Untouched j ((consumeStep τ hN)^[t] S) := by
  induction t with
  | zero => exact h
  | succ t ih => rw [Function.iterate_succ_apply']; exact consumeStep_untouched τ hN j _ ih

noncomputable def answerSimulation (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) :
    Simulation M (capacity M n m T) :=
  (consumeStep τ (capacity_ge_two M n m T))^[j] (decoderSimulation M n m T)

noncomputable def answerExpression (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) : Expr :=
  parsedTrit τ (capacity_ge_two M n m T) (answerSimulation M τ n m T j).registers

end F3MachineCompiler

-- Source: Solutions.T31.Answer

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum Turing
open Classical

lemma answer_spec (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod 3)) (b : Fin m → ZMod 3) (s : Fin n → ZMod 3)
    (y : ℕ → ZMod 3) (hz : ∀ i, reserve n m  ≤  i → y i = 0)
    (hA : ∀ i j, y (n*i.val+j.val) = A j i) (hb : ∀ i, y (n*m+i.val) = b i)
    (hrun : TM2OutputsInTime M.tm (encodeInstance A (fun i => b i-1))
      (some ((encodeSecret s).map τ)) T) (j : Fin n) :
    Simulates (answerSimulation M τ n m T j.val)
      (M.finalCfg ((encodeValues (((List.finRange n).map s).drop j.val)).map τ)) y ∧
    (answerExpression M τ n m T j.val).eval
      (rawRun (answerSimulation M τ n m T j.val).gates y) = s j := by
  let vs : List (ZMod 3) := (List.finRange n).map s
  have hvs : vs.length = n := by simp [vs]
  have hencode : encodeValues vs = encodeSecret s := by
    simp [vs,encodeValues,encodeSecret,List.flatMap_map]
  have hclock := clock_outputs M (encodeInstance A (fun i => b i-1)) ((encodeSecret s).map τ) T hrun
  have hsim := decoderSimulation_correct M n m T A b y hz hA hb
  rw [hclock] at hsim
  have hfit := clock_fits M (encodeInstance A (fun i => b i-1)) T
  rw [hclock] at hfit
  have hlen := hfit M.output
  simp only [OAI.MetricKMedian.Binary.Machine.finalCfg,ite_true] at hlen
  have hcap : ((encodeSecret s).map τ).length  ≤  capacity M n m T :=
    le_trans hlen (capacity_fits M A (fun i => b i-1) T)
  have hword : encodeValues (vs.take j.val)++encodeValues (vs.drop j.val) = encodeSecret s := by
    rw [← encodeValues_append,List.take_append_drop,hencode]
  have hstart : Simulates (decoderSimulation M n m T)
      (M.finalCfg ((encodeValues (vs.take j.val)++encodeValues (vs.drop j.val)).map τ)) y := by
    rw [hword]
    exact hsim
  have hsize : ((encodeValues (vs.take j.val)++encodeValues (vs.drop j.val)).map τ).length  ≤ 
      capacity M n m T := by rw [hword]; exact hcap
  have hc := consumePrefix_correct τ (capacity_ge_two M n m T) (vs.take j.val)
    (encodeValues (vs.drop j.val)) (decoderSimulation M n m T) y hstart hsize
  rw [List.length_take,hvs,Nat.min_eq_left (Nat.le_of_lt j.isLt)] at hc
  change Simulates (answerSimulation M τ n m T j.val)
    (M.finalCfg ((encodeValues (vs.drop j.val)).map τ)) y at hc
  have hj : j.val < vs.length := by rw [hvs]; exact j.isLt
  have hdrop : vs.drop j.val = s j::vs.drop (j.val+1) := by
    have hd := List.drop_eq_getElem_cons hj
    simpa [vs,List.getElem_map,List.getElem_finRange] using hd
  have hout : (M.finalCfg ((encodeValues (vs.drop j.val)).map τ)).stk M.output =
      (unaryD (s j).val++encodeValues (vs.drop (j.val+1))).map τ := by
    simp only [OAI.MetricKMedian.Binary.Machine.finalCfg,ite_true,hdrop,encodeValues,List.flatMap_cons]
  exact ⟨hc,parsedTrit_eval τ (capacity_ge_two M n m T) _ _ _ hc.2.2.1 (s j) _ hout⟩

end F3MachineCompiler

-- Source: Solutions.T31.Collisions

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open scoped BigOperators
open F3SubsetSum Matrix

section
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]

-- A surjective homomorphism sends the uniform distribution to the uniform distribution.
open Classical in
lemma uniform_preimage_card (f : G →+ H) (hf : Function.Surjective f) (S : Finset H) :
    (Finset.univ.filter fun x => f x ∈ S).card * Fintype.card H =
      S.card * Fintype.card G := by
  classical
  let N := (Finset.univ.filter fun x : G => f x = 0).card
  have hcard (y : H) : (Finset.univ.filter fun x => f x = y).card = N := by
    obtain ⟨d, hd⟩ := hf y
    symm
    apply Finset.card_equiv (Equiv.addRight d)
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight, map_add, hd]
    simp
  have hfull : Fintype.card G = Fintype.card H * N := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset G)
      (Finset.univ : Finset H) f
    simpa only [hcard, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mem_univ, Finset.filter_true, Nat.cast_id] using h.symm
  have hS : (Finset.univ.filter fun x => f x ∈ S).card = S.card * N := by
    have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset G) S f
    simpa only [hcard, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using h.symm
  rw [hS, hfull]
  ring
end

abbrev Instance (n m : ℕ) := Matrix (Fin n) (Fin m) (ZMod 3)
abbrev Secret (n : ℕ) := Fin n → ZMod 3
abbrev Word (m : ℕ) := Fin m → ZMod 3
abbrev Errors (m : ℕ) := Fin m → Bool

def sampleHom {n m : ℕ} (u : Secret n) : Instance n m →+ Word m where
  toFun A := Aᵀ *ᵥ u
  map_zero' := by simp
  map_add' A B := by
    funext i
    simp [Matrix.mulVec,dotProduct,add_mul,Finset.sum_add_distrib]

lemma sampleHom_onto {n m : ℕ} (u : Secret n) (hu : u ≠ 0) :
    Function.Surjective (sampleHom (m := m) u) := by
  obtain ⟨j,hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    apply hu
    funext j
    simpa using not_exists.mp h j
  intro b
  let A : Instance n m := fun k i => if k = j then b i/u j else 0
  refine ⟨A,?_⟩
  funext i
  change ∑ k, A k i*u k = b i
  simp [A,ite_mul,div_mul_cancel₀ _ hj]

lemma sample_fiber_count {n m : ℕ} (u : Secret n) (hu : u ≠ 0) (b : Word m) :
    (Finset.univ.filter (fun A : Instance n m => Aᵀ *ᵥ u = b)).card*3^m = 3^(n*m) := by
  have hh := uniform_preimage_card (sampleHom (m := m) u) (sampleHom_onto u hu) {b}
  simpa [sampleHom,Fintype.card_fun,Matrix,ZMod.card,← pow_mul,Nat.mul_comm] using hh

lemma sample_probability {n m : ℕ} (u : Secret n) (hu : u ≠ 0) (b : Word m) :
    ((Finset.univ.filter (fun A : Instance n m => Aᵀ *ᵥ u = b)).card : ℝ)/(3:ℝ)^(n*m) =
      1/(3:ℝ)^m := by
  have hh : ((Finset.univ.filter (fun A : Instance n m => Aᵀ *ᵥ u = b)).card : ℝ)*(3:ℝ)^m =
      (3:ℝ)^(n*m) := by exact_mod_cast sample_fiber_count u hu b
  apply (div_eq_div_iff (by positivity) (by positivity)).mpr
  simpa using hh

def delta {m : ℕ} (e : Errors m) : Word m := fun i => if e i then -1 else 1

lemma delta_injective (m : ℕ) : Function.Injective (@delta m) := by
  intro e f h
  funext i
  have hi := congrFun h i
  cases he : e i <;> cases hf : f i <;> simp [delta,he,hf] at hi ⊢

lemma delta_binary {m : ℕ} (e : Errors m) : (fun i => delta e i-1) = binVec 3 e := by
  funext i
  cases he : e i <;> simp [delta,binVec,he]

def noisyWord {n m : ℕ} (A : Instance n m) (s : Secret n) (e : Errors m) : Word m := Aᵀ *ᵥ s+delta e

lemma noisy_collision {n m : ℕ} (A : Instance n m) (s t : Secret n) (e f : Errors m) :
    noisyWord A s e = noisyWord A t f ↔ Aᵀ *ᵥ (s-t) = delta f-delta e := by
  rw [Matrix.mulVec_sub]
  unfold noisyWord
  constructor <;> intro h <;> linear_combination h

lemma noisy_same_secret {n m : ℕ} (A : Instance n m) (s : Secret n) (e f : Errors m)
    (h : noisyWord A s e = noisyWord A s f) : e = f :=
  delta_injective m (add_left_cancel h)

lemma decoder_sample {n m : ℕ} (A : Instance n m) (s : Secret n) (e : Errors m) :
    (fun i => noisyWord A s e i-1) = lweSample A s e := by
  funext i
  have hd := congrFun (delta_binary e) i
  simp only [noisyWord,lweSample,Pi.add_apply] at ⊢
  linear_combination hd

/-- Distinct secrets collide with probability exactly 3^{-m}, for every fixed pair of errors. -/
lemma noisy_probability {n m : ℕ} (s t : Secret n) (hst : s ≠ t) (e f : Errors m) :
    ((Finset.univ.filter (fun A : Instance n m => noisyWord A s e = noisyWord A t f)).card : ℝ)/
      (3:ℝ)^(n*m) = 1/(3:ℝ)^m := by
  simp only [noisy_collision]
  exact sample_probability (s-t) (sub_ne_zero.mpr hst) (delta f-delta e)

end F3Reduction

-- Source: Solutions.T31.Tensor

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

noncomputable def tensorMatrix {ι : Type} [Fintype ι]
    (M : ι → Matrix (ZMod 3) (ZMod 3) ℂ) : (ι → ZMod 3) → (ι → ZMod 3) → ℂ :=
  fun a b => ∏ i, M i (a i) (b i)

lemma tensor_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Matrix (ZMod 3) (ZMod 3) ℂ)
    (hM : ∀ i a b, ∑ j, star (M i j a)*M i j b = if a = b then 1 else 0)
    (a b : ι → ZMod 3) :
    ∑ j : ι → ZMod 3, star (tensorMatrix M j a)*tensorMatrix M j b = if a = b then 1 else 0 := by
  simp only [tensorMatrix,star_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (j : ZMod 3) => star (M i j (a i))*M i j (b i))]
  simp_rw [hM]
  by_cases hab : a = b
  · subst b
    simp
  · obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by
      by_contra h
      exact hab (funext (fun i => not_not.mp (not_exists.mp h i)))
    rw [if_neg hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma tensor_apply_product {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Matrix (ZMod 3) (ZMod 3) ℂ)
    (v : ι → ZMod 3 → ℂ) (a : ι → ZMod 3) :
    matApply (tensorMatrix M) (fun b => ∏ i, v i (b i)) a =
      ∏ i, matApply (M i) (v i) (a i) := by
  simp only [matApply,tensorMatrix,← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]

noncomputable def scaledNot (a b : ZMod 3) : ℂ :=
  if b = a+1 then 1 else if b = a-1 then -1 else 0
noncomputable def scaledTrine (a b : ZMod 3) : ℂ :=
  if b = 0 then 0 else phase (a*b)

lemma scaledNot_eq (a b : ZMod 3) : scaledNot a b = (Real.sqrt 2 : ℂ)*notState a b := by
  unfold scaledNot notState
  split_ifs <;> field_simp [sqrt2_ne] <;> ring

lemma scaledTrine_eq (a b : ZMod 3) : scaledTrine a b = (Real.sqrt 2 : ℂ)*trine a b := by
  unfold scaledTrine trine
  split_ifs <;> field_simp [sqrt2_ne] <;> ring

lemma matApply_mul {ι κ : Type} [Fintype ι] (M : κ → ι → ℂ) (c : ℂ) (v : ι → ℂ) (a : κ) :
    matApply M (fun i => c*v i) a = c*matApply M v a := by
  simp only [matApply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma uInv_scaled (a b : ZMod 3) : matApply uMat.conjTranspose (scaledNot a) b = scaledTrine a b := by
  have he : scaledNot a = fun b => (Real.sqrt 2 : ℂ)*notState a b := funext (scaledNot_eq a)
  rw [he,matApply_mul,uInv_not]
  exact (scaledTrine_eq a b).symm

lemma tensor_uInv (m : ℕ) (v c : Word m) :
    matApply (tensorMatrix (fun _ : Fin m => uMat.conjTranspose))
      (fun b => ∏ i, scaledNot (v i) (b i)) c = ∏ i, scaledTrine (v i) (c i) := by
  have h := tensor_apply_product (fun _ : Fin m => uMat.conjTranspose)
    (fun i => scaledNot (v i)) c
  simpa only [uInv_scaled] using h

end F3Reduction

-- Source: Solutions.T31.Block

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

def blockPlace {W : ℕ} (y : QBasis W) (off len : ℕ) (v : Fin len → ZMod 3) : QBasis W :=
  fun w => if h : off  ≤  w.val ∧ w.val < off+len then v ⟨w.val-off,by omega⟩ else y w

lemma blockPlace_at {W off len : ℕ} (y : QBasis W) (h : off+len  ≤  W)
    (v : Fin len → ZMod 3) (i : Fin len) :
    blockPlace y off len v ⟨off+i.val,by have := i.isLt; omega⟩ = v i := by
  simp only [blockPlace]
  split_ifs with hi
  · congr 1; apply Fin.ext; change off+i.val-off = i.val; omega
  · have := i.isLt; omega

lemma blockPlace_outside {W off len : ℕ} (y : QBasis W) (v : Fin len → ZMod 3)
    (i : Fin W) (hi : i.val < off ∨ off+len  ≤  i.val) : blockPlace y off len v i = y i := by
  simp only [blockPlace]
  split_ifs with h
  · omega
  · rfl

lemma blockPlace_injective {W off len : ℕ} (y : QBasis W) (h : off+len  ≤  W) :
    Function.Injective (blockPlace y off len) := by
  intro v w he
  funext i
  have he := congrFun he ⟨off+i.val,by have := i.isLt; omega⟩
  simpa only [blockPlace_at y h] using he

lemma blockPlace_zero {W off : ℕ} (y : QBasis W) (v : Fin 0 → ZMod 3) :
    blockPlace y off 0 v = y := by
  funext i
  apply blockPlace_outside
  omega

lemma blockPlace_snoc {W off n : ℕ} (y : QBasis W) (h : off+(n+1)  ≤  W)
    (v : Fin n → ZMod 3) (a : ZMod 3) :
    blockPlace y off (n+1) (Fin.snoc v a) =
      Function.update (blockPlace y off n v) ⟨off+n,by omega⟩ a := by
  funext w
  by_cases hw : w.val = off+n
  · have hw' : w = ⟨off+n,by omega⟩ := Fin.ext hw
    rw [hw',Function.update_self]
    have ht := blockPlace_at y h (Fin.snoc v a) (Fin.last n)
    exact ht.trans (Fin.snoc_last _ _)
  · have hne : w ≠ ⟨off+n,by omega⟩ := fun hh => hw (congrArg Fin.val hh)
    rw [Function.update_of_ne hne]
    by_cases hr : off  ≤  w.val ∧ w.val < off+n
    · have hs : off  ≤  w.val ∧ w.val < off+(n+1) := by omega
      simp only [blockPlace,dif_pos hs,dif_pos hr]
      have hi : (⟨w.val-off,by omega⟩ : Fin (n+1)) =
          (⟨w.val-off,by omega⟩ : Fin n).castSucc := rfl
      rw [hi,Fin.snoc_castSucc]
    · rw [blockPlace_outside y v w (by omega)]
      exact blockPlace_outside y (Fin.snoc v a) w (by omega)

noncomputable def rangeApply {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (off : ℕ) :
    (len : ℕ) → off+len  ≤  W → Ket W → Ket W
  | 0, _, ψ => ψ
  | n+1, h, ψ => applySingle M ⟨off+n,by omega⟩ (rangeApply M off n (by omega) ψ)

lemma rangeApply_basis {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (off n : ℕ)
    (h : off+n  ≤  W) (y : QBasis W) :
    rangeApply M off n h (basisKet y) =
      ∑ v : Fin n → ZMod 3, (∏ i, M (v i) (y ⟨off+i.val,by have := i.isLt; omega⟩)) •
        basisKet (blockPlace y off n v) := by
  induction n with
  | zero => simp [rangeApply,blockPlace_zero]
  | succ n ih =>
    rw [rangeApply,ih]
    have hs' : ∀ (s : Finset (Fin n → ZMod 3)) (f : (Fin n → ZMod 3) → Ket W),
        applySingle M ⟨off+n,by omega⟩ (∑ v ∈ s, f v) =
          ∑ v ∈ s, applySingle M ⟨off+n,by omega⟩ (f v) := by
      intro s f
      induction s using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; funext z; simp [applySingle]
      | @insert v s hv hi => simp only [Finset.sum_insert hv,applySingle_add,hi]
    rw [hs' Finset.univ]
    simp_rw [applySingle_smul,applySingle_basis,Finset.smul_sum,smul_smul]
    have hout (v : Fin n → ZMod 3) :
        blockPlace y off n v ⟨off+n,by omega⟩ = y ⟨off+n,by omega⟩ :=
      blockPlace_outside y v _ (Or.inr (by change off+n  ≤  off+n; exact le_rfl))
    simp_rw [hout,← blockPlace_snoc y h]
    have he := Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => ZMod 3))
      (fun p => ((∏ i : Fin n, M (p.2 i) (y ⟨off+i.val,by have := i.isLt; omega⟩)) *
        M p.1 (y ⟨off+n,by omega⟩)) • basisKet (blockPlace y off (n+1) (Fin.snoc p.2 p.1)))
      (fun v => (∏ i : Fin (n+1), M (v i) (y ⟨off+i.val,by have := i.isLt; omega⟩)) •
        basisKet (blockPlace y off (n+1) v)) (by
          intro p
          simp only [Fin.snocEquiv_apply,Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
          rfl)
    rw [← he,Fintype.sum_prod_type,Finset.sum_comm]
noncomputable def singleLinear {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (i : Fin W) :
    Ket W →ₗ[ℂ] Ket W where
  toFun := applySingle M i
  map_add' := applySingle_add M i
  map_smul' := applySingle_smul M i

noncomputable def rangeLinear {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (off : ℕ) :
    (n : ℕ) → off+n  ≤  W → Ket W →ₗ[ℂ] Ket W
  | 0, _ => LinearMap.id
  | n+1, h => (singleLinear M ⟨off+n,by omega⟩).comp (rangeLinear M off n (by omega))

lemma rangeLinear_apply {W : ℕ} (M : Matrix (ZMod 3) (ZMod 3) ℂ) (off n : ℕ)
    (h : off+n  ≤  W) (ψ : Ket W) : rangeLinear M off n h ψ = rangeApply M off n h ψ := by
  induction n with
  | zero => rfl
  | succ n ih => change applySingle M _ (rangeLinear M off n _ ψ) = _; rw [ih]; rfl

noncomputable def singleMatrix (tag : ℕ) : Matrix (ZMod 3) (ZMod 3) ℂ :=
  if tag = 0 then fourierMat else if tag = 1 then pMat else uMat.conjTranspose

lemma single_run (W tag i : ℕ) (hi : i < W) (ψ : Ket W) :
    (single W tag i).foldl (fun φ g => applyGate g φ) ψ =
      applySingle (singleMatrix tag) ⟨i,hi⟩ ψ := by
  simp only [single,dif_pos hi,List.foldl_cons,List.foldl_nil,singleMatrix]
  split_ifs <;> rfl

lemma rangeGates_run {W : ℕ} (tag off n : ℕ) (h : off+n  ≤  W) (ψ : Ket W) :
    ((List.range n).flatMap (fun i => single W tag (off+i))).foldl
      (fun φ g => applyGate g φ) ψ = rangeApply (singleMatrix tag) off n h ψ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,List.foldl_append,ih,
      single_run W tag (off+n) (by omega)]
    rfl

end F3Reduction

-- Source: Solutions.T31.Embedding

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

def frontEmbedding (W E : ℕ) : Fin W ↪ Fin (W+E) :=
  ⟨fun i => ⟨i.val,by omega⟩,fun _ _ h => Fin.ext (congrArg (fun j : Fin (W+E) => j.val) h)⟩

def restrictBasis {W E : ℕ} (y : QBasis (W+E)) : QBasis W := y ∘ frontEmbedding W E

def zeroTail {W E : ℕ} (y : QBasis (W+E)) : Prop := ∀ i, W  ≤  i.val → y i = 0

def extendBasis {W : ℕ} (E : ℕ) (y : QBasis W) : QBasis (W+E) :=
  fun i => if hi : i.val < W then y ⟨i.val,hi⟩ else 0

noncomputable def extendKet {W : ℕ} (E : ℕ) (ψ : Ket W) : Ket (W+E) :=
  fun y => if zeroTail y then ψ (restrictBasis y) else 0

lemma restrict_extend {W : ℕ} (E : ℕ) (y : QBasis W) : restrictBasis (extendBasis E y) = y := by
  funext i
  simp [restrictBasis,extendBasis,frontEmbedding]

lemma zeroTail_extend {W : ℕ} (E : ℕ) (y : QBasis W) : zeroTail (extendBasis E y) := by
  intro i hi
  simp only [extendBasis,dif_neg (by omega : ¬i.val < W)]

lemma extend_restrict {W E : ℕ} (y : QBasis (W+E)) (hy : zeroTail y) :
    extendBasis E (restrictBasis y) = y := by
  funext i
  by_cases hi : i.val < W
  · simp only [extendBasis,dif_pos hi,restrictBasis,Function.comp_apply,frontEmbedding]
    congr 1
  · simp only [extendBasis,dif_neg hi]
    exact (hy i (by omega)).symm

lemma restrict_update {W E : ℕ} (y : QBasis (W+E)) (i : Fin W) (a : ZMod 3) :
    restrictBasis (Function.update y (frontEmbedding W E i) a) =
      Function.update (restrictBasis y) i a := by
  funext j
  simp [restrictBasis,Function.update_apply,(frontEmbedding W E).injective.eq_iff]

lemma zeroTail_update {W E : ℕ} (y : QBasis (W+E)) (i : Fin W) (a : ZMod 3) :
    zeroTail (Function.update y (frontEmbedding W E i) a) ↔ zeroTail y := by
  constructor <;> intro h j hj
  · have hn : j ≠ frontEmbedding W E i := by
      intro he; have he := congrArg Fin.val he; have := i.isLt; dsimp [frontEmbedding] at he; omega
    simpa only [Function.update_of_ne hn] using h j hj
  · have hn : j ≠ frontEmbedding W E i := by
      intro he; have he := congrArg Fin.val he; have := i.isLt; dsimp [frontEmbedding] at he; omega
    simpa only [Function.update_of_ne hn] using h j hj

lemma extendKet_basis {W : ℕ} (E : ℕ) (y : QBasis W) :
    extendKet E (basisKet y) = basisKet (extendBasis E y) := by
  funext z
  by_cases hz : zeroTail z
  · have he : restrictBasis z = y ↔ z = extendBasis E y := by
      constructor
      · intro h; rw [← h,extend_restrict z hz]
      · intro h; rw [h,restrict_extend]
    simp [extendKet,basisKet,hz,he]
  · have he : z ≠ extendBasis E y := by intro h; subst z; exact hz (zeroTail_extend E y)
    simp [extendKet,basisKet,hz,he]

lemma extendKet_single {W : ℕ} (E : ℕ) (M : Matrix (ZMod 3) (ZMod 3) ℂ)
    (i : Fin W) (ψ : Ket W) :
    extendKet E (applySingle M i ψ) = applySingle M (frontEmbedding W E i) (extendKet E ψ) := by
  funext y
  by_cases hy : zeroTail y
  · simp only [extendKet,applySingle,if_pos hy,zeroTail_update,restrict_update]
    rfl
  · simp only [extendKet,applySingle,if_neg hy,zeroTail_update,restrict_update]
    simp only [hy,ite_false,mul_zero,Finset.sum_const_zero]

lemma extendKet_gate {W : ℕ} (E : ℕ) (g : Gate W) (ψ : Ket W) :
    extendKet E (applyGate g ψ) = applyGate (mapGate (frontEmbedding W E) g) (extendKet E ψ) := by
  cases g with
  | fourier i => exact extendKet_single E fourierMat i ψ
  | fourierInv i => exact extendKet_single E fourierMat.conjTranspose i ψ
  | p i => exact extendKet_single E pMat i ψ
  | pInv i => exact extendKet_single E pMat.conjTranspose i ψ
  | u i => exact extendKet_single E uMat i ψ
  | uInv i => exact extendKet_single E uMat.conjTranspose i ψ
  | x i | xInv i | csum i j hij | csumInv i j hij | ccmul i j k hij hik hjk | ccmulInv i j k hij hik hjk =>
    funext y
    simp only [extendKet,applyGate,mapGate,zeroTail_update,restrict_update]
    rfl

lemma extendKet_run {W : ℕ} (E : ℕ) (gs : List (Gate W)) (ψ : Ket W) :
    extendKet E (gs.foldl (fun φ g => applyGate g φ) ψ) =
      (gs.map (mapGate (frontEmbedding W E))).foldl (fun φ g => applyGate g φ) (extendKet E ψ) := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,List.map_cons]
    rw [ih,extendKet_gate]

end F3Reduction

-- Source: Solutions.T31.Characters

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum Matrix
open Classical

noncomputable def dot3 {n : ℕ} (s y : Secret n) : ZMod 3 := ∑ j, s j*y j

lemma dot3_add {n : ℕ} (s t y : Secret n) : dot3 (s+t) y = dot3 s y+dot3 t y := by
  simp [dot3,add_mul,Finset.sum_add_distrib]

lemma phase_ne_one (a : ZMod 3) (ha : a ≠ 0) : phase a ≠ 1 := by
  rcases cases_three a with rfl | rfl | rfl
  · exact False.elim (ha rfl)
  · simpa only [phase_one] using omega_ne_one
  · rw [phase_two]
    intro h
    have hc := omega_cube
    rw [show (3:ℕ) = 2+1 by decide,pow_succ,h,one_mul] at hc
    exact omega_ne_one hc

lemma character_sum {n : ℕ} (y : Secret n) :
    (∑ s : Secret n, phase (dot3 s y)) = if y = 0 then (3:ℂ)^n else 0 := by
  by_cases hy : y = 0
  · subst y
    simp [dot3,Fintype.card_fun,ZMod.card,Secret]
  · rw [if_neg hy]
    obtain ⟨j,hj⟩ : ∃ j, y j ≠ 0 := by
      by_contra h
      apply hy
      funext j
      exact not_not.mp (not_exists.mp h j)
    let t : Secret n := Pi.single j 1
    have hdot : dot3 t y = y j := by simp [dot3,t,Pi.single_apply,ite_mul]
    have he : (∑ s : Secret n, phase (dot3 (s+t) y)) = ∑ s : Secret n, phase (dot3 s y) :=
      Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
    simp only [dot3_add,phase_add,← Finset.sum_mul,hdot] at he
    have hm : (∑ s : Secret n, phase (dot3 s y))*(phase (y j)-1) = 0 := by
      linear_combination he
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr (phase_ne_one _ hj))

lemma phase_finset_sum {ι : Type} (s : Finset ι) (f : ι → ZMod 3) :
    phase (∑ i ∈ s, f i) = ∏ i ∈ s, phase (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha,phase_add,ih]

lemma matrix_character_identity {n m : ℕ} (A : Instance n m) (s : Secret n) (c : Word m) :
    (∑ i, (Aᵀ *ᵥ s) i*c i) = dot3 s (A *ᵥ c) := by
  simp only [Matrix.mulVec,dotProduct,dot3,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

end F3Reduction

-- Source: Solutions.T31.CollisionEnergy

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open Classical

noncomputable def push {ι κ : Type} [Fintype ι] (f : ι → κ) (c : ι → ℂ) : κ → ℂ := by
  classical
  exact matApply (fun y x => if f x = y then 1 else 0) c

lemma push_gram {ι κ : Type} [Fintype κ] (f : ι → κ) (a b : ι) :
    (∑ y : κ, star (if f a = y then (1:ℂ) else 0)*(if f b = y then 1 else 0)) =
      if f a = f b then 1 else 0 := by
  classical
  by_cases h : f a = f b
  · simp [h]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y hy
    by_cases ha : f a = y <;> by_cases hb : f b = y <;> simp_all

lemma push_energy {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ) (c : ι → ℂ) :
    energy (push f c) = ∑ a, ∑ b, if f a = f b then (star (c a)*c b).re else 0 := by
  classical
  have h := matApply_ip (fun y x => if f x = y then (1:ℂ) else 0) c c
  rw [ip_self] at h
  simp only [push_gram] at h
  have hr := congrArg Complex.re h
  simpa only [push,mul_ite,mul_one,mul_zero,Complex.re_sum,Complex.ofReal_re,apply_ite Complex.re,Complex.zero_re] using hr

lemma push_energy_injective {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (c : ι → ℂ) : energy (push f c) = energy c := by
  classical
  rw [push_energy]
  simp only [hf.eq_iff]
  simp [energy,Complex.normSq, pow_two]

lemma signs_product_bound (a b : ℂ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    (star a*b).re  ≤  1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

/-- Coalescing signed amplitudes costs at most one per off-diagonal collision. -/
lemma push_energy_bound {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → κ) (c : ι → ℂ) (hc : ∀ a, c a = 1 ∨ c a = -1) (P : ι → Prop) :
    energy (push f (fun a => if P a then c a else 0))  ≤ 
      (∑ a, if P a then (1:ℝ) else 0)+
        ∑ a, ∑ b, if a ≠ b ∧ f a = f b then (1:ℝ) else 0 := by
  classical
  rw [push_energy]
  have hdiag : (∑ a : ι, ∑ b : ι, if a = b then (if P a then (1:ℝ) else 0) else 0) =
      ∑ a, if P a then (1:ℝ) else 0 := by simp
  rw [← hdiag,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b hb
  by_cases hab : a = b
  · subst b
    by_cases hp : P a
    · rcases hc a with h | h <;> simp [hp,h]
    · simp [hp]
  by_cases hfab : f a = f b
  · simp only [hab,hfab,ne_eq,not_false_eq_true,and_self,if_true,if_false,zero_add]
    by_cases hpa : P a <;> by_cases hpb : P b
    · simpa only [if_pos hpa,if_pos hpb] using signs_product_bound (c a) (c b) (hc a) (hc b)
    all_goals simp [hpa,hpb]
  · simp [hab,hfab]

lemma energy_smul {ι : Type} [Fintype ι] (c : ℂ) (v : ι → ℂ) :
    energy (c • v) = Complex.normSq c*energy v := by
  simp [energy,Complex.normSq_mul,Finset.mul_sum]

lemma neg_one_power_sign (k : ℕ) : (-1:ℂ)^k = 1 ∨ (-1:ℂ)^k = -1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    rcases ih with h | h <;> simp [h]

end F3Reduction

-- Source: Solutions.T31.DecodingEnergy

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

abbrev Pair (n m : ℕ) := Secret n × Errors m

noncomputable def sign {m : ℕ} (e : Errors m) : ℂ :=
  (-1)^((Finset.univ.filter fun i => e i).card)

lemma sign_pm {m : ℕ} (e : Errors m) : sign e = 1 ∨ sign e = -1 := neg_one_power_sign _

noncomputable def bad {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (x : Pair n m) : Prop :=
  Dec n m A (lweSample A x.1 x.2) ≠ x.1

noncomputable def afterErase {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (x : Pair n m) :
    Word m × Secret n :=
  (noisyWord A x.1 x.2,x.1-Dec n m A (fun i => noisyWord A x.1 x.2 i-1))

lemma erase_injective {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    Function.Injective (afterErase Dec A) := by
  rintro ⟨s,e⟩ ⟨t,f⟩ h
  have hw := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change noisyWord A s e = noisyWord A t f at hw
  change s-Dec n m A (fun i => noisyWord A s e i-1) =
    t-Dec n m A (fun i => noisyWord A t f i-1) at hr
  rw [hw] at hr
  have hs : s = t := by linear_combination hr
  subst t
  have he := noisy_same_secret A s e f hw
  subst f
  rfl

lemma erase_zero_iff {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (x : Pair n m) :
    (afterErase Dec A x).2 = 0 ↔ ¬bad Dec A x := by
  simp only [afterErase,bad,decoder_sample,sub_eq_zero,ne_eq,not_not]
  exact eq_comm

noncomputable def rawError {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    Word m × Secret n → ℂ :=
  push (afterErase Dec A) (fun x => if bad Dec A x then sign x.2 else 0)

noncomputable def rawMissing {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) : Word m → ℂ :=
  push (fun x : Pair n m => noisyWord A x.1 x.2) (fun x => if bad Dec A x then sign x.2 else 0)

noncomputable def badMass {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) : ℝ :=
  ∑ x : Pair n m, if bad Dec A x then 1 else 0

noncomputable def collisions {n m : ℕ} (A : Instance n m) : ℝ :=
  ∑ x : Pair n m, ∑ y : Pair n m,
    if x ≠ y ∧ noisyWord A x.1 x.2 = noisyWord A y.1 y.2 then 1 else 0

lemma error_energy {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    energy (rawError Dec A) = badMass Dec A := by
  rw [rawError,push_energy_injective _ (erase_injective Dec A)]
  unfold energy badMass
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb : bad Dec A x
  · rcases sign_pm x.2 with hs | hs <;> simp [hb,hs]
  · simp [hb]

lemma missing_energy {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    energy (rawMissing Dec A)  ≤  badMass Dec A+collisions A := by
  unfold rawMissing badMass collisions
  convert push_energy_bound (fun x : Pair n m => noisyWord A x.1 x.2)
    (fun x => sign x.2) (fun x => sign_pm x.2) (bad Dec A) using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases h : x ≠ y ∧ noisyWord A x.1 x.2 = noisyWord A y.1 y.2 <;> simp [h]

lemma rawError_zero_slice {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (b : Word m) :
    rawError Dec A (b,0) = 0 := by
  unfold rawError push matApply
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hb : bad Dec A x
  · have hn : afterErase Dec A x ≠ (b,0) := by
      intro he
      have hz := congrArg Prod.snd he
      exact (erase_zero_iff Dec A x).mp hz hb
    simp [hb,hn]
  · simp [hb]

/-- Average bad-pair mass is exactly the error probability used by the platform. -/
lemma average_badMass (Dec : DecoderFn 3) (n m : ℕ) :
    (∑ A : Instance n m, badMass Dec A)/((3:ℝ)^(n*m)*(3:ℝ)^n*(2:ℝ)^m) = avgError Dec n m := by
  unfold badMass avgError bad
  rw [Finset.card_eq_sum_ones,Nat.cast_sum]
  simp only [Finset.sum_filter,Nat.cast_one]
  rw [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : Dec n m A (lweSample A x.1 x.2) ≠ x.1 <;> simp [h]

lemma collision_term_bound {n m : ℕ} (x y : Pair n m) :
    (∑ A : Instance n m,
      if x ≠ y ∧ noisyWord A x.1 x.2 = noisyWord A y.1 y.2 then (1:ℝ) else 0)/
      (3:ℝ)^(n*m)  ≤  1/(3:ℝ)^m := by
  by_cases hst : x.1 = y.1
  · have hz : ∀ A : Instance n m, ¬(x ≠ y ∧ noisyWord A x.1 x.2 = noisyWord A y.1 y.2) := by
      intro A ⟨hne,he⟩
      apply hne
      apply Prod.ext hst
      rw [hst] at he
      exact noisy_same_secret A y.1 x.2 y.2 he
    simp [hz]
  · have hc := noisy_probability x.1 y.1 hst x.2 y.2
    have hne : x ≠ y := fun h => hst (congrArg Prod.fst h)
    rw [Finset.card_eq_sum_ones,Nat.cast_sum] at hc
    simp only [Nat.cast_one,Finset.sum_filter] at hc
    have he : (∑ A : Instance n m, if x ≠ y ∧ noisyWord A x.1 x.2 = noisyWord A y.1 y.2 then (1:ℝ) else 0) =
        ∑ A : Instance n m, if noisyWord A x.1 x.2 = noisyWord A y.1 y.2 then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      by_cases h : noisyWord A x.1 x.2 = noisyWord A y.1 y.2 <;> simp [hne,h]
    rw [he]
    exact le_of_eq hc

lemma average_collisions (n m : ℕ) :
    (∑ A : Instance n m, collisions A)/(3:ℝ)^(n*m)  ≤ 
      ((3:ℝ)^n*(2:ℝ)^m)^2/(3:ℝ)^m := by
  unfold collisions
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Instance n m)))]
  rw [Finset.sum_div]
  have hsum : (∑ x : Pair n m, (∑ y : Pair n m, ∑ A : Instance n m,
      if x ≠ y ∧ noisyWord A x.1 x.2 = noisyWord A y.1 y.2 then (1:ℝ) else 0)/(3:ℝ)^(n*m))  ≤ 
      ∑ x : Pair n m, ∑ y : Pair n m, 1/(3:ℝ)^m := by
    apply Finset.sum_le_sum
    intro x hx
    rw [Finset.sum_div]
    exact Finset.sum_le_sum (fun y _ => collision_term_bound x y)
  apply hsum.trans
  have hc : (Fintype.card (Pair n m) : ℝ) = (3:ℝ)^n*(2:ℝ)^m := by
    simp [Pair,Secret,Errors,Fintype.card_fun,ZMod.card]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hc]
  ring_nf
  exact le_rfl

end F3Reduction

-- Source: Solutions.T31.ReductionState

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

noncomputable def liftZero {n m : ℕ} (v : Word m → ℂ) : Word m × Secret n → ℂ :=
  fun p => if p.2 = 0 then v p.1 else 0

noncomputable def rawIdeal {n m : ℕ} (A : Instance n m) : Word m → ℂ :=
  push (fun x : Pair n m => noisyWord A x.1 x.2) (fun x => sign x.2)

noncomputable def rawState {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) : Word m × Secret n → ℂ :=
  push (afterErase Dec A) (fun x => sign x.2)

lemma erase_zero_pair {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (x : Pair n m) (b : Word m) :
    afterErase Dec A x = (b,0) ↔ noisyWord A x.1 x.2 = b ∧ ¬bad Dec A x := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h,(erase_zero_iff Dec A x).mp (congrArg Prod.snd h)⟩
  · rintro ⟨hw,hgood⟩
    apply Prod.ext hw
    exact (erase_zero_iff Dec A x).mpr hgood

lemma state_zero_slice {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (b : Word m) :
    rawState Dec A (b,0) = rawIdeal A b-rawMissing Dec A b := by
  unfold rawState rawIdeal rawMissing push matApply
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [erase_zero_pair]
  by_cases hb : bad Dec A x <;> by_cases hw : noisyWord A x.1 x.2 = b <;> simp [hb,hw]

lemma state_nonzero_slice {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) (b : Word m) (r : Secret n)
    (hr : r ≠ 0) : rawState Dec A (b,r) = rawError Dec A (b,r) := by
  unfold rawState rawError push matApply
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb : bad Dec A x
  · simp [hb]
  · have hn : afterErase Dec A x ≠ (b,r) := by
      intro he
      have hz := (erase_zero_iff Dec A x).mpr hb
      have he' := congrArg Prod.snd he
      exact hr (he'.symm.trans hz)
    simp [hb,hn]

lemma state_decomposition {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    rawState Dec A = liftZero (rawIdeal A-rawMissing Dec A)+rawError Dec A := by
  funext p
  obtain ⟨b,r⟩ := p
  by_cases hr : r = 0
  · subst r
    simp only [Pi.add_apply,liftZero,ite_true,Pi.sub_apply,rawError_zero_slice,add_zero]
    exact state_zero_slice Dec A b
  · simp only [Pi.add_apply,liftZero,if_neg hr,zero_add]
    exact state_nonzero_slice Dec A b r hr

lemma energy_liftZero {n m : ℕ} (v : Word m → ℂ) : energy (@liftZero n m v) = energy v := by
  simp only [energy,liftZero,Fintype.sum_prod_type]
  simp_rw [apply_ite Complex.normSq]
  simp

lemma energy_disjoint {ι : Type} [Fintype ι] (u v : ι → ℂ) (h : ∀ i, u i = 0 ∨ v i = 0) :
    energy (u+v) = energy u+energy v := by
  unfold energy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases h i with hu | hv
  · simp [hu]
  · simp [hv]

noncomputable def rawCombinedError {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    Word m × Secret n → ℂ := liftZero (-rawMissing Dec A)+rawError Dec A

lemma combined_error_energy {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    energy (rawCombinedError Dec A) = energy (rawMissing Dec A)+badMass Dec A := by
  unfold rawCombinedError
  rw [energy_disjoint]
  · rw [energy_liftZero,error_energy]
    congr 1
    simp [energy]
  · intro p
    obtain ⟨b,r⟩ := p
    by_cases hr : r = 0
    · subst r
      exact Or.inr (rawError_zero_slice Dec A b)
    · exact Or.inl (by simp [liftZero,hr])

lemma combined_error_bound {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    energy (rawCombinedError Dec A)  ≤  2*badMass Dec A+collisions A := by
  rw [combined_error_energy]
  have := missing_energy Dec A
  linarith

lemma rawState_energy {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    energy (rawState Dec A) = (3:ℝ)^n*(2:ℝ)^m := by
  rw [rawState,push_energy_injective _ (erase_injective Dec A)]
  have hc : energy (fun x : Pair n m => sign x.2) = (Fintype.card (Pair n m) : ℝ) := by
    unfold energy
    have hs (x : Pair n m) : Complex.normSq (sign x.2) = 1 := by
      rcases sign_pm x.2 with h | h <;> simp [h]
    simp only [hs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [hc]
  simp [Pair,Secret,Errors,Fintype.card_fun,ZMod.card]

end F3Reduction

-- Source: Solutions.T31.Normalized

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

noncomputable def pairCount (n m : ℕ) : ℝ := (3:ℝ)^n*(2:ℝ)^m
noncomputable def normalizer (n m : ℕ) : ℂ := 1/(Real.sqrt (pairCount n m) : ℂ)

lemma pairCount_pos (n m : ℕ) : 0 < pairCount n m := by unfold pairCount; positivity

lemma normalizer_normSq (n m : ℕ) : Complex.normSq (normalizer n m) = 1/pairCount n m := by
  simp only [normalizer,Complex.normSq_div,Complex.normSq_one,Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (le_of_lt (pairCount_pos n m))]

noncomputable def state {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) : Word m × Secret n → ℂ :=
  normalizer n m • rawState Dec A
noncomputable def ideal {n m : ℕ} (A : Instance n m) : Word m × Secret n → ℂ :=
  normalizer n m • liftZero (rawIdeal A)
noncomputable def err {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) : Word m × Secret n → ℂ :=
  normalizer n m • rawCombinedError Dec A

lemma normalized_decomposition {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    state Dec A = ideal A+err Dec A := by
  unfold state ideal err rawCombinedError
  rw [state_decomposition]
  funext p
  obtain ⟨b,r⟩ := p
  by_cases hr : r = 0 <;> simp [liftZero,hr,smul_eq_mul,mul_add,mul_sub]
  ring

lemma state_energy {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) : energy (state Dec A) = 1 := by
  rw [state,energy_smul,normalizer_normSq,rawState_energy]
  exact one_div_mul_cancel (ne_of_gt (pairCount_pos n m))

lemma err_energy_bound {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    energy (err Dec A)  ≤  (2*badMass Dec A+collisions A)/pairCount n m := by
  rw [err,energy_smul,normalizer_normSq]
  have h := Nat.zero_le 0
  have hb := combined_error_bound Dec A
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using
    mul_le_mul_of_nonneg_left hb (le_of_lt (one_div_pos.mpr (pairCount_pos n m)))

/-- The statistical part of the reduction, assuming the final isometry sends the ideal
component entirely to valid outputs. -/
lemma reduction_for_isometry {n m : ℕ} {κ : Type} [Fintype κ]
    (Dec : DecoderFn 3) (A : Instance n m)
    (T : (Word m × Secret n → ℂ) → (κ → ℂ))
    (hadd : ∀ u v, T (u+v) = T u+T v)
    (hiso : ∀ u, energy (T u) = energy u)
    (P : κ → Prop) (hsupport : ∀ i, ¬P i → T (ideal A) i = 0) :
    1-(2*badMass Dec A+collisions A)/pairCount n m  ≤  mass P (T (state Dec A)) := by
  have hs := success_of_ideal T hadd hiso P (ideal A) (err Dec A) hsupport
    (by rw [← normalized_decomposition,state_energy])
  rw [← normalized_decomposition] at hs
  have hb := err_energy_bound Dec A
  linarith

lemma average_error_bound (Dec : DecoderFn 3) (n m : ℕ) :
    (∑ A : Instance n m, (2*badMass Dec A+collisions A)/pairCount n m)/(3:ℝ)^(n*m)  ≤ 
      2*avgError Dec n m+(3:ℝ)^n*(2/3:ℝ)^m := by
  have hb := average_badMass Dec n m
  have hc := average_collisions n m
  have hN := pairCount_pos n m
  have hA : 0 < (3:ℝ)^(n*m) := by positivity
  have hP : 0 < (3:ℝ)^m := by positivity
  rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
  have he : (2*(∑ A : Instance n m, badMass Dec A)+∑ A : Instance n m, collisions A)/
      pairCount n m/(3:ℝ)^(n*m) =
      2*avgError Dec n m+((∑ A : Instance n m, collisions A)/(3:ℝ)^(n*m))/pairCount n m := by
    rw [← hb]
    unfold pairCount
    field_simp <;> ring
  rw [he]
  apply add_le_add_right
  have hc' := div_le_div_of_nonneg_right hc (le_of_lt hN)
  have he' : ((3:ℝ)^n*(2:ℝ)^m)^2/(3:ℝ)^m/pairCount n m = (3:ℝ)^n*(2/3:ℝ)^m := by
    rw [div_pow]
    unfold pairCount
    field_simp <;> ring
  simpa only [he'] using hc'

end F3Reduction

-- Source: Solutions.T31.IdealSupport

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum Matrix
open Classical

lemma sign_product {m : ℕ} (e : Errors m) :
    (∏ i, if e i then (-1:ℂ) else 1) = sign e := by
  rw [Finset.prod_ite]
  simp [sign]

lemma scaledNot_bool (a b : ZMod 3) : scaledNot a b =
    ∑ e : Bool, if b = a+(if e then (-1:ZMod 3) else 1) then (if e then (-1:ℂ) else 1) else 0 := by
  rcases cases_three a with rfl | rfl | rfl <;> rcases cases_three b with rfl | rfl | rfl
  all_goals simp [scaledNot,Fintype.sum_bool]

lemma scaledNot_product (m : ℕ) (v b : Word m) :
    (∏ i, scaledNot (v i) (b i)) =
      ∑ e : Errors m, if v+delta e = b then sign e else 0 := by
  simp_rw [scaledNot_bool]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hv : v+delta e = b
  · rw [if_pos hv,← sign_product]
    apply Finset.prod_congr rfl
    intro i hi
    have hw := congrFun hv i
    dsimp only [Pi.add_apply,delta] at hw
    rw [if_pos hw.symm]
  · rw [if_neg hv]
    obtain ⟨i,hi⟩ : ∃ i, b i ≠ v i+delta e i := by
      by_contra h
      apply hv
      funext i
      exact (not_not.mp (not_exists.mp h i)).symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    dsimp only [delta] at hi
    rw [if_neg hi]

lemma rawIdeal_tensor {n m : ℕ} (A : Instance n m) (b : Word m) :
    rawIdeal A b = ∑ s : Secret n, ∏ i, scaledNot ((Aᵀ *ᵥ s) i) (b i) := by
  unfold rawIdeal push matApply
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s hs
  rw [scaledNot_product]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hw : noisyWord A s e = b <;> simp [noisyWord] at hw ⊢ <;> simp [hw]

lemma matApply_sum {ι κ α : Type} [Fintype ι] (M : κ → ι → ℂ) (s : Finset α)
    (v : α → ι → ℂ) (a : κ) :
    matApply M (fun i => ∑ x ∈ s, v x i) a = ∑ x ∈ s, matApply M (v x) a := by
  simp only [matApply,Finset.mul_sum]
  rw [Finset.sum_comm]

noncomputable def signedValid {n m : ℕ} (A : Instance n m) (c : Word m) : Prop :=
  (∀ i, c i ≠ 0) ∧ A *ᵥ c = 0

lemma transformed_ideal {n m : ℕ} (A : Instance n m) (c : Word m) :
    matApply (tensorMatrix (fun _ : Fin m => uMat.conjTranspose)) (rawIdeal A) c =
      ∑ s : Secret n, ∏ i, scaledTrine ((Aᵀ *ᵥ s) i) (c i) := by
  have he : rawIdeal A = fun b => ∑ s : Secret n, ∏ i, scaledNot ((Aᵀ *ᵥ s) i) (b i) :=
    funext (rawIdeal_tensor A)
  rw [he,matApply_sum]
  simp only [tensor_uInv]

lemma ideal_signed_support {n m : ℕ} (A : Instance n m) (c : Word m) (hc : ¬signedValid A c) :
    matApply (tensorMatrix (fun _ : Fin m => uMat.conjTranspose)) (rawIdeal A) c = 0 := by
  rw [transformed_ideal]
  by_cases hz : ∀ i, c i ≠ 0
  · have hA : A *ᵥ c ≠ 0 := fun he => hc ⟨hz,he⟩
    have hs (s : Secret n) : (∏ i, scaledTrine ((Aᵀ *ᵥ s) i) (c i)) = phase (dot3 s (A *ᵥ c)) := by
      simp only [scaledTrine,if_neg (hz _)]
      rw [← phase_finset_sum,matrix_character_identity]
    simp only [hs]
    rw [character_sum,if_neg hA]
  · obtain ⟨i,hi⟩ : ∃ i, c i = 0 := by simpa only [not_forall,not_not] using hz
    apply Finset.sum_eq_zero
    intro s hs
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [scaledTrine,hi]

end F3Reduction

-- Source: Solutions.T31.QuantumBound

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

noncomputable abbrev wordInverse (m : ℕ) := tensorMatrix (fun _ : Fin m => uMat.conjTranspose)
noncomputable def pairTransform {n m : ℕ} (ψ : Word m × Secret n → ℂ) : Word m × Secret n → ℂ :=
  fun p => matApply (wordInverse m) (fun b => ψ (b,p.2)) p.1

lemma pairTransform_add {n m : ℕ} (u v : Word m × Secret n → ℂ) :
    pairTransform (u+v) = pairTransform u+pairTransform v := by
  funext p
  exact congrFun (matApply_add (wordInverse m) (fun b => u (b,p.2)) (fun b => v (b,p.2))) p.1

lemma pairTransform_energy {n m : ℕ} (ψ : Word m × Secret n → ℂ) :
    energy (pairTransform ψ) = energy ψ := by
  simp only [energy,Fintype.sum_prod_type]
  rw [Finset.sum_comm,Finset.sum_comm (f := fun b r => Complex.normSq (ψ (b,r)))]
  apply Finset.sum_congr rfl
  intro r hr
  change energy (matApply (wordInverse m) (fun b => ψ (b,r))) = energy (fun b => ψ (b,r))
  apply matApply_isometry (wordInverse m)
  intro a b
  have h := tensor_orthogonal (fun _ : Fin m => uMat.conjTranspose)
    (fun _ => adjoint_orthogonal uMat u_orthogonal) a b
  by_cases hab : a = b <;> simpa only [if_pos, if_neg, hab] using h

lemma pairTransform_ideal_support {n m : ℕ} (A : Instance n m) (p : Word m × Secret n)
    (hp : ¬signedValid A p.1) : pairTransform (ideal A) p = 0 := by
  obtain ⟨c,r⟩ := p
  change matApply (wordInverse m) (fun b => ideal A (b,r)) c = 0
  unfold ideal liftZero
  simp only [Pi.smul_apply,smul_eq_mul]
  by_cases hr : r = 0
  · simp only [if_pos hr]
    rw [matApply_mul]
    have hs := ideal_signed_support A c hp
    change matApply (wordInverse m) (rawIdeal A) c = 0 at hs
    rw [hs,mul_zero]
  · simp [hr,matApply]

noncomputable def signedSuccess (Dec : DecoderFn 3) (n m : ℕ) : ℝ :=
  (∑ A : Instance n m, mass (fun p : Word m × Secret n => signedValid A p.1)
    (pairTransform (state Dec A)))/(3:ℝ)^(n*m)

lemma fixed_signed_bound {n m : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    1-(2*badMass Dec A+collisions A)/pairCount n m  ≤ 
      mass (fun p : Word m × Secret n => signedValid A p.1) (pairTransform (state Dec A)) :=
  reduction_for_isometry Dec A pairTransform pairTransform_add pairTransform_energy _
    (pairTransform_ideal_support A)

lemma matrix_card (n m : ℕ) : (Fintype.card (Instance n m) : ℝ) = (3:ℝ)^(n*m) := by
  simp [Instance,Matrix,Fintype.card_fun,ZMod.card,← pow_mul,Nat.mul_comm]

/-- The full error bound of Theorem 3.1 for the explicit coherent erasure state and
its tensor U-inverse transform. Circuit realization is handled separately. -/
lemma quantum_error_bound (Dec : DecoderFn 3) (n m : ℕ) :
    1-2*avgError Dec n m-(3:ℝ)^n*(2/3:ℝ)^m  ≤  signedSuccess Dec n m := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Instance n m)))
    (fun A _ => fixed_signed_bound Dec A)
  have hdiv := div_le_div_of_nonneg_right hsum (by positivity : 0  ≤  (3:ℝ)^(n*m))
  have he : ((∑ A : Instance n m, (1-(2*badMass Dec A+collisions A)/pairCount n m))/(3:ℝ)^(n*m)) =
      1-(∑ A : Instance n m, (2*badMass Dec A+collisions A)/pairCount n m)/(3:ℝ)^(n*m) := by
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,matrix_card]
    rw [sub_div,div_self (by positivity)]
  rw [he] at hdiv
  have herr := average_error_bound Dec n m
  change _  ≤  signedSuccess Dec n m at hdiv
  linarith

end F3Reduction

-- Source: Solutions.T31.SubsetReduction

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum Matrix
open Classical

def shiftedColumns {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) : Fin m → Fin n → ZMod 3 :=
  Function.update h a (h a-∑ i ∈ Finset.univ.erase a, h i)

def unshiftedColumns {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) : Fin m → Fin n → ZMod 3 :=
  Function.update h a (h a+∑ i ∈ Finset.univ.erase a, h i)

lemma otherColumns_shift {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) :
    (∑ i ∈ Finset.univ.erase a, shiftedColumns a h i) = ∑ i ∈ Finset.univ.erase a, h i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _

lemma otherColumns_unshift {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) :
    (∑ i ∈ Finset.univ.erase a, unshiftedColumns a h i) = ∑ i ∈ Finset.univ.erase a, h i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact Function.update_of_ne (Finset.mem_erase.mp hi).1 _ _

lemma columns_unshift_shift {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) :
    unshiftedColumns a (shiftedColumns a h) = h := by
  funext i
  by_cases hi : i = a
  · subst i
    simp only [unshiftedColumns,Function.update_self,otherColumns_shift]
    simp [shiftedColumns]
  · simp [unshiftedColumns,shiftedColumns,hi]

lemma columns_shift_unshift {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) :
    shiftedColumns a (unshiftedColumns a h) = h := by
  funext i
  by_cases hi : i = a
  · subst i
    simp only [shiftedColumns,Function.update_self,otherColumns_unshift]
    simp [unshiftedColumns]
  · simp [unshiftedColumns,shiftedColumns,hi]

def columnEquiv (n m : ℕ) (a : Fin m) :
    (Fin m → Fin n → ZMod 3) ≃ (Fin m → Fin n → ZMod 3) where
  toFun := shiftedColumns a
  invFun := unshiftedColumns a
  left_inv := columns_unshift_shift a
  right_inv := columns_shift_unshift a

def relativeSigns {m : ℕ} (a : Fin m) (c : Word m) : Word m :=
  fun i => if i = a then 1 else c i*c a-1

lemma nonzero_square (a : ZMod 3) (ha : a ≠ 0) : a*a = 1 := by
  rcases cases_three a with rfl | rfl | rfl
  · exact (ha rfl).elim
  · rfl
  · exact zmul_2_2

lemma relativeSigns_binary {m : ℕ} (a : Fin m) (c : Word m) (hc : ∀ i, c i ≠ 0) (i : Fin m) :
    relativeSigns a c i = 0 ∨ relativeSigns a c i = 1 := by
  by_cases hi : i = a
  · exact Or.inr (by simp [relativeSigns,hi])
  · have hci := hc i
    have hca := hc a
    rcases cases_three (c i) with he | he | he <;>
      rcases cases_three (c a) with hf | hf | hf <;>
      simp_all [relativeSigns]

lemma relativeSigns_sum {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) (c : Word m)
    (hc : c a ≠ 0) (j : Fin n) :
    ∑ i, h i j*relativeSigns a c i = c a*∑ i, shiftedColumns a h i j*c i := by
  have hs : c a*c a = 1 := nonzero_square _ hc
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),
    ← Finset.sum_erase_add (Finset.univ : Finset (Fin m)) (fun i => shiftedColumns a h i j*c i)
      (Finset.mem_univ a)]
  have he : (∑ i ∈ Finset.univ.erase a, h i j*relativeSigns a c i) =
      (∑ i ∈ Finset.univ.erase a, h i j*c i)*c a-∑ i ∈ Finset.univ.erase a, h i j := by
    rw [Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [relativeSigns,if_neg (Finset.mem_erase.mp hi).1]
    ring
  have ht : (∑ i ∈ Finset.univ.erase a, shiftedColumns a h i j*c i) =
      ∑ i ∈ Finset.univ.erase a, h i j*c i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [shiftedColumns,Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [he,ht]
  simp only [relativeSigns,ite_true,mul_one,shiftedColumns,Function.update_self,Pi.sub_apply,Finset.sum_apply]
  linear_combination ((∑ i ∈ Finset.univ.erase a, h i j)-h a j)*hs

lemma relativeSigns_solution {n m : ℕ} (a : Fin m) (h : Fin m → Fin n → ZMod 3) (c : Word m)
    (hc : signedValid (fun j i => shiftedColumns a h i j) c) :
    IsZeroSubsetSum h (Finset.univ.filter (fun i => relativeSigns a c i ≠ 0)) := by
  constructor
  · exact ⟨a,by simp [relativeSigns]⟩
  · funext j
    have hz := congrFun hc.2 j
    change (∑ i, shiftedColumns a h i j*c i) = 0 at hz
    have he := relativeSigns_sum a h c (hc.1 a) j
    rw [hz,mul_zero] at he
    simp only [Finset.sum_apply,Pi.zero_apply]
    rw [Finset.sum_filter]
    have hs : (∑ i, if relativeSigns a c i ≠ 0 then h i j else 0) =
        ∑ i, h i j*relativeSigns a c i := by
      apply Finset.sum_congr rfl
      intro i hi
      rcases relativeSigns_binary a c hc.1 i with hh | hh <;> simp [hh]
    exact hs.trans he

end F3Reduction

-- Source: Solutions.T31.RegisterFrame

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

lemma decoderBasis_word {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (hW : n*m+m  ≤  W) (i : Fin m) :
    decoderBasis n m W A b r ⟨n*m+i.val,by have := i.isLt; omega⟩ = b i := by
  have hi := i.isLt
  simp only [decoderBasis]
  split_ifs with hA hb hr
  · omega
  · congr 1; apply Fin.ext; change n*m+i.val-n*m = i.val; omega
  · omega
  · omega

lemma decoderBasis_secret {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (hW : n*m+m+n  ≤  W) (i : Fin n) :
    decoderBasis n m W A b r ⟨n*m+m+i.val,by have := i.isLt; omega⟩ = r i := by
  have hi := i.isLt
  simp only [decoderBasis]
  split_ifs with hA hb hr
  · omega
  · omega
  · congr 1; apply Fin.ext; change n*m+m+i.val-(n*m+m) = i.val; omega
  · omega

lemma decoderBasis_injective {n m W : ℕ} (A : Instance n m) (hW : n*m+m+n  ≤  W) :
    Function.Injective (fun p : Word m × Secret n => decoderBasis n m W A p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · funext i
    have h := congrFun h ⟨n*m+i.val,by have := i.isLt; omega⟩
    dsimp only at h
    have hw : n*m+m  ≤  W := by omega
    rw [decoderBasis_word A p.1 p.2 hw i,decoderBasis_word A q.1 q.2 hw i] at h
    exact h
  · funext i
    have h := congrFun h ⟨n*m+m+i.val,by have := i.isLt; omega⟩
    dsimp only at h
    rw [decoderBasis_secret A p.1 p.2 hW i,decoderBasis_secret A q.1 q.2 hW i] at h
    exact h

lemma decoderBasis_initial {n m W : ℕ} (A : Instance n m) :
    decoderBasis n m W A 0 0 = inputBasis n m W (fun i j => A j i) := by
  funext w
  simp only [decoderBasis]
  split_ifs with hA hb hr
  · rfl
  all_goals simp [inputBasis,hA]

lemma decoderBasis_block_word {n m W : ℕ} (A : Instance n m) (b v : Word m) (r : Secret n) :
    blockPlace (decoderBasis n m W A b r) (n*m) m v = decoderBasis n m W A v r := by
  funext w
  simp only [blockPlace,decoderBasis]
  split_ifs <;> first | rfl | omega

lemma decoderBasis_block_secret {n m W : ℕ} (A : Instance n m) (b : Word m) (r s : Secret n) :
    blockPlace (decoderBasis n m W A b r) (n*m+m) n s = decoderBasis n m W A b s := by
  funext w
  simp only [blockPlace,decoderBasis]
  split_ifs <;> first | rfl | omega

lemma range_word_basis {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (hW : n*m+m  ≤  W) (M : Matrix (ZMod 3) (ZMod 3) ℂ) :
    rangeApply M (n*m) m hW (basisKet (decoderBasis n m W A b r)) =
      ∑ v : Word m, (∏ i, M (v i) (b i)) • basisKet (decoderBasis n m W A v r) := by
  rw [rangeApply_basis]
  simp_rw [decoderBasis_word A b r hW,decoderBasis_block_word]

lemma range_secret_basis {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (hW : n*m+m+n  ≤  W) (M : Matrix (ZMod 3) (ZMod 3) ℂ) :
    rangeApply M (n*m+m) n hW (basisKet (decoderBasis n m W A b r)) =
      ∑ s : Secret n, (∏ i, M (s i) (r i)) • basisKet (decoderBasis n m W A b s) := by
  rw [rangeApply_basis]
  simp_rw [decoderBasis_secret A b r hW,decoderBasis_block_secret]

noncomputable def frame {n m W : ℕ} (A : Instance n m) (ψ : Word m × Secret n → ℂ) : Ket W :=
  push (fun p => decoderBasis n m W A p.1 p.2) ψ

lemma frame_expand {n m W : ℕ} (A : Instance n m) (ψ : Word m × Secret n → ℂ) :
    (frame A ψ : Ket W) = ∑ p, ψ p • basisKet (decoderBasis n m W A p.1 p.2) := by
  funext y
  simp only [frame,push,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,basisKet]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hh : y = decoderBasis n m W A p.1 p.2 <;> simp [hh,eq_comm]

lemma frame_energy {n m W : ℕ} (A : Instance n m) (ψ : Word m × Secret n → ℂ)
    (hW : n*m+m+n  ≤  W) : energy (frame A ψ : Ket W) = energy ψ :=
  push_energy_injective _ (decoderBasis_injective A hW) ψ

end F3Reduction

-- Source: Solutions.T31.Registers

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum

/-- The decoder layout as an unbounded register store, with an all-zero tail. -/
def decoderRegisters {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) : ℕ → ZMod 3 :=
  fun w => if hA : w < n*m then F3Search.registers (fun i j => A j i) w
    else if hb : w < n*m+m then b ⟨w-n*m,by omega⟩
    else if hr : w < n*m+m+n then r ⟨w-(n*m+m),by omega⟩ else 0

lemma decoderRegisters_basis {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) :
    decoderBasis n m W A b r = fun i => decoderRegisters A b r i.val := by
  funext i
  simp only [decoderBasis,decoderRegisters,inputBasis,F3Search.registers]

lemma decoderRegisters_matrix {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (i : Fin m) (j : Fin n) : decoderRegisters A b r (n*i.val+j.val) = A j i := by
  have hn : n*i.val+j.val < n*m := by nlinarith [i.isLt,j.isLt]
  rw [decoderRegisters,dif_pos hn]
  exact F3Search.registers_entry (fun i j => A j i) i j

lemma decoderRegisters_word {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) (i : Fin m) :
    decoderRegisters A b r (n*m+i.val) = b i := by
  have hi := i.isLt
  simp only [decoderRegisters]
  split_ifs
  · omega
  · congr 1; apply Fin.ext; change n*m+i.val-n*m = i.val; omega
  · omega
  · omega

lemma decoderRegisters_secret {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) (i : Fin n) :
    decoderRegisters A b r (n*m+m+i.val) = r i := by
  have hi := i.isLt
  simp only [decoderRegisters]
  split_ifs
  · omega
  · omega
  · congr 1; apply Fin.ext; change n*m+m+i.val-(n*m+m) = i.val; omega
  · omega

lemma decoderRegisters_zero {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) (i : ℕ)
    (hi : n*m+m+n  ≤  i) : decoderRegisters A b r i = 0 := by
  simp only [decoderRegisters,dif_neg (by omega : ¬i < n*m),dif_neg (by omega : ¬i < n*m+m),
    dif_neg (by omega : ¬i < n*m+m+n)]

end F3Reduction

-- Source: Solutions.T31.FiniteArithmetic

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum F3Tools
open Classical

def finiteStore {W : ℕ} (y : QBasis W) : ℕ → ZMod 3 :=
  fun i => if hi : i < W then y ⟨i,hi⟩ else 0

lemma finiteStore_restrict {W : ℕ} (y : QBasis W) : (fun i : Fin W => finiteStore y i.val) = y := by
  funext i
  simp [finiteStore]

lemma restrict_natUpdate {W : ℕ} (y : ℕ → ZMod 3) (j : Fin W) (v : ZMod 3) :
    (fun i : Fin W => Function.update y j.val v i.val) =
      Function.update (fun i : Fin W => y i.val) j v := by
  funext i
  simp [Function.update_apply,Fin.ext_iff]

lemma rawCircuit_readonly {W : ℕ} (gs : List Raw) (hv : ∀ g ∈ gs, Valid W g) (j : Fin W)
    (h : ∀ g ∈ gs, NoTouch j.val g) (z : QBasis W) (v : ZMod 3) :
    (rawCircuit W gs).forward (Function.update z j v) =
      Function.update ((rawCircuit W gs).forward z) j v := by
  let y := finiteStore z
  have hy : (fun i : Fin W => y i.val) = z := finiteStore_restrict z
  have h₀ := rawCircuit_forward W gs hv y
  rw [hy] at h₀
  have h₁ := rawCircuit_forward W gs hv (Function.update y j.val v)
  rw [restrict_natUpdate,hy,rawRun_update j.val gs h y v,restrict_natUpdate,← h₀] at h₁
  exact h₁

lemma rawCircuit_target_preserved {W : ℕ} (gs : List Raw) (hv : ∀ g ∈ gs, Valid W g) (j : Fin W)
    (h : ∀ g ∈ gs, NoTouch j.val g) (z : QBasis W) :
    (rawCircuit W gs).forward z j = z j := by
  have h₀ := rawCircuit_forward W gs hv (finiteStore z)
  rw [finiteStore_restrict] at h₀
  rw [h₀]
  have hh := rawRun_preserve gs (finiteStore z) j.val (fun g hg => Ne.symm (h g hg).1)
  simpa [finiteStore] using hh

noncomputable abbrev cleanRaw (W : ℕ) (gs : List Raw) (source target : ℕ) : Circuit :=
  ⟨W,(rawCircuit W gs).gates++(rawRev W (2,source,0,target)).gates++
    (inverseCircuit (reversibleCircuit (rawCircuit W gs))).gates⟩

lemma cleanRaw_basis {W : ℕ} (gs : List Raw) (hv : ∀ g ∈ gs, Valid W g)
    (k j : Fin W) (hkj : k ≠ j) (h : ∀ g ∈ gs, NoTouch j.val g) (z : QBasis W) :
    (cleanRaw W gs k.val j.val).run (basisKet z) =
      basisKet (Function.update z j (z j-(rawCircuit W gs).forward z k)) := by
  have hc : (rawRev W (2,k.val,0,j.val)).gates = [.csumInv k j hkj] := by
    simp only [rawRev,dif_pos j.isLt,show ¬(2:ℕ) = 0 by decide,if_false]
    have hn : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    rw [dif_pos ⟨k.isLt,hn⟩]
    simp only [show ¬(2:ℕ) = 1 by decide,if_false,ite_true]
    rfl
  have hb := bennett_basis (rawCircuit W gs) k j hkj
    (backward_readonly _ j (rawCircuit_readonly gs hv j h)) z
    (rawCircuit_target_preserved gs hv j h z)
  unfold Circuit.run at hb ⊢
  dsimp only [cleanRaw,bennettCircuit] at hb ⊢
  rw [hc]
  exact hb

end F3Reduction

-- Source: Solutions.T31.CoherentOracle

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction Turing
open Classical

lemma answer_untouched (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) (k : Fin n) :
    Untouched (n*m+m+k.val) (answerSimulation M τ n m T j) :=
  consumeClock_untouched τ (capacity_ge_two M n m T) _ _
    (decoderSimulation_untouched M n m T _ (by omega) (by dsimp [reserve]; have := k.isLt; omega)) j

lemma answer_bounded (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) (j : Fin n) :
    (answerExpression M τ n m T j.val).Bounded (answerSimulation M τ n m T j.val).pointer :=
  inputs_bounded _ _ (parsedTrit_inputs _ τ (capacity_ge_two M n m T) _
    (answer_untouched M τ n m T j.val j).bounded)

noncomputable def computation (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) : CompileState :=
  let S := answerSimulation M τ n m T j
  let Q := one S.pointer (answerExpression M τ n m T j)
  ((S.gates++Q.1.1,Q.1.2),[result S.pointer (answerExpression M τ n m T j)])

noncomputable def answerWire (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) : ℕ :=
  result (answerSimulation M τ n m T j).pointer (answerExpression M τ n m T j)

lemma computation_shape (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) (j k : Fin n) :
    n*m+m+k.val < answerWire M τ n m T j.val ∧
      answerWire M τ n m T j.val < (computation M τ n m T j.val).1.2 := by
  have hq := one_shape _ _ (answer_bounded M τ n m T j)
  have hs := answer_untouched M τ n m T j.val k
  exact ⟨lt_trans hs.below hq.1,hq.2⟩

lemma computation_noTouch (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) (j k : Fin n) :
    ∀ g ∈ (computation M τ n m T j.val).1.1, NoTouch (n*m+m+k.val) g := by
  have hs := answer_untouched M τ n m T j.val k
  intro g hg
  rcases List.mem_append.mp hg with hpre|hpost
  · exact hs.gates g hpre
  · exact one_noTouch _ _ _ hs.below
      (inputs_code _ _ (parsedTrit_inputs _ τ (capacity_ge_two M n m T) _ hs.registers)) g hpost

lemma computation_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod 3)) (b : Fin m → ZMod 3) (r s : Fin n → ZMod 3)
    (hrun : TM2OutputsInTime M.tm (encodeInstance A (fun i => b i-1))
      (some ((encodeSecret s).map τ)) T) (j : Fin n) :
    (∀ g ∈ (computation M τ n m T j.val).1.1, Valid (computation M τ n m T j.val).1.2 g) ∧
      rawRun (computation M τ n m T j.val).1.1 (decoderRegisters A b r)
        (answerWire M τ n m T j.val) = s j := by
  have ha := answer_spec M τ n m T A b s (decoderRegisters A b r)
    (fun i hi => decoderRegisters_zero A b r i (by dsimp [reserve] at hi; omega))
    (decoderRegisters_matrix A b r) (decoderRegisters_word A b r) hrun j
  have hb := answer_bounded M τ n m T j
  have hq := one_inv (answerSimulation M τ n m T j.val).pointer
    (answerExpression M τ n m T j.val) hb
    (rawRun (answerSimulation M τ n m T j.val).gates (decoderRegisters A b r)) ha.1.2.1
  constructor
  · intro g hg
    rcases List.mem_append.mp hg with hpre|hpost
    · exact (ha.1.1 g hpre).mono (le_trans (by omega :
        (answerSimulation M τ n m T j.val).pointer  ≤  (answerSimulation M τ n m T j.val).pointer+1) hq.1.growing)
    · exact hq.2.1 g hpost
  · change rawRun ((answerSimulation M τ n m T j.val).gates++
        (one (answerSimulation M τ n m T j.val).pointer (answerExpression M τ n m T j.val)).1.1)
        (decoderRegisters A b r) _ = _
    rw [rawRun_append]
    exact (one_value _ _ hb _ ha.1.2.1).trans ha.2

end F3MachineCompiler

-- Source: Solutions.T31.CleanDecoder

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

lemma decoderBasis_update_secret {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (hW : n*m+m+n  ≤  W) (j : Fin n) (v : ZMod 3) :
    Function.update (decoderBasis n m W A b r) ⟨n*m+m+j.val,by have := j.isLt; omega⟩ v =
      decoderBasis n m W A b (Function.update r j v) := by
  funext w
  simp only [decoderBasis,Function.update_apply,Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma fold_subtract {α : Type} [DecidableEq α] (is : List α) (hn : is.Nodup)
    (r s : α → ZMod 3) (i : α) :
    is.foldl (fun r j => Function.update r j (r j-s j)) r i =
      if i ∈ is then r i-s i else r i := by
  induction is generalizing r with
  | nil => simp
  | cons a is ih =>
    have hnot := (List.nodup_cons.mp hn).1
    have htail := (List.nodup_cons.mp hn).2
    rw [List.foldl_cons,ih htail]
    by_cases hi : i = a
    · subst i
      simp [hnot]
    · simp [Function.update_of_ne hi,hi]

end F3Reduction

namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction Turing
open Classical

noncomputable def oracleWidth (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) : ℕ :=
  reserve n m+∑ j : Fin n, (computation M τ n m T j.val).1.2

lemma oracleWidth_reserve (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) :
    reserve n m  ≤  oracleWidth M τ n m T := Nat.le_add_right _ _
lemma oracleWidth_computation (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) (j : Fin n) :
    (computation M τ n m T j.val).1.2  ≤  oracleWidth M τ n m T := by
  have h := Finset.single_le_sum (f := fun j : Fin n => (computation M τ n m T j.val).1.2)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  dsimp only [oracleWidth]
  omega

noncomputable abbrev coordinateOracle (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) : Circuit :=
  cleanRaw (oracleWidth M τ n m T) (computation M τ n m T j).1.1
    (answerWire M τ n m T j) (n*m+m+j)

noncomputable abbrev decoderCircuit (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) : Circuit :=
  ⟨oracleWidth M τ n m T,(List.finRange n).flatMap (fun j => (coordinateOracle M τ n m T j.val).gates)⟩

lemma coordinateOracle_basis (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ)
    (A : Matrix (Fin n) (Fin m) (ZMod 3)) (b : Fin m → ZMod 3) (r s : Fin n → ZMod 3)
    (hrun : TM2OutputsInTime M.tm (encodeInstance A (fun i => b i-1))
      (some ((encodeSecret s).map τ)) T) (j : Fin n) :
    (coordinateOracle M τ n m T j.val).run
      (basisKet (decoderBasis n m (oracleWidth M τ n m T) A b r)) =
      basisKet (decoderBasis n m (oracleWidth M τ n m T) A b (Function.update r j (r j-s j))) := by
  let W := oracleWidth M τ n m T
  have hs := computation_shape M τ n m T j j
  have hc := computation_correct M τ n m T A b r s hrun j
  have hle := oracleWidth_computation M τ n m T j
  have hw := oracleWidth_reserve M τ n m T
  have hW : n*m+m+n  ≤  W := by dsimp [W]; dsimp [reserve] at hw; omega
  let k : Fin W := ⟨answerWire M τ n m T j.val,lt_of_lt_of_le hs.2 hle⟩
  let t : Fin W := ⟨n*m+m+j.val,by have := j.isLt; omega⟩
  have hkt : k ≠ t := by intro he; have he := congrArg Fin.val he; dsimp [k,t] at he; omega
  have hv : ∀ g ∈ (computation M τ n m T j.val).1.1, Valid W g :=
    fun g hg => (hc.1 g hg).mono hle
  have hb := cleanRaw_basis (computation M τ n m T j.val).1.1 hv k t hkt
    (computation_noTouch M τ n m T j j) (decoderBasis n m W A b r)
  have hvalue : (rawCircuit W (computation M τ n m T j.val).1.1).forward
      (decoderBasis n m W A b r) k = s j := by
    rw [decoderRegisters_basis,rawCircuit_forward W _ hv (decoderRegisters A b r)]
    exact hc.2
  rw [hvalue,decoderBasis_secret A b r hW j,decoderBasis_update_secret A b r hW j] at hb
  exact hb

lemma decoderCircuit_clean (M : BinaryMachine) (τ : Bool ≃ Bool) (Dec : DecoderFn 3) (n m T : ℕ)
    (h : ∀ A b, Nonempty (TM2OutputsInTime M.tm (encodeInstance A b)
      (some ((encodeSecret (Dec n m A b)).map τ)) T)) :
    CleanDecoder Dec n m (decoderCircuit M τ n m T) := by
  have hw := oracleWidth_reserve M τ n m T
  refine ⟨by dsimp [decoderCircuit]; dsimp [reserve] at hw; omega,?_⟩
  intro A b r
  obtain ⟨hrun⟩ := h A (fun i => b i-1)
  let s := Dec n m A (fun i => b i-1)
  have hlist : ∀ is : List (Fin n), ∀ r : Fin n → ZMod 3,
      (is.flatMap (fun j => (coordinateOracle M τ n m T j.val).gates)).foldl
        (fun φ g => applyGate g φ) (basisKet (decoderBasis n m (oracleWidth M τ n m T) A b r)) =
        basisKet (decoderBasis n m (oracleWidth M τ n m T) A b
          (is.foldl (fun r j => Function.update r j (r j-s j)) r)) := by
    intro is
    induction is with
    | nil => intro r; rfl
    | cons j is ih =>
      intro r
      rw [List.flatMap_cons,List.foldl_append]
      have hj := coordinateOracle_basis M τ n m T A b r s hrun j
      unfold Circuit.run at hj
      rw [hj,ih]
      rfl
  have hall := hlist (List.finRange n) r
  have hfinal : (List.finRange n).foldl (fun r j => Function.update r j (r j-s j)) r = r-s := by
    funext i
    rw [fold_subtract _ (List.nodup_finRange n)]
    simp
  rw [hfinal] at hall
  exact hall

end F3MachineCompiler

-- Source: Solutions.T31.FamilyMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

theorem Poly.map_fixed {α β γ : Type} [Coding α] [Coding γ] (xs : List β) (f : α → β → γ)
    (hf : ∀ b ∈ xs, Poly (fun a => f a b)) : Poly (fun a => xs.map (f a)) := by
  induction xs with
  | nil => exact OAI.MetricKMedian.Binary.Automatic.Poly.const []
  | cons b bs ih =>
    have ht := ih (fun c hc => hf c (by simp [hc]))
    have hh := hf b (by simp)
    exact L3.Poly.list_cons_comp hh ht

lemma select_family_poly {α β : Type} [Coding α] [Fintype β] (v : α → β → Expr)
    (f : β → ZMod 3) (h : ∀ b, Poly (fun a => v a b)) : Poly (fun a => select (v a) f) := by
  apply exprSum_comp
  apply Poly.map_fixed
  intro b hb
  apply exprTimes_comp (h b) (OAI.MetricKMedian.Binary.Automatic.Poly.const (literal (f b)))

lemma blend_family_poly {α β : Type} [Coding α] [Fintype β] (v f : α → β → Expr)
    (hv : ∀ b, Poly (fun a => v a b)) (hf : ∀ b, Poly (fun a => f a b)) :
    Poly (fun a => blend (v a) (f a)) := by
  apply exprSum_comp
  apply Poly.map_fixed
  intro b hb
  exact exprTimes_comp (hv b) (hf b)

def readStack {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (k : M.K) (i : ℕ) : Expr :=
  if hi : i < N then S.stack k ⟨i,hi⟩ else .zero

structure FamilyPoly {α : Type} [Coding α] (M : BinaryMachine) (N : α → ℕ)
    (S : (a : α) → Symbolic M (N a)) : Prop where
  label : ∀ l, Poly (fun a => (S a).label l)
  state : ∀ s, Poly (fun a => (S a).state s)
  stack : ∀ k, Poly (fun x : α × ℕ => readStack (S x.1) k x.2)

lemma FamilyPoly.read {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S)
    (k : M.K) {i : α → ℕ} (hi : Poly i) : Poly (fun a => readStack (S a) k (i a)) :=
  Poly.comp (h.stack k) (Poly.pair Poly.identity hi)

lemma FamilyPoly.stateTable {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (f : M.State → ZMod 3) :
    Poly (fun a => F3MachineCompiler.stateTable (S a) f) := select_family_poly _ f h.state

lemma FamilyPoly.headTable {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (hN : ∀ a, 0 < N a)
    (k : M.K) (f : M.State → Option Bool → ZMod 3) :
    Poly (fun a => headTable (S a) k (hN a) f) := by
  apply select_family_poly
  intro p
  apply exprTimes_comp (h.state p.1)
  apply exprIsZero_comp
  apply exprPlus_comp
  · have hh := h.read k (OAI.MetricKMedian.Binary.Automatic.Poly.const 0)
    simpa only [readStack,dif_pos (hN _)] using hh
  · exact OAI.MetricKMedian.Binary.Automatic.Poly.const (Expr.minus (literal (symbol p.2)))

lemma readStack_symLoad {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (f : M.State → M.State) (k : M.K) (i : ℕ) :
    readStack (symLoad S f) k i = readStack S k i := by
  unfold readStack
  split_ifs <;> rfl

lemma FamilyPoly.symLoad {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (f : M.State → M.State) :
    FamilyPoly M N (fun a => symLoad (S a) f) := by
  refine ⟨h.label,fun s => h.stateTable _,?_⟩
  intro k
  simpa only [readStack_symLoad] using h.stack k

lemma readStack_symRead {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (k j : M.K)
    (hN : 0 < N) (f : M.State → Option Bool → M.State) (i : ℕ) :
    readStack (symRead S k hN f) j i = readStack S j i := by
  unfold readStack
  split_ifs <;> rfl

lemma FamilyPoly.symRead {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (hN : ∀ a, 0 < N a)
    (k : M.K) (f : M.State → Option Bool → M.State) :
    FamilyPoly M N (fun a => symRead (S a) k (hN a) f) := by
  refine ⟨h.label,fun s => h.headTable hN k (fun a b => if f a b = s then 1 else 0),?_⟩
  intro j
  simpa only [readStack_symRead] using h.stack j

end F3MachineCompiler

namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

lemma readStack_symPush {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (k j : M.K) (f : M.State → Bool) (i : ℕ) :
    readStack (symPush S k f) j i = if i < N then
      (if j = k then if i = 0 then F3MachineCompiler.stateTable S (fun a => symbol (some (f a)))
        else readStack S j (i-1) else readStack S j i) else .zero := by
  unfold readStack symPush
  dsimp only
  split_ifs <;> first | rfl | omega

lemma FamilyPoly.symPush {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (hN : Poly N)
    (k : M.K) (f : M.State → Bool) : FamilyPoly M N (fun a => symPush (S a) k f) := by
  refine ⟨h.label,h.state,?_⟩
  intro j
  have hbound : Poly (fun x : α × ℕ => N x.1) := Poly.comp hN Poly.fst
  have hstate : Poly (fun x : α × ℕ => F3MachineCompiler.stateTable (S x.1) (fun a => symbol (some (f a)))) :=
    Poly.comp (f := fun a : α => F3MachineCompiler.stateTable (S a) (fun s => symbol (some (f s))))
      (g := fun x : α × ℕ => x.1) (h.stateTable (fun s => symbol (some (f s)))) Poly.fst
  have hstack := h.stack j
  have hprev : Poly (fun x : α × ℕ => readStack (S x.1) j (x.2-1)) :=
    Poly.comp (h.stack j) (g := fun x : α × ℕ => (x.1,x.2-1)) (by fun_prop)
  have hr : Poly (fun x : α × ℕ => if x.2 < N x.1 then
      (if j = k then if x.2 = 0 then F3MachineCompiler.stateTable (S x.1) (fun a => symbol (some (f a)))
        else readStack (S x.1) j (x.2-1) else readStack (S x.1) j x.2) else Expr.zero) := by
    by_cases hj : j = k
    · subst j
      simp only [ite_true]
      fun_prop
    · simp only [if_neg hj]
      fun_prop
  simpa only [readStack_symPush] using hr

lemma readStack_symDrop {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (k j : M.K) (i : ℕ) :
    readStack (symDrop S k) j i = if i < N then
      (if j = k then readStack S j (i+1) else readStack S j i) else .zero := by
  unfold readStack symDrop
  dsimp only
  split_ifs <;> first | rfl | omega

lemma FamilyPoly.symDrop {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (hN : Poly N)
    (k : M.K) : FamilyPoly M N (fun a => symDrop (S a) k) := by
  refine ⟨h.label,h.state,?_⟩
  intro j
  have hbound : Poly (fun x : α × ℕ => N x.1) := Poly.comp hN Poly.fst
  have hstack := h.stack j
  have hnext : Poly (fun x : α × ℕ => readStack (S x.1) j (x.2+1)) :=
    Poly.comp (h.stack j) (g := fun x : α × ℕ => (x.1,x.2+1)) (by fun_prop)
  have hr : Poly (fun x : α × ℕ => if x.2 < N x.1 then
      (if j = k then readStack (S x.1) j (x.2+1) else readStack (S x.1) j x.2) else Expr.zero) := by
    by_cases hj : j = k
    · subst j
      simp only [ite_true]
      fun_prop
    · simp only [if_neg hj]
      fun_prop
  simpa only [readStack_symDrop] using hr

lemma readStack_symGoto {M : BinaryMachine} {N : ℕ} (S : Symbolic M N)
    (f : M.State → M.Label) (k : M.K) (i : ℕ) :
    readStack (symGoto S f) k i = readStack S k i := by
  unfold readStack
  split_ifs <;> rfl
lemma readStack_symHalt {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (k : M.K) (i : ℕ) :
    readStack (symHalt S) k i = readStack S k i := by
  unfold readStack
  split_ifs <;> rfl

lemma FamilyPoly.symGoto {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) (f : M.State → M.Label) :
    FamilyPoly M N (fun a => symGoto (S a) f) := by
  refine ⟨fun l => h.stateTable _,h.state,?_⟩
  intro k
  simpa only [readStack_symGoto] using h.stack k
lemma FamilyPoly.symHalt {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S : (a : α) → Symbolic M (N a)} (h : FamilyPoly M N S) :
    FamilyPoly M N (fun a => symHalt (S a)) := by
  refine ⟨fun l => OAI.MetricKMedian.Binary.Automatic.Poly.const (literal (if l = none then 1 else 0)),h.state,?_⟩
  intro k
  simpa only [readStack_symHalt] using h.stack k

lemma readStack_symChoose {M : BinaryMachine} {N : ℕ} (S T : Symbolic M N) (e : Expr)
    (k : M.K) (i : ℕ) : readStack (symChoose e S T) k i =
      if i < N then e.choose (readStack S k i) (readStack T k i) else .zero := by
  unfold readStack symChoose
  dsimp only
  split_ifs <;> rfl

lemma FamilyPoly.symChoose {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    {S T : (a : α) → Symbolic M (N a)} (hS : FamilyPoly M N S) (hT : FamilyPoly M N T)
    (hN : Poly N) (e : α → Expr) (he : Poly e) :
    FamilyPoly M N (fun a => symChoose (e a) (S a) (T a)) := by
  refine ⟨fun l => exprChoose_comp he (hS.label l) (hT.label l),
    fun s => exprChoose_comp he (hS.state s) (hT.state s),?_⟩
  intro k
  have hbound : Poly (fun x : α × ℕ => N x.1) := Poly.comp hN Poly.fst
  have he' := Poly.comp he (Poly.fst (β := ℕ))
  have hs := hS.stack k
  have ht := hT.stack k
  have hr : Poly (fun x : α × ℕ => if x.2 < N x.1 then
      (e x.1).choose (readStack (S x.1) k x.2) (readStack (T x.1) k x.2) else Expr.zero) := by fun_prop
  simpa only [readStack_symChoose] using hr

end F3MachineCompiler

namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

lemma readStack_combine {M : BinaryMachine} {N : ℕ} {β : Type} [Fintype β]
    (v : β → Expr) (S : β → Symbolic M N) (k : M.K) (i : ℕ) :
    readStack (combine v S) k i =
      if i < N then blend v (fun b => readStack (S b) k i) else .zero := by
  unfold readStack combine
  dsimp only
  split_ifs <;> rfl

lemma family_combine {α β : Type} [Coding α] [Fintype β] {M : BinaryMachine} {N : α → ℕ}
    (S : β → (a : α) → Symbolic M (N a)) (v : α → β → Expr)
    (hN : Poly N) (hS : ∀ b, FamilyPoly M N (S b)) (hv : ∀ b, Poly (fun a => v a b)) :
    FamilyPoly M N (fun a => combine (v a) (fun b => S b a)) := by
  refine ⟨fun l => blend_family_poly _ _ hv (fun b => (hS b).label l),
    fun s => blend_family_poly _ _ hv (fun b => (hS b).state s),?_⟩
  intro k
  have hbound : Poly (fun x : α × ℕ => N x.1) := Poly.comp hN Poly.fst
  have hblend : Poly (fun x : α × ℕ => blend (v x.1) (fun b => readStack (S b x.1) k x.2)) :=
    blend_family_poly _ _ (fun b => Poly.comp (hv b) Poly.fst) (fun b => (hS b).stack k)
  have hr : Poly (fun x : α × ℕ => if x.2 < N x.1 then
      blend (v x.1) (fun b => readStack (S b x.1) k x.2) else Expr.zero) := by fun_prop
  simpa only [readStack_combine] using hr

lemma family_symbolicAux {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (hN : Poly N) (hpos : ∀ a, 0 < N a) (q : Statement M)
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) :
    FamilyPoly M N (fun a => symbolicAux (hpos a) q (S a)) := by
  induction q generalizing S with
  | push k f q ih => exact ih _ (hS.symPush hN k f)
  | peek k f q ih => exact ih _ (hS.symRead hpos k f)
  | pop k f q ih => exact ih _ ((hS.symRead hpos k f).symDrop hN k)
  | load f q ih => exact ih _ (hS.symLoad f)
  | branch f q r ihq ihr =>
    exact FamilyPoly.symChoose (ihq S hS) (ihr S hS) hN
      (fun a => stateTable (S a) (fun s => if f s then 1 else 0)) (hS.stateTable _)
  | goto f => exact hS.symGoto f
  | halt => exact hS.symHalt

lemma family_symbolicStep {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (hN : Poly N) (hpos : ∀ a, 0 < N a) (S : (a : α) → Symbolic M (N a))
    (hS : FamilyPoly M N S) : FamilyPoly M N (fun a => symbolicStep (hpos a) (S a)) := by
  apply family_combine (fun l a => match l with
    | none => S a
    | some l => symbolicAux (hpos a) (M.code l) (S a)) (fun a => (S a).label) hN _ hS.label
  intro l
  cases l with
  | none => exact hS
  | some l => exact family_symbolicAux hN hpos (M.code l) S hS

lemma family_initial {α : Type} [Coding α] (M : BinaryMachine) (N : α → ℕ) :
    FamilyPoly M N (fun a => initialSymbolic M (N a)) := by
  refine ⟨fun l => OAI.MetricKMedian.Binary.Automatic.Poly.const (literal (if l = some M.main then 1 else 0)),
    fun s => OAI.MetricKMedian.Binary.Automatic.Poly.const (literal (if s = M.initial then 1 else 0)),?_⟩
  intro k
  have he : (fun x : α × ℕ => readStack (initialSymbolic M (N x.1)) k x.2) = fun _ => Expr.zero := by
    funext x
    unfold readStack
    split_ifs <;> rfl
  rw [he]
  exact OAI.MetricKMedian.Binary.Automatic.Poly.const Expr.zero

end F3MachineCompiler

-- Source: Solutions.T31.CoordinateMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

lemma coordinates_label (M : BinaryMachine) (N : ℕ) (l : Option M.Label) :
    (coordinates M N (.inl l)).val = (Fintype.equivFin (Option M.Label) l).val := rfl
lemma coordinates_state (M : BinaryMachine) (N : ℕ) (s : M.State) :
    (coordinates M N (.inr (.inl s))).val = Fintype.card (Option M.Label)+(Fintype.equivFin M.State s).val := rfl
lemma coordinates_stack (M : BinaryMachine) (N : ℕ) (k : M.K) (i : Fin N) :
    (coordinates M N (.inr (.inr (k,i)))).val =
      Fintype.card (Option M.Label)+(Fintype.card M.State+(i.val+N*(Fintype.equivFin M.K k).val)) := rfl

lemma expressionList_blocks {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) :
    expressionList S =
      List.ofFn (fun l : Fin (Fintype.card (Option M.Label)) => S.label ((Fintype.equivFin _).symm l)) ++
      (List.ofFn (fun s : Fin (Fintype.card M.State) => S.state ((Fintype.equivFin _).symm s)) ++
      (List.ofFn (fun k : Fin (Fintype.card M.K) => List.ofFn
        (fun i : Fin N => S.stack ((Fintype.equivFin _).symm k) i))).flatten) := by
  unfold expressionList
  change List.ofFn (n := Fintype.card (Option M.Label)+(Fintype.card M.State+Fintype.card M.K*N)) _ = _
  rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    change S.get ((coordinates M N).symm _) = S.get (.inl ((Fintype.equivFin _).symm i))
    apply congrArg S.get
    apply (coordinates M N).symm_apply_eq.mpr
    apply Fin.ext
    rw [coordinates_label]
    simp
  · rw [List.ofFn_add]
    congr 1
    · apply congrArg List.ofFn
      funext i
      change S.get ((coordinates M N).symm _) = S.get (.inr (.inl ((Fintype.equivFin _).symm i)))
      apply congrArg S.get
      apply (coordinates M N).symm_apply_eq.mpr
      apply Fin.ext
      rw [coordinates_state]
      simp
    · rw [List.ofFn_mul]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext k
      apply congrArg List.ofFn
      funext i
      change S.get ((coordinates M N).symm _) = S.get (.inr (.inr ((Fintype.equivFin _).symm k,i)))
      apply congrArg S.get
      apply (coordinates M N).symm_apply_eq.mpr
      apply Fin.ext
      rw [coordinates_stack]
      simp [Nat.mul_comm,Nat.add_comm]

@[fun_prop] lemma Poly.flatten_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List (List β)} (hf : Poly f) : Poly (fun a => (f a).flatten) :=
  Poly.comp (Poly.of_program (PolyProgram.listFlatten (enc : β → List Bool) default)) hf

lemma family_expressionList {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S)
    (hrange : Poly (fun a => List.range (N a))) : Poly (fun a => expressionList (S a)) := by
  have hl : Poly (fun a => List.ofFn (fun l : Fin (Fintype.card (Option M.Label)) =>
      (S a).label ((Fintype.equivFin _).symm l))) := by
    have hh := Poly.map_fixed (List.finRange (Fintype.card (Option M.Label)))
      (fun a (l : Fin (Fintype.card (Option M.Label))) => (S a).label ((Fintype.equivFin _).symm l))
      (fun l _ => hS.label _)
    simpa only [← List.ofFn_eq_map] using hh
  have hs : Poly (fun a => List.ofFn (fun s : Fin (Fintype.card M.State) =>
      (S a).state ((Fintype.equivFin _).symm s))) := by
    have hh := Poly.map_fixed (List.finRange (Fintype.card M.State))
      (fun a (s : Fin (Fintype.card M.State)) => (S a).state ((Fintype.equivFin _).symm s))
      (fun s _ => hS.state _)
    simpa only [← List.ofFn_eq_map] using hh
  have hstack (k : M.K) : Poly (fun a => List.ofFn (fun i : Fin (N a) => (S a).stack k i)) := by
    have hh : Poly (fun a => (List.range (N a)).map (fun i => readStack (S a) k i)) :=
      Poly.list_map (hS.stack k) hrange
    have he : (fun a => (List.range (N a)).map (fun i => readStack (S a) k i)) =
        fun a => List.ofFn (fun i : Fin (N a) => (S a).stack k i) := by
      funext a
      apply List.ext_getElem
      · simp
      · intro i hi hj
        have hi' : i < N a := by simpa only [List.length_map,List.length_range] using hi
        simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
        simp only [readStack,dif_pos hi']
    rwa [he] at hh
  have hk : Poly (fun a => List.ofFn (fun k : Fin (Fintype.card M.K) => List.ofFn
      (fun i : Fin (N a) => (S a).stack ((Fintype.equivFin _).symm k) i))) := by
    have hh := Poly.map_fixed (List.finRange (Fintype.card M.K))
      (fun a (k : Fin (Fintype.card M.K)) => List.ofFn
        (fun i : Fin (N a) => (S a).stack ((Fintype.equivFin _).symm k) i))
      (fun k _ => hstack _)
    simpa only [← List.ofFn_eq_map] using hh
  simp_rw [expressionList_blocks]
  fun_prop

end F3MachineCompiler

-- Source: Solutions.T31.WireFamily

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

noncomputable def wireSymbolic (M : BinaryMachine) (N : ℕ) (as : List ℕ) : Symbolic M N :=
  Symbolic.of (fun i => Expr.input (as.getD (coordinates M N i).val 0))

lemma readStack_wire (M : BinaryMachine) (N : ℕ) (as : List ℕ) (k : M.K) (i : ℕ) :
    readStack (wireSymbolic M N as) k i = if i < N then
      Expr.input (as.getD (Fintype.card (Option M.Label)+(Fintype.card M.State+
        (i+N*(Fintype.equivFin M.K k).val))) 0) else Expr.zero := by
  unfold readStack wireSymbolic Symbolic.of
  dsimp only
  split_ifs
  · rw [coordinates_stack]
  · rfl

lemma family_wires {α : Type} [Coding α] (M : BinaryMachine) (N : α → ℕ)
    (as : α → List ℕ) (hN : Poly N) (has : Poly as) :
    FamilyPoly M N (fun a => wireSymbolic M (N a) (as a)) := by
  refine ⟨?_,?_,?_⟩
  · intro l
    change Poly (fun a => Expr.input ((as a).getD (coordinates M (N a) (.inl l)).val 0))
    simp_rw [coordinates_label]
    fun_prop
  · intro s
    change Poly (fun a => Expr.input ((as a).getD (coordinates M (N a) (.inr (.inl s))).val 0))
    simp_rw [coordinates_state]
    fun_prop
  · intro k
    simp_rw [readStack_wire]
    have hN' := Poly.comp hN (Poly.fst (β := ℕ))
    have has' := Poly.comp has (Poly.fst (β := ℕ))
    fun_prop

lemma stored_wire {M : BinaryMachine} {N : ℕ} (p : ℕ) (S : Symbolic M N) :
    stored p S = wireSymbolic M N (store p S).2 := rfl

end F3MachineCompiler

-- Source: Solutions.T31.PhaseMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

lemma symbolicIf_label {M : BinaryMachine} {N : ℕ} (b : Bool) (S T : Symbolic M N) (l : Option M.Label) :
    (if b then S else T).label l = if b then S.label l else T.label l := by cases b <;> rfl
lemma symbolicIf_state {M : BinaryMachine} {N : ℕ} (b : Bool) (S T : Symbolic M N) (s : M.State) :
    (if b then S else T).state s = if b then S.state s else T.state s := by cases b <;> rfl
lemma symbolicIf_stack {M : BinaryMachine} {N : ℕ} (b : Bool) (S T : Symbolic M N) (k : M.K) (i : ℕ) :
    readStack (if b then S else T) k i = if b then readStack S k i else readStack T k i := by cases b <;> rfl

lemma family_if {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S T : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (hT : FamilyPoly M N T)
    (b : α → Bool) (hb : Poly b) : FamilyPoly M N (fun a => if b a then S a else T a) := by
  refine ⟨?_,?_,?_⟩
  · intro l
    simp_rw [symbolicIf_label]
    exact Poly.ite hb (hS.label l) (hT.label l)
  · intro s
    simp_rw [symbolicIf_state]
    exact Poly.ite hb (hS.state s) (hT.state s)
  · intro k
    simp_rw [symbolicIf_stack]
    exact Poly.ite (Poly.comp hb Poly.fst) (hS.stack k) (hT.stack k)

lemma family_fillTrit {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (hN : Poly N)
    (e : α → Expr) (he : Poly e) : FamilyPoly M N (fun a => fillTrit (e a) (S a)) := by
  have h₀ := hS.symPush hN M.input (fun _ => false)
  have h₁ := FamilyPoly.symChoose (h₀.symPush hN M.input (fun _ => true)) h₀ hN
    (fun a => Expr.plus Expr.one ((e a).isZero.minus)) (by fun_prop)
  have h₂ := FamilyPoly.symChoose (h₁.symPush hN M.input (fun _ => true)) h₁ hN
    (fun a => (Expr.plus (e a) (Expr.minus (literal 2))).isZero) (by fun_prop)
  exact h₂

lemma equalsTrue_family {α : Type} [Coding α] (τ : Bool ≃ Bool) (e : α → Expr) (he : Poly e) :
    Poly (fun a => equalsTrue τ (e a)) := by unfold equalsTrue; fun_prop

lemma family_headMask {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (τ : Bool ≃ Bool)
    (hN : ∀ a, 2  ≤  N a) : Poly (fun a => headMask τ (hN a) (S a)) := by
  have h0 : ∀ a, 0 < N a := by intro a; have := hN a; omega
  have hz : Poly (fun a => (S a).stack M.output ⟨0,h0 a⟩) := by
    simpa only [readStack,dif_pos (h0 _)] using hS.read M.output (OAI.MetricKMedian.Binary.Automatic.Poly.const 0)
  exact equalsTrue_family τ _ hz

lemma family_nextMask {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (τ : Bool ≃ Bool)
    (hN : ∀ a, 2  ≤  N a) : Poly (fun a => nextMask τ (hN a) (S a)) := by
  have h1 : ∀ a, 1 < N a := by intro a; have := hN a; omega
  have hz : Poly (fun a => (S a).stack M.output ⟨1,h1 a⟩) := by
    simpa only [readStack,dif_pos (h1 _)] using hS.read M.output (OAI.MetricKMedian.Binary.Automatic.Poly.const 1)
  exact equalsTrue_family τ _ hz

lemma family_twoMask {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (τ : Bool ≃ Bool)
    (hN : ∀ a, 2  ≤  N a) : Poly (fun a => twoMask τ (hN a) (S a)) :=
  exprTimes_comp (family_headMask S hS τ hN) (family_nextMask S hS τ hN)

lemma family_parsedTrit {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (τ : Bool ≃ Bool)
    (hN : ∀ a, 2  ≤  N a) : Poly (fun a => parsedTrit τ (hN a) (S a)) :=
  exprPlus_comp (family_headMask S hS τ hN) (family_twoMask S hS τ hN)

lemma family_consumeTrit {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (hNP : Poly N)
    (τ : Bool ≃ Bool) (hN : ∀ a, 2  ≤  N a) :
    FamilyPoly M N (fun a => consumeTrit τ (hN a) (S a)) := by
  have h₀ := hS.symDrop hNP M.output
  have h₁ := FamilyPoly.symChoose (h₀.symDrop hNP M.output) h₀ hNP
    (fun a => headMask τ (hN a) (S a)) (family_headMask S hS τ hN)
  have h₂ := FamilyPoly.symChoose (h₁.symDrop hNP M.output) h₁ hNP
    (fun a => twoMask τ (hN a) (S a)) (family_twoMask S hS τ hN)
  exact h₂

abbrev Phase := ℕ × ℕ

noncomputable def phaseTransform {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (p : Phase) (S : Symbolic M N) : Symbolic M N :=
  if p.1 == 0 then symPush S M.input (fun _ => false)
  else if p.1 == 1 then symPush S M.input (fun _ => true)
  else if p.1 == 2 then fillTrit (.input p.2) S
  else if p.1 == 3 then fillTrit (.plus (.input p.2) (.minus .one)) S
  else if p.1 == 4 then symbolicStep (by omega) S
  else consumeTrit τ hN S

lemma family_phaseTransform {α : Type} [Coding α] {M : BinaryMachine} {N : α → ℕ}
    (S : (a : α) → Symbolic M (N a)) (hS : FamilyPoly M N S) (hNP : Poly N)
    (τ : Bool ≃ Bool) (hN : ∀ a, 2  ≤  N a) (p : α → Phase) (hp : Poly p) :
    FamilyPoly M N (fun a => phaseTransform τ (hN a) (p a) (S a)) := by
  have hpos : ∀ a, 0 < N a := by intro a; have := hN a; omega
  have hcode : Poly (fun a => Expr.input (p a).2) := by fun_prop
  have hcode' : Poly (fun a => Expr.plus (Expr.input (p a).2) (Expr.minus Expr.one)) := by fun_prop
  have he := family_consumeTrit S hS hNP τ hN
  have ht := family_symbolicStep hNP hpos S hS
  have hw := family_fillTrit S hS hNP _ hcode'
  have ha := family_fillTrit S hS hNP _ hcode
  have hb₁ := hS.symPush hNP M.input (fun _ => true)
  have hb₀ := hS.symPush hNP M.input (fun _ => false)
  apply family_if _ _ hb₀
  · apply family_if _ _ hb₁
    · apply family_if _ _ ha
      · apply family_if _ _ hw
        · apply family_if _ _ ht he <;> fun_prop
        · fun_prop
      · fun_prop
    · fun_prop
  · fun_prop

end F3MachineCompiler

-- Source: Solutions.T31.PhaseBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

def fillIntermediate (M : BinaryMachine) :=
  2*15+tableFactor M*(tableFactor M*4+1)+tableFactor M*4+6

def fillSize (M : BinaryMachine) :=
  2*22+tableFactor M*(fillIntermediate M+1)+fillIntermediate M+6

def phaseSize (M : BinaryMachine) := fillSize M+tableFactor M*4+stepFactor M*4+300

lemma fillTrit_size {M : BinaryMachine} {N : ℕ} (S : Symbolic M N) (hS : Size S 3)
    (e : Expr) (he : e.code.length  ≤  4) : Size (fillTrit e S) (fillSize M) := by
  have h₀ := size_symPush S 3 hS M.input (fun _ => false)
  have hm₁ : (Expr.plus Expr.one e.isZero.minus).code.length  ≤  15 := by
    simp only [Expr.code,List.length_append,List.length_singleton,isZero_size]
    omega
  have hm₂ : (Expr.plus e (Expr.minus (literal 2))).isZero.code.length  ≤  22 := by
    have hl := literal_size (2 : ZMod 3)
    simp only [isZero_size,Expr.code,List.length_append,List.length_singleton]
    omega
  have h₁ := size_symChoose _ _ 15 (tableFactor M*(tableFactor M*4+1)) (tableFactor M*4)
    (size_symPush _ _ h₀ M.input (fun _ => true)) h₀ (.plus .one e.isZero.minus) hm₁
  have h₂ := size_symChoose _ _ 22 (tableFactor M*(fillIntermediate M+1)) (fillIntermediate M)
    (size_symPush _ _ h₁ M.input (fun _ => true)) h₁ (.isZero (.plus e (.minus (literal 2)))) hm₂
  exact h₂

lemma equalsTrue_size (τ : Bool ≃ Bool) (e : Expr) :
    (equalsTrue τ e).code.length  ≤  2*e.code.length+14 := by
  have hl := literal_size (symbol (some (τ true)))
  simp only [equalsTrue,isZero_size,Expr.code,List.length_append,List.length_singleton]
  omega

lemma headMask_size {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (hS : Size S 3) : (headMask τ hN S).code.length  ≤  20 := by
  have hh := equalsTrue_size τ (S.stack M.output ⟨0,by omega⟩)
  have hs := hS.2.2 M.output ⟨0,by omega⟩
  exact le_trans hh (by omega)

lemma nextMask_size {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (hS : Size S 3) : (nextMask τ hN S).code.length  ≤  20 := by
  have hh := equalsTrue_size τ (S.stack M.output ⟨1,by omega⟩)
  have hs := hS.2.2 M.output ⟨1,by omega⟩
  exact le_trans hh (by omega)

lemma twoMask_size {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (hS : Size S 3) : (twoMask τ hN S).code.length  ≤  41 := by
  have h₀ := headMask_size τ hN S hS
  have h₁ := nextMask_size τ hN S hS
  simp only [twoMask,Expr.code,List.length_append,List.length_singleton]
  omega

lemma parsedTrit_size {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (hS : Size S 3) : (parsedTrit τ hN S).code.length  ≤  62 := by
  have h₀ := headMask_size τ hN S hS
  have h₁ := twoMask_size τ hN S hS
  simp only [parsedTrit,Expr.code,List.length_append,List.length_singleton]
  omega

lemma consumeTrit_size {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Symbolic M N) (hS : Size S 3) : Size (consumeTrit τ hN S) 199 := by
  have h₀ := size_symDrop S 3 hS M.output
  have h₁ := size_symChoose _ _ 20 5 4 (size_symDrop _ 4 h₀ M.output) h₀
    (headMask τ hN S) (headMask_size τ hN S hS)
  have h₂ := size_symChoose _ _ 41 56 55 (size_symDrop _ 55 h₁ M.output) h₁
    (twoMask τ hN S) (twoMask_size τ hN S hS)
  exact h₂

lemma phaseTransform_size {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (p : Phase) (S : Symbolic M N) (hS : Size S 3) : Size (phaseTransform τ hN p S) (phaseSize M) := by
  unfold phaseTransform
  split_ifs
  · exact size_mono _ (size_symPush S 3 hS M.input (fun _ => false)) (by dsimp [phaseSize]; omega)
  · exact size_mono _ (size_symPush S 3 hS M.input (fun _ => true)) (by dsimp [phaseSize]; omega)
  · exact size_mono _ (fillTrit_size S hS (.input p.2) (by simp [Expr.code])) (by dsimp [phaseSize]; omega)
  · exact size_mono _ (fillTrit_size S hS (.plus (.input p.2) (.minus .one)) (by simp [Expr.code]))
      (by dsimp [phaseSize]; omega)
  · exact size_mono _ (symbolicStep_size (by omega) S 3 hS) (by dsimp [phaseSize]; omega)
  · exact size_mono _ (consumeTrit_size τ hN S hS) (by dsimp [phaseSize]; omega)

lemma phaseTransform_safe {M : BinaryMachine} {N : ℕ} (P : ℕ → Prop) (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (p : Phase) (S : Symbolic M N) (hS : Safe P S) (hp : P p.2) : Safe P (phaseTransform τ hN p S) := by
  unfold phaseTransform
  split_ifs
  · exact safe_symPush P S hS M.input (fun _ => false)
  · exact safe_symPush P S hS M.input (fun _ => true)
  · exact fillTrit_safe S P hS (.input p.2) hp
  · exact fillTrit_safe S P hS (.plus (.input p.2) (.minus .one)) ⟨hp,trivial⟩
  · exact safe_symbolicStep P (by omega) S hS
  · exact consumeTrit_safe P τ hN S hS

end F3MachineCompiler

-- Source: Solutions.T31.PhaseSchedule

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

noncomputable def phaseStep {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Simulation M N) (p : Phase) : Simulation M N := emit (phaseTransform τ hN p) S
noncomputable def phaseLoop {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (ps : List Phase) (S : Simulation M N) : Simulation M N := ps.foldl (phaseStep τ hN) S

def dataSchedule (n m : ℕ) : List Phase :=
  (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => (2,n*i.val+j.val))) ++
    (List.finRange m).map (fun i => (3,n*m+i.val))

def bitSchedule (bs : List Bool) : List Phase := bs.map (fun b => (if b then 1 else 0,0))

def dataExpression (p : Phase) : Expr := if p.1 == 2 then .input p.2 else .plus (.input p.2) (.minus .one)

lemma dataSchedule_tags (n m : ℕ) : ∀ p ∈ dataSchedule n m, p.1 = 2 ∨ p.1 = 3 := by
  intro p hp
  rcases List.mem_append.mp hp with hA|hb
  · obtain ⟨i,_,hA⟩ := List.mem_flatMap.mp hA
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hA
    exact Or.inl rfl
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    exact Or.inr rfl

lemma dataSchedule_expressions (n m : ℕ) : (dataSchedule n m).map dataExpression = inputExprs n m := by
  simp only [dataSchedule,inputExprs,List.map_append,List.map_flatMap,List.map_map]
  rfl

lemma phaseLoop_data {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (ps : List Phase) (hp : ∀ p ∈ ps, p.1 = 2 ∨ p.1 = 3) (S : Simulation M N) :
    phaseLoop τ hN ps.reverse S = prepare (ps.map dataExpression) S := by
  unfold phaseLoop
  rw [List.foldl_reverse]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldr_cons,List.map_cons,prepare,List.foldr_cons]
    have ht := ih (fun p hp' => hp p (by simp [hp']))
    change phaseStep τ hN _ p = _
    rw [ht]
    have hf : phaseTransform (M := M) τ hN p = fillTrit (M := M) (dataExpression p) := by
      funext R
      rcases hp p (by simp) with hh|hh <;> simp [phaseTransform,dataExpression,hh]
    unfold phaseStep
    rw [hf]
    rfl

lemma phaseLoop_bits {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (bs : List Bool) (S : Simulation M N) :
    phaseLoop τ hN (bitSchedule bs).reverse S = prepareBits bs S := by
  unfold phaseLoop bitSchedule
  rw [List.foldl_reverse,List.foldr_map]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldr_cons,prepareBits,List.foldr_cons]
    rw [ih]
    cases b <;> rfl

lemma phaseLoop_tm {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N) (t : ℕ)
    (S : Simulation M N) : phaseLoop τ hN (List.replicate t (4,0)) S =
      (simulateStep (by omega))^[t] S := by
  induction t generalizing S with
  | zero => rfl
  | succ t ih =>
    change phaseLoop τ hN (List.replicate t (4,0)) (phaseStep τ hN S (4,0)) = _
    rw [ih,Function.iterate_succ_apply]
    rfl

lemma phaseLoop_consume {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N) (t : ℕ)
    (S : Simulation M N) : phaseLoop τ hN (List.replicate t (5,0)) S =
      (consumeStep τ hN)^[t] S := by
  induction t generalizing S with
  | zero => rfl
  | succ t ih =>
    change phaseLoop τ hN (List.replicate t (5,0)) (phaseStep τ hN S (5,0)) = _
    rw [ih,Function.iterate_succ_apply]
    rfl

def decoderSchedule (n m T j : ℕ) : List Phase :=
  (dataSchedule n m).reverse++(bitSchedule (unaryD n++unaryD m)).reverse++
    List.replicate T (4,0)++List.replicate j (5,0)

lemma phaseLoop_append {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (ps qs : List Phase) (S : Simulation M N) :
    phaseLoop τ hN (ps++qs) S = phaseLoop τ hN qs (phaseLoop τ hN ps S) := List.foldl_append

lemma decoderSchedule_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) :
    phaseLoop τ (capacity_ge_two M n m T) (decoderSchedule n m T j)
      (initialSimulation M (capacity M n m T) (reserve n m)) = answerSimulation M τ n m T j := by
  simp only [decoderSchedule,phaseLoop_append,phaseLoop_data τ _ _ (dataSchedule_tags n m),
    dataSchedule_expressions,phaseLoop_bits,phaseLoop_tm,phaseLoop_consume]
  rfl

end F3MachineCompiler

-- Source: Solutions.L2.CompileMachine

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace F3Generate
open F3Tools F3Search OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

abbrev CState := (List Raw × ℕ) × List ℕ
abbrev CEnv := Env × List Token
abbrev LoopState := CEnv × (List Token × CState)

theorem replicate_mod (k : ℕ) {α : Type} (a : α) :
    List.replicate (k%3) a = [a,a].take (k%3) := by
  change List.replicate (k%3) a = (List.replicate 2 a).take (k%3)
  rw [List.take_replicate]
  congr 1
  omega

@[fun_prop] theorem decide_or_poly {α : Type} [Coding α] {p q : α → Prop}
    [DecidablePred p] [DecidablePred q] (hp : Poly (fun x => decide (p x)))
    (hq : Poly (fun x => decide (q x))) : Poly (fun x => decide (p x ∨ q x)) := by
  have he : (fun x => decide (p x ∨ q x)) = (fun x => decide (p x) || decide (q x)) := by
    funext x
    by_cases hp : p x <;> by_cases hq : q x <;> simp [hp,hq]
  rw [he]
  fun_prop

@[fun_prop] theorem headD_poly {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → List β} (d : β) (hf : Poly f) : Poly (fun x => (f x).headD d) := by
  have he : (fun x => (f x).headD d) = (fun x => (f x).getD 0 d) := by
    funext x
    cases f x <;> rfl
  rw [he]
  fun_prop

@[fun_prop] theorem tokenGates_poly : Poly (fun x : ((ℕ × ℕ) × List ℕ) × Token =>
    tokenGates x.1.1.1 x.1.1.2 x.1.2 x.2) := by
  unfold tokenGates source
  simp_rw [replicate_mod]
  fun_prop

@[fun_prop] theorem tokenGates_comp {α : Type} [Coding α] {I p : α → ℕ}
    {s : α → List ℕ} {t : α → Token} (hI : Poly I) (hp : Poly p) (hs : Poly s) (ht : Poly t) :
    Poly (fun x => tokenGates (I x) (p x) (s x) (t x)) :=
  Poly.comp tokenGates_poly (Poly.pair (Poly.pair (Poly.pair hI hp) hs) ht)

@[fun_prop] theorem compileStep_poly : Poly (fun x : (ℕ × CState) × Token =>
    compileStep x.1.1 x.1.2 x.2) := by
  unfold compileStep tokenStack
  fun_prop

@[fun_prop] theorem compileStep_comp {α : Type} [Coding α] {I : α → ℕ}
    {s : α → CState} {t : α → Token} (hI : Poly I) (hs : Poly s) (ht : Poly t) :
    Poly (fun x => compileStep (I x) (s x) (t x)) :=
  Poly.comp compileStep_poly (Poly.pair (Poly.pair hI hs) ht)

def compileBody (s : LoopState) : (CEnv × CState) ⊕ LoopState :=
  if s.2.1.isEmpty then .inl (s.1,s.2.2)
  else .inr (s.1,(s.2.1.tail,compileStep (L3.inputN s.1.1*L3.inputM s.1.1) s.2.2 (s.2.1.headD (0,0))))

noncomputable def compileProgram : PolyProgram enc (encodeLoop enc enc) compileBody := by
  have hp : Poly (fun s : LoopState => s.2.1.isEmpty) := by fun_prop
  have hd : Poly (fun s : LoopState => (s.1,s.2.2)) := by fun_prop
  have hc : Poly (fun s : LoopState => (s.1,(s.2.1.tail,
    compileStep (L3.inputN s.1.1*L3.inputM s.1.1) s.2.2 (s.2.1.headD (0,0))))) := by
    fun_prop
  exact (PolyProgram.ite hp.program
    (hc.program.comp (PolyProgram.injectRight enc enc))
    (hd.program.comp (PolyProgram.injectLeft enc enc))).congr _ (fun _ => rfl)

theorem nat_enc_bound (n M : ℕ) (h : n  ≤  M) : (enc n).length  ≤  M+1 := by
  rw [L3.enc_nat_length]
  apply Nat.size_le.mpr
  exact lt_of_le_of_lt (show n  ≤  M+1 by omega) (Nat.lt_two_pow_self (n := M+1))

def RawBound (M : ℕ) (g : Raw) := g.1  ≤  M ∧ g.2.1  ≤  M ∧ g.2.2.1  ≤  M ∧ g.2.2.2  ≤  M

theorem token_numbers (I p M : ℕ) (s : List ℕ) (t : Token) (hI : I < p)
    (hs : ∀ a ∈ s, a < p) (hp : p+2  ≤  M) (hM : 3  ≤  M) :
    ∀ g ∈ tokenGates I p s t, RawBound M g := by
  have h0 := source_lt I p s hI hs 0
  have h1 := source_lt I p s hI hs 1
  have hv : (if t.2 < I then t.2 else I) < p := by split_ifs <;> omega
  unfold tokenGates
  split_ifs
  · intro g hg
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hg
    dsimp [RawBound]; omega
  all_goals intro g hg; simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  all_goals rcases hg with rfl | rfl <;> dsimp [RawBound] <;> omega

theorem token_enc_bound (M : ℕ) (t : Token) (h : t.1  ≤  M ∧ t.2  ≤  M) :
    (enc t).length  ≤  4*(M+1) := by
  have h1 := nat_enc_bound t.1 M h.1
  have h2 := nat_enc_bound t.2 M h.2
  rw [L3.enc_pair_length]
  omega

theorem raw_enc_bound (M : ℕ) (g : Raw) (h : RawBound M g) : (enc g).length  ≤  10*(M+1) := by
  have h0 := nat_enc_bound g.1 M h.1
  have h1 := nat_enc_bound g.2.1 M h.2.1
  have h2 := nat_enc_bound g.2.2.1 M h.2.2.1
  have h3 := nat_enc_bound g.2.2.2 M h.2.2.2
  simp only [L3.enc_pair_length]
  omega

theorem loop_encoding (e : CEnv) (ts : List Token) (s : CState) (M L : ℕ)
    (ht : ∀ t ∈ ts, t.1  ≤  M ∧ t.2  ≤  M) (hlt : ts.length  ≤  L)
    (hg : ∀ g ∈ s.1.1, RawBound M g) (hlg : s.1.1.length  ≤  2*L)
    (hp : s.1.2  ≤  M) (hs : ∀ a ∈ s.2, a  ≤  M) (hls : s.2.length  ≤  L) :
    (enc (e,(ts,s))).length  ≤  10*(enc e).length+200*(M+1)*(L+1) := by
  have htlen := EncodedList.length_bound (enc : Token → List Bool) ts (4*(M+1))
    (fun t ht' => token_enc_bound M t (ht t ht'))
  have hglen := EncodedList.length_bound (enc : Raw → List Bool) s.1.1 (10*(M+1))
    (fun g hg' => raw_enc_bound M g (hg g hg'))
  have hslen := EncodedList.length_bound (enc : ℕ → List Bool) s.2 (M+1)
    (fun a ha => nat_enc_bound a M (hs a ha))
  have hplen := nat_enc_bound s.1.2 M hp
  have hT : (enc ts).length  ≤  L*(2*(4*(M+1))+1) := htlen.trans (Nat.mul_le_mul_right (2*(4*(M+1))+1) hlt)
  have hG : (enc s.1.1).length  ≤  2*L*(2*(10*(M+1))+1) := hglen.trans (Nat.mul_le_mul_right (2*(10*(M+1))+1) hlg)
  have hS : (enc s.2).length  ≤  L*(2*(M+1)+1) := hslen.trans (Nat.mul_le_mul_right (2*(M+1)+1) hls)
  simp only [L3.enc_pair_length]
  ring_nf at hT hG hS ⊢
  omega

theorem tokenStack_length (p : ℕ) (s : List ℕ) (t : Token) :
    (tokenStack p s t).length  ≤  s.length+1 := by
  unfold tokenStack
  split_ifs <;> simp <;> omega

theorem compile_run (e : CEnv) (ts : List Token) (s : CState) (M L : ℕ)
    (hM : 3  ≤  M) (hI : L3.inputN e.1*L3.inputM e.1 < s.1.2)
    (ht : ∀ t ∈ ts, t.1  ≤  M ∧ t.2  ≤  M)
    (hg : ∀ g ∈ s.1.1, RawBound M g)
    (hs : ∀ a ∈ s.2, a < s.1.2)
    (hp : s.1.2+2*ts.length  ≤  M)
    (hlg : s.1.1.length+2*ts.length  ≤  2*L)
    (hls : s.2.length+ts.length  ≤  L) :
    BoundedRun enc compileBody (10*(enc e).length+200*(M+1)*(L+1)) (ts.length+1)
      (e,(ts,s)) (e,ts.foldl (compileStep (L3.inputN e.1*L3.inputM e.1)) s) := by
  induction ts generalizing s with
  | nil =>
    apply BoundedRun.stop
    · exact loop_encoding e [] s M L ht (by simp) hg (by simpa using hlg)
        (by simpa using hp) (fun a ha => by have := hs a ha; simp at hp; omega) (by simpa using hls)
    · rfl
  | cons t ts ih =>
    have hsize := loop_encoding e (t::ts) s M L ht (by simp at hls; omega) hg
      (by omega) (by omega) (fun a ha => by have := hs a ha; omega) (by omega)
    let sn := compileStep (L3.inputN e.1*L3.inputM e.1) s t
    have hgl := tokenGates_length (L3.inputN e.1*L3.inputM e.1) s.1.2 s.2 t
    have hsl := tokenStack_length s.1.2 s.2 t
    have hnI : L3.inputN e.1*L3.inputM e.1 < sn.1.2 := by dsimp [sn,compileStep]; omega
    have hnt : ∀ t ∈ ts, t.1  ≤  M ∧ t.2  ≤  M := fun t ht' => ht t (by simp [ht'])
    have hng : ∀ g ∈ sn.1.1, RawBound M g := by
      intro g hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact hg g hold
      · exact token_numbers _ _ M _ t hI hs (by simp only [List.length_cons] at hp; omega) hM g hnew
    have hns : ∀ a ∈ sn.2, a < sn.1.2 := tokenStack_lt (L3.inputN e.1*L3.inputM e.1) _ _ t hs
    have hnp : sn.1.2+2*ts.length  ≤  M := by
      dsimp [sn,compileStep]
      simp only [List.length_cons] at hp
      omega
    have hnlg : sn.1.1.length+2*ts.length  ≤  2*L := by
      dsimp [sn,compileStep]
      rw [List.length_append]
      simp only [List.length_cons] at hlg
      omega
    have hnls : sn.2.length+ts.length  ≤  L := by
      change (tokenStack s.1.2 s.2 t).length+ts.length  ≤  L
      simp only [List.length_cons] at hls
      omega
    have hr := BoundedRun.step (ea := enc) (f := compileBody) (a := (e,(t::ts,s)))
      (a' := (e,(ts,sn))) hsize (by simp [compileBody,sn])
      (ih sn hnI hnt hng hns hnp hnlg hnls)
    exact hr

end F3Generate

-- Source: Solutions.T31.LoopMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

lemma Poly.from_bounded_loop {α σ β : Type} [Coding α] [Coding σ] [Coding β]
    (f : σ → β ⊕ σ) (P : PolyProgram enc (encodeLoop enc enc) f)
    (initial : α → σ) (out : α → β) (hinit : Poly initial) (N S : Polynomial ℕ)
    (hr : ∀ a, ∃ k s, k  ≤  N.eval (enc a).length ∧ s  ≤  S.eval (enc a).length ∧
      BoundedRun enc f s k (initial a) (out a)) : Poly out := by
  let I := hinit.program
  let Q := Loop.machine P.machine
  let R := N*(P.time.comp S+2*P.sizeBound.comp S+3)
  refine ⟨⟨Compose.machine I.machine Q,I.time+2*I.sizeBound+2+R,?_⟩⟩
  intro a
  apply Classical.choice
  obtain ⟨k,s,hk,hs,hloop⟩ := hr a
  obtain ⟨t,ht,tr⟩ := P.run_loop hloop
  have hmono : P.passTime s  ≤  P.passTime (S.eval (enc a).length) := by
    unfold PolyProgram.passTime
    exact Nat.add_le_add_right (Nat.add_le_add (polynomial_eval_mono _ hs)
      (Nat.mul_le_mul_left 2 (polynomial_eval_mono _ hs))) 3
  have hbound : t  ≤  R.eval (enc a).length := by
    have hb := ht.trans (Nat.mul_le_mul hk hmono)
    simpa [R,PolyProgram.passTime] using hb
  have hi := I.outputs a
  have htr := Compose.run I.machine Q (Trace.of_inTime hi) tr
  refine ⟨⟨⟨_,htr.iterate_eq⟩,?_⟩⟩
  have hsize := I.length_bound a
  have htime := hi.steps_le_m
  simp only [eval_add,eval_mul,eval_ofNat]
  change hi.steps+2*(enc (initial a)).length+2+t  ≤ 
    I.time.eval (enc a).length+2*I.sizeBound.eval (enc a).length+2+R.eval (enc a).length
  omega

end F3MachineCompiler

-- Source: Solutions.T31.SafeCompilerMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial
open Classical

abbrev CompilerEnv := F3Generate.CEnv

def compilerInputCount (w : List Bool) := L3.inputN w*L3.inputM w

def sanitizeCode (p : ℕ) (ts : List Token) := ts.map (fun t => (min t.1 4,min t.2 (p+4)))

def safeEnvironment (e : CompilerEnv) : CompilerEnv := (e.1,sanitizeCode (compilerInputCount e.1) e.2)

def compilerInitial (e : CompilerEnv) : F3Generate.LoopState :=
  let e' := safeEnvironment e
  (e',(e'.2,(([],compilerInputCount e.1+1),[])))

def compilerOutput (e : CompilerEnv) : CompilerEnv × CompileState :=
  (safeEnvironment e,compile (compilerInputCount e.1) (compilerInputCount e.1+1) (safeEnvironment e).2)

@[fun_prop] lemma compilerInputCount_poly : Poly compilerInputCount := by unfold compilerInputCount; fun_prop
@[fun_prop] lemma compilerInputCount_comp {α : Type} [Coding α] {w : α → List Bool} (hw : Poly w) :
    Poly (fun a => compilerInputCount (w a)) := Poly.comp compilerInputCount_poly hw
@[fun_prop] lemma sanitizeCode_poly : Poly (fun x : ℕ × List Token => sanitizeCode x.1 x.2) := by
  unfold sanitizeCode
  fun_prop
@[fun_prop] lemma safeEnvironment_poly : Poly safeEnvironment := by unfold safeEnvironment; fun_prop
@[fun_prop] lemma compilerInitial_poly : Poly compilerInitial := by unfold compilerInitial; fun_prop

lemma compilerInputCount_bound (w : List Bool) : compilerInputCount w  ≤  w.length^2 := by
  have hn : L3.inputN w  ≤  w.length := List.findIdx_le_length
  have hm : L3.inputM w  ≤  w.length := by unfold L3.inputM; omega
  simpa only [compilerInputCount,pow_two] using Nat.mul_le_mul hn hm

lemma sanitize_numbers (p : ℕ) (ts : List Token) :
    ∀ t ∈ sanitizeCode p ts, t.1  ≤  4 ∧ t.2  ≤  p+4 := by
  intro t ht
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨Nat.min_le_right _ _,Nat.min_le_right _ _⟩

lemma safeCompiler_run (e : CompilerEnv) :
    let p := compilerInputCount e.1
    let ts := (safeEnvironment e).2
    let L := ts.length
    let M := p+2*L+5
    BoundedRun enc F3Generate.compileBody (10*(enc (safeEnvironment e)).length+200*(M+1)*(L+1)) (L+1)
      (compilerInitial e) (compilerOutput e) := by
  dsimp only
  let p := compilerInputCount e.1
  let ts := (safeEnvironment e).2
  let L := ts.length
  let M := p+2*L+5
  have hnum : ∀ t ∈ ts, t.1  ≤  M ∧ t.2  ≤  M := by
    intro t ht
    have h := sanitize_numbers p e.2 t ht
    dsimp [M]
    omega
  have hr := F3Generate.compile_run (safeEnvironment e) ts (([],p+1),[]) M L
    (by dsimp [M]; omega) (by change p < p+1; omega) hnum (by simp) (by simp)
    (by change p+1+2*L  ≤  M; dsimp [M]; omega) (by change 0+2*L  ≤  2*L; omega)
    (by change 0+L  ≤  L; omega)
  exact hr

lemma safeCompiler_bounds (e : CompilerEnv) :
    let p := compilerInputCount e.1
    let L := (safeEnvironment e).2.length
    L+1  ≤  (X+1 : Polynomial ℕ).eval (enc e).length ∧
      10*(enc (safeEnvironment e)).length+200*(p+2*L+6)*(L+1)  ≤ 
        (100000*(X+1)^4 : Polynomial ℕ).eval (enc e).length := by
  dsimp only
  let a := (enc e).length
  let p := compilerInputCount e.1
  let L := (safeEnvironment e).2.length
  let u := (a+1)^2
  have he : a = 2*(enc e.1).length+1+(enc e.2).length := L3.enc_pair_length e
  have hw : e.1.length  ≤  a := by rw [L3.enc_bool_length] at he; omega
  have hwe : (enc e.1).length  ≤  a := by omega
  have hL0 : e.2.length  ≤  (enc e.2).length := EncodedList.length_le enc e.2
  have hLeq : L = e.2.length := by simp [L,safeEnvironment,sanitizeCode]
  have hL : L  ≤  a := by omega
  have hp : p  ≤  a^2 := le_trans (compilerInputCount_bound e.1) (Nat.pow_le_pow_left hw 2)
  have hu : 1  ≤  u := by dsimp [u]; nlinarith
  have hau : a  ≤  u := by dsimp [u]; nlinarith
  have hpu : p  ≤  u := by dsimp [u]; nlinarith
  have hLu : L  ≤  u := le_trans hL hau
  have htok : ∀ t ∈ (safeEnvironment e).2, (enc t).length  ≤  4*(p+5) := by
    intro t ht
    have hn := sanitize_numbers p e.2 t ht
    exact F3Generate.token_enc_bound (p+4) t ⟨le_trans hn.1 (by omega),hn.2⟩
  have hcode := EncodedList.length_bound enc (safeEnvironment e).2 (4*(p+5)) htok
  change (enc ((safeEnvironment e).2)).length  ≤  L*(2*(4*(p+5))+1) at hcode
  have hE : (enc (safeEnvironment e)).length  ≤  100*u^2 := by
    rw [L3.enc_pair_length]
    have hm := Nat.mul_le_mul hLu (show 2*(4*(p+5))+1  ≤  8*u+41 by omega)
    change 2*(enc e.1).length+1+(enc ((safeEnvironment e).2)).length  ≤  _
    nlinarith
  have hM : p+2*L+6  ≤  9*u := by omega
  have hL' : L+1  ≤  2*u := by omega
  have hprod := Nat.mul_le_mul hM hL'
  constructor
  · simp only [eval_add,eval_X,eval_one]
    exact Nat.add_le_add_right hL 1
  · calc
      _  ≤  100000*u^2 := by nlinarith
      _ = _ := by simp only [eval_mul,eval_pow,eval_ofNat,eval_add,eval_X,eval_one]; dsimp [u,a]; ring

lemma safeCompiler_poly : Poly compilerOutput := by
  apply Poly.from_bounded_loop F3Generate.compileBody F3Generate.compileProgram
    compilerInitial compilerOutput compilerInitial_poly (X+1) (100000*(X+1)^4)
  intro e
  let L := (safeEnvironment e).2.length
  refine ⟨L+1,10*(enc (safeEnvironment e)).length+200*(compilerInputCount e.1+2*L+6)*(L+1),
    (safeCompiler_bounds e).1,(safeCompiler_bounds e).2,?_⟩
  exact safeCompiler_run e

end F3MachineCompiler

-- Source: Solutions.T31.SafeOne

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

lemma Expr.code_tags (e : Expr) : ∀ t ∈ e.code, t.1  ≤  4 ∧ (t.1 = 0 → t.2  ≤  1) := by
  induction e with
  | zero | one | input i => simp [Expr.code]
  | plus a b ha hb | times a b ha hb =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with (ht|ht)|rfl
    · exact ha t ht
    · exact hb t ht
    · simp
  | minus a ha =>
    intro t ht
    simp only [Expr.code,List.mem_append,List.mem_singleton] at ht
    rcases ht with ht|rfl
    · exact ha t ht
    · simp

lemma sanitized_step (p : ℕ) (S : CompileState) (t : Token)
    (h : t.1  ≤  4 ∧ (t.1 = 0 → t.2  ≤  1)) :
    compileStep p S (min t.1 4,min t.2 (p+4)) = compileStep p S t := by
  rw [Nat.min_eq_left h.1]
  have hg : tokenGates p S.1.2 S.2 (t.1,min t.2 (p+4)) = tokenGates p S.1.2 S.2 t := by
    by_cases h0 : t.1 = 0
    · have hmin : t.2  ≤  p+4 := by have := h.2 h0; omega
      rw [Nat.min_eq_left hmin]
    · by_cases h1 : t.1 = 1
      · have he : (if min t.2 (p+4) < p then min t.2 (p+4) else p) =
            if t.2 < p then t.2 else p := by
          by_cases ht : t.2 < p
          · rw [Nat.min_eq_left (by omega : t.2  ≤  p+4)]
          · have hm : p  ≤  min t.2 (p+4) := Nat.le_min.mpr ⟨by omega,by omega⟩
            simp [ht,not_lt_of_ge hm]
        simpa only [tokenGates,if_neg h0,if_pos h1] using congrArg (fun i => [(1,i,0,S.1.2+1)]) he
      · simp only [tokenGates,if_neg h0,if_neg h1]
  simp only [compileStep,hg]
  rfl

lemma compile_sanitize (p : ℕ) (ts : List Token)
    (h : ∀ t ∈ ts, t.1  ≤  4 ∧ (t.1 = 0 → t.2  ≤  1)) (S : CompileState) :
    (sanitizeCode p ts).foldl (compileStep p) S = ts.foldl (compileStep p) S := by
  induction ts generalizing S with
  | nil => rfl
  | cons t ts ih =>
    change (sanitizeCode p ts).foldl (compileStep p) (compileStep p S (min t.1 4,min t.2 (p+4))) = _
    rw [sanitized_step p S t (h t (by simp)),ih (fun t ht => h t (by simp [ht]))]
    rfl

def boundedWord (pad : List Bool) (p : ℕ) : List Bool :=
  (pad.map (fun _ => true)).take (min p pad.length) ++ [false,true]

lemma boundedWord_eq (pad : List Bool) (p : ℕ) :
    boundedWord pad p = unaryD (min p pad.length)++unary 1 := by
  have hmin : min p pad.length  ≤  pad.length := Nat.min_le_right _ _
  simp only [boundedWord,List.map_const,List.take_replicate,Nat.min_eq_left hmin,unaryD,unary]
  simp

lemma boundedWord_count (pad : List Bool) (p : ℕ) :
    compilerInputCount (boundedWord pad p) = min p pad.length := by
  rw [boundedWord_eq,compilerInputCount,L3.inputN_word,L3.inputM_word,Nat.mul_one]

@[fun_prop] lemma boundedWord_poly : Poly (fun x : List Bool × ℕ => boundedWord x.1 x.2) := by
  unfold boundedWord
  fun_prop

noncomputable def safeOne (x : (List Bool × ℕ) × Expr) : CompileState :=
  (compilerOutput (boundedWord x.1.1 x.1.2,x.2.code)).2

lemma safeOne_poly : Poly safeOne := by
  have hin : Poly (fun x : (List Bool × ℕ) × Expr => (boundedWord x.1.1 x.1.2,x.2.code)) := by
    fun_prop
  change Poly (fun x : (List Bool × ℕ) × Expr => (compilerOutput (boundedWord x.1.1 x.1.2,x.2.code)).2)
  exact Poly.comp (f := fun z : CompilerEnv × CompileState => z.2)
    (g := fun x : (List Bool × ℕ) × Expr => compilerOutput (boundedWord x.1.1 x.1.2,x.2.code))
    Poly.snd (Poly.comp safeCompiler_poly hin)

lemma safeOne_eq (pad : List Bool) (p : ℕ) (e : Expr) :
    safeOne ((pad,p),e) = one (min p pad.length) e := by
  change compile (compilerInputCount (boundedWord pad p)) (compilerInputCount (boundedWord pad p)+1)
    (sanitizeCode (compilerInputCount (boundedWord pad p)) e.code) = _
  simp only [boundedWord_count]
  unfold compile
  rw [compile_sanitize _ _ (Expr.code_tags e)]
  rfl

end F3MachineCompiler

-- Source: Solutions.T31.ResultPointer

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools

lemma source_after_last (p : ℕ) (S : CompileState) (ts : List Token) (t : Token) :
    source p ((ts++[t]).foldl (compileStep p) S).2 0 =
      ((ts++[t]).foldl (compileStep p) S).1.2-1 := by
  rw [List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,compileStep,tokenStack,source,List.getD_cons_zero]
  omega

lemma result_pointer (p : ℕ) (e : Expr) : result p e = (one p e).1.2-1 := by
  cases e with
  | zero => exact source_after_last p (([],p+1),[]) [] (0,0)
  | one => exact source_after_last p (([],p+1),[]) [] (0,1)
  | input i => exact source_after_last p (([],p+1),[]) [] (1,i)
  | plus a b => exact source_after_last p (([],p+1),[]) (a.code++b.code) (2,0)
  | times a b => exact source_after_last p (([],p+1),[]) (a.code++b.code) (3,0)
  | minus a => exact source_after_last p (([],p+1),[]) a.code (4,0)

end F3MachineCompiler

-- Source: Solutions.T31.SafeBatchMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial
open Classical

@[fun_prop] lemma safeOne_comp {α : Type} [Coding α] {pad : α → List Bool} {p : α → ℕ} {e : α → Expr}
    (hpad : Poly pad) (hp : Poly p) (he : Poly e) : Poly (fun a => safeOne ((pad a,p a),e a)) :=
  Poly.comp safeOne_poly (Poly.pair (Poly.pair hpad hp) he)

lemma enc_append_length {α : Type} [Coding α] (xs ys : List α) :
    (enc (xs++ys)).length = (enc xs).length+(enc ys).length := by
  change (encodeList enc (xs++ys)).length = _
  rw [EncodedList.append,List.length_append]
  rfl

lemma compileState_encoding (S : CompileState) :
    (enc S).length = 4*(enc S.1.1).length+2*(enc S.1.2).length+3+(enc S.2).length := by
  simp only [L3.enc_pair_length]
  omega

noncomputable def oneSize : Polynomial ℕ := safeOne_poly.program.sizeBound.comp (10*X+10)

lemma safeOne_encoding (pad : List Bool) (p : ℕ) (e : Expr) :
    (enc (safeOne ((pad,p),e))).length  ≤  oneSize.eval ((enc pad).length+(enc e).length) := by
  have heq : safeOne ((pad,p),e) = safeOne ((pad,min p pad.length),e) := by
    rw [safeOne_eq,safeOne_eq,Nat.min_eq_left (Nat.min_le_right p pad.length)]
  rw [heq]
  have hp : (enc (min p pad.length)).length  ≤  pad.length+1 :=
    F3Generate.nat_enc_bound _ _ (Nat.min_le_right _ _)
  have hpad : pad.length  ≤  (enc pad).length := by rw [L3.enc_bool_length]; omega
  have hinput : (enc ((pad,min p pad.length),e)).length  ≤ 
      (10*X+10 : Polynomial ℕ).eval ((enc pad).length+(enc e).length) := by
    simp only [L3.enc_pair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega
  have ho := safeOne_poly.program.length_bound ((pad,min p pad.length),e)
  simpa only [oneSize,eval_comp] using ho.trans (polynomial_eval_mono _ hinput)

noncomputable def batchMachineStep (pad : List Bool) (S : CompileState) (e : Expr) : CompileState :=
  let Q := safeOne ((pad,S.1.2),e)
  ((S.1.1++Q.1.1,Q.1.2),S.2++[Q.1.2-1])

@[fun_prop] lemma batchMachineStep_poly :
    Poly (fun x : (List Bool × CompileState) × Expr => batchMachineStep x.1.1 x.1.2 x.2) := by
  unfold batchMachineStep
  fun_prop

lemma batchMachineStep_growth (pad : List Bool) (S : CompileState) (e : Expr) :
    (enc (batchMachineStep pad S e)).length  ≤  (enc S).length+
      2*(enc (safeOne ((pad,S.1.2),e))).length+1 := by
  let Q := safeOne ((pad,S.1.2),e)
  have hp : (enc (Q.1.2-1)).length  ≤  (enc Q.1.2).length := by
    simp only [L3.enc_nat_length]
    exact Nat.size_le_size (Nat.sub_le _ _)
  have hs := EncodedList.length_bound (enc : ℕ → List Bool) [Q.1.2-1] (enc Q.1.2).length (by
    intro a ha
    simpa only [List.mem_singleton.mp ha] using hp)
  change (enc ([Q.1.2-1] : List ℕ)).length  ≤  1*(2*(enc Q.1.2).length+1) at hs
  change (enc ((S.1.1++Q.1.1,Q.1.2),S.2++[Q.1.2-1])).length  ≤  _
  simp only [compileState_encoding,enc_append_length]
  dsimp only [Q] at hp hs ⊢
  omega

noncomputable def batchMachine (x : (List Bool × ℕ) × List Expr) : CompileState :=
  x.2.foldl (batchMachineStep x.1.1) (([],x.1.2),[])

lemma batchMachine_poly : Poly batchMachine := by
  unfold batchMachine
  apply L3.Poly.list_foldl (by unfold batchMachineStep; fun_prop) (by fun_prop) (by fun_prop)
    (2*oneSize+1)
  intro x S e
  have hg := batchMachineStep_growth x.1.1 S e
  have hq := safeOne_encoding x.1.1 S.1.2 e
  have hpad : (enc x.1.1).length  ≤  (enc x).length := by
    simp only [L3.enc_pair_length]
    omega
  have hm := polynomial_eval_mono oneSize (Nat.add_le_add_right hpad (enc e).length)
  simp only [eval_add,eval_mul,eval_ofNat,eval_one]
  omega

end F3MachineCompiler

-- Source: Solutions.T31.BatchMachineCorrect

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools

lemma batchMachine_fold (pad : List Bool) (S : CompileState) (es : List Expr)
    (he : ∀ e ∈ es, e.Bounded S.1.2) (hlimit : (batch S.1.2 es).1.2  ≤  pad.length) :
    es.foldl (batchMachineStep pad) S =
      ((S.1.1++(batch S.1.2 es).1.1,(batch S.1.2 es).1.2),S.2++(batch S.1.2 es).2) := by
  induction es generalizing S with
  | nil => simp [batch]
  | cons e es ih =>
    let Q := one S.1.2 e
    have ho := one_inv S.1.2 e (he e (by simp)) (fun _ => 0) (by simp)
    have hp : S.1.2  ≤  Q.1.2 := le_trans (by omega : S.1.2  ≤  S.1.2+1) ho.1.growing
    have ht : ∀ a ∈ es, a.Bounded Q.1.2 :=
      fun a ha => a.bounded_mono (he a (by simp [ha])) hp
    have hb := batch_correct Q.1.2 es ht (fun _ => 0) (by simp)
    have hlow : S.1.2  ≤  pad.length := le_trans hp (le_trans hb.monotone hlimit)
    let S' : CompileState := ((S.1.1++Q.1.1,Q.1.2),S.2++[result S.1.2 e])
    have hstep : batchMachineStep pad S e = S' := by
      unfold batchMachineStep
      rw [safeOne_eq,Nat.min_eq_left hlow]
      dsimp only
      rw [← result_pointer]
    rw [List.foldl_cons,hstep,ih S' ht hlimit]
    simp only [S',Q,batch,List.append_assoc,List.singleton_append]

lemma batchMachine_correct (pad : List Bool) (p : ℕ) (es : List Expr)
    (he : ∀ e ∈ es, e.Bounded p) (hlimit : (batch p es).1.2  ≤  pad.length) :
    batchMachine ((pad,p),es) = batch p es := by
  have hh := batchMachine_fold pad (([],p),[]) es he hlimit
  simpa only [batchMachine,List.nil_append] using hh

end F3MachineCompiler

-- Source: Solutions.T31.MetadataMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial
open Classical

abbrev GeneratorEnv := List Bool × List Bool
abbrev RegisterCode := (ℕ × List ℕ) × Bool
abbrev ChunkInput := (GeneratorEnv × RegisterCode) × Phase
abbrev Metadata := (List Raw × ℕ) × (List ℕ × Bool)

def envCapacity (E : GeneratorEnv) := E.1.length+2
lemma envCapacity_two (E : GeneratorEnv) : 2  ≤  envCapacity E := by dsimp [envCapacity]; omega

noncomputable def rawRegisters (M : BinaryMachine) (x : ChunkInput) : Symbolic M (envCapacity x.1.1) :=
  if x.1.2.2 then initialSymbolic M (envCapacity x.1.1)
  else wireSymbolic M (envCapacity x.1.1) x.1.2.1.2

lemma rawRegisters_family (M : BinaryMachine) :
    FamilyPoly M (fun x : ChunkInput => envCapacity x.1.1) (rawRegisters M) := by
  have hN : Poly (fun x : ChunkInput => envCapacity x.1.1) := by unfold envCapacity; fun_prop
  apply family_if _ _ (family_initial M _) (family_wires M _ _ hN (by fun_prop))
  fun_prop

noncomputable def rawChunk (M : BinaryMachine) (τ : Bool ≃ Bool) (x : ChunkInput) : CompileState :=
  batchMachine ((x.1.1.2,x.1.2.1.1),expressionList
    (phaseTransform τ (envCapacity_two x.1.1) x.2 (rawRegisters M x)))

lemma rawChunk_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (rawChunk M τ) := by
  have hN : Poly (fun x : ChunkInput => envCapacity x.1.1) := by unfold envCapacity; fun_prop
  have hrange : Poly (fun x : ChunkInput => List.range (envCapacity x.1.1)) := by
    have hh : Poly (fun x : ChunkInput => List.range (x.1.1.1++[true,true]).length) := by fun_prop
    simpa only [envCapacity,List.length_append,List.length_cons,List.length_nil] using hh
  have hF := family_phaseTransform (rawRegisters M) (rawRegisters_family M) hN τ
    (fun x => envCapacity_two x.1.1) (fun x => x.2) (by fun_prop)
  have hcode := family_expressionList _ hF hrange
  change Poly (fun x : ChunkInput => batchMachine ((x.1.1.2,x.1.2.1.1),expressionList
    (phaseTransform τ (envCapacity_two x.1.1) x.2 (rawRegisters M x))))
  exact Poly.comp batchMachine_poly (by fun_prop)

noncomputable def clampRegisters (M : BinaryMachine) (E : GeneratorEnv) (S : Metadata) : RegisterCode :=
  ((min S.1.2 E.2.length,(S.2.1.take (dimension M (envCapacity E))).map (fun i => min i E.2.length)),S.2.2)

lemma clampRegisters_poly (M : BinaryMachine) :
    Poly (fun x : GeneratorEnv × Metadata => clampRegisters M x.1 x.2) := by
  unfold clampRegisters dimension envCapacity
  fun_prop

@[fun_prop] lemma clampRegisters_comp {α : Type} [Coding α] (M : BinaryMachine)
    {E : α → GeneratorEnv} {S : α → Metadata} (hE : Poly E) (hS : Poly S) :
    Poly (fun a => clampRegisters M (E a) (S a)) :=
  Poly.comp (clampRegisters_poly M) (Poly.pair hE hS)

noncomputable def metadataStep (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv)
    (S : Metadata) (p : Phase) : Metadata :=
  let Q := rawChunk M τ ((E,clampRegisters M E S),p)
  ((S.1.1++Q.1.1,Q.1.2),(Q.2,false))

lemma metadataStep_poly (M : BinaryMachine) (τ : Bool ≃ Bool) :
    Poly (fun x : (GeneratorEnv × Metadata) × Phase => metadataStep M τ x.1.1 x.1.2 x.2) := by
  unfold metadataStep
  have hchunk : Poly (fun x : (GeneratorEnv × Metadata) × Phase =>
      rawChunk M τ ((x.1.1,clampRegisters M x.1.1 x.1.2),x.2)) :=
    Poly.comp (rawChunk_poly M τ) (by fun_prop)
  fun_prop

end F3MachineCompiler

-- Source: Solutions.T31.MetadataBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial
open Classical

def dimensionFactor (M : BinaryMachine) :=
  Fintype.card (Option M.Label)+Fintype.card M.State+3*Fintype.card M.K+1

lemma env_length_bounds (E : GeneratorEnv) :
    E.1.length  ≤  (enc E).length ∧ E.2.length  ≤  (enc E).length := by
  simp only [L3.enc_pair_length,L3.enc_bool_length]
  constructor <;> omega

lemma dimension_encoding_bound (M : BinaryMachine) (E : GeneratorEnv) :
    dimension M (envCapacity E)  ≤  dimensionFactor M*((enc E).length+1) := by
  have hcap : envCapacity E  ≤  3*((enc E).length+1) := by
    have hh := (env_length_bounds E).1
    dsimp [envCapacity]
    omega
  have hm := Nat.mul_le_mul_left (Fintype.card M.K) hcap
  dsimp [dimension,dimensionFactor]
  nlinarith

lemma bool_encoding (b : Bool) : (enc b).length = 1 := by cases b <;> rfl

lemma registerCode_encoding (R : RegisterCode) :
    (enc R).length = 4*(enc R.1.1).length+2*(enc R.1.2).length+4 := by
  simp only [L3.enc_pair_length,bool_encoding]
  omega

lemma metadata_encoding (S : Metadata) :
    (enc S).length = 4*(enc S.1.1).length+2*(enc S.1.2).length+2*(enc S.2.1).length+5 := by
  simp only [L3.enc_pair_length,bool_encoding]
  omega

noncomputable def chunkInputBound (M : BinaryMachine) : Polynomial ℕ := C (20*dimensionFactor M+100)*(X+1)^2

lemma normalized_input_bound (M : BinaryMachine) (E : GeneratorEnv) (S : Metadata) (p : Phase) :
    (enc ((E,clampRegisters M E S),p)).length  ≤  (chunkInputBound M).eval ((enc E).length+(enc p).length) := by
  let z := (enc E).length+(enc p).length
  let d := dimensionFactor M
  let R := clampRegisters M E S
  have hpad : E.2.length  ≤  z := le_trans (env_length_bounds E).2 (Nat.le_add_right _ _)
  have hD : dimension M (envCapacity E)  ≤  d*(z+1) :=
    le_trans (dimension_encoding_bound M E) (Nat.mul_le_mul_left _ (by dsimp [z]; omega))
  have hptr : (enc R.1.1).length  ≤  z+1 := by
    have hh := F3Generate.nat_enc_bound (min S.1.2 E.2.length) E.2.length (Nat.min_le_right _ _)
    exact le_trans hh (by omega)
  have hwlen : R.1.2.length  ≤  d*(z+1) := by
    change ((S.2.1.take (dimension M (envCapacity E))).map (fun i => min i E.2.length)).length  ≤  _
    simp only [List.length_map,List.length_take]
    exact le_trans (Nat.min_le_left _ _) hD
  have hwords : ∀ w ∈ R.1.2, (enc w).length  ≤  z+1 := by
    intro w hw
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
    exact le_trans (F3Generate.nat_enc_bound _ E.2.length (Nat.min_le_right _ _)) (by omega)
  have hwenc := EncodedList.length_bound (enc : ℕ → List Bool) R.1.2 (z+1) hwords
  change (enc R.1.2).length  ≤  R.1.2.length*(2*(z+1)+1) at hwenc
  have hwordbound : (enc R.1.2).length  ≤  3*d*(z+1)^2 := by
    have hh := Nat.mul_le_mul hwlen (show 2*(z+1)+1  ≤  3*(z+1) by omega)
    change (enc R.1.2).length  ≤  _
    nlinarith
  have hreg : (enc R).length  ≤  (6*d+8)*(z+1)^2 := by
    rw [registerCode_encoding]
    nlinarith
  have hwhole : (enc ((E,R),p)).length = 4*(enc E).length+2*(enc R).length+3+(enc p).length := by
    simp only [L3.enc_pair_length]
    omega
  change (enc ((E,R),p)).length  ≤  _
  rw [hwhole]
  simp only [chunkInputBound,eval_mul,eval_add,eval_pow,eval_ofNat,eval_C,eval_X,eval_one]
  change _  ≤  (20*d+100)*(z+1)^2
  have hz : (enc E).length  ≤  z := Nat.le_add_right _ _
  have hp : (enc p).length  ≤  z := Nat.le_add_left _ _
  nlinarith

noncomputable def chunkSize (M : BinaryMachine) (τ : Bool ≃ Bool) : Polynomial ℕ :=
  (rawChunk_poly M τ).program.sizeBound.comp (chunkInputBound M)

lemma chunk_encoding_bound (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (S : Metadata) (p : Phase) :
    (enc (rawChunk M τ ((E,clampRegisters M E S),p))).length  ≤ 
      (chunkSize M τ).eval ((enc E).length+(enc p).length) := by
  have ho := (rawChunk_poly M τ).program.length_bound ((E,clampRegisters M E S),p)
  have hm := polynomial_eval_mono (rawChunk_poly M τ).program.sizeBound (normalized_input_bound M E S p)
  simpa only [chunkSize,eval_comp] using ho.trans hm

lemma metadataStep_growth (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (S : Metadata) (p : Phase) :
    (enc (metadataStep M τ E S p)).length  ≤  (enc S).length+
      2*(enc (rawChunk M τ ((E,clampRegisters M E S),p))).length := by
  let Q := rawChunk M τ ((E,clampRegisters M E S),p)
  change (enc ((S.1.1++Q.1.1,Q.1.2),(Q.2,false)) : List Bool).length  ≤  _
  simp only [metadata_encoding,compileState_encoding,enc_append_length]
  dsimp only [Q]
  omega

noncomputable def metadataLoop (M : BinaryMachine) (τ : Bool ≃ Bool)
    (x : (GeneratorEnv × ℕ) × List Phase) : Metadata :=
  x.2.foldl (metadataStep M τ x.1.1) (([],x.1.2),([],true))

lemma metadataLoop_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (metadataLoop M τ) := by
  unfold metadataLoop
  apply L3.Poly.list_foldl (α := (GeneratorEnv × ℕ) × List Phase) (β := Metadata) (γ := Phase) (by
    exact Poly.comp (metadataStep_poly M τ)
      (g := fun x : (((GeneratorEnv × ℕ) × List Phase) × Metadata) × Phase =>
        ((x.1.1.1.1,x.1.2),x.2)) (by fun_prop)) (by fun_prop) (by fun_prop) (2*chunkSize M τ)
  intro x S p
  have hg := metadataStep_growth M τ x.1.1 S p
  have hq := chunk_encoding_bound M τ x.1.1 S p
  have henv : (enc x.1.1).length  ≤  (enc x).length := by simp only [L3.enc_pair_length]; omega
  have hm := polynomial_eval_mono (chunkSize M τ) (Nat.add_le_add_right henv (enc p).length)
  simp only [eval_mul,eval_ofNat]
  omega

end F3MachineCompiler

-- Source: Solutions.T31.PhaseLoopBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

def phaseBudget (M : BinaryMachine) (N : ℕ) := dimension M N*(2*phaseSize M+1)

lemma phaseStep_bounds {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (S : Simulation M N) (p : Phase) (hS : Safe (fun i => i < S.pointer) S.registers)
    (hsize : Size S.registers 3) (hp : p.2 < S.pointer) :
    Safe (fun i => i < (phaseStep τ hN S p).pointer) (phaseStep τ hN S p).registers ∧
      Size (phaseStep τ hN S p).registers 3 ∧ S.pointer  ≤  (phaseStep τ hN S p).pointer ∧
      (phaseStep τ hN S p).pointer  ≤  S.pointer+phaseBudget M N := by
  have hf := phaseTransform_safe _ τ hN p S.registers hS hp
  have hz := phaseTransform_size τ hN p S.registers hsize
  have hr := store_size_bound S.pointer _ hf (phaseSize M) hz
  exact ⟨safe_stored _ _ hf,size_mono _ (size_stored _ _) (by decide),emit_monotone _ _ hf,hr.1⟩

lemma phaseLoop_bounds {M : BinaryMachine} {N : ℕ} (τ : Bool ≃ Bool) (hN : 2  ≤  N)
    (seed : ℕ) (ps : List Phase) (S : Simulation M N)
    (hS : Safe (fun i => i < S.pointer) S.registers) (hsize : Size S.registers 3)
    (hseed : seed  ≤  S.pointer) (hps : ∀ p ∈ ps, p.2 < seed) :
    Safe (fun i => i < (phaseLoop τ hN ps S).pointer) (phaseLoop τ hN ps S).registers ∧
      Size (phaseLoop τ hN ps S).registers 3 ∧ seed  ≤  (phaseLoop τ hN ps S).pointer ∧
      (phaseLoop τ hN ps S).pointer  ≤  S.pointer+ps.length*phaseBudget M N := by
  induction ps generalizing S with
  | nil => exact ⟨hS,hsize,hseed,by simp [phaseLoop]⟩
  | cons p ps ih =>
    have hp := lt_of_lt_of_le (hps p (by simp)) hseed
    obtain ⟨hn,hs,hmono,hbound⟩ := phaseStep_bounds τ hN S p hS hsize hp
    have ht := ih (phaseStep τ hN S p) hn hs (le_trans hseed hmono) (fun p hp => hps p (by simp [hp]))
    refine ⟨ht.1,ht.2.1,ht.2.2.1,?_⟩
    change (phaseLoop τ hN ps (phaseStep τ hN S p)).pointer  ≤  _
    have hb := ht.2.2.2
    simp only [List.length_cons,Nat.succ_mul]
    omega

lemma dataSchedule_indices (n m : ℕ) : ∀ p ∈ dataSchedule n m, p.2 < reserve n m := by
  intro p hp
  rcases List.mem_append.mp hp with hA|hb
  · obtain ⟨i,_,hA⟩ := List.mem_flatMap.mp hA
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hA
    have hx : n*i.val+j.val < n*m := by nlinarith [i.isLt,j.isLt]
    dsimp [reserve]
    omega
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
    have hi := i.isLt
    dsimp [reserve]
    omega

lemma decoderSchedule_indices (n m T j : ℕ) :
    ∀ p ∈ decoderSchedule n m T j, p.2 < reserve n m := by
  intro p hp
  simp only [decoderSchedule,List.mem_append,List.mem_reverse] at hp
  rcases hp with ((hd|hb)|ht)|hc
  · exact dataSchedule_indices n m p hd
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hb
    dsimp [reserve]
    omega
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp ht
    dsimp [reserve]
    omega
  · obtain ⟨_,rfl⟩ := List.mem_replicate.mp hc
    dsimp [reserve]
    omega

lemma decoderSchedule_length (n m T j : ℕ) :
    (decoderSchedule n m T j).length = n*m+n+2*m+T+j+2 := by
  simp only [decoderSchedule,List.length_append,List.length_reverse,List.length_replicate,
    bitSchedule,List.length_map,unaryD,unary,List.length_append,List.length_replicate,List.length_singleton]
  have hd : (dataSchedule n m).length = n*m+m := by
    simp [dataSchedule,List.length_flatMap,List.sum_const_nat,Nat.mul_comm]
  rw [hd]
  omega

lemma initialSimulation_size (M : BinaryMachine) (N p : ℕ) : Size (initialSimulation M N p).registers 3 :=
  ⟨fun _ => literal_size _,fun _ => literal_size _,by intros; simp [initialSimulation,initialSymbolic,Expr.code]⟩

lemma answerSimulation_resources (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) :
    Safe (fun i => i < (answerSimulation M τ n m T j).pointer) (answerSimulation M τ n m T j).registers ∧
      Size (answerSimulation M τ n m T j).registers 3 ∧
      reserve n m  ≤  (answerSimulation M τ n m T j).pointer ∧
      (answerSimulation M τ n m T j).pointer  ≤  reserve n m+
        (n*m+n+2*m+T+j+2)*phaseBudget M (capacity M n m T) := by
  have hr := phaseLoop_bounds τ (capacity_ge_two M n m T) (reserve n m) (decoderSchedule n m T j)
    (initialSimulation M (capacity M n m T) (reserve n m))
    (initialSymbolic_safe M _ _) (initialSimulation_size M _ _) le_rfl (decoderSchedule_indices n m T j)
  rw [decoderSchedule_correct,decoderSchedule_length] at hr
  exact hr

lemma computation_pointer_bound (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) :
    (computation M τ n m T j).1.2  ≤  reserve n m+
      (n*m+n+2*m+T+j+2)*phaseBudget M (capacity M n m T)+125 := by
  obtain ⟨hs,hsize,hseed,hp⟩ := answerSimulation_resources M τ n m T j
  have hb := parsedTrit_inputs _ τ (capacity_ge_two M n m T) _ hs
  have he := one_inv (answerSimulation M τ n m T j).pointer (answerExpression M τ n m T j)
    (inputs_bounded _ _ hb) (fun _ => 0) (by simp)
  have hl := parsedTrit_size τ (capacity_ge_two M n m T) _ hsize
  change (one (answerSimulation M τ n m T j).pointer (answerExpression M τ n m T j)).1.2  ≤  _
  rw [he.2.2.1]
  change _+(1:ℕ)+2*(parsedTrit τ (capacity_ge_two M n m T) _).code.length  ≤  _
  omega

end F3MachineCompiler

-- Source: Solutions.T31.MetadataCorrect

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools
open Classical

lemma clamp_access (as : List ℕ) (D B i : ℕ) (hi : i < D) (hv : as.getD i 0  ≤  B) :
    ((as.take D).map (fun a => min a B)).getD i 0 = as.getD i 0 := by
  by_cases ha : i < as.length
  · have hn : i < ((as.take D).map (fun a => min a B)).length := by
      simp only [List.length_map,List.length_take]
      omega
    rw [List.getD_eq_getElem _ _ hn,List.getElem_map,List.getElem_take,List.getD_eq_getElem _ _ ha]
    have hv' : as[i]  ≤  B := by simpa only [List.getD_eq_getElem _ _ ha] using hv
    exact Nat.min_eq_left hv'
  · have hn : ((as.take D).map (fun a => min a B)).length  ≤  i := by
      simp only [List.length_map,List.length_take]
      omega
    rw [List.getD_eq_default _ _ hn,List.getD_eq_default _ _ (by omega)]

lemma wireSymbolic_clamp (M : BinaryMachine) (N p B : ℕ) (as : List ℕ)
    (h : Safe (fun i => i < p) (wireSymbolic M N as)) (hp : p  ≤  B) :
    wireSymbolic M N ((as.take (dimension M N)).map (fun a => min a B)) = wireSymbolic M N as := by
  unfold wireSymbolic
  apply congrArg Symbolic.of
  funext c
  congr 1
  have hs := safe_get _ (wireSymbolic M N as) h c
  simp only [wireSymbolic,Symbolic.get_of,Inputs] at hs
  exact clamp_access as (dimension M N) B (coordinates M N c).val (coordinates M N c).isLt
    (le_trans (Nat.le_of_lt hs) hp)

noncomputable def metadataRegisters (M : BinaryMachine) (E : GeneratorEnv) (m : Metadata) :
    Symbolic M (envCapacity E) := rawRegisters M ((E,((m.1.2,m.2.1),m.2.2)),(0,0))

def MetadataRep (M : BinaryMachine) (E : GeneratorEnv) (m : Metadata)
    (S : Simulation M (envCapacity E)) : Prop :=
  m.1.1 = S.gates ∧ m.1.2 = S.pointer ∧ metadataRegisters M E m = S.registers

lemma clampRegisters_correct (M : BinaryMachine) (E : GeneratorEnv) (m : Metadata)
    (S : Simulation M (envCapacity E)) (hr : MetadataRep M E m S)
    (hs : Safe (fun i => i < S.pointer) S.registers) (hp : S.pointer  ≤  E.2.length) (p : Phase) :
    rawRegisters M ((E,clampRegisters M E m),p) = S.registers := by
  have hh := hr.2.2
  cases hf : m.2.2
  · have hh' : wireSymbolic M (envCapacity E) m.2.1 = S.registers := by
      simpa only [metadataRegisters,rawRegisters,hf,Bool.false_eq_true,if_false] using hh
    have hsafe : Safe (fun i => i < S.pointer) (wireSymbolic M (envCapacity E) m.2.1) := by rw [hh']; exact hs
    have hc := wireSymbolic_clamp M (envCapacity E) S.pointer E.2.length m.2.1 hsafe hp
    change (if m.2.2 then initialSymbolic M (envCapacity E) else
      wireSymbolic M (envCapacity E) ((m.2.1.take (dimension M (envCapacity E))).map (fun i => min i E.2.length))) = _
    rw [hf]
    simpa only [Bool.false_eq_true,if_false] using hc.trans hh'
  · have hh' : initialSymbolic M (envCapacity E) = S.registers := by
      simpa only [metadataRegisters,rawRegisters,hf,ite_true] using hh
    change (if m.2.2 then initialSymbolic M (envCapacity E) else _) = _
    rw [hf]
    exact hh'

lemma metadataStep_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (m : Metadata)
    (S : Simulation M (envCapacity E)) (hr : MetadataRep M E m S)
    (hs : Safe (fun i => i < S.pointer) S.registers) (p : Phase) (hi : p.2 < S.pointer)
    (hlimit : (phaseStep τ (envCapacity_two E) S p).pointer  ≤  E.2.length) :
    MetadataRep M E (metadataStep M τ E m p) (phaseStep τ (envCapacity_two E) S p) := by
  have hF := phaseTransform_safe _ τ (envCapacity_two E) p S.registers hs hi
  have hp : S.pointer  ≤  E.2.length := le_trans (emit_monotone S _ hF) hlimit
  have hreg := clampRegisters_correct M E m S hr hs hp p
  have hq : rawChunk M τ ((E,clampRegisters M E m),p) =
      store S.pointer (phaseTransform τ (envCapacity_two E) p S.registers) := by
    unfold rawChunk
    rw [hreg]
    change batchMachine ((E.2,min m.1.2 E.2.length),expressionList
      (phaseTransform τ (envCapacity_two E) p S.registers)) = _
    rw [hr.2.1,Nat.min_eq_left hp]
    exact batchMachine_correct E.2 S.pointer _
      (fun e he => inputs_bounded _ e (safe_expressionList _ _ hF e he)) hlimit
  refine ⟨?_,?_,?_⟩
  · change m.1.1++(rawChunk M τ ((E,clampRegisters M E m),p)).1.1 = _
    rw [hq,hr.1]
    rfl
  · change (rawChunk M τ ((E,clampRegisters M E m),p)).1.2 = _
    rw [hq]
    rfl
  · change wireSymbolic M (envCapacity E) (rawChunk M τ ((E,clampRegisters M E m),p)).2 = _
    rw [hq]
    exact (stored_wire S.pointer (phaseTransform τ (envCapacity_two E) p S.registers)).symm

lemma metadata_fold_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv)
    (ps : List Phase) (seed : ℕ) (m : Metadata) (S : Simulation M (envCapacity E))
    (hr : MetadataRep M E m S) (hs : Safe (fun i => i < S.pointer) S.registers)
    (hsize : Size S.registers 3) (hseed : seed  ≤  S.pointer) (hps : ∀ p ∈ ps, p.2 < seed)
    (hlimit : (phaseLoop τ (envCapacity_two E) ps S).pointer  ≤  E.2.length) :
    MetadataRep M E (ps.foldl (metadataStep M τ E) m) (phaseLoop τ (envCapacity_two E) ps S) := by
  induction ps generalizing m S with
  | nil => exact hr
  | cons p ps ih =>
    have hi := lt_of_lt_of_le (hps p (by simp)) hseed
    obtain ⟨hs',hz',hmono,hbound⟩ := phaseStep_bounds τ (envCapacity_two E) S p hs hsize hi
    have htail : ∀ p ∈ ps, p.2 < seed := fun p hp => hps p (by simp [hp])
    have hstep : (phaseStep τ (envCapacity_two E) S p).pointer  ≤  E.2.length := by
      have hh := phaseLoop_bounds τ (envCapacity_two E) (phaseStep τ (envCapacity_two E) S p).pointer ps
        (phaseStep τ (envCapacity_two E) S p) hs' hz' le_rfl
        (fun q hq => lt_of_lt_of_le (htail q hq) (le_trans hseed hmono))
      exact le_trans hh.2.2.1 hlimit
    exact ih (metadataStep M τ E m p) (phaseStep τ (envCapacity_two E) S p)
      (metadataStep_correct M τ E m S hr hs p hi hstep) hs' hz' (le_trans hseed hmono) htail hlimit

end F3MachineCompiler

-- Source: Solutions.T31.FinalMetadata

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

lemma metadataLoop_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (seed : ℕ)
    (ps : List Phase) (hps : ∀ p ∈ ps, p.2 < seed)
    (hlimit : (phaseLoop τ (envCapacity_two E) ps (initialSimulation M (envCapacity E) seed)).pointer  ≤  E.2.length) :
    MetadataRep M E (metadataLoop M τ ((E,seed),ps))
      (phaseLoop τ (envCapacity_two E) ps (initialSimulation M (envCapacity E) seed)) := by
  exact metadata_fold_correct M τ E ps seed (([],seed),([],true)) (initialSimulation M (envCapacity E) seed)
    ⟨rfl,rfl,rfl⟩ (initialSymbolic_safe M _ _) (initialSimulation_size M _ _) le_rfl hps hlimit

noncomputable def rawAnswerChunk (M : BinaryMachine) (τ : Bool ≃ Bool) (x : ChunkInput) : CompileState :=
  safeOne ((x.1.1.2,x.1.2.1.1),parsedTrit τ (envCapacity_two x.1.1) (rawRegisters M x))

lemma rawAnswerChunk_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (rawAnswerChunk M τ) := by
  have he := family_parsedTrit (rawRegisters M) (rawRegisters_family M) τ (fun x => envCapacity_two x.1.1)
  change Poly (fun x : ChunkInput => safeOne ((x.1.1.2,x.1.2.1.1),
    parsedTrit τ (envCapacity_two x.1.1) (rawRegisters M x)))
  exact safeOne_comp (by fun_prop) (by fun_prop) he

noncomputable def finishMetadata (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (S : Metadata) : CompileState :=
  let Q := rawAnswerChunk M τ ((E,clampRegisters M E S),(0,0))
  ((S.1.1++Q.1.1,Q.1.2),[Q.1.2-1])

lemma finishMetadata_poly (M : BinaryMachine) (τ : Bool ≃ Bool) :
    Poly (fun x : GeneratorEnv × Metadata => finishMetadata M τ x.1 x.2) := by
  have hQ : Poly (fun x : GeneratorEnv × Metadata => rawAnswerChunk M τ ((x.1,clampRegisters M x.1 x.2),(0,0))) :=
    Poly.comp (rawAnswerChunk_poly M τ) (by fun_prop)
  unfold finishMetadata
  fun_prop

lemma finishMetadata_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (m : Metadata)
    (S : Simulation M (envCapacity E)) (hr : MetadataRep M E m S)
    (hs : Safe (fun i => i < S.pointer) S.registers) (hp : S.pointer  ≤  E.2.length) :
    finishMetadata M τ E m =
      ((S.gates++(one S.pointer (parsedTrit τ (envCapacity_two E) S.registers)).1.1,
        (one S.pointer (parsedTrit τ (envCapacity_two E) S.registers)).1.2),
        [result S.pointer (parsedTrit τ (envCapacity_two E) S.registers)]) := by
  have hreg := clampRegisters_correct M E m S hr hs hp (0,0)
  have hQ : rawAnswerChunk M τ ((E,clampRegisters M E m),(0,0)) =
      one S.pointer (parsedTrit τ (envCapacity_two E) S.registers) := by
    unfold rawAnswerChunk
    rw [hreg,safeOne_eq]
    change one (min (min m.1.2 E.2.length) E.2.length) _ = _
    rw [hr.2.1]
    simp only [Nat.min_eq_left hp]
  unfold finishMetadata
  rw [hQ]
  dsimp only
  rw [hr.1,← result_pointer]

noncomputable def coordinateGenerator (M : BinaryMachine) (τ : Bool ≃ Bool)
    (x : (GeneratorEnv × ℕ) × List Phase) : CompileState :=
  finishMetadata M τ x.1.1 (metadataLoop M τ x)

lemma coordinateGenerator_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (coordinateGenerator M τ) := by
  change Poly (fun x : (GeneratorEnv × ℕ) × List Phase => finishMetadata M τ x.1.1 (metadataLoop M τ x))
  exact Poly.comp (finishMetadata_poly M τ) (Poly.pair (by fun_prop) (metadataLoop_poly M τ))

lemma coordinateGenerator_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (E : GeneratorEnv) (seed : ℕ)
    (ps : List Phase) (hps : ∀ p ∈ ps, p.2 < seed)
    (hlimit : (phaseLoop τ (envCapacity_two E) ps (initialSimulation M (envCapacity E) seed)).pointer  ≤  E.2.length) :
    coordinateGenerator M τ ((E,seed),ps) =
      let S := phaseLoop τ (envCapacity_two E) ps (initialSimulation M (envCapacity E) seed)
      ((S.gates++(one S.pointer (parsedTrit τ (envCapacity_two E) S.registers)).1.1,
        (one S.pointer (parsedTrit τ (envCapacity_two E) S.registers)).1.2),
        [result S.pointer (parsedTrit τ (envCapacity_two E) S.registers)]) := by
  have hr := metadataLoop_correct M τ E seed ps hps hlimit
  have hb := phaseLoop_bounds τ (envCapacity_two E) seed ps (initialSimulation M (envCapacity E) seed)
    (initialSymbolic_safe M _ _) (initialSimulation_size M _ _) le_rfl hps
  exact finishMetadata_correct M τ E _ _ hr hb.1 hlimit

end F3MachineCompiler

-- Source: Solutions.L2.CodeCorrect

set_option maxHeartbeats 3000000
namespace F3Generate
open F3Tools F3Search F3SubsetSum

def word (n m : ℕ) := unaryD n ++ unary m

theorem nr_word (n m : ℕ) : nr (word n m) = List.range n := by
  unfold nr
  rw [show L3.inputN (word n m) = n from L3.inputN_word n m,List.take_range]
  rw [Nat.min_eq_left (by simp [word,unaryD,unary] <;> omega)]

theorem mr_word (n m : ℕ) : mr (word n m) = List.range m := by
  unfold mr
  rw [show L3.inputM (word n m) = m from L3.inputM_word n m,List.take_range]
  rw [Nat.min_eq_left (by simp [word,unaryD,unary] <;> omega)]

theorem sumCode_word (n m j : ℕ) (s : List Bool) :
    sumCode (word n m) j s = (sumExpr n m j s).code := by
  unfold sumCode
  rw [mr_word,List.foldl_reverse]
  have hn : L3.inputN (word n m) = n := L3.inputN_word n m
  rw [hn]
  have he : ∀ is : List ℕ,
      is.foldr (fun i acc => [(if s.getD i false then 1 else 0,
        if s.getD i false then n*i+j else 0)]++acc++[(2,0)]) [(0,0)] =
        (Expr.sum (is.map (fun i => if s.getD i false then Expr.input (n*i+j) else Expr.zero))).code := by
    intro is
    induction is with
    | nil => rfl
    | cons i is ih =>
      simp only [List.foldr_cons,List.map_cons,Expr.sum,List.foldr_cons,Expr.code]
      rw [← show (Expr.sum (is.map (fun i => if s.getD i false then Expr.input (n*i+j) else Expr.zero))).code = _ from ih.symm]
      split_ifs <;> rfl
  exact he _

theorem goodCode_word (n m : ℕ) (s : List Bool) :
    goodCode (word n m) s = (goodExpr n m s).code := by
  unfold goodCode goodExpr
  split_ifs
  · rw [nr_word,List.foldl_reverse]
    simp_rw [sumCode_word]
    have he : ∀ js : List ℕ,
        js.foldr (fun j acc => [(0,1)]++(sumExpr n m j s).code++(sumExpr n m j s).code++
          [(3,0),(4,0),(2,0)]++acc++[(3,0)]) [(0,1)] =
          (Expr.product (js.map (fun j => (sumExpr n m j s).isZero))).code := by
      intro js
      induction js with
      | nil => rfl
      | cons j js ih =>
        change [(0,1)]++(sumExpr n m j s).code++(sumExpr n m j s).code++
          [(3,0),(4,0),(2,0)]++_++[(3,0)] = _
        rw [ih]
        simp [Expr.product,Expr.isZero,Expr.code,List.append_assoc]
    exact he _
  · rfl

theorem searchCode_word (n m i : ℕ) (ss : List (List Bool)) :
    searchCode (word n m) ss i = (searchExpr n m i ss).code := by
  unfold searchCode
  rw [List.foldl_reverse]
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldr_cons]
    rw [ih]
    simp only [searchPrefix,goodCode_word,searchExpr,Expr.choose,Expr.code]
    split_ifs <;> simp [Expr.code,List.append_assoc]

theorem outputCode_word (n m : ℕ) : outputCode (word n m) (bits m) = code n m := by
  unfold outputCode code outputExprs
  rw [mr_word,List.flatMap_map]
  congr 1
  funext i
  exact searchCode_word n m i (bits m)

end F3Generate

-- Source: Solutions.L2.Serialize

set_option maxHeartbeats 2000000
namespace F3Generate
open F3Tools F3Search F3SubsetSum OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

def rawEncode (pad : List Bool) (g : Raw) : List Bool :=
  let u (i : ℕ) := pad.take i ++ [false]
  if g.1 = 0 then [false,false,false,false] ++ u g.2.2.2
  else if g.1 = 1 then [false,false,true,false] ++ u g.2.1 ++ u g.2.2.2
  else if g.1 = 2 then [false,false,true,true] ++ u g.2.1 ++ u g.2.2.2
  else [false,true,false,false] ++ u g.2.1 ++ u g.2.2.1 ++ u g.2.2.2

theorem rawEncode_correct (W : ℕ) (g : Raw) (hv : Valid W g) (pad : List Bool)
    (hp : ∀ i < W, pad.take i = List.replicate i true) :
    (rawRev W g).gates.flatMap encodeGate = rawEncode pad g := by
  rcases hv with ⟨hk,hv⟩
  unfold rawRev
  rw [dif_pos hk]
  rcases hv with h0 | ⟨hi,hik,hs⟩
  · rw [if_pos h0]
    simp [shift,rawEncode,h0,encodeGate,hp _ hk]
  · by_cases h0 : g.1 = 0
    · rw [if_pos h0]
      simp [shift,rawEncode,h0,encodeGate,hp _ hk]
    rw [if_neg h0,dif_pos ⟨hi,hik⟩]
    rcases hs with h1 | h2 | ⟨hj,hjk,hij,h3⟩
    · rw [if_pos h1]
      simp [add,rawEncode,h1,encodeGate,hp _ hi,hp _ hk]
    · have h1 : g.1 ≠ 1 := by omega
      rw [if_neg h1,if_pos h2]
      simp [subtract,Reversible.inverse,add,rawEncode,h2,encodeGate,hp _ hi,hp _ hk]
    · have h1 : g.1 ≠ 1 := by omega
      have h2 : g.1 ≠ 2 := by omega
      rw [if_neg h1,if_neg h2,dif_pos ⟨hj,hjk,hij,h3⟩]
      simp [mulAdd,rawEncode,h0,h1,h2,encodeGate,hp _ hi,hp _ hj,hp _ hk]

theorem rawCircuit_codes (W : ℕ) (gs : List Raw) (hv : ∀ g ∈ gs, Valid W g) (pad : List Bool)
    (hp : ∀ i < W, pad.take i = List.replicate i true) :
    (rawCircuit W gs).gates.flatMap encodeGate = gs.flatMap (rawEncode pad) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change ((rawRev W g).gates++(rawCircuit W gs).gates).flatMap encodeGate = _
    rw [List.flatMap_append,rawEncode_correct W g (hv _ (by simp)) pad hp,
      ih (fun g hg => hv g (by simp [hg]))]
    rfl

def copyIndices (start : ℕ) (as : List ℕ) : List Raw :=
  (as.zip (List.range as.length)).map (fun x => (1,x.1,0,start+x.2))

theorem copyIndices_eq (start : ℕ) (as : List ℕ) : copyIndices start as = copyBlock start as := by
  have hlen : ∀ start as, (copyBlock start as).length = as.length := by
    intro start as
    induction as generalizing start with
    | nil => rfl
    | cons a as ih => simp [copyBlock,ih]
  have helem : ∀ start as i (hi : i < as.length),
      (copyBlock start as)[i]'(by rw [hlen]; exact hi) = (1,as[i],0,start+i) := by
    intro start as
    induction as generalizing start with
    | nil => intro i hi; simp at hi
    | cons a as ih =>
      intro i hi
      cases i with
      | zero => rfl
      | succ i =>
        simpa [copyBlock,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          (ih (start+1) i (by simpa using hi))
  apply List.ext_getElem
  · simp [copyIndices,hlen]
  · intro i hi hj
    simp only [copyIndices,List.getElem_map,List.getElem_zip,List.getElem_range]
    exact (helem start as i (by simpa [copyIndices] using hi)).symm

/-- A polynomially constructible supply of unary wire indices. -/
def wirePad (e : Env × List Token) : List Bool :=
  e.1.flatMap (fun _ => e.1.map (fun _ => true)) ++ e.1.map (fun _ => true) ++ [true] ++
    e.2.flatMap (fun _ => [true,true])

def serialize (x : (Env × List Token) × ((List Raw × ℕ) × List ℕ)) : List Bool :=
  let pad := wirePad x.1
  pad.take x.2.1.2 ++ [false] ++
    (x.2.1.1++copyIndices (L3.inputN x.1.1*L3.inputM x.1.1) x.2.2).flatMap (rawEncode pad)

@[fun_prop] theorem rawEncode_poly : Poly (fun x : List Bool × Raw => rawEncode x.1 x.2) := by
  unfold rawEncode
  dsimp only
  fun_prop

@[fun_prop] theorem rawEncode_comp {α : Type} [Coding α] {p : α → List Bool} {g : α → Raw}
    (hp : Poly p) (hg : Poly g) : Poly (fun x => rawEncode (p x) (g x)) :=
  Poly.comp rawEncode_poly (Poly.pair hp hg)

@[fun_prop] theorem copyIndices_poly : Poly (fun x : ℕ × List ℕ => copyIndices x.1 x.2) := by
  unfold copyIndices
  fun_prop

@[fun_prop] theorem copyIndices_comp {α : Type} [Coding α] {p : α → ℕ} {g : α → List ℕ}
    (hp : Poly p) (hg : Poly g) : Poly (fun x => copyIndices (p x) (g x)) :=
  Poly.comp copyIndices_poly (Poly.pair hp hg)

@[fun_prop] theorem wirePad_poly : Poly wirePad := by unfold wirePad; fun_prop
@[fun_prop] theorem serialize_poly : Poly serialize := by unfold serialize; fun_prop

theorem wirePad_length (e : Env × List Token) :
    (wirePad e).length = e.1.length*e.1.length+e.1.length+1+2*e.2.length := by
  simp [wirePad,List.length_flatMap]
  omega

theorem wirePad_true (e : Env × List Token) : wirePad e = List.replicate (wirePad e).length true := by
  apply List.eq_replicate_length.mpr
  intro b hb
  simp only [wirePad,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with ((⟨_,_,_,_,rfl⟩ | ⟨_,_,rfl⟩) | rfl) | ⟨_,_,rfl | rfl⟩ <;> rfl

theorem compile_pointer (I : ℕ) (ts : List Token) (state : (List Raw × ℕ) × List ℕ) :
    (ts.foldl (compileStep I) state).1.2 = state.1.2+2*ts.length := by
  induction ts generalizing state with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons,ih]
    change state.1.2+2+2*ts.length = state.1.2+2*(ts.length+1)
    omega

theorem compiled_pointer (n m : ℕ) : (compiled n m).1.2 = base n m+2*(code n m).length :=
  compile_pointer _ _ _

theorem serialize_correct (n m : ℕ) :
    serialize ((word n m,code n m),compiled n m) = encodeCircuit (circuit n m) := by
  let e := (word n m,code n m)
  have hW : (compiled n m).1.2  ≤  (wirePad e).length := by
    rw [compiled_pointer,wirePad_length]
    have hw : (word n m).length = n+m+1 := by simp [word,unaryD,unary]; omega
    change base n m+2*(code n m).length  ≤ 
      (word n m).length*(word n m).length+(word n m).length+1+2*(code n m).length
    rw [hw]
    dsimp [base]
    nlinarith
  have hp (i : ℕ) (hi : i  ≤  (compiled n m).1.2) : (wirePad e).take i = List.replicate i true := by
    rw [wirePad_true,List.take_replicate,Nat.min_eq_left (hi.trans hW)]
  have hcodes := rawCircuit_codes (compiled n m).1.2 (gates n m) (gates_valid n m)
    (wirePad e) (fun i hi => hp i (Nat.le_of_lt hi))
  unfold serialize encodeCircuit circuit
  rw [copyIndices_eq]
  change (wirePad e).take (compiled n m).1.2 ++ [false] ++
    ((compiled n m).1.1 ++ copyBlock (L3.inputN (word n m)*L3.inputM (word n m)) (compiled n m).2).flatMap
      (rawEncode (wirePad e)) = _
  rw [hp _ le_rfl,show L3.inputN (word n m) = n from L3.inputN_word n m,
    show L3.inputM (word n m) = m from L3.inputM_word n m]
  exact congrArg (fun gs => List.replicate (compiled n m).1.2 true ++ [false] ++ gs) hcodes.symm

end F3Generate

-- Source: Solutions.T31.Parameters

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

def parameterN (w : List Bool) := w.findIdx (! ·)
def afterN (w : List Bool) := w.drop (parameterN w+1)
def parameterM (w : List Bool) := (afterN w).findIdx (! ·)
def parameterT (w : List Bool) := ((afterN w).drop (parameterM w+1)).length

@[fun_prop] lemma parameterN_poly : Poly parameterN := by unfold parameterN; fun_prop
@[fun_prop] lemma afterN_poly : Poly afterN := by unfold afterN; fun_prop
@[fun_prop] lemma parameterM_poly : Poly parameterM := by unfold parameterM; fun_prop
@[fun_prop] lemma parameterT_poly : Poly parameterT := by unfold parameterT; fun_prop

def parameterWord (n m T : ℕ) := unaryD n++unaryD m++unary T
lemma findIdx_unaryD (n : ℕ) (bs : List Bool) : (unaryD n++bs).findIdx (! ·) = n := by
  induction n with
  | zero => simp [unaryD,unary,List.findIdx_cons]
  | succ n ih => simpa [unaryD,unary,List.replicate_succ,List.cons_append,List.findIdx_cons] using congrArg Nat.succ ih
lemma parameterWord_values (n m T : ℕ) :
    parameterN (parameterWord n m T) = n ∧ parameterM (parameterWord n m T) = m ∧ parameterT (parameterWord n m T) = T := by
  have hn : parameterN (parameterWord n m T) = n := by
    unfold parameterN parameterWord
    rw [List.append_assoc,findIdx_unaryD]
  have ha : afterN (parameterWord n m T) = unaryD m++unary T := by
    unfold afterN
    rw [hn]
    simp [parameterWord,unaryD,unary,List.drop_append]
  have hm : parameterM (parameterWord n m T) = m := by unfold parameterM; rw [ha,findIdx_unaryD]
  refine ⟨hn,hm,?_⟩
  unfold parameterT
  rw [ha,hm]
  simp [unaryD,unary,List.drop_append]
lemma parameter_bounds (w : List Bool) : parameterN w  ≤  w.length ∧ parameterM w  ≤  w.length ∧ parameterT w  ≤  w.length := by
  have hn := List.findIdx_le_length (p := (! ·)) (xs := w)
  have hm := List.findIdx_le_length (p := (! ·)) (xs := afterN w)
  have ha : (afterN w).length  ≤  w.length := by simp [afterN,parameterT]
  have ht : parameterT w  ≤  (afterN w).length := by simp only [parameterT,List.length_drop]; omega
  exact ⟨hn,hm.trans ha,ht.trans ha⟩
lemma parameterWord_length (n m T : ℕ) : (parameterWord n m T).length = n+m+T+2 := by
  simp [parameterWord,unaryD,unary]; omega

/-- A fixed-degree unary polynomial, generated by nested maps. -/
def powerPad (w : List Bool) : ℕ → List Bool
  | 0 => [true]
  | k+1 => (w++[true]).flatMap (fun _ => powerPad w k)
lemma powerPad_eq (w : List Bool) (k : ℕ) : powerPad w k = List.replicate ((w.length+1)^k) true := by
  induction k with
  | zero => simp [powerPad]
  | succ k ih =>
    simp only [powerPad,ih]
    have he : ∀ xs : List Bool, xs.flatMap (fun _ => List.replicate ((w.length+1)^k) true) =
        List.replicate (xs.length*((w.length+1)^k)) true := by
      intro xs
      induction xs with
      | nil => simp
      | cons a xs ih => simp [ih,Nat.add_mul,Nat.add_comm]
    rw [he]
    simp [pow_succ,Nat.mul_comm]
@[fun_prop] lemma powerPad_poly (k : ℕ) : Poly (fun w => powerPad w k) := by
  induction k with
  | zero => change Poly (fun _ : List Bool => [true]); fun_prop
  | succ k ih => unfold powerPad; fun_prop

def repeatedPad (w : List Bool) (k c : ℕ) := (List.replicate c true).flatMap (fun _ => powerPad w k)
lemma repeatedPad_eq (w : List Bool) (k c : ℕ) : repeatedPad w k c = List.replicate (c*(w.length+1)^k) true := by
  unfold repeatedPad
  rw [powerPad_eq]
  induction c with
  | zero => simp
  | succ c ih => simp [List.replicate_succ,ih,Nat.add_mul,Nat.add_comm]
@[fun_prop] lemma repeatedPad_poly (k c : ℕ) : Poly (fun w => repeatedPad w k c) := by unfold repeatedPad; fun_prop

def dimensionCoefficient (M : BinaryMachine) := Fintype.card (Option M.Label)+Fintype.card M.State+
  Fintype.card M.K*(machineGrowth M+20)
def wireCoefficient (M : BinaryMachine) := 131+8*dimensionCoefficient M*(2*phaseSize M+1)
def globalPad (M : BinaryMachine) (w : List Bool) := repeatedPad w 6 (wireCoefficient M+3)
def capCount (M : BinaryMachine) (w : List Bool) := 4*(parameterN w+parameterM w+1)^2+parameterT w*machineGrowth M+1
def generatorEnv (M : BinaryMachine) (w : List Bool) : GeneratorEnv :=
  ((repeatedPad w 2 (machineGrowth M+20)).take (capCount M w),globalPad M w)
@[fun_prop] lemma globalPad_poly (M : BinaryMachine) : Poly (globalPad M) := repeatedPad_poly _ _
@[fun_prop] lemma capCount_poly (M : BinaryMachine) : Poly (capCount M) := by unfold capCount; simp only [pow_two]; fun_prop
@[fun_prop] lemma generatorEnv_poly (M : BinaryMachine) : Poly (generatorEnv M) := by unfold generatorEnv; fun_prop

lemma capCount_bound (M : BinaryMachine) (w : List Bool) : capCount M w  ≤  (machineGrowth M+20)*(w.length+1)^2 := by
  obtain ⟨hn,hm,ht⟩ := parameter_bounds w
  have ha : parameterN w+parameterM w+1  ≤  2*(w.length+1) := by omega
  have hsq := Nat.mul_self_le_mul_self ha
  have ht' : parameterT w  ≤  (w.length+1)^2 := by nlinarith
  have hg := Nat.mul_le_mul_right (machineGrowth M) ht'
  dsimp only [capCount]
  nlinarith
lemma generatorEnv_capacity (M : BinaryMachine) (w : List Bool) :
    envCapacity (generatorEnv M w) = capacity M (parameterN w) (parameterM w) (parameterT w) := by
  simp only [generatorEnv,envCapacity,List.length_take,repeatedPad_eq,List.length_replicate,
    Nat.min_eq_left (capCount_bound M w)]
  dsimp only [capCount,capacity]
lemma globalPad_eq (M : BinaryMachine) (w : List Bool) : globalPad M w =
    List.replicate ((wireCoefficient M+3)*(w.length+1)^6) true := repeatedPad_eq _ _ _

end F3MachineCompiler

-- Source: Solutions.T31.GlobalBounds

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum
open Classical

lemma dimensions_bounded (M : BinaryMachine) (n m T L : ℕ) (hn : n  ≤  L) (hm : m  ≤  L) (ht : T  ≤  L) :
    dimension M (capacity M n m T)  ≤  dimensionCoefficient M*(L+1)^2 := by
  have ha : n+m+1  ≤  2*L+1 := by omega
  have hsq := Nat.mul_self_le_mul_self ha
  have hT : T  ≤  (L+1)^2 := by nlinarith
  have hg := Nat.mul_le_mul_right (machineGrowth M) hT
  have hcap : capacity M n m T  ≤  (machineGrowth M+20)*(L+1)^2 := by
    dsimp only [capacity]
    nlinarith
  have hK := Nat.mul_le_mul_left (Fintype.card M.K) hcap
  have hq : 1  ≤  (L+1)^2 := by nlinarith
  have hC := Nat.mul_le_mul_left (Fintype.card (Option M.Label)+Fintype.card M.State) hq
  dsimp only [dimension,dimensionCoefficient]
  nlinarith

lemma reserve_bounded (n m L : ℕ) (hn : n  ≤  L) (hm : m  ≤  L) : reserve n m  ≤  3*(L+1)^2 := by
  have hp := Nat.mul_le_mul hn hm
  dsimp only [reserve]
  nlinarith
lemma schedule_bounded (n m T j L : ℕ) (hn : n  ≤  L) (hm : m  ≤  L) (ht : T  ≤  L) (hj : j  ≤  L) :
    n*m+n+2*m+T+j+2  ≤  8*(L+1)^2 := by
  have hp := Nat.mul_le_mul hn hm
  nlinarith
lemma computation_global_bound (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j L : ℕ)
    (hn : n  ≤  L) (hm : m  ≤  L) (ht : T  ≤  L) (hj : j  ≤  L) :
    (computation M τ n m T j).1.2  ≤  wireCoefficient M*(L+1)^4 := by
  have h := computation_pointer_bound M τ n m T j
  have hr := reserve_bounded n m L hn hm
  have hd := dimensions_bounded M n m T L hn hm ht
  have hs := schedule_bounded n m T j L hn hm ht hj
  have hm₁ := Nat.mul_le_mul_left (2*phaseSize M+1) hd
  have hm₂ := Nat.mul_le_mul hs (Nat.mul_le_mul_right (2*phaseSize M+1) hd)
  have hq : 1  ≤  (L+1)^2 := by nlinarith
  have hq₂ : (L+1)^2  ≤  (L+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : (L+1)^2*(L+1)^2 = (L+1)^4 := by ring
  dsimp only [phaseBudget] at h
  dsimp only [wireCoefficient]
  nlinarith only [h,hr,hm₂,hq,hq₂,he]

lemma oracle_global_bound (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T L : ℕ)
    (hn : n  ≤  L) (hm : m  ≤  L) (ht : T  ≤  L) :
    oracleWidth M τ n m T  ≤  (wireCoefficient M+3)*(L+1)^6 := by
  have hb : ∑ j : Fin n, (computation M τ n m T j.val).1.2  ≤  n*(wireCoefficient M*(L+1)^4) := by
    calc
      _  ≤  ∑ _j : Fin n, wireCoefficient M*(L+1)^4 := Finset.sum_le_sum (fun j _ =>
        computation_global_bound M τ n m T j.val L hn hm ht (Nat.le_trans (Nat.le_of_lt j.isLt) hn))
      _ = _ := by simp [Nat.mul_comm]
  have hr := reserve_bounded n m L hn hm
  have hp : n*(wireCoefficient M*(L+1)^4)  ≤  (L+1)*(wireCoefficient M*(L+1)^4) :=
    Nat.mul_le_mul_right _ (by omega)
  have hq₂ : (L+1)^2  ≤  (L+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hq₅ : (L+1)^5  ≤  (L+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have he : (L+1)*(wireCoefficient M*(L+1)^4) = wireCoefficient M*(L+1)^5 := by ring
  have hcp := Nat.mul_le_mul_left (wireCoefficient M) hq₅
  dsimp only [oracleWidth]
  nlinarith only [hb,hr,hp,hq₂,he,hcp]

lemma computation_globalPad (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) (j : ℕ)
    (hj : j  ≤  w.length) :
    (computation M τ (parameterN w) (parameterM w) (parameterT w) j).1.2  ≤  (globalPad M w).length := by
  obtain ⟨hn,hm,ht⟩ := parameter_bounds w
  have h := computation_global_bound M τ _ _ _ j w.length hn hm ht hj
  have hp : (w.length+1)^4  ≤  (w.length+1)^6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hc := Nat.mul_le_mul (by omega : wireCoefficient M  ≤  wireCoefficient M+3) hp
  rw [globalPad_eq,List.length_replicate]
  exact h.trans hc

end F3MachineCompiler

-- Source: Solutions.T31.ParallelArithmetic

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3Tools F3SubsetSum

/-- An instruction reads no value from the specified register. -/
def ReadFree (j : ℕ) (g : Raw) : Prop :=
  g.1 = 0 ∨ (g.2.1 ≠ j ∧ (g.1 = 1 ∨ g.1 = 2 ∨ g.2.2.1 ≠ j))

lemma rawValue_readFree (j : ℕ) (g : Raw) (h : ReadFree j g) (y : ℕ → ZMod 3) (v : ZMod 3) :
    rawValue g (Function.update y j v) = rawValue g y := by
  unfold rawValue
  rcases h with h0|⟨hi,hg⟩
  · simp [h0]
  · by_cases h0 : g.1 = 0
    · simp [h0]
    rcases hg with h1|h2|hj
    · simp [h1,Function.update_of_ne hi]
    · simp [h2,Function.update_of_ne hi]
    · simp [Function.update_of_ne hi,Function.update_of_ne hj]

lemma rawRun_parallel (gs : List Raw)
    (hfree : ∀ g ∈ gs, ∀ h ∈ gs, ReadFree g.2.2.2 h)
    (y : ℕ → ZMod 3) (k : ℕ) :
    rawRun gs y k = y k+(gs.map (fun g => if g.2.2.2 = k then rawValue g y else 0)).sum := by
  induction gs generalizing y with
  | nil => simp [rawRun]
  | cons g gs ih =>
    change rawRun gs (rawStep g y) k = _
    rw [ih (fun g hg h hh => hfree g (by simp [hg]) h (by simp [hh]))]
    have he : (gs.map (fun h => if h.2.2.2 = k then rawValue h (rawStep g y) else 0)).sum =
        (gs.map (fun h => if h.2.2.2 = k then rawValue h y else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro h hh
      rw [rawStep,rawValue_readFree g.2.2.2 h (hfree g (by simp) h (by simp [hh]))]
    rw [he]
    simp only [List.map_cons,List.sum_cons,rawStep,Function.update_apply]
    by_cases hk : k = g.2.2.2 <;> simp [hk,eq_comm] <;> ring

end F3Reduction

-- Source: Solutions.T31.FrameAction

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

lemma sum_three_reverse {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ]
    [AddCommMonoid δ] (f : α → β → γ → δ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma range_word_frame {n m W : ℕ} (A : Instance n m) (ψ : Word m × Secret n → ℂ)
    (hW : n*m+m  ≤  W) (M : Matrix (ZMod 3) (ZMod 3) ℂ) :
    rangeApply M (n*m) m hW (frame A ψ) =
      frame A (fun p => matApply (tensorMatrix (fun _ : Fin m => M)) (fun b => ψ (b,p.2)) p.1) := by
  rw [frame_expand,← rangeLinear_apply,map_sum]
  simp_rw [map_smul,rangeLinear_apply,range_word_basis A _ _ hW M]
  rw [frame_expand]
  funext y
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Fintype.sum_prod_type,Finset.mul_sum,
    matApply,tensorMatrix,Finset.sum_mul]
  rw [sum_three_reverse]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma range_uInv_frame {n m W : ℕ} (A : Instance n m) (ψ : Word m × Secret n → ℂ)
    (hW : n*m+m  ≤  W) :
    rangeApply uMat.conjTranspose (n*m) m hW (frame A ψ) = frame A (pairTransform ψ) :=
  range_word_frame A ψ hW uMat.conjTranspose

end F3Reduction

-- Source: Solutions.T31.MassTransfer

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum F3Tools
open Classical

noncomputable def mask {ι : Type} (P : ι → Prop) (ψ : ι → ℂ) : ι → ℂ :=
  fun i => if P i then ψ i else 0

lemma energy_mask {ι : Type} [Fintype ι] (P : ι → Prop) (ψ : ι → ℂ) :
    energy (mask P ψ) = mass P ψ := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : P i <;> simp [mask,hp]

lemma mask_push {ι κ : Type} [Fintype ι] (f : ι → κ) (P : κ → Prop) (ψ : ι → ℂ) :
    mask P (push f ψ) = push f (mask (fun i => P (f i)) ψ) := by
  funext y
  simp only [mask,push,matApply]
  by_cases hp : P y
  · rw [if_pos hp]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases he : f i = y
    · simp [he,hp]
    · simp [he]
  · rw [if_neg hp]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    by_cases he : f i = y <;> simp [he,hp]

lemma mass_push {ι κ : Type} [Fintype ι] [Fintype κ] (f : ι → κ)
    (hf : Function.Injective f) (P : κ → Prop) (ψ : ι → ℂ) :
    mass P (push f ψ) = mass (fun i => P (f i)) ψ := by
  rw [← energy_mask,mask_push,push_energy_injective f hf,energy_mask]

lemma mass_mono {ι : Type} [Fintype ι] (P Q : ι → Prop) (h : ∀ i, P i → Q i) (ψ : ι → ℂ) :
    mass P ψ  ≤  mass Q ψ := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases hp : P i
  · simp [hp,h i hp]
  · simp only [hp,ite_false]
    by_cases hq : Q i <;> simp [hq,Complex.normSq_nonneg]

lemma reversible_push {ι : Type} [Fintype ι] {W : ℕ} (C : Reversible W)
    (f : ι → QBasis W) (ψ : ι → ℂ) :
    C.gates.foldl (fun φ g => applyGate g φ) (push f ψ) = push (C.forward ∘ f) ψ := by
  rw [C.action]
  funext y
  simp only [push,matApply,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have he : f i = C.backward y ↔ C.forward (f i) = y := by
    constructor
    · intro h; rw [h,C.right_inv]
    · intro h; rw [← h,C.left_inv]
  simp only [he]
  by_cases hh : C.forward (f i) = y <;> simp only [if_pos,if_neg,hh]

lemma reversible_mass_transfer {ι : Type} [Fintype ι] {W : ℕ} (C : Reversible W)
    (f : ι → QBasis W) (hf : Function.Injective f) (P : ι → Prop) (Q : QBasis W → Prop)
    (hgood : ∀ i, P i → Q (C.forward (f i))) (ψ : ι → ℂ) :
    mass P ψ  ≤  mass Q (C.gates.foldl (fun φ g => applyGate g φ) (push f ψ)) := by
  rw [reversible_push,mass_push _ (C.left_inv.injective.comp hf)]
  exact mass_mono P _ hgood ψ

end F3Reduction

-- Source: Solutions.T31.Preparation

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

lemma sqrt_natpow (a : ℝ) (ha : 0  ≤  a) (n : ℕ) : Real.sqrt (a^n) = (Real.sqrt a)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg ha n),ih,pow_succ]

lemma normalizer_product (n m : ℕ) :
    normalizer n m = (1/(Real.sqrt 3 : ℂ))^n*(1/(Real.sqrt 2 : ℂ))^m := by
  simp only [normalizer,pairCount,Real.sqrt_mul (by positivity : 0  ≤  (3:ℝ)^n),
    sqrt_natpow 3 (by positivity) n,sqrt_natpow 2 (by positivity) m,
    Complex.ofReal_mul,Complex.ofReal_pow,one_div,mul_inv_rev,inv_pow]
  ring

lemma p_zero_scaled (b : ZMod 3) : pMat b 0 = (1/(Real.sqrt 2 : ℂ))*scaledNot 0 b := by
  rcases cases_three b with rfl | rfl | rfl <;> simp [pMat,scaledNot] <;> ring

lemma fourier_zero (b : ZMod 3) : fourierMat b 0 = 1/(Real.sqrt 3 : ℂ) := by simp [fourierMat]

lemma preparation_coefficient {n m : ℕ} (s : Secret n) (b : Word m) :
    (∏ j, fourierMat (s j) 0)*(∏ i, pMat (b i) 0) =
      normalizer n m*∑ e : Errors m, if delta e = b then sign e else 0 := by
  simp_rw [fourier_zero,p_zero_scaled]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← mul_assoc,← normalizer_product]
  have hs := scaledNot_product m (0 : Word m) b
  simp only [Pi.zero_apply,zero_add] at hs
  rw [hs]

lemma p_prepared_basis {n m W : ℕ} (A : Instance n m) (s : Secret n) (hW : n*m+m  ≤  W) :
    rangeApply pMat (n*m) m hW (basisKet (decoderBasis n m W A 0 s)) =
      (1/(Real.sqrt 2 : ℂ))^m • ∑ e : Errors m,
        sign e • basisKet (decoderBasis n m W A (delta e) s) := by
  rw [range_word_basis]
  change (∑ b : Word m, (∏ i, pMat (b i) 0) • basisKet (decoderBasis n m W A b s)) = _
  have hp (b : Word m) :
      (∏ i, (1/(Real.sqrt 2 : ℂ))*scaledNot 0 (b i)) =
        (1/(Real.sqrt 2 : ℂ))^m*(∑ e : Errors m, if delta e = b then sign e else 0) := by
    rw [Finset.prod_mul_distrib]
    have hs := scaledNot_product m (0 : Word m) b
    simp only [Pi.zero_apply,zero_add] at hs
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,hs]
  simp_rw [p_zero_scaled,hp,mul_smul]
  rw [← Finset.smul_sum]
  congr 1
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hh : (∑ b : Word m, (if delta e = b then sign e else 0) •
      basisKet (decoderBasis n m W A b s)) = sign e • basisKet (decoderBasis n m W A (delta e) s) := by
    simp [eq_comm]
  exact hh

lemma prepared_basis {n m W : ℕ} (A : Instance n m) (hW : n*m+m+n  ≤  W) :
    rangeApply pMat (n*m) m (by omega)
      (rangeApply fourierMat (n*m+m) n hW (basisKet (decoderBasis n m W A 0 0))) =
      ∑ x : Pair n m, (normalizer n m*sign x.2) •
        basisKet (decoderBasis n m W A (delta x.2) x.1) := by
  have hf := range_secret_basis A (0 : Word m) (0 : Secret n) hW fourierMat
  change rangeApply fourierMat (n*m+m) n hW (basisKet (decoderBasis n m W A 0 0)) =
    ∑ s : Secret n, (∏ j, fourierMat (s j) 0) • basisKet (decoderBasis n m W A 0 s) at hf
  simp_rw [fourier_zero] at hf
  rw [hf]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← rangeLinear_apply,map_sum]
  have hw : n*m+m  ≤  W := by omega
  simp_rw [map_smul,rangeLinear_apply,p_prepared_basis A _ hw,smul_smul]
  simp_rw [Finset.smul_sum,smul_smul]
  simp only [Pair,Fintype.sum_prod_type,normalizer_product]

end F3Reduction

-- Source: Solutions.T31.NotStates

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3Tools F3SubsetSum Matrix
open Classical

lemma range_finRange (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

lemma notStates_fin (n m : ℕ) : notStates n m =
    (List.finRange m).flatMap (fun i => (List.finRange n).map
      (fun j => (3,n*i.val+j.val,n*m+m+j.val,n*m+i.val))) := by
  rw [notStates,range_finRange m,range_finRange n]
  simp only [List.flatMap_map,List.map_map,Function.comp_apply]
  rfl

lemma notStates_readFree (n m : ℕ) :
    ∀ g ∈ notStates n m, ∀ h ∈ notStates n m, ReadFree g.2.2.2 h := by
  rw [notStates_fin]
  intro g hg
  obtain ⟨i,_,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  intro h hh
  obtain ⟨i',_,hh⟩ := List.mem_flatMap.mp hh
  obtain ⟨j',_,rfl⟩ := List.mem_map.mp hh
  have ha : n*i'.val+j'.val < n*m := by nlinarith [i'.isLt,j'.isLt]
  have hi := i.isLt
  simp only [ReadFree]
  right
  exact ⟨by omega,Or.inr (Or.inr (by omega))⟩

lemma notStates_valid (n m W : ℕ) (hW : n*m+m+n  ≤  W) :
    ∀ g ∈ notStates n m, Valid W g := by
  rw [notStates_fin]
  intro g hg
  obtain ⟨i,_,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  have ha : n*i.val+j.val < n*m := by nlinarith [i.isLt,j.isLt]
  have hi := i.isLt
  have hj := j.isLt
  simp [Valid]
  omega

lemma list_sum_flatMap {α β γ : Type} [AddCommMonoid γ] (xs : List α) (f : α → List β) (g : β → γ) :
    ((xs.flatMap f).map g).sum = (xs.map (fun a => ((f a).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons,List.map_append,List.sum_append,ih]

lemma notStates_sum {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) (k : ℕ) :
    ((notStates n m).map (fun g => if g.2.2.2 = k then rawValue g (decoderRegisters A b r) else 0)).sum =
      ∑ i : Fin m, ∑ j : Fin n, if n*m+i.val = k then A j i*r j else 0 := by
  rw [notStates_fin,list_sum_flatMap]
  simp only [List.map_map,Function.comp_apply,rawValue,show ¬(3:ℕ) = 0 by decide,if_false,
    show ¬(3:ℕ) = 1 by decide,show ¬(3:ℕ) = 2 by decide,
    decoderRegisters_matrix,decoderRegisters_secret]
  simp only [← List.ofFn_eq_map,List.sum_ofFn]
  simp [Function.comp_apply,rawValue,decoderRegisters_matrix,decoderRegisters_secret]

lemma notStates_word {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) (i : Fin m) :
    rawRun (notStates n m) (decoderRegisters A b r) (n*m+i.val) = b i+(Aᵀ *ᵥ r) i := by
  rw [rawRun_parallel _ (notStates_readFree n m),decoderRegisters_word,notStates_sum]
  simp only [Nat.add_left_cancel_iff,Fin.val_inj]
  simp [Matrix.mulVec,dotProduct]

lemma notStates_outside {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) (k : ℕ)
    (hk : k < n*m ∨ n*m+m  ≤  k) :
    rawRun (notStates n m) (decoderRegisters A b r) k = decoderRegisters A b r k := by
  rw [rawRun_parallel _ (notStates_readFree n m),notStates_sum]
  have hs : (∑ i : Fin m, ∑ j : Fin n, if n*m+i.val = k then A j i*r j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg (by have := i.isLt; omega)]
  rw [hs,add_zero]

lemma notStates_forward {n m : ℕ} (A : Instance n m) (b : Word m) (r : Secret n) :
    rawRun (notStates n m) (decoderRegisters A b r) = decoderRegisters A (b+Aᵀ *ᵥ r) r := by
  funext k
  by_cases hA : k < n*m
  · rw [notStates_outside A b r k (Or.inl hA)]
    simp only [decoderRegisters,dif_pos hA]
  · by_cases hb : k < n*m+m
    · let i : Fin m := ⟨k-n*m,by omega⟩
      have he : k = n*m+i.val := by dsimp [i]; omega
      rw [he,notStates_word,decoderRegisters_word]
      rfl
    · rw [notStates_outside A b r k (Or.inr (by omega))]
      simp only [decoderRegisters,dif_neg hA,dif_neg hb]

lemma rawCircuit_gates (W : ℕ) (gs : List Raw) :
    (rawCircuit W gs).gates = gs.flatMap (fun g => (rawRev W g).gates) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp only [rawCircuit,Reversible.then,List.flatMap_cons,ih]

lemma notStates_basis {n m W : ℕ} (A : Instance n m) (b : Word m) (r : Secret n)
    (hW : n*m+m+n  ≤  W) :
    ((notStates n m).flatMap (fun g => (rawRev W g).gates)).foldl (fun φ g => applyGate g φ)
      (basisKet (decoderBasis n m W A b r)) =
      basisKet (decoderBasis n m W A (b+Aᵀ *ᵥ r) r) := by
  rw [← rawCircuit_gates,(rawCircuit W (notStates n m)).basis]
  rw [decoderRegisters_basis,rawCircuit_forward W _ (notStates_valid n m W hW),notStates_forward]
  rw [← decoderRegisters_basis]

end F3Reduction

-- Source: Solutions.T31.ScheduleGenerator

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

def boundedRange (w : List Bool) (k : ℕ) := (List.range w.length).take k
@[fun_prop] lemma boundedRange_poly : Poly (fun x : List Bool × ℕ => boundedRange x.1 x.2) := by unfold boundedRange; fun_prop
@[fun_prop] lemma boundedRange_comp {α : Type} [Coding α] {w : α → List Bool} {k : α → ℕ}
    (hw : Poly w) (hk : Poly k) : Poly (fun a => boundedRange (w a) (k a)) := Poly.comp boundedRange_poly (Poly.pair hw hk)
lemma boundedRange_eq (w : List Bool) (k : ℕ) : boundedRange w k = List.range (min k w.length) := List.take_range

def scheduleFromWord (x : List Bool × ℕ) : List Phase :=
  let w := x.1
  let n := parameterN w
  let m := parameterM w
  ((boundedRange w m).flatMap (fun i => (boundedRange w n).map (fun j => (2,n*i+j))) ++
    (boundedRange w m).map (fun i => (3,n*m+i))).reverse ++
  (bitSchedule (((w.take n).map (fun _ => true)++[false])++((w.take m).map (fun _ => true)++[false]))).reverse ++
  (boundedRange w (parameterT w)).map (fun _ => (4,0)) ++
  (boundedRange w x.2).map (fun _ => (5,0))
@[fun_prop] lemma scheduleFromWord_poly : Poly scheduleFromWord := by
  unfold scheduleFromWord bitSchedule
  fun_prop
lemma take_map_true (w : List Bool) (k : ℕ) : (w.take k).map (fun _ => true) = List.replicate (min k w.length) true := by
  simp [List.map_const',List.length_take]
lemma scheduleFromWord_eq (w : List Bool) (j : ℕ) :
    scheduleFromWord (w,j) = decoderSchedule (parameterN w) (parameterM w) (parameterT w) (min j w.length) := by
  obtain ⟨hn,hm,ht⟩ := parameter_bounds w
  simp only [scheduleFromWord,boundedRange_eq,Nat.min_eq_left hn,Nat.min_eq_left hm,Nat.min_eq_left ht,
    take_map_true,List.length_take,Nat.min_eq_left hn,Nat.min_eq_left hm,List.map_const',List.length_range,decoderSchedule,unaryD,unary]
  congr 3
  unfold dataSchedule
  simp only [F3Reduction.range_finRange,List.flatMap_map,List.map_map]
  rfl

noncomputable def coordinateFromWord (M : BinaryMachine) (τ : Bool ≃ Bool) (x : List Bool × ℕ) : CompileState :=
  coordinateGenerator M τ ((generatorEnv M x.1,reserve (parameterN x.1) (parameterM x.1)),scheduleFromWord x)
@[fun_prop] lemma coordinateFromWord_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (coordinateFromWord M τ) := by
  unfold coordinateFromWord reserve
  apply Poly.comp (coordinateGenerator_poly M τ)
  fun_prop

lemma phaseLoop_pointer_congr (M : BinaryMachine) (τ : Bool ≃ Bool) (N N' : ℕ)
    (hN : 2  ≤  N) (hN' : 2  ≤  N') (he : N = N') (seed : ℕ) (ps : List Phase) :
    (phaseLoop τ hN ps (initialSimulation M N seed)).pointer =
      (phaseLoop τ hN' ps (initialSimulation M N' seed)).pointer := by subst N'; rfl

noncomputable def phaseLoopOutput (M : BinaryMachine) (τ : Bool ≃ Bool) (N : ℕ) (hN : 2  ≤  N)
    (seed : ℕ) (ps : List Phase) : CompileState :=
  let S := phaseLoop τ hN ps (initialSimulation M N seed)
  ((S.gates++(one S.pointer (parsedTrit τ hN S.registers)).1.1,
    (one S.pointer (parsedTrit τ hN S.registers)).1.2),[result S.pointer (parsedTrit τ hN S.registers)])
lemma phaseLoopOutput_congr (M : BinaryMachine) (τ : Bool ≃ Bool) (N N' : ℕ)
    (hN : 2  ≤  N) (hN' : 2  ≤  N') (he : N = N') (seed : ℕ) (ps : List Phase) :
    phaseLoopOutput M τ N hN seed ps = phaseLoopOutput M τ N' hN' seed ps := by subst N'; rfl

lemma coordinateFromWord_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) (j : ℕ)
    (hj : j  ≤  w.length) : coordinateFromWord M τ (w,j) =
    computation M τ (parameterN w) (parameterM w) (parameterT w) j := by
  let n := parameterN w
  let m := parameterM w
  let T := parameterT w
  have hN : envCapacity (generatorEnv M w) = capacity M n m T := generatorEnv_capacity M w
  have hps := decoderSchedule_indices n m T j
  have hlimit : (answerSimulation M τ n m T j).pointer  ≤  (globalPad M w).length := by
    have hq := computation_globalPad M τ w j hj
    have hs := answerSimulation_resources M τ n m T j
    have he := one_inv (answerSimulation M τ n m T j).pointer (answerExpression M τ n m T j)
      (inputs_bounded _ _ (parsedTrit_inputs _ τ (capacity_ge_two M n m T) _ hs.1))
      (fun _ => 0) (by simp)
    have hg : (answerSimulation M τ n m T j).pointer  ≤  (computation M τ n m T j).1.2 := by
      change _  ≤  (one _ _).1.2
      rw [he.2.2.1]
      omega
    exact hg.trans hq
  unfold coordinateFromWord
  rw [scheduleFromWord_eq,Nat.min_eq_left hj]
  -- Normalize the dependent symbolic capacity before applying the generic generator theorem.
  have hc := coordinateGenerator_correct M τ (generatorEnv M w) (reserve n m) (decoderSchedule n m T j) hps
  have hl : (phaseLoop τ (envCapacity_two (generatorEnv M w)) (decoderSchedule n m T j)
      (initialSimulation M (envCapacity (generatorEnv M w)) (reserve n m))).pointer  ≤  (generatorEnv M w).2.length := by
    rw [phaseLoop_pointer_congr M τ _ _ _ (capacity_ge_two M n m T) hN,decoderSchedule_correct]
    exact hlimit
  have hh := hc hl
  change coordinateGenerator M τ _ = phaseLoopOutput M τ _ _ _ _ at hh
  rw [phaseLoopOutput_congr M τ _ _ _ (capacity_ge_two M n m T) hN] at hh
  unfold phaseLoopOutput at hh
  rw [decoderSchedule_correct] at hh
  exact hh

end F3MachineCompiler

-- Source: Solutions.T31.Postprocessing

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3Tools F3SubsetSum
open Classical

lemma postprocess_fin (n k : ℕ) : postprocess n (k+1) =
    (List.finRange k).map (fun i => (2,n*(k+1)+k,0,n*(k+1)+i.val)) := by
  simp only [postprocess,Nat.add_sub_cancel,range_finRange,List.map_map]
  rfl

lemma postprocess_readFree (n k : ℕ) :
    ∀ g ∈ postprocess n (k+1), ∀ h ∈ postprocess n (k+1), ReadFree g.2.2.2 h := by
  rw [postprocess_fin]
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  intro h hh
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hh
  have hi := i.isLt
  simp only [ReadFree]
  right
  exact ⟨by omega,Or.inr (Or.inl True.intro)⟩

lemma postprocess_valid (n k W : ℕ) (hW : n*(k+1)+(k+1)  ≤  W) :
    ∀ g ∈ postprocess n (k+1), Valid W g := by
  rw [postprocess_fin]
  intro g hg
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg
  have hi := i.isLt
  simp [Valid]
  omega

lemma postprocess_sum {n k : ℕ} (A : Instance n (k+1)) (c : Word (k+1)) (r : Secret n) (t : ℕ) :
    ((postprocess n (k+1)).map (fun g => if g.2.2.2 = t then rawValue g (decoderRegisters A c r) else 0)).sum =
      ∑ i : Fin k, if n*(k+1)+i.val = t then -c (Fin.last k) else 0 := by
  rw [postprocess_fin]
  simp only [List.map_map,← List.ofFn_eq_map,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,rawValue,show ¬(2:ℕ) = 0 by decide,if_false,
    show ¬(2:ℕ) = 1 by decide,ite_true]
  have hh := decoderRegisters_word A c r (Fin.last k)
  change decoderRegisters A c r (n*(k+1)+k) = c (Fin.last k) at hh
  rw [hh]

lemma postprocess_word {n k : ℕ} (A : Instance n (k+1)) (c : Word (k+1)) (r : Secret n) (i : Fin (k+1)) :
    rawRun (postprocess n (k+1)) (decoderRegisters A c r) (n*(k+1)+i.val) =
      if i = Fin.last k then c i else c i-c (Fin.last k) := by
  rw [rawRun_parallel _ (postprocess_readFree n k),decoderRegisters_word,postprocess_sum]
  by_cases hi : i = Fin.last k
  · subst i
    have hz : (∑ j : Fin k, if n*(k+1)+j.val = n*(k+1)+(Fin.last k).val then -c (Fin.last k) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg (by have := j.isLt; change ¬n*(k+1)+j.val = n*(k+1)+k; omega)]
    rw [hz,add_zero,if_pos rfl]
  · have hik : i.val < k := by
      have hin := i.isLt
      have hine : i.val ≠ k := fun hh => hi (Fin.ext hh)
      omega
    let j : Fin k := ⟨i.val,hik⟩
    have hs : (∑ l : Fin k, if n*(k+1)+l.val = n*(k+1)+i.val then -c (Fin.last k) else 0) =
        -c (Fin.last k) := by
      change (∑ l : Fin k, if n*(k+1)+l.val = n*(k+1)+j.val then -c (Fin.last k) else 0) = _
      simp only [Nat.add_left_cancel_iff,Fin.val_inj]
      simp
    rw [hs,if_neg hi,sub_eq_add_neg]

lemma relativeSigns_nonzero {m : ℕ} (a : Fin m) (c : Word m) (hc : ∀ i, c i ≠ 0) (i : Fin m) :
    relativeSigns a c i ≠ 0 ↔ i = a ∨ c i ≠ c a := by
  by_cases hi : i = a
  · simp [relativeSigns,hi]
  · have hci := hc i
    have hca := hc a
    rcases cases_three (c i) with he|he|he <;>
      rcases cases_three (c a) with hf|hf|hf <;> simp_all [relativeSigns]

lemma mem_outSet {n m W : ℕ} (y : QBasis W) (hW : n*m+m  ≤  W) (i : Fin m) :
    i ∈ outSet n m y ↔ y ⟨n*m+i.val,by have := i.isLt; omega⟩ ≠ 0 := by
  simp only [outSet,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hi,h⟩
    exact h
  · intro h
    exact ⟨by have := i.isLt; omega,h⟩

lemma postprocess_set {n k W : ℕ} (A : Instance n (k+1)) (c : Word (k+1)) (r : Secret n)
    (hW : n*(k+1)+(k+1)+n  ≤  W) (hc : ∀ i, c i ≠ 0) :
    outSet n (k+1) ((rawCircuit W (postprocess n (k+1))).forward (decoderBasis n (k+1) W A c r)) =
      Finset.univ.filter (fun i => relativeSigns (Fin.last k) c i ≠ 0) := by
  apply Finset.ext
  intro i
  rw [mem_outSet _ (by omega),decoderRegisters_basis,
    rawCircuit_forward W _ (postprocess_valid n k W (by omega))]
  dsimp only
  rw [postprocess_word]
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,relativeSigns_nonzero _ c hc i]
  by_cases hi : i = Fin.last k
  · simp [hi,hc]
  · simp [hi,sub_ne_zero]

end F3Reduction

-- Source: Solutions.T31.ColumnTransform

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3Tools F3SubsetSum
open Classical

lemma transform_fin (n k : ℕ) : transform n (k+1) 2 =
    (List.finRange k).flatMap (fun i => (List.finRange n).map
      (fun j => (2,n*i.val+j.val,0,n*k+j.val))) := by
  simp only [transform,Nat.add_sub_cancel,range_finRange,List.flatMap_map,List.map_map]
  rfl

lemma transform_readFree (n k : ℕ) :
    ∀ g ∈ transform n (k+1) 2, ∀ h ∈ transform n (k+1) 2, ReadFree g.2.2.2 h := by
  rw [transform_fin]
  intro g hg
  obtain ⟨i,_,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  intro h hh
  obtain ⟨i',_,hh⟩ := List.mem_flatMap.mp hh
  obtain ⟨j',_,rfl⟩ := List.mem_map.mp hh
  have hs : n*i'.val+j'.val < n*k := by nlinarith [i'.isLt,j'.isLt]
  simp only [ReadFree]
  right
  exact ⟨by omega,Or.inr (Or.inl True.intro)⟩

lemma transform_valid (n k W : ℕ) (hW : n*(k+1)  ≤  W) :
    ∀ g ∈ transform n (k+1) 2, Valid W g := by
  rw [transform_fin]
  intro g hg
  obtain ⟨i,_,hg⟩ := List.mem_flatMap.mp hg
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
  have hs : n*i.val+j.val < n*k := by nlinarith [i.isLt,j.isLt]
  have ht : n*k+j.val < n*(k+1) := by nlinarith [j.isLt]
  simp [Valid]
  omega

lemma sum_erase_last {α : Type} [AddCommGroup α] {k : ℕ} (f : Fin (k+1) → α) :
    (∑ i ∈ Finset.univ.erase (Fin.last k), f i) = ∑ i : Fin k, f i.castSucc := by
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ (Fin.last k))
  rw [Fin.sum_univ_castSucc] at h
  exact add_right_cancel h

lemma transform_sum {n k : ℕ} (h : Fin (k+1) → Fin n → ZMod 3)
    (b : Word (k+1)) (r : Secret n) (t : ℕ) :
    ((transform n (k+1) 2).map (fun g => if g.2.2.2 = t then
      rawValue g (decoderRegisters (fun j i => h i j) b r) else 0)).sum =
      ∑ i : Fin k, ∑ j : Fin n, if n*k+j.val = t then -h i.castSucc j else 0 := by
  rw [transform_fin,list_sum_flatMap]
  simp only [List.map_map,← List.ofFn_eq_map,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,rawValue,show ¬(2:ℕ) = 0 by decide,if_false,
    show ¬(2:ℕ) = 1 by decide,ite_true]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he := decoderRegisters_matrix (fun j i => h i j) b r i.castSucc j
  change decoderRegisters (fun j i => h i j) b r (n*i.val+j.val) = h i.castSucc j at he
  rw [he]

lemma transform_entry {n k : ℕ} (h : Fin (k+1) → Fin n → ZMod 3)
    (b : Word (k+1)) (r : Secret n) (i : Fin (k+1)) (j : Fin n) :
    rawRun (transform n (k+1) 2) (decoderRegisters (fun j i => h i j) b r) (n*i.val+j.val) =
      shiftedColumns (Fin.last k) h i j := by
  rw [rawRun_parallel _ (transform_readFree n k),decoderRegisters_matrix,transform_sum]
  by_cases hi : i = Fin.last k
  · subst i
    change h (Fin.last k) j+(∑ a : Fin k, ∑ z : Fin n,
      if n*k+z.val = n*k+j.val then -h a.castSucc z else 0) = _
    simp only [Nat.add_left_cancel_iff,Fin.val_inj]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [Finset.sum_neg_distrib]
    simp only [shiftedColumns,Function.update_self,sum_erase_last,Pi.sub_apply,Finset.sum_apply]
    ring
  · have hik : i.val < k := by
      have hin := i.isLt
      have hine : i.val ≠ k := fun hh => hi (Fin.ext hh)
      omega
    have hs : n*i.val+j.val < n*k := by nlinarith [j.isLt]
    have hz : (∑ a : Fin k, ∑ z : Fin n,
        if n*k+z.val = n*i.val+j.val then -h a.castSucc z else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro z hz
      rw [if_neg (by omega)]
    rw [hz,add_zero]
    simp only [shiftedColumns,Function.update_of_ne hi]

lemma transform_outside {n k : ℕ} (h : Fin (k+1) → Fin n → ZMod 3)
    (b : Word (k+1)) (r : Secret n) (t : ℕ) (ht : n*(k+1)  ≤  t) :
    rawRun (transform n (k+1) 2) (decoderRegisters (fun j i => h i j) b r) t =
      decoderRegisters (fun j i => h i j) b r t := by
  rw [rawRun_parallel _ (transform_readFree n k),transform_sum]
  have hz : (∑ a : Fin k, ∑ z : Fin n,
      if n*k+z.val = t then -h a.castSucc z else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro z hz
    rw [if_neg (by have := z.isLt; nlinarith)]
  rw [hz,add_zero]

lemma transform_forward {n k : ℕ} (h : Fin (k+1) → Fin n → ZMod 3)
    (b : Word (k+1)) (r : Secret n) :
    rawRun (transform n (k+1) 2) (decoderRegisters (fun j i => h i j) b r) =
      decoderRegisters (fun j i => shiftedColumns (Fin.last k) h i j) b r := by
  funext t
  by_cases ht : t < n*(k+1)
  · have hn : 0 < n := by
      by_contra hh
      have he : n = 0 := by omega
      subst n
      simp at ht
    let i : Fin (k+1) := ⟨t/n,Nat.div_lt_of_lt_mul ht⟩
    let j : Fin n := ⟨t%n,Nat.mod_lt _ hn⟩
    have he : t = n*i.val+j.val := by
      dsimp only [i,j]
      exact (Nat.div_add_mod t n).symm
    rw [he,transform_entry,decoderRegisters_matrix]
  · rw [transform_outside h b r t (by omega)]
    simp only [decoderRegisters,dif_neg ht]

lemma transform_basis {n k W : ℕ} (h : Fin (k+1) → Fin n → ZMod 3)
    (b : Word (k+1)) (r : Secret n) (hW : n*(k+1)  ≤  W) :
    ((transform n (k+1) 2).flatMap (fun g => (rawRev W g).gates)).foldl (fun φ g => applyGate g φ)
      (basisKet (decoderBasis n (k+1) W (fun j i => h i j) b r)) =
      basisKet (decoderBasis n (k+1) W (fun j i => shiftedColumns (Fin.last k) h i j) b r) := by
  rw [← rawCircuit_gates,(rawCircuit W (transform n (k+1) 2)).basis,decoderRegisters_basis,
    rawCircuit_forward W _ (transform_valid n k W hW),transform_forward,← decoderRegisters_basis]

end F3Reduction

-- Source: Solutions.T31.PushAlgebra

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3SubsetSum
open Classical

lemma push_smul {α β : Type} [Fintype α] (f : α → β) (c : ℂ) (v : α → ℂ) :
    push f (c • v) = c • push f v := by
  funext y
  simp only [push,matApply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma push_comp {α β γ : Type} [Fintype α] [Fintype β] (f : α → β) (g : β → γ) (v : α → ℂ) :
    push g (push f v) = push (g ∘ f) v := by
  funext y
  simp only [push,matApply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [mul_ite,mul_one,mul_zero,ite_mul]
  simp [eq_comm,Function.comp_apply]

lemma push_basis_expansion {α : Type} [Fintype α] {W : ℕ} (f : α → QBasis W) (v : α → ℂ) :
    push f v = ∑ a, v a • basisKet (f a) := by
  funext y
  simp only [push,matApply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,basisKet]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : f a = y
  · simp [he]
  · simp [he,Ne.symm he]

lemma frame_state_expand {n m W : ℕ} (Dec : DecoderFn 3) (A : Instance n m) :
    (frame A (state Dec A) : Ket W) = ∑ x : Pair n m,
      (normalizer n m*sign x.2) • basisKet (decoderBasis n m W A
        (noisyWord A x.1 x.2) (fun j => x.1 j-Dec n m A (fun i => noisyWord A x.1 x.2 i-1) j)) := by
  unfold frame state rawState
  rw [push_smul,push_comp,push_basis_expansion,Finset.smul_sum]
  simp only [smul_smul,afterErase,Function.comp_apply]
  rfl

end F3Reduction

-- Source: Solutions.T31.CoreReduction

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3Tools F3SubsetSum Matrix
open Classical

noncomputable abbrev eraseCircuit (n m : ℕ) (R : Circuit) : Circuit :=
  ⟨R.wires,(notStates n m).flatMap (fun g => (rawRev R.wires g).gates)++R.gates⟩

lemma eraseCircuit_basis {n m : ℕ} (Dec : DecoderFn 3) (R : Circuit) (hR : CleanDecoder Dec n m R)
    (A : Instance n m) (x : Pair n m) :
    (eraseCircuit n m R).run (basisKet (decoderBasis n m R.wires A (delta x.2) x.1)) =
      basisKet (decoderBasis n m R.wires A (noisyWord A x.1 x.2)
        (fun j => x.1 j-Dec n m A (fun i => noisyWord A x.1 x.2 i-1) j)) := by
  unfold Circuit.run
  dsimp only [eraseCircuit]
  rw [List.foldl_append,notStates_basis A (delta x.2) x.1 hR.1]
  have hb := hR.2 A (delta x.2+Aᵀ *ᵥ x.1) x.1
  unfold Circuit.run at hb
  rw [hb]
  have he : delta x.2+Aᵀ *ᵥ x.1 = noisyWord A x.1 x.2 := by simp only [noisyWord,add_comm]
  rw [he]

lemma prepared_erased {n m : ℕ} (Dec : DecoderFn 3) (R : Circuit) (hR : CleanDecoder Dec n m R)
    (A : Instance n m) :
    (eraseCircuit n m R).run
      (rangeApply pMat (n*m) m (by change n*m+m  ≤  R.wires; have := hR.1; omega)
        (rangeApply fourierMat (n*m+m) n hR.1 (basisKet (decoderBasis n m R.wires A 0 0)))) =
      frame A (state Dec A) := by
  rw [prepared_basis A hR.1,run_sum]
  rw [frame_state_expand]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← circuitLinear_apply,LinearMap.map_smul,circuitLinear_apply,eraseCircuit_basis Dec R hR A x]

@[simp] lemma singleMatrix_zero : singleMatrix 0 = fourierMat := rfl
@[simp] lemma singleMatrix_one : singleMatrix 1 = pMat := rfl
@[simp] lemma singleMatrix_two : singleMatrix 2 = uMat.conjTranspose := rfl

lemma coreCircuit_run {n m : ℕ} (Dec : DecoderFn 3) (R : Circuit) (hR : CleanDecoder Dec n m R)
    (A : Instance n m) :
    (coreCircuit n m R).run (basisKet (inputBasis n m R.wires (fun i j => A j i))) =
      frame A (pairTransform (state Dec A)) := by
  rw [← decoderBasis_initial A]
  unfold Circuit.run
  dsimp only [coreCircuit]
  simp only [List.foldl_append]
  rw [rangeGates_run 0 (n*m+m) n hR.1]
  have hw : n*m+m  ≤  R.wires := by have := hR.1; omega
  rw [rangeGates_run 1 (n*m) m hw]
  simp only [singleMatrix_zero,singleMatrix_one]
  have hgroup (ψ : Ket R.wires) :
      R.gates.foldl (fun φ g => applyGate g φ)
        (((notStates n m).flatMap (fun g => (rawRev R.wires g).gates)).foldl (fun φ g => applyGate g φ) ψ) =
      (eraseCircuit n m R).run ψ := by
    exact (List.foldl_append (f := fun φ g => applyGate g φ)).symm
  rw [hgroup,prepared_erased Dec R hR A,rangeGates_run 2 (n*m) m hw,singleMatrix_two,range_uInv_frame]

end F3Reduction

-- Source: Solutions.T31.QuantumWrapper

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3Reduction
open F3Tools F3SubsetSum
open Classical

def matrixColumnsEquiv (n m : ℕ) : (Fin m → Fin n → ZMod 3) ≃ Instance n m where
  toFun h j i := h i j
  invFun A i j := A j i
  left_inv _ := rfl
  right_inv _ := rfl

def reductionEquiv (n m : ℕ) (a : Fin m) : (Fin m → Fin n → ZMod 3) ≃ Instance n m :=
  (columnEquiv n m a).trans (matrixColumnsEquiv n m)

@[simp] lemma reductionEquiv_apply (n m : ℕ) (a : Fin m) (h : Fin m → Fin n → ZMod 3) :
    reductionEquiv n m a h = fun j i => shiftedColumns a h i j := rfl

lemma wrap_run {n k : ℕ} (Dec : DecoderFn 3) (R : Circuit) (hR : CleanDecoder Dec n (k+1) R)
    (h : Fin (k+1) → Fin n → ZMod 3) :
    (wrap n (k+1) R).run (basisKet (inputBasis n (k+1) R.wires h)) =
      ((postprocess n (k+1)).flatMap (fun g => (rawRev R.wires g).gates)).foldl
        (fun φ g => applyGate g φ)
        (frame (reductionEquiv n (k+1) (Fin.last k) h)
          (pairTransform (state Dec (reductionEquiv n (k+1) (Fin.last k) h)))) := by
  simp only [Circuit.run,wrap,show ¬k+1 = 0 by omega,if_false,List.foldl_append]
  rw [← decoderBasis_initial (fun j i => h i j)]
  have hw : n*(k+1)  ≤  R.wires := by have := hR.1; omega
  rw [transform_basis h 0 0 hw,decoderBasis_initial]
  have hc := coreCircuit_run Dec R hR (reductionEquiv n (k+1) (Fin.last k) h)
  unfold Circuit.run at hc
  simp only [coreCircuit,List.foldl_append,reductionEquiv_apply] at hc ⊢
  rw [hc]

lemma wrap_fixed_bound {n k : ℕ} (Dec : DecoderFn 3) (R : Circuit) (hR : CleanDecoder Dec n (k+1) R)
    (h : Fin (k+1) → Fin n → ZMod 3) :
    mass (fun p : Word (k+1) × Secret n => signedValid (reductionEquiv n (k+1) (Fin.last k) h) p.1)
      (pairTransform (state Dec (reductionEquiv n (k+1) (Fin.last k) h)))  ≤ 
      mass (fun y => IsZeroSubsetSum h (outSet n (k+1) y))
        ((wrap n (k+1) R).run (basisKet (inputBasis n (k+1) R.wires h))) := by
  rw [wrap_run Dec R hR h,← rawCircuit_gates]
  let A := reductionEquiv n (k+1) (Fin.last k) h
  apply reversible_mass_transfer (rawCircuit R.wires (postprocess n (k+1)))
    (fun p : Word (k+1) × Secret n => decoderBasis n (k+1) R.wires A p.1 p.2)
    (decoderBasis_injective A hR.1)
  intro p hp
  rw [postprocess_set A p.1 p.2 hR.1 hp.1]
  exact relativeSigns_solution (Fin.last k) h p.1 hp

lemma successProb_nonneg (n m : ℕ) (R : Circuit) : 0  ≤  successProb n m R := by
  unfold successProb
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro h hh
    apply Finset.sum_nonneg
    intro y hy
    split_ifs
    · exact Complex.normSq_nonneg _
    · exact le_rfl
  · positivity

theorem quantum_wrapper (Dec : DecoderFn 3) (n m : ℕ) (R : Circuit) (hR : CleanDecoder Dec n m R) :
    1-2*avgError Dec n m-(3:ℝ)^n*(2/3:ℝ)^m  ≤  successProb n m (wrap n m R) := by
  cases m with
  | zero =>
    have he : 0  ≤  avgError Dec n 0 := by unfold avgError; positivity
    have hp : 1  ≤  (3:ℝ)^n := one_le_pow₀ (by norm_num)
    have hs := successProb_nonneg n 0 (wrap n 0 R)
    simp only [pow_zero,mul_one]
    linarith
  | succ k =>
    let F (A : Instance n (k+1)) : ℝ :=
      mass (fun p : Word (k+1) × Secret n => signedValid A p.1) (pairTransform (state Dec A))
    have hsum : (∑ h : Fin (k+1) → Fin n → ZMod 3,
        F (reductionEquiv n (k+1) (Fin.last k) h)) = ∑ A : Instance n (k+1), F A := by
      exact Fintype.sum_equiv (reductionEquiv n (k+1) (Fin.last k)) _ _ (fun _ => rfl)
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (k+1) → Fin n → ZMod 3)))
      (fun h _ => wrap_fixed_bound Dec R hR h)
    change (∑ h, F (reductionEquiv n (k+1) (Fin.last k) h))  ≤  _ at hs
    rw [hsum] at hs
    have hd := div_le_div_of_nonneg_right hs (by positivity : 0  ≤  (3:ℝ)^(n*(k+1)))
    change signedSuccess Dec n (k+1)  ≤  successProb n (k+1) (wrap n (k+1) R) at hd
    exact (quantum_error_bound Dec n (k+1)).trans hd

end F3Reduction

-- Source: Solutions.T31.SerializeMachine

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction F3Generate OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

def inverseCode (bs : List Bool) := bs.take 3++[!bs[3]?.getD false]++bs.drop 4
@[fun_prop] lemma inverseCode_poly : Poly inverseCode := by unfold inverseCode; fun_prop
lemma inverseCode_gate {W : ℕ} (g : Gate W) : encodeGate (inverseGate g) = inverseCode (encodeGate g) := by
  cases g <;> simp [inverseGate,encodeGate,inverseCode,List.take_cons,List.drop_succ_cons]

def inverseRawEncode (pad : List Bool) (g : Raw) := inverseCode (rawEncode pad g)
@[fun_prop] lemma inverseRawEncode_poly : Poly (fun x : List Bool × Raw => inverseRawEncode x.1 x.2) := by
  unfold inverseRawEncode
  fun_prop
@[fun_prop] lemma inverseRawEncode_comp {α : Type} [Coding α] {p : α → List Bool} {g : α → Raw}
    (hp : Poly p) (hg : Poly g) : Poly (fun x => inverseRawEncode (p x) (g x)) :=
  show Poly (fun x => inverseCode (rawEncode (p x) (g x))) from Poly.comp inverseCode_poly (rawEncode_comp hp hg)

lemma rawRev_singleton (W : ℕ) (g : Raw) (hv : Valid W g) : ∃ a, (rawRev W g).gates = [a] := by
  rcases hv with ⟨hk,hv⟩
  unfold rawRev
  rw [dif_pos hk]
  rcases hv with h0 | ⟨hi,hik,hs⟩
  · rw [if_pos h0]; exact ⟨_,rfl⟩
  · by_cases h0 : g.1 = 0
    · rw [if_pos h0]; exact ⟨_,rfl⟩
    rw [if_neg h0,dif_pos ⟨hi,hik⟩]
    rcases hs with h1 | h2 | ⟨hj,hjk,hij,h3⟩
    · rw [if_pos h1]; exact ⟨_,rfl⟩
    · rw [if_neg (by omega),if_pos h2]; exact ⟨_,rfl⟩
    · rw [if_neg (by omega),if_neg (by omega),dif_pos ⟨hj,hjk,hij,h3⟩]; exact ⟨_,rfl⟩

lemma inverseRaw_codes (W : ℕ) (gs : List Raw) (hv : ∀ g ∈ gs, Valid W g) (pad : List Bool)
    (hp : ∀ i < W, pad.take i = List.replicate i true) :
    ((rawCircuit W gs).gates.reverse.map inverseGate).flatMap encodeGate = gs.reverse.flatMap (inverseRawEncode pad) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have ht := ih (fun g hg => hv g (by simp [hg]))
    have hg := hv g (by simp)
    obtain ⟨a,ha⟩ := rawRev_singleton W g hg
    have hc := rawEncode_correct W g hg pad hp
    rw [ha] at hc
    have hca : encodeGate a = rawEncode pad g := by simpa using hc
    change (((rawRev W g).gates++(rawCircuit W gs).gates).reverse.map inverseGate).flatMap encodeGate = _
    rw [List.reverse_append,List.map_append,List.flatMap_append,ht,ha]
    simp only [List.reverse_singleton,List.map_singleton,List.flatMap_singleton,List.reverse_cons,List.reverse_nil,List.nil_append,List.flatMap_append]
    rw [inverseCode_gate,hca]
    rfl

def singleEncode (pad : List Bool) (tag i : ℕ) :=
  (if tag = 0 then [false,true,true,false] else if tag = 1 then [true,false,false,false] else [true,false,true,true]) ++
    pad.take i++[false]
@[fun_prop] lemma singleEncode_poly : Poly (fun x : List Bool × (ℕ × ℕ) => singleEncode x.1 x.2.1 x.2.2) := by
  unfold singleEncode
  fun_prop
@[fun_prop] lemma singleEncode_comp {α : Type} [Coding α] {p : α → List Bool} {t i : α → ℕ}
    (hp : Poly p) (ht : Poly t) (hi : Poly i) : Poly (fun x => singleEncode (p x) (t x) (i x)) :=
  Poly.comp singleEncode_poly (Poly.pair hp (Poly.pair ht hi))
lemma single_codes (W tag i : ℕ) (hi : i < W) (pad : List Bool)
    (hp : pad.take i = List.replicate i true) :
    (single W tag i).flatMap encodeGate = singleEncode pad tag i := by
  unfold single
  rw [dif_pos hi]
  split_ifs <;> simp_all [encodeGate,singleEncode,List.append_assoc]

def coordinateEncode (pad : List Bool) (target : ℕ) (q : CompileState) : List Bool :=
  q.1.1.flatMap (rawEncode pad) ++rawEncode pad (2,q.1.2-1,0,target) ++q.1.1.reverse.flatMap (inverseRawEncode pad)
@[fun_prop] lemma coordinateEncode_poly : Poly (fun x : (List Bool × ℕ) × CompileState => coordinateEncode x.1.1 x.1.2 x.2) := by
  unfold coordinateEncode
  fun_prop
@[fun_prop] lemma coordinateEncode_comp {α : Type} [Coding α] {p : α → List Bool} {t : α → ℕ} {q : α → CompileState}
    (hp : Poly p) (ht : Poly t) (hq : Poly q) : Poly (fun x => coordinateEncode (p x) (t x) (q x)) :=
  Poly.comp coordinateEncode_poly (Poly.pair (Poly.pair hp ht) hq)

lemma answerWire_pointer (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T j : ℕ) :
    answerWire M τ n m T j = (computation M τ n m T j).1.2-1 := result_pointer _ _

lemma coordinateEncode_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (n m T : ℕ) (j : Fin n)
    (hv : ∀ g ∈ (computation M τ n m T j.val).1.1, Valid (oracleWidth M τ n m T) g)
    (pad : List Bool) (hp : ∀ i < oracleWidth M τ n m T, pad.take i = List.replicate i true) :
    (coordinateOracle M τ n m T j.val).gates.flatMap encodeGate =
      coordinateEncode pad (n*m+m+j.val) (computation M τ n m T j.val) := by
  have hW := oracleWidth_reserve M τ n m T
  have hq := oracleWidth_computation M τ n m T j
  have hs := computation_shape M τ n m T j j
  have hc : Valid (oracleWidth M τ n m T) (2,answerWire M τ n m T j.val,0,n*m+m+j.val) := by
    dsimp [Valid]
    dsimp [reserve] at hW
    have hj := j.isLt
    exact ⟨by omega,Or.inr ⟨by omega,by omega,Or.inr (Or.inl rfl)⟩⟩
  change ((rawCircuit _ _).gates++(rawRev _ _).gates++_).flatMap encodeGate = _
  rw [List.flatMap_append,List.flatMap_append,rawCircuit_codes _ _ hv pad hp,
    rawEncode_correct _ _ hc pad hp,inverseRaw_codes _ _ hv pad hp,answerWire_pointer]
  rfl

end F3MachineCompiler

-- Source: Solutions.T31.CircuitGenerator

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction F3Generate OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open Classical

noncomputable def allCoordinates (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) :=
  (boundedRange w (parameterN w)).map (fun j => coordinateFromWord M τ (w,j))
@[fun_prop] lemma allCoordinates_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (allCoordinates M τ) := by
  unfold allCoordinates
  fun_prop
lemma allCoordinates_eq (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) :
    allCoordinates M τ w = (List.finRange (parameterN w)).map
      (fun j => computation M τ (parameterN w) (parameterM w) (parameterT w) j.val) := by
  unfold allCoordinates
  rw [boundedRange_eq,Nat.min_eq_left (parameter_bounds w).1,F3Reduction.range_finRange,List.map_map]
  apply List.map_congr_left
  intro j hj
  exact coordinateFromWord_correct M τ w j.val (Nat.le_trans (Nat.le_of_lt j.isLt) (parameter_bounds w).1)

noncomputable def generatedWidth (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) :=
  reserve (parameterN w) (parameterM w)+
    ((allCoordinates M τ w).flatMap (fun q => (globalPad M w).take q.1.2)).length
@[fun_prop] lemma generatedWidth_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (generatedWidth M τ) := by
  unfold generatedWidth reserve
  fun_prop
lemma generatedWidth_eq (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) :
    generatedWidth M τ w = oracleWidth M τ (parameterN w) (parameterM w) (parameterT w) := by
  unfold generatedWidth
  rw [allCoordinates_eq,List.flatMap_map,List.length_flatMap]
  have he : (List.finRange (parameterN w)).map (fun j =>
      ((globalPad M w).take (computation M τ (parameterN w) (parameterM w) (parameterT w) j.val).1.2).length) =
      (List.finRange (parameterN w)).map (fun j => (computation M τ (parameterN w) (parameterM w) (parameterT w) j.val).1.2) := by
    apply List.map_congr_left
    intro j hj
    rw [List.length_take,Nat.min_eq_left (computation_globalPad M τ w j.val
      (Nat.le_trans (Nat.le_of_lt j.isLt) (parameter_bounds w).1))]
  rw [he,← List.ofFn_eq_map,List.sum_ofFn]
  rfl

noncomputable def generatedCode (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) : List Bool :=
  let n := parameterN w
  let m := parameterM w
  let pad := globalPad M w
  pad.take (generatedWidth M τ w)++[false]++
    (if m = 0 then [] else
      ((boundedRange w (m-1)).flatMap (fun i => (boundedRange w n).map (fun j => (2,n*i+j,0,n*(m-1)+j)))).flatMap (rawEncode pad) ++
      (boundedRange w n).flatMap (fun j => singleEncode pad 0 (n*m+m+j)) ++
      (boundedRange w m).flatMap (fun i => singleEncode pad 1 (n*m+i)) ++
      ((boundedRange w m).flatMap (fun i => (boundedRange w n).map (fun j => (3,n*i+j,n*m+m+j,n*m+i)))).flatMap (rawEncode pad) ++
      (((allCoordinates M τ w).zip (boundedRange w n)).flatMap (fun q => coordinateEncode pad (n*m+m+q.2) q.1)) ++
      (boundedRange w m).flatMap (fun i => singleEncode pad 2 (n*m+i)) ++
      ((boundedRange w (m-1)).map (fun i => (2,n*m+(m-1),0,n*m+i))).flatMap (rawEncode pad))
@[fun_prop] lemma generatedCode_poly (M : BinaryMachine) (τ : Bool ≃ Bool) : Poly (generatedCode M τ) := by
  unfold generatedCode
  fun_prop

end F3MachineCompiler

-- Source: Solutions.T31.GeneratorCorrect

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction F3Generate
open Classical
lemma flatMap_congr {α β : Type} {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih => rw [List.flatMap_cons,List.flatMap_cons,h a (by simp),ih (fun x hx => h x (by simp [hx]))]

lemma rawCircuit_gates (W : ℕ) (gs : List Raw) :
    (rawCircuit W gs).gates = gs.flatMap (fun g => (rawRev W g).gates) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => change (rawRev W g).gates++(rawCircuit W gs).gates = _; rw [ih]; rfl

lemma zip_map_same {α β γ : Type} (xs : List α) (f : α → β) (g : α → γ) :
    (xs.map f).zip (xs.map g) = xs.map (fun x => (f x,g x)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.map_cons,List.zip_cons_cons,ih]

lemma computation_gates_valid (M : BinaryMachine) (τ : Bool ≃ Bool) (Dec : DecoderFn 3) (n m T : ℕ)
    (h : ∀ A b, Nonempty (Turing.TM2OutputsInTime M.tm (encodeInstance A b)
      (some ((encodeSecret (Dec n m A b)).map τ)) T)) (j : Fin n) :
    ∀ g ∈ (computation M τ n m T j.val).1.1, Valid (oracleWidth M τ n m T) g := by
  let A : Matrix (Fin n) (Fin m) (ZMod 3) := 0
  let b : Fin m → ZMod 3 := 0
  obtain ⟨hr⟩ := h A (fun i => b i-1)
  have hc := computation_correct M τ n m T A b 0 (Dec n m A (fun i => b i-1)) hr j
  exact fun g hg => (hc.1 g hg).mono (oracleWidth_computation M τ n m T j)

lemma generatedCode_correct (M : BinaryMachine) (τ : Bool ≃ Bool) (Dec : DecoderFn 3) (w : List Bool)
    (h : ∀ A b, Nonempty (Turing.TM2OutputsInTime M.tm (encodeInstance A b)
      (some ((encodeSecret (Dec (parameterN w) (parameterM w) A b)).map τ)) (parameterT w))) :
    generatedCode M τ w = encodeCircuit (wrap (parameterN w) (parameterM w)
      (decoderCircuit M τ (parameterN w) (parameterM w) (parameterT w))) := by
  let n := parameterN w
  let m := parameterM w
  let T := parameterT w
  let W := oracleWidth M τ n m T
  let pad := globalPad M w
  change generatedCode M τ w = encodeCircuit (wrap n m (decoderCircuit M τ n m T))
  obtain ⟨hn,hm,ht⟩ := parameter_bounds w
  have hw : W  ≤  pad.length := by
    dsimp only [pad]
    rw [globalPad_eq,List.length_replicate]
    exact oracle_global_bound M τ n m T w.length hn hm ht
  have hpad : pad = List.replicate pad.length true := by
    dsimp only [pad]
    conv_lhs => rw [globalPad_eq]
    rw [globalPad_eq,List.length_replicate]
  have hp : ∀ i < W, pad.take i = List.replicate i true := by
    intro i hi
    conv_lhs => rw [hpad,List.take_replicate,Nat.min_eq_left (Nat.le_trans (Nat.le_of_lt hi) hw)]
  have hpW : pad.take W = List.replicate W true := by
    conv_lhs => rw [hpad,List.take_replicate,Nat.min_eq_left hw]
  have hW := oracleWidth_reserve M τ n m T
  have hw' : n*m+m+n  ≤  W := by dsimp only [W]; dsimp only [reserve] at hW; omega
  have hrn : boundedRange w n = List.range n := by rw [boundedRange_eq,Nat.min_eq_left hn]
  have hrm : boundedRange w m = List.range m := by rw [boundedRange_eq,Nat.min_eq_left hm]
  have hrm' : boundedRange w (m-1) = List.range (m-1) := by rw [boundedRange_eq,Nat.min_eq_left (by omega)]
  have horacle : ((allCoordinates M τ w).zip (boundedRange w n)).flatMap
      (fun q => coordinateEncode pad (n*m+m+q.2) q.1) =
      (decoderCircuit M τ n m T).gates.flatMap encodeGate := by
    rw [allCoordinates_eq,hrn,F3Reduction.range_finRange,zip_map_same,List.flatMap_map]
    change (List.finRange n).flatMap _ = ((List.finRange n).flatMap _).flatMap encodeGate
    rw [List.flatMap_assoc]
    apply flatMap_congr
    intro j hj
    exact (coordinateEncode_correct M τ n m T j (computation_gates_valid M τ Dec n m T h j) pad hp).symm
  have hprep : (List.range n).flatMap (fun j => singleEncode pad 0 (n*m+m+j)) =
      ((List.range n).flatMap (fun j => single W 0 (n*m+m+j))).flatMap encodeGate := by
    rw [List.flatMap_assoc]
    apply flatMap_congr
    intro j hj
    have hj := List.mem_range.mp hj
    have hi : n*m+m+j < W := by omega
    exact (single_codes W 0 _ hi pad (hp _ hi)).symm
  have hpword (tag : ℕ) : (List.range m).flatMap (fun i => singleEncode pad tag (n*m+i)) =
      ((List.range m).flatMap (fun i => single W tag (n*m+i))).flatMap encodeGate := by
    rw [List.flatMap_assoc]
    apply flatMap_congr
    intro i hi
    have hi := List.mem_range.mp hi
    have hi' : n*m+i < W := by omega
    exact (single_codes W tag _ hi' pad (hp _ hi')).symm
  unfold generatedCode
  simp only [generatedWidth_eq]
  change pad.take W++[false]++(if m=0 then [] else
      ((boundedRange w (m-1)).flatMap (fun i => (boundedRange w n).map (fun j => (2,n*i+j,0,n*(m-1)+j)))).flatMap (rawEncode pad) ++
      (boundedRange w n).flatMap (fun j => singleEncode pad 0 (n*m+m+j)) ++
      (boundedRange w m).flatMap (fun i => singleEncode pad 1 (n*m+i)) ++
      ((boundedRange w m).flatMap (fun i => (boundedRange w n).map (fun j => (3,n*i+j,n*m+m+j,n*m+i)))).flatMap (rawEncode pad) ++
      (((allCoordinates M τ w).zip (boundedRange w n)).flatMap (fun q => coordinateEncode pad (n*m+m+q.2) q.1)) ++
      (boundedRange w m).flatMap (fun i => singleEncode pad 2 (n*m+i)) ++
      ((boundedRange w (m-1)).map (fun i => (2,n*m+(m-1),0,n*m+i))).flatMap (rawEncode pad)) = _
  rw [hpW]
  by_cases hm0 : m=0
  · simp only [wrap,if_pos hm0,encodeCircuit,List.append_nil,List.flatMap_nil]
    rfl
  rw [if_neg hm0,horacle,hrm',hrn,hrm,hprep,hpword 1,hpword 2]
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have htr : ∀ g ∈ transform n m 2, Valid W g := by
    rw [hk]
    exact transform_valid n k W (by simpa only [hk] using (show n*m  ≤  W by omega))
  have hpost : ∀ g ∈ postprocess n m, Valid W g := by
    rw [hk]
    exact postprocess_valid n k W (by simpa only [hk] using (show n*m+m  ≤  W by omega))
  have hnot := notStates_valid n m W hw'
  have htc := rawCircuit_codes W _ htr pad hp
  have hpc := rawCircuit_codes W _ hpost pad hp
  have hnc := rawCircuit_codes W _ hnot pad hp
  simp only [rawCircuit_gates] at htc hpc hnc
  change List.replicate W true++[false]++((transform n m 2).flatMap (rawEncode pad)++_++_++
    (notStates n m).flatMap (rawEncode pad)++_++_++(postprocess n m).flatMap (rawEncode pad)) = _
  rw [← htc,← hpc,← hnc]
  simp only [encodeCircuit,wrap,if_neg hm0,coreCircuit,List.flatMap_append,W,List.append_assoc]

end F3MachineCompiler

-- Source: Solutions.T31.Runtime

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3MachineCompiler
open F3Tools F3SubsetSum F3Reduction OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial
open Classical

noncomputable def generatorProgram (M : BinaryMachine) (τ : Bool ≃ Bool) :
    PolyProgram id id (generatedCode M τ) :=
  BooleanLists.packProgram.comp ((generatedCode_poly M τ).program.comp BooleanLists.unpackProgram)
noncomputable def uniformGenerator (M : BinaryMachine) (τ : Bool ≃ Bool) : Turing.TM2ComputableAux Bool Bool :=
  ⟨(generatorProgram M τ).machine.tm,Equiv.refl _,Equiv.refl _⟩

lemma uniformGenerator_outputs (M : BinaryMachine) (τ : Bool ≃ Bool) (w : List Bool) :
    HMBinPacking.OutputsWithin (uniformGenerator M τ) w (generatedCode M τ w)
      ((generatorProgram M τ).time.eval w.length) := by
  have hr := (generatorProgram M τ).outputs w
  unfold uniformGenerator HMBinPacking.OutputsWithin
  change Nonempty (Turing.TM2OutputsInTime (generatorProgram M τ).machine.tm
    (w.map id) (some ((generatedCode M τ w).map id)) ((generatorProgram M τ).time.eval w.length))
  rw [List.map_id,List.map_id]
  exact ⟨hr⟩

lemma polynomial_bound (P : Polynomial ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ x : ℕ, 1  ≤  x → P.eval x  ≤  C*x^C := by
  refine ⟨P.eval 1+P.natDegree+1,by omega,?_⟩
  intro x hx
  have hP : P.eval x  ≤  P.eval 1*x^P.natDegree := by
    rw [eval_eq_sum_range,eval_eq_sum_range,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [one_pow,mul_one]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by have := Finset.mem_range.mp hi; omega))
  exact hP.trans (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hx (by omega)))
lemma gate_code_nonempty {W : ℕ} (g : Gate W) : 1  ≤  (encodeGate g).length := by
  cases g <;> simp [encodeGate] <;> omega
lemma gate_codes_length {W : ℕ} (gs : List (Gate W)) : gs.length  ≤  (gs.flatMap encodeGate).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => have := gate_code_nonempty g; simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega
lemma circuit_encoding_bounds (c : Circuit) : c.wires  ≤  (encodeCircuit c).length ∧ c.gates.length  ≤  (encodeCircuit c).length := by
  have h := gate_codes_length c.gates
  simp only [encodeCircuit,List.length_append,List.length_replicate,List.length_singleton]
  omega
lemma runtime_outputs_mono {M : Turing.TM2ComputableAux Bool Bool} {w out : List Bool} {t u : ℕ}
    (h : HMBinPacking.OutputsWithin M w out t) (hle : t  ≤  u) : HMBinPacking.OutputsWithin M w out u := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo,h.steps_le_m.trans hle⟩⟩

lemma generated_resources (M : BinaryMachine) (τ : Bool ≃ Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ n m T : ℕ,
      ∀ (Dec : DecoderFn 3),
      (∀ A b, Nonempty (Turing.TM2OutputsInTime M.tm (encodeInstance A b)
        (some ((encodeSecret (Dec n m A b)).map τ)) T)) →
      HMBinPacking.OutputsWithin (uniformGenerator M τ) (parameterWord n m T)
        (encodeCircuit (wrap n m (decoderCircuit M τ n m T))) ⌊C*((n+m+T+1:ℕ):ℝ)^C⌋₊ ∧
      ((wrap n m (decoderCircuit M τ n m T)).gates.length:ℝ)  ≤  C*((n+m+T+1:ℕ):ℝ)^C ∧
      ((wrap n m (decoderCircuit M τ n m T)).wires:ℝ)  ≤  C*((n+m+T+1:ℕ):ℝ)^C := by
  let P := ((generatorProgram M τ).time+(generatorProgram M τ).sizeBound).comp (X+1)
  obtain ⟨C,hC,hbound⟩ := polynomial_bound P
  refine ⟨C,by exact_mod_cast hC,?_⟩
  intro n m T Dec h
  let w := parameterWord n m T
  have hv := parameterWord_values n m T
  have hcode : generatedCode M τ w = encodeCircuit (wrap n m (decoderCircuit M τ n m T)) := by
    have hc := generatedCode_correct M τ Dec (parameterWord n m T)
    rw [hv.1,hv.2.1,hv.2.2] at hc
    exact hc h
  have hr := uniformGenerator_outputs M τ w
  rw [hcode] at hr
  have hb := hbound (n+m+T+1) (by omega)
  simp only [P,eval_comp,eval_add,eval_X,eval_one] at hb
  have hw : w.length = n+m+T+1+1 := by simp only [w,parameterWord_length,Nat.add_assoc]
  have ht : (generatorProgram M τ).time.eval w.length  ≤  C*(n+m+T+1)^C := by rw [hw]; omega
  have hs : (generatorProgram M τ).sizeBound.eval w.length  ≤  C*(n+m+T+1)^C := by rw [hw]; omega
  have hlen := (generatorProgram M τ).length_bound w
  change (generatedCode M τ w).length  ≤  _ at hlen
  rw [hcode] at hlen
  have hsize := hlen.trans hs
  have hg := (circuit_encoding_bounds (wrap n m (decoderCircuit M τ n m T))).2.trans hsize
  have hwire := (circuit_encoding_bounds (wrap n m (decoderCircuit M τ n m T))).1.trans hsize
  have he : (C:ℝ)*((n+m+T+1:ℕ):ℝ)^(C:ℝ) = ((C*(n+m+T+1)^C:ℕ):ℝ) := by
    simp [Real.rpow_natCast]
  rw [he,Nat.floor_natCast]
  exact ⟨runtime_outputs_mono hr ht,by exact_mod_cast hg,by exact_mod_cast hwire⟩

end F3MachineCompiler

-- Source: Solutions.T31.Final

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open F3SubsetSum F3MachineCompiler F3Reduction

theorem solution (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn 3) :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → ℕ → Circuit) (C : ℝ), 0 < C ∧
      ∀ n m T : ℕ, ComputesWithin M Dec n m T →
        HMBinPacking.OutputsWithin G (unaryD n ++ unaryD m ++ unary T) (encodeCircuit (circ n m T))
            ⌊C * ((n + m + T + 1 : ℕ) : ℝ) ^ C⌋₊ ∧
          n * m + m  ≤  (circ n m T).wires ∧
          ((circ n m T).gates.length : ℝ)  ≤  C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          ((circ n m T).wires : ℝ)  ≤  C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          1 - 2 * avgError Dec n m - (3 : ℝ) ^ n * (2 / 3 : ℝ) ^ m  ≤ 
            successProb n m (circ n m T) := by
  obtain ⟨B,τ,hB⟩ := boolean_decoder M Dec
  obtain ⟨C,hC,hgen⟩ := generated_resources B τ
  refine ⟨uniformGenerator B τ,fun n m T => wrap n m (decoderCircuit B τ n m T),C,hC,?_⟩
  intro n m T h
  have hb := hB n m T h
  obtain ⟨hout,hg,hw⟩ := hgen n m T Dec hb
  have hclean := decoderCircuit_clean B τ Dec n m T hb
  refine ⟨hout,?_,hg,hw,quantum_wrapper Dec n m _ hclean⟩
  have hr := oracleWidth_reserve B τ n m T
  change n*m+m  ≤  oracleWidth B τ n m T
  dsimp only [reserve] at hr
  omega


#print axioms solution

open F3SubsetSum in
example (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn 3) :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → ℕ → Circuit) (C : ℝ), 0 < C ∧
      ∀ n m T : ℕ, ComputesWithin M Dec n m T →
        HMBinPacking.OutputsWithin G (unaryD n ++ unaryD m ++ unary T) (encodeCircuit (circ n m T))
            ⌊C * ((n + m + T + 1 : ℕ) : ℝ) ^ C⌋₊ ∧
          n * m + m  ≤  (circ n m T).wires ∧
          ((circ n m T).gates.length : ℝ)  ≤  C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          ((circ n m T).wires : ℝ)  ≤  C * ((n + m + T + 1 : ℕ) : ℝ) ^ C ∧
          1 - 2 * avgError Dec n m - (3 : ℝ) ^ n * (2 / 3 : ℝ) ^ m  ≤ 
            successProb n m (circ n m T) := solution M Dec
