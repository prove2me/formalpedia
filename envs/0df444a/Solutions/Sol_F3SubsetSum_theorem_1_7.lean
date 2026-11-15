-- Prove2me | solution 1 for F3SubsetSum.theorem_1_7
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T18:50:11.857307+00:00
-- url     : https://prove2.me/submissions/958eee8a-5531-4155-9408-3b23a2420253

import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_RelationSpace
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_F3SubsetSum_fact_1_6
import Theorems.Thm_F3SubsetSum_proposition_4_9
import Theorems.Thm_F3SubsetSum_theorem_4_12

section File_T17M_TimeBound1

/-! # Real-analysis bounds for the running time -/

namespace T17M

open Polynomial

theorem poly_bound (P : Polynomial ℕ) : ∀ x : ℕ, P.eval x ≤ P.eval 1 * (x + 1) ^ P.natDegree := by
  intro x
  rw [eval_eq_sum_range, eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  simp only [one_pow, mul_one]
  exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (Nat.le_succ x) i).trans
    (Nat.pow_le_pow_right (Nat.succ_pos x) (by omega)))

/-- `n ≤ r^(h/δ)` with `δ = min (1/2) (log κ / 2)`. -/
theorem n_le_rpow (κ r h : ℝ) (n : ℕ) (hκ : 1 < κ) (hn : 1 ≤ n) (hr : κ ≤ r) (hh1 : 1 ≤ h)
    (hh : (n : ℝ) / r ≤ h) :
    (n : ℝ) ≤ r ^ (h / min (1 / 2) (Real.log κ / 2)) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 < r := by linarith
  have hlk : 0 < Real.log κ := Real.log_pos hκ
  have hlr : Real.log κ ≤ Real.log r := Real.log_le_log (by linarith) hr
  have hlr0 : 0 < Real.log r := Real.log_pos hr1
  set δ := min (1 / 2) (Real.log κ / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ Real.log κ / 2 := min_le_right _ _
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 ≤ Real.log n := Real.log_nonneg hnR
  -- reduce to logs
  rw [← Real.exp_log (show (0 : ℝ) < n by linarith), ← Real.exp_log (Real.rpow_pos_of_pos hr0 _),
    Real.log_rpow hr0]
  apply Real.exp_le_exp.2
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
  -- goal: log n * δ ≤ h * log r
  have hhr : (n : ℝ) / r * Real.log r ≤ h * Real.log r := mul_le_mul_of_nonneg_right hh hlr0.le
  by_cases c1 : (n : ℝ) ≤ r
  · have : Real.log n ≤ Real.log r := Real.log_le_log (by linarith) c1
    nlinarith
  · push_neg at c1
    by_cases c2 : Real.sqrt n < r
    · -- log r ≥ (1/2) log n and n / r ≥ 1
      have hs : Real.log n / 2 ≤ Real.log r := by
        have := Real.log_le_log (Real.sqrt_pos.2 (by linarith)) c2.le
        rw [Real.log_sqrt (by linarith)] at this; linarith
      have hnr : 1 ≤ (n : ℝ) / r := by rw [le_div_iff₀ hr0]; linarith
      have : Real.log r ≤ (n : ℝ) / r * Real.log r := by nlinarith
      nlinarith
    · push_neg at c2
      -- n / r ≥ √n ≥ log n / 2
      have hsq : Real.sqrt n ≤ (n : ℝ) / r := by
        rw [le_div_iff₀ hr0]
        have h1 : Real.sqrt n * r ≤ Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_left c2 (Real.sqrt_nonneg _)
        rw [Real.mul_self_sqrt (by linarith)] at h1; exact h1
      have hlog : Real.log n / 2 ≤ Real.sqrt n := by
        have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (show (0:ℝ) < n by linarith))
        rw [Real.log_sqrt (by linarith)] at h1; linarith
      have : Real.log n / 2 * Real.log κ ≤ (n : ℝ) / r * Real.log r := by
        apply mul_le_mul (hlog.trans hsq) hlr hlk.le (by positivity)
      nlinarith

end T17M

end File_T17M_TimeBound1

section File_T17M_Lib

/-! # Extra automation for `Poly`: folds, arithmetic wrappers -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

section
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

theorem foldl_env (f : α → β → γ → β) (x : α) (l : List γ) (b : β) :
    l.foldl (fun (p : α × β) a => (p.1, f p.1 p.2 a)) (x, b) = (x, l.foldl (f x) b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => exact ih _

theorem fold_size (f : α → β → γ → β) (G : Polynomial ℕ)
    (hG : ∀ x b a, (enc (f x b a)).length ≤ (enc b).length + G.eval ((enc x).length + (enc a).length))
    (x : α) (M : ℕ) (pre : List γ) (hpre : ∀ a ∈ pre, (enc a).length ≤ M) (acc : β) :
    (enc (pre.foldl (f x) acc)).length ≤ (enc acc).length + pre.length * G.eval ((enc x).length + M) := by
  induction pre generalizing acc with
  | nil => simp
  | cons a pre ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (fun a' ha' => hpre a' (List.mem_cons_of_mem _ ha')) (f x acc a)
    have h2 := hG x acc a
    have h3 := polynomial_eval_mono G (show (enc x).length + (enc a).length ≤ (enc x).length + M by
      have := hpre a (List.mem_cons_self); omega)
    nlinarith

theorem Poly.list_foldl [Inhabited γ] {f : α → β → γ → β} {as : α → List γ} {b0 : α → β}
    (hf : Poly (fun y : (α × β) × γ => f y.1.1 y.1.2 y.2)) (has : Poly as) (hb0 : Poly b0)
    (G : Polynomial ℕ)
    (hG : ∀ x b a, (enc (f x b a)).length ≤ (enc b).length + G.eval ((enc x).length + (enc a).length)) :
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
      have hpre : ∀ a ∈ pre, (enc a).length ≤ (encodeList enc as').length := by
        intro a ha
        exact EncodedList.member_length _ as' a (by rw [hsplit]; exact List.mem_append_left _ ha)
      have hs := fold_size f G hG x _ pre hpre acc
      have hlen : pre.length ≤ (encodeList enc as').length := by
        have h1 := EncodedList.length_le (enc : γ → List Bool) as'
        have h2 : pre.length ≤ as'.length := by rw [hsplit, List.length_append]; omega
        omega
      simp only [encodePair_length, eval_add, eval_X, eval_mul]
      set L := 2 * (encodeList enc as').length + 1 + (2 * (enc x).length + 1 + (enc acc).length)
      have hG' := polynomial_eval_mono G (show (enc x).length + (encodeList enc as').length ≤ L by omega)
      have hm : pre.length * G.eval ((enc x).length + (encodeList enc as').length) ≤ L * G.eval L :=
        Nat.mul_le_mul (by omega) hG'
      change 2 * (enc x).length + 1 + (enc (pre.foldl (f x) acc)).length ≤ L + L * G.eval L
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
  have : (fun x => min (f x) (g x)) = (fun x => if f x ≤ g x then f x else g x) := by
    funext x; split_ifs with h <;> omega
  rw [this]; fun_prop

@[fun_prop] theorem Poly.nat_max_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => max (f x) (g x)) := by
  have : (fun x => max (f x) (g x)) = (fun x => if f x ≤ g x then g x else f x) := by
    funext x; split_ifs with h <;> omega
  rw [this]; fun_prop

/-- `List.range k` for a number `k` given in binary is *not* polynomial; we provide it when the
number is bounded by the length of a list in the input. -/
theorem range_eq_take (k : ℕ) (l : List β) (h : k ≤ l.length) :
    List.range k = (List.range l.length).take k := by
  rw [List.take_range, Nat.min_eq_left h]

end Arith

end T17M

end File_T17M_Lib

section File_T17M_Timed

/-! # Machines with explicit (non-polynomial) running times -/

namespace T17M

open OAI.MetricKMedian.Binary Polynomial

/-- A machine computing `f` from `ea`-codes to `eb`-codes within `T a` steps. -/
structure Timed {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) (T : α → ℕ) where
  machine : Machine
  run : ∀ a, ∃ t, t ≤ T a ∧ Trace machine.step t (machine.initialCfg (ea a)) (machine.finalCfg (eb (f a)))

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

noncomputable def mono {f : α → β} {T T' : α → ℕ} (P : Timed ea eb f T) (h : ∀ a, T a ≤ T' a) :
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

end T17M

end File_T17M_Timed

section File_T17_Echelon

/-! # Echelon bases over `F_q` on lists of naturals (with a linear payload) -/

namespace T17

variable (q : ℕ)

def addq (a b : ℕ) : ℕ := (a + b) % q
def mulq (a b : ℕ) : ℕ := (a * b) % q
def negq (a : ℕ) : ℕ := (q - a % q) % q
/-- Inverse by Fermat: `a^(q-2)`. -/
def invq (a : ℕ) : ℕ := (List.replicate (q - 2) a).foldl (mulq q) 1

/-- `x - c • y` coordinatewise (lists of equal length). -/
def axpy (c : ℕ) (x y : List ℕ) : List ℕ := (x.zip y).map (fun p => addq q p.1 (mulq q (negq q c) p.2))
def smul (c : ℕ) (x : List ℕ) : List ℕ := x.map (mulq q c)

abbrev Row := ℕ × List ℕ × List ℕ

def redStep (xw : List ℕ × List ℕ) (r : Row) : List ℕ × List ℕ :=
  let c := xw.1.getD r.1 0
  (axpy q c xw.1 r.2.1, axpy q c xw.2 r.2.2)

def reduce (B : List Row) (xw : List ℕ × List ℕ) : List ℕ × List ℕ := B.foldl (redStep q) xw

def pivotOf (x : List ℕ) : ℕ := x.findIdx (fun a => a % q != 0)

def insertRow (B : List Row) (xw : List ℕ × List ℕ) : List Row :=
  let r := reduce q B xw
  let p := pivotOf q r.1
  if p < r.1.length then
    let c := invq q (r.1.getD p 0)
    B ++ [(p, smul q c r.1, smul q c r.2)]
  else B

def insertAll (B : List Row) (L : List (List ℕ × List ℕ)) : List Row := L.foldl (insertRow q) B

/-! ## Semantics -/

def toV (x : List ℕ) : ℕ → ZMod q := fun i => ((x.getD i 0 : ℕ) : ZMod q)

variable {q}

theorem toV_zip_map (x y : List ℕ) (hl : x.length = y.length) (f : ℕ → ℕ → ℕ) (g : ZMod q → ZMod q → ZMod q)
    (hf : ∀ a b, ((f a b : ℕ) : ZMod q) = g a b) (hg : g 0 0 = 0) :
    toV q ((x.zip y).map (fun p => f p.1 p.2)) = fun i => g (toV q x i) (toV q y i) := by
  funext i
  unfold toV
  by_cases hi : i < x.length
  · have hi' : i < y.length := hl ▸ hi
    rw [List.getD_eq_getElem _ _ (by simp [hi, hi']), List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ hi']
    simp [hf]
  · have hi' : ¬ i < y.length := hl ▸ hi
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]
    simp [hg]

variable [NeZero q]

theorem cast_addq (a b : ℕ) : ((addq q a b : ℕ) : ZMod q) = a + b := by
  simp [addq, ZMod.natCast_mod]
theorem cast_mulq (a b : ℕ) : ((mulq q a b : ℕ) : ZMod q) = a * b := by
  simp [mulq, ZMod.natCast_mod]
theorem cast_negq (a : ℕ) : ((negq q a : ℕ) : ZMod q) = -a := by
  unfold negq
  rw [ZMod.natCast_mod]
  have h : a % q ≤ q := (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))).le
  rw [Nat.cast_sub h, ZMod.natCast_self, ZMod.natCast_mod]
  ring

theorem toV_axpy (c : ℕ) (x y : List ℕ) (hl : x.length = y.length) :
    toV q (axpy q c x y) = toV q x - (c : ZMod q) • toV q y := by
  unfold axpy
  rw [toV_zip_map x y hl (fun a b => addq q a (mulq q (negq q c) b)) (fun a b => a - (c : ZMod q) * b)
    (fun a b => by rw [cast_addq, cast_mulq, cast_negq]; ring) (by simp)]
  funext i; simp [smul_eq_mul]

theorem toV_smul (c : ℕ) (x : List ℕ) : toV q (smul q c x) = (c : ZMod q) • toV q x := by
  funext i
  have h0 : (0 : ℕ) = mulq q c 0 := by simp [mulq]
  simp only [toV, smul, Pi.smul_apply, smul_eq_mul]
  rw [h0, List.getD_map, ← h0, cast_mulq]

/-! ## Invariants -/

/-- All vectors have length `d`, payloads length `e`. -/
def Shape (d e : ℕ) (B : List Row) : Prop := ∀ r ∈ B, r.2.1.length = d ∧ r.2.2.length = e ∧ r.1 < d

def Echelon : List Row → Prop
  | [] => True
  | r :: B => toV q r.2.1 r.1 = 1 ∧ (∀ r' ∈ B, toV q r'.2.1 r.1 = 0) ∧ Echelon B

def vecs (B : List Row) : Set (ℕ → ZMod q) := {v | ∃ r ∈ B, v = toV q r.2.1}

def PayOK (L : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) (B : List Row) : Prop :=
  ∀ r ∈ B, toV q r.2.1 = L (toV q r.2.2)

theorem vecs_cons (r : Row) (B : List Row) : vecs (q := q) (r :: B) = insert (toV q r.2.1) (vecs B) := by
  ext v; simp [vecs, eq_comm]

theorem vecs_append (B B' : List Row) : vecs (q := q) (B ++ B') = vecs B ∪ vecs B' := by
  ext v; simp [vecs, or_and_right, exists_or]

theorem length_axpy (c : ℕ) (x y : List ℕ) (h : x.length = y.length) :
    (axpy q c x y).length = x.length := by simp [axpy, h]

theorem length_smul (c : ℕ) (x : List ℕ) : (smul q c x).length = x.length := by simp [smul]

theorem length_redStep {d e : ℕ} (xw : List ℕ × List ℕ) (r : Row) (hx : xw.1.length = d)
    (hw : xw.2.length = e) (hr : r.2.1.length = d ∧ r.2.2.length = e) :
    (redStep q xw r).1.length = d ∧ (redStep q xw r).2.length = e := by
  simp only [redStep]
  exact ⟨by rw [length_axpy _ _ _ (by rw [hx, hr.1])]; exact hx,
    by rw [length_axpy _ _ _ (by rw [hw, hr.2])]; exact hw⟩

theorem length_reduce {d e : ℕ} (B : List Row) (hB : Shape d e B) (xw : List ℕ × List ℕ)
    (hx : xw.1.length = d) (hw : xw.2.length = e) :
    (reduce q B xw).1.length = d ∧ (reduce q B xw).2.length = e := by
  induction B generalizing xw with
  | nil => exact ⟨hx, hw⟩
  | cons r B ih =>
    have hr := hB r (List.mem_cons_self ..)
    have h1 := length_redStep (q := q) xw r hx hw ⟨hr.1, hr.2.1⟩
    exact ih (fun r' hr' => hB r' (List.mem_cons_of_mem _ hr')) _ h1.1 h1.2

/-- Reduction stays in the coset and keeps `x − L w`. -/
theorem reduce_spec {d e : ℕ} (L : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) (B : List Row)
    (hB : Shape d e B) (hP : PayOK L B) (xw : List ℕ × List ℕ)
    (hx : xw.1.length = d) (hw : xw.2.length = e) :
    toV q xw.1 - toV q (reduce q B xw).1 ∈ Submodule.span (ZMod q) (vecs B) ∧
      toV q (reduce q B xw).1 - L (toV q (reduce q B xw).2) = toV q xw.1 - L (toV q xw.2) := by
  induction B generalizing xw with
  | nil => simp [reduce]
  | cons r B ih =>
    have hr := hB r (List.mem_cons_self ..)
    have hl := length_redStep (q := q) xw r hx hw ⟨hr.1, hr.2.1⟩
    obtain ⟨h1, h2⟩ := ih (fun r' hr' => hB r' (List.mem_cons_of_mem _ hr'))
      (fun r' hr' => hP r' (List.mem_cons_of_mem _ hr')) (redStep q xw r) hl.1 hl.2
    have hstep1 : toV q (redStep q xw r).1 = toV q xw.1 - ((xw.1.getD r.1 0 : ℕ) : ZMod q) • toV q r.2.1 :=
      toV_axpy _ _ _ (by rw [hx, hr.1])
    have hstep2 : toV q (redStep q xw r).2 = toV q xw.2 - ((xw.1.getD r.1 0 : ℕ) : ZMod q) • toV q r.2.2 :=
      toV_axpy _ _ _ (by rw [hw, hr.2.1])
    have hPr := hP r (List.mem_cons_self ..)
    simp only [reduce, List.foldl_cons] at h1 h2 ⊢
    constructor
    · have : toV q xw.1 - toV q (List.foldl (redStep q) (redStep q xw r) B).1 =
          ((xw.1.getD r.1 0 : ℕ) : ZMod q) • toV q r.2.1 +
            (toV q (redStep q xw r).1 - toV q (List.foldl (redStep q) (redStep q xw r) B).1) := by
        rw [hstep1]; abel
      rw [this, vecs_cons]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))) ?_
      exact Submodule.span_mono (Set.subset_insert _ _) h1
    · rw [h2, hstep1, hstep2, map_sub, map_smul, ← hPr]; abel

/-- If every vector of `B` vanishes at `p`, reduction keeps a zero at `p`. -/
theorem reduce_keeps_zero {d e : ℕ} (B : List Row) (hB : Shape d e B) (p : ℕ)
    (hz : ∀ r ∈ B, toV q r.2.1 p = 0) (xw : List ℕ × List ℕ)
    (hx : xw.1.length = d) (hw : xw.2.length = e) (h0 : toV q xw.1 p = 0) :
    toV q (reduce q B xw).1 p = 0 := by
  induction B generalizing xw with
  | nil => exact h0
  | cons r B ih =>
    have hr := hB r (List.mem_cons_self ..)
    have hl := length_redStep (q := q) xw r hx hw ⟨hr.1, hr.2.1⟩
    simp only [reduce, List.foldl_cons]
    apply ih (fun r' hr' => hB r' (List.mem_cons_of_mem _ hr'))
      (fun r' hr' => hz r' (List.mem_cons_of_mem _ hr')) _ hl.1 hl.2
    have : toV q (redStep q xw r).1 = toV q xw.1 - ((xw.1.getD r.1 0 : ℕ) : ZMod q) • toV q r.2.1 :=
      toV_axpy _ _ _ (by rw [hx, hr.1])
    rw [this]
    simp [h0, hz r (List.mem_cons_self ..)]

/-- After reduction by an echelon list, all pivots are zero. -/
theorem reduce_pivots {d e : ℕ} (B : List Row) (hB : Shape d e B) (hE : Echelon (q := q) B)
    (xw : List ℕ × List ℕ) (hx : xw.1.length = d) (hw : xw.2.length = e) :
    ∀ r ∈ B, toV q (reduce q B xw).1 r.1 = 0 := by
  induction B generalizing xw with
  | nil => simp
  | cons r B ih =>
    obtain ⟨hone, hzero, hE'⟩ := hE
    have hr := hB r (List.mem_cons_self ..)
    have hl := length_redStep (q := q) xw r hx hw ⟨hr.1, hr.2.1⟩
    have hB' : Shape d e B := fun r' hr' => hB r' (List.mem_cons_of_mem _ hr')
    intro r' hr'
    simp only [reduce, List.foldl_cons]
    rcases List.mem_cons.1 hr' with rfl | hr'
    · apply reduce_keeps_zero B hB' r'.1 hzero _ hl.1 hl.2
      have : toV q (redStep q xw r').1 = toV q xw.1 - ((xw.1.getD r'.1 0 : ℕ) : ZMod q) • toV q r'.2.1 :=
        toV_axpy _ _ _ (by rw [hx, hr.1])
      rw [this]
      show toV q xw.1 r'.1 - ((xw.1.getD r'.1 0 : ℕ) : ZMod q) * toV q r'.2.1 r'.1 = 0
      rw [hone, mul_one]
      simp [toV]
    · exact ih hB' hE' _ hl.1 hl.2 r' hr'

/-- A combination of an echelon list vanishing at all pivots is zero. -/
theorem echelon_zero (B : List Row) (hE : Echelon (q := q) B) (y : ℕ → ZMod q)
    (hy : y ∈ Submodule.span (ZMod q) (vecs B)) (hp : ∀ r ∈ B, y r.1 = 0) : y = 0 := by
  induction B generalizing y with
  | nil =>
    simp only [vecs, List.not_mem_nil, false_and, exists_false, Set.setOf_false,
      Submodule.span_empty, Submodule.mem_bot] at hy
    exact hy
  | cons r B ih =>
    obtain ⟨hone, hzero, hE'⟩ := hE
    rw [vecs_cons, Submodule.mem_span_insert] at hy
    obtain ⟨a, z, hz, rfl⟩ := hy
    have hzp : z r.1 = 0 := by
      have key : ∀ w ∈ Submodule.span (ZMod q) (vecs (q := q) B), w r.1 = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r', hr', rfl⟩ := hx
          exact hzero r' hr'
        | zero => rfl
        | add x y _ _ hx hy => simp [hx, hy]
        | smul c x _ hx => simp [hx]
      exact key z hz
    have ha : a = 0 := by
      have := hp r (List.mem_cons_self ..)
      simpa [hone, hzp] using this
    subst ha
    simp only [zero_smul, zero_add]
    exact ih hE' z hz (fun r' hr' => by
      have := hp r' (List.mem_cons_of_mem _ hr'); simpa using this)

theorem mem_span_iff_reduce {d e : ℕ} (L : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) (B : List Row)
    (hB : Shape d e B) (hE : Echelon (q := q) B) (hP : PayOK L B) (xw : List ℕ × List ℕ)
    (hx : xw.1.length = d) (hw : xw.2.length = e) :
    toV q xw.1 ∈ Submodule.span (ZMod q) (vecs B) ↔ toV q (reduce q B xw).1 = 0 := by
  obtain ⟨h1, -⟩ := reduce_spec L B hB hP xw hx hw
  constructor
  · intro hmem
    apply echelon_zero B hE
    · have := Submodule.sub_mem _ hmem h1
      simpa using this
    · exact reduce_pivots B hB hE xw hx hw
  · intro h0
    have := h1
    rw [h0, sub_zero] at this
    exact this

/-! ## Insertion -/

theorem invq_cast (a : ℕ) (k : ℕ) (b : ℕ) :
    (((List.replicate k a).foldl (mulq q) b : ℕ) : ZMod q) = (b : ZMod q) * (a : ZMod q) ^ k := by
  induction k generalizing b with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, ih, cast_mulq]; ring

theorem invq_spec (hq : q.Prime) (a : ℕ) (ha : (a : ZMod q) ≠ 0) :
    ((invq q a : ℕ) : ZMod q) * a = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  unfold invq
  rw [invq_cast, Nat.cast_one, one_mul, ← pow_succ]
  have h2 : 2 ≤ q := hq.two_le
  rw [show q - 2 + 1 = q - 1 by omega]
  exact ZMod.pow_card_sub_one_eq_one ha

theorem pivotOf_spec (x : List ℕ) (h : pivotOf q x < x.length) :
    ((x.getD (pivotOf q x) 0 : ℕ) : ZMod q) ≠ 0 := by
  have h2 : (x.getD (pivotOf q x) 0) % q ≠ 0 := by
    rw [List.getD_eq_getElem _ _ h]
    unfold pivotOf at h ⊢
    simpa using List.findIdx_getElem (w := h)
  intro h0
  apply h2
  rw [ZMod.natCast_eq_zero_iff] at h0
  exact Nat.mod_eq_zero_of_dvd h0

theorem pivotOf_none (x : List ℕ) (h : ¬ pivotOf q x < x.length) : toV q x = 0 := by
  funext i
  simp only [toV, Pi.zero_apply]
  by_cases hi : i < x.length
  · rw [List.getD_eq_getElem _ _ hi]
    have := List.not_of_lt_findIdx (p := fun a => a % q != 0) (show i < x.findIdx _ by
      unfold pivotOf at h; omega)
    have h5 : x[i] % q = 0 := by simpa using this
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero h5
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem echelon_append (B : List Row) (r : Row) (hE : Echelon (q := q) B)
    (h0 : ∀ r' ∈ B, toV q r.2.1 r'.1 = 0) (h1 : toV q r.2.1 r.1 = 1) :
    Echelon (q := q) (B ++ [r]) := by
  induction B with
  | nil => exact ⟨h1, by simp, trivial⟩
  | cons r' B ih =>
    obtain ⟨a, b, c⟩ := hE
    refine ⟨a, ?_, ih c (fun r'' hr'' => h0 r'' (List.mem_cons_of_mem _ hr''))⟩
    intro r'' hr''
    rcases List.mem_append.1 hr'' with h | h
    · exact b r'' h
    · simp only [List.mem_singleton] at h; subst h; exact h0 r' (List.mem_cons_self ..)

theorem insertRow_spec (hq : q.Prime) {d e : ℕ} (L : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q))
    (B : List Row) (hB : Shape d e B) (hE : Echelon (q := q) B) (hP : PayOK L B)
    (xw : List ℕ × List ℕ) (hx : xw.1.length = d) (hw : xw.2.length = e)
    (hxw : toV q xw.1 = L (toV q xw.2)) :
    Shape d e (insertRow q B xw) ∧ Echelon (q := q) (insertRow q B xw) ∧ PayOK L (insertRow q B xw) ∧
      Submodule.span (ZMod q) (vecs (insertRow q B xw)) =
        Submodule.span (ZMod q) (vecs B) ⊔ Submodule.span (ZMod q) {toV q xw.1} := by
  obtain ⟨hs1, hs2⟩ := reduce_spec L B hB hP xw hx hw
  obtain ⟨hl1, hl2⟩ := length_reduce (q := q) B hB xw hx hw
  have hpiv := reduce_pivots B hB hE xw hx hw
  haveI : Fact q.Prime := ⟨hq⟩
  set r := reduce q B xw with hr
  unfold insertRow
  dsimp only
  simp only [← hr]
  split_ifs with hp
  · set p := pivotOf q r.1
    set c := invq q (r.1.getD p 0)
    have hne := pivotOf_spec r.1 hp
    have hc : (c : ZMod q) * ((r.1.getD p 0 : ℕ) : ZMod q) = 1 := invq_spec hq _ hne
    have hc0 : (c : ZMod q) ≠ 0 := by intro h; rw [h, zero_mul] at hc; exact zero_ne_one hc
    have hv : toV q (smul q c r.1) = (c : ZMod q) • toV q r.1 := toV_smul _ _
    have hu : toV q (smul q c r.2) = (c : ZMod q) • toV q r.2 := toV_smul _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r' hr'
      rcases List.mem_append.1 hr' with h | h
      · exact hB r' h
      · simp only [List.mem_singleton] at h; subst h
        exact ⟨by rw [length_smul, hl1], by rw [length_smul, hl2], by rw [← hl1]; exact hp⟩
    · apply echelon_append B _ hE
      · intro r' hr'; simp only; rw [hv]; simp [hpiv r' hr']
      · simp only; rw [hv]; simp only [Pi.smul_apply, smul_eq_mul]; exact hc
    · intro r' hr'
      rcases List.mem_append.1 hr' with h | h
      · exact hP r' h
      · simp only [List.mem_singleton] at h; subst h
        simp only; rw [hv, hu, map_smul]
        congr 1
        have := hs2; rw [hxw, sub_self] at this
        exact sub_eq_zero.1 this
    · rw [vecs_append]
      have hsing : vecs (q := q) [(p, smul q c r.1, smul q c r.2)] = {(c : ZMod q) • toV q r.1} := by
        ext v; simp [vecs, hv]
      rw [hsing, Submodule.span_union]
      apply le_antisymm
      · apply sup_le le_sup_left
        rw [Submodule.span_le, Set.singleton_subset_iff]
        apply Submodule.smul_mem
        have : toV q r.1 = toV q xw.1 - (toV q xw.1 - toV q r.1) := by abel
        rw [this]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
          (Submodule.mem_sup_left hs1)
      · apply sup_le le_sup_left
        rw [Submodule.span_le, Set.singleton_subset_iff]
        have : toV q xw.1 = (toV q xw.1 - toV q r.1) + ((c : ZMod q)⁻¹ • ((c : ZMod q) • toV q r.1)) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]; abel
        rw [this]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hs1)
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span rfl)))
  · refine ⟨hB, hE, hP, ?_⟩
    have hz := pivotOf_none r.1 hp
    rw [hz, sub_zero] at hs1
    apply le_antisymm le_sup_left
    apply sup_le le_rfl
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hs1

theorem insertAll_spec (hq : q.Prime) {d e : ℕ} (L : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q))
    (Ls : List (List ℕ × List ℕ)) (hLs : ∀ xw ∈ Ls, xw.1.length = d ∧ xw.2.length = e ∧
      toV q xw.1 = L (toV q xw.2)) :
    ∀ B : List Row, Shape d e B → Echelon (q := q) B → PayOK L B →
      Shape d e (insertAll q B Ls) ∧ Echelon (q := q) (insertAll q B Ls) ∧ PayOK L (insertAll q B Ls) ∧
      Submodule.span (ZMod q) (vecs (insertAll q B Ls)) =
        Submodule.span (ZMod q) (vecs B) ⊔ Submodule.span (ZMod q) {v | ∃ xw ∈ Ls, v = toV q xw.1} := by
  induction Ls with
  | nil => intro B h1 h2 h3; simp [insertAll, h1, h2, h3]
  | cons xw Ls ih =>
    intro B h1 h2 h3
    obtain ⟨hx, hw, hxw⟩ := hLs xw (List.mem_cons_self ..)
    obtain ⟨g1, g2, g3, g4⟩ := insertRow_spec hq L B h1 h2 h3 xw hx hw hxw
    obtain ⟨k1, k2, k3, k4⟩ := ih (fun xw' h => hLs xw' (List.mem_cons_of_mem _ h)) _ g1 g2 g3
    refine ⟨k1, k2, k3, ?_⟩
    simp only [insertAll, List.foldl_cons] at k4 ⊢
    rw [k4, g4]
    have : {v | ∃ xw' ∈ xw :: Ls, v = toV q xw'.1} = insert (toV q xw.1) {v | ∃ xw' ∈ Ls, v = toV q xw'.1} := by
      ext v; simp [eq_comm]
    rw [this, Submodule.span_insert, sup_assoc]

end T17

end File_T17_Echelon

section File_T17_Algo

/-! # The decoder of Theorem 1.7 as a list program -/

namespace T17

variable (q : ℕ)

/-- Reduced exponent vectors of length `k` and total degree `d`. -/
def monosEq : ℕ → ℕ → List (List ℕ)
  | 0, d => if d = 0 then [[]] else []
  | k + 1, d => (List.range (min (q - 1) d + 1)).flatMap
      (fun e => (monosEq k (d - e)).map (fun t => e :: t))

/-- Reduced monomials of degree `< D`. -/
def monosLt (n D : ℕ) : List (List ℕ) := (List.range D).flatMap (monosEq q n)

def idxOf (Ms : List (List ℕ)) (a : List ℕ) : ℕ := Ms.findIdx (fun b => b == a)

/-- `β + e_j`. -/
def bump (β : List ℕ) (j : ℕ) : List ℕ := (List.range β.length).map (fun t => β.getD t 0 + if t = j then 1 else 0)

/-- Reduction modulo `x^q − x` of an exponent. -/
def redE (e : ℕ) : ℕ := if e < q then e else (e - 1) % (q - 1) + 1
def redM (β : List ℕ) : List ℕ := β.map (redE q)

def unitV (d t : ℕ) : List ℕ := (List.range d).map (fun r => if r = t then 1 else 0)
def zeroV (d : ℕ) : List ℕ := List.replicate d 0
def vsum (d : ℕ) (vs : List (List ℕ)) : List ℕ :=
  (List.range d).map (fun r => (vs.map (fun v => v.getD r 0)).foldl (addq q) 0)
def sumq (xs : List ℕ) : ℕ := xs.foldl (addq q) 0

/-- Column `(i, β)` of `Φ` (coefficients of the truncated product `L_i² x^β` at `MD`). -/
def colPhi (MD : List (List ℕ)) (a : List ℕ) (β : List ℕ) : List ℕ :=
  let n := a.length
  MD.map (fun α => sumq q ((List.range n).flatMap (fun j => (List.range n).map (fun k =>
    if bump (bump β j) k == α then mulq q (a.getD j 0) (a.getD k 0) else 0))))

/-- Coefficient at `δ` of `red(f_i · x^β)`, `f_i = L² + (1 − 2b) L + b² − b`. -/
def coefRed (a : List ℕ) (bi : ℕ) (β δ : List ℕ) : ℕ :=
  let n := a.length
  let quad := sumq q ((List.range n).flatMap (fun j => (List.range n).map (fun k =>
    if redM q (bump (bump β j) k) == δ then mulq q (a.getD j 0) (a.getD k 0) else 0)))
  let lin := sumq q ((List.range n).map (fun j =>
    if redM q (bump β j) == δ then a.getD j 0 else 0))
  let c1 := addq q 1 (mulq q 2 (negq q bi))
  let c0 := addq q (mulq q bi bi) (negq q bi)
  addq q quad (addq q (mulq q c1 lin) (if β == δ then c0 else 0))

/-- One reduction pass applying a matrix given by columns to a vector. -/
def matVec (d : ℕ) (cols : List (List ℕ)) (v : List ℕ) : List ℕ :=
  vsum q d ((List.range cols.length).map (fun t => smul q (v.getD t 0) (cols.getD t [])))

def vsub (x y : List ℕ) : List ℕ := axpy q 1 x y
def vlin (c : ℕ) (x y : List ℕ) : List ℕ := (x.zip y).map (fun p => addq q p.1 (mulq q c p.2))

structure Inst where
  n : ℕ
  m : ℕ
  cols : List (List ℕ)   -- column i of A
  b : List ℕ

section Main
variable (I : Inst) (D : ℕ)

def MVl : List (List ℕ) := monosLt q I.n D
def MDl : List (List ℕ) := monosEq q I.n D
def M2l : List (List ℕ) := monosEq q I.n (D - 2)
def dVl : ℕ := (MVl q I D).length
def dDl : ℕ := (MDl q I D).length
def El : ℕ := I.m * (M2l q I D).length

/-- `Φ` columns with unit payloads. -/
def phiGens : List (List ℕ × List ℕ) := (List.range I.m).flatMap (fun i =>
    (List.range (M2l q I D).length).map (fun t =>
      (colPhi q (MDl q I D) (I.cols.getD i []) ((M2l q I D).getD t []),
        unitV (El q I D) (i * (M2l q I D).length + t))))

def Bphi : List Row := insertAll q [] (phiGens q I D)

/-- `Q_α` (as a payload) for the `t`-th degree-`D` monomial, given the echelon form `BP` of `Φ`. -/
def Qvec (BP : List Row) (t : ℕ) : List ℕ :=
  smul q (q - 1) (reduce q BP (unitV (dDl q I D) t, zeroV (El q I D))).2

/-- Coordinates of `r_α` on `MV`. -/
def rvec (Qα : List ℕ) : List ℕ := (MVl q I D).map (fun δ => negq q (sumq q
    ((List.range I.m).flatMap (fun i => (List.range (M2l q I D).length).map (fun t =>
      mulq q (Qα.getD (i * (M2l q I D).length + t) 0)
        (coefRed q (I.cols.getD i []) (I.b.getD i 0) ((M2l q I D).getD t []) δ))))))

def rvecs (BP : List Row) : List (List ℕ) := (List.range (dDl q I D)).map (fun t => rvec q I D (Qvec q I D BP t))

/-- Column `β` of `X_j`, given the remainders `RV`. -/
def Xcol (RV : List (List ℕ)) (j : ℕ) (β : List ℕ) : List ℕ :=
  let γ := redM q (bump β j)
  if γ.sum < D then unitV (dVl q I D) (idxOf (MVl q I D) γ)
  else RV.getD (idxOf (MDl q I D) γ) (zeroV (dVl q I D))

def Xcols (RV : List (List ℕ)) : List (List (List ℕ)) :=
  (List.range I.n).map (fun j => (MVl q I D).map (Xcol q I D RV j))

variable (XC : List (List (List ℕ)))

def Xl (j : ℕ) (v : List ℕ) : List ℕ := matVec q (dVl q I D) (XC.getD j []) v

def Ll (i : ℕ) (v : List ℕ) : List ℕ :=
  vsum q (dVl q I D) ((List.range I.n).map (fun j => smul q ((I.cols.getD i []).getD j 0) (Xl q I D XC j v)))

def Fl (i : ℕ) (v : List ℕ) : List ℕ :=
  let bi := I.b.getD i 0
  let w := vlin q 1 (vlin q (negq q bi) (Ll q I D XC i v) v) v
  vlin q (negq q bi) (Ll q I D XC i w) w

def Hl (j : ℕ) (v : List ℕ) : List ℕ :=
  vsub q ((List.replicate q j).foldl (fun u j' => Xl q I D XC j' u) v) (Xl q I D XC j v)

def Cl (j k : ℕ) (v : List ℕ) : List ℕ :=
  vsub q (Xl q I D XC j (Xl q I D XC k v)) (Xl q I D XC k (Xl q I D XC j v))

def gens0 : List (List ℕ) := (List.range (dVl q I D)).flatMap (fun t =>
    let v := unitV (dVl q I D) t
    ((List.range I.n).flatMap (fun j => (List.range I.n).filterMap (fun k =>
      if j < k then some (Cl q I D XC j k v) else none))) ++
    (List.range I.n).map (fun j => Hl q I D XC j v) ++
    (List.range I.m).map (fun i => Fl q I D XC i v))

def B0 : List Row := insertAll q [] ((gens0 q I D XC).map (fun v => (v, v)))

def stepB (B : List Row) : List Row :=
  insertAll q B (B.flatMap (fun r => (List.range I.n).map (fun j =>
    (Xl q I D XC j r.2.1, Xl q I D XC j r.2.1))))

def Bk (k : ℕ) : List Row := (List.range k).foldl (fun B _ => stepB q I D XC B) (B0 q I D XC)

def outTest (B : List Row) (j c : ℕ) : Bool :=
  let v := vlin q (negq q c) (unitV (dVl q I D) (idxOf (MVl q I D) (unitV I.n j)))
    (unitV (dVl q I D) (idxOf (MVl q I D) (zeroV I.n)))
  (reduce q B (v, v)).1.all (fun a => a % q == 0)

def readOut (B : List Row) : List ℕ :=
  (List.range I.n).map (fun j => (List.range q).findIdx (fun c => outTest q I D B j c))

/-- The main algorithm with degree `D`. -/
def mainDec : List ℕ :=
  let BP := Bphi q I D
  let RV := rvecs q I D BP
  let XC := Xcols q I D RV
  readOut q I D (Bk q I D XC (dVl q I D + 1))

end Main

/-- All vectors in `F_q^k`. -/
def allVecs : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range q).flatMap (fun e => (allVecs k).map (fun t => e :: t))

def consistent (I : Inst) (u : List ℕ) : Bool :=
  (List.range I.m).all (fun i =>
    let r := addq q (I.b.getD i 0) (negq q (sumq q ((List.range I.n).map
      (fun j => mulq q ((I.cols.getD i []).getD j 0) (u.getD j 0)))))
    r == 0 || r == 1)

def bruteDec (I : Inst) : List ℕ :=
  ((allVecs q I.n).find? (consistent q I)).getD (zeroV I.n)

end T17

end File_T17_Algo

section File_T17M_AlgoC

/-! # The decoder written over a precomputed context (for the machine) -/

namespace T17M

open T17

/-- Context: `n, m, range n, range m, columns, b, D, MV, MD, M2, range E`. -/
abbrev Ctx := ℕ × ℕ × List ℕ × List ℕ × List (List ℕ) × List ℕ × ℕ × List (List ℕ) × List (List ℕ) ×
  List (List ℕ) × List ℕ

@[reducible] def Ctx.n (c : Ctx) : ℕ := c.1
@[reducible] def Ctx.m (c : Ctx) : ℕ := c.2.1
@[reducible] def Ctx.nR (c : Ctx) : List ℕ := c.2.2.1
@[reducible] def Ctx.mR (c : Ctx) : List ℕ := c.2.2.2.1
@[reducible] def Ctx.cols (c : Ctx) : List (List ℕ) := c.2.2.2.2.1
@[reducible] def Ctx.b (c : Ctx) : List ℕ := c.2.2.2.2.2.1
@[reducible] def Ctx.D (c : Ctx) : ℕ := c.2.2.2.2.2.2.1
@[reducible] def Ctx.MV (c : Ctx) : List (List ℕ) := c.2.2.2.2.2.2.2.1
@[reducible] def Ctx.MD (c : Ctx) : List (List ℕ) := c.2.2.2.2.2.2.2.2.1
@[reducible] def Ctx.M2 (c : Ctx) : List (List ℕ) := c.2.2.2.2.2.2.2.2.2.1
@[reducible] def Ctx.ER (c : Ctx) : List ℕ := c.2.2.2.2.2.2.2.2.2.2

variable (q : ℕ)

/-- The context of an instance. -/
def ctxOf (I : Inst) (D : ℕ) : Ctx :=
  (I.n, I.m, List.range I.n, List.range I.m, I.cols, I.b, D, monosLt q I.n D, monosEq q I.n D,
    monosEq q I.n (D - 2), List.range (I.m * (monosEq q I.n (D - 2)).length))

def unitVL (R : List ℕ) (t : ℕ) : List ℕ := R.map (fun r => if r = t then 1 else 0)
def zeroVL (R : List ℕ) : List ℕ := R.map (fun _ => 0)
def vsumL (R : List ℕ) (vs : List (List ℕ)) : List ℕ :=
  R.map (fun r => (vs.map (fun v => v.getD r 0)).foldl (addq q) 0)
def matVecL (R : List ℕ) (cols : List (List ℕ)) (v : List ℕ) : List ℕ :=
  vsumL q R ((List.range cols.length).map (fun t => smul q (v.getD t 0) (cols.getD t [])))

theorem unitVL_range (d t : ℕ) : unitVL (List.range d) t = unitV d t := rfl
theorem zeroVL_range (d : ℕ) : zeroVL (List.range d) = zeroV d := by
  simp [zeroVL, zeroV, List.map_const']
theorem vsumL_range (d : ℕ) (vs : List (List ℕ)) : vsumL q (List.range d) vs = vsum q d vs := rfl
theorem matVecL_range (d : ℕ) (cols : List (List ℕ)) (v : List ℕ) :
    matVecL q (List.range d) cols v = matVec q d cols v := rfl

section
variable (c : Ctx)

def VR : List ℕ := List.range c.MV.length

def phiGensC : List (List ℕ × List ℕ) := c.mR.flatMap (fun i =>
    (List.range c.M2.length).map (fun t =>
      (colPhi q c.MD (c.cols.getD i []) (c.M2.getD t []), unitVL c.ER (i * c.M2.length + t))))

def BphiC : List Row := insertAll q [] (phiGensC q c)

def QvecC (BP : List Row) (t : ℕ) : List ℕ :=
  smul q (q - 1) (reduce q BP (unitVL (List.range c.MD.length) t, zeroVL c.ER)).2

def rvecC (Qα : List ℕ) : List ℕ := c.MV.map (fun δ => negq q (sumq q
    (c.mR.flatMap (fun i => (List.range c.M2.length).map (fun t =>
      mulq q (Qα.getD (i * c.M2.length + t) 0)
        (coefRed q (c.cols.getD i []) (c.b.getD i 0) (c.M2.getD t []) δ))))))

def rvecsC (BP : List Row) : List (List ℕ) :=
  (List.range c.MD.length).map (fun t => rvecC q c (QvecC q c BP t))

def XcolC (RV : List (List ℕ)) (j : ℕ) (β : List ℕ) : List ℕ :=
  let γ := redM q (bump β j)
  if γ.sum < c.D then unitVL (VR c) (idxOf c.MV γ)
  else RV.getD (idxOf c.MD γ) (zeroVL (VR c))

def XcolsC (RV : List (List ℕ)) : List (List (List ℕ)) :=
  c.nR.map (fun j => c.MV.map (XcolC q c RV j))

variable (XC : List (List (List ℕ)))

def XlC (j : ℕ) (v : List ℕ) : List ℕ := matVecL q (VR c) (XC.getD j []) v

def LlC (i : ℕ) (v : List ℕ) : List ℕ :=
  vsumL q (VR c) (c.nR.map (fun j => smul q ((c.cols.getD i []).getD j 0) (XlC q c XC j v)))

def FlC (i : ℕ) (v : List ℕ) : List ℕ :=
  let bi := c.b.getD i 0
  let w := vlin q 1 (vlin q (negq q bi) (LlC q c XC i v) v) v
  vlin q (negq q bi) (LlC q c XC i w) w

def HlC (j : ℕ) (v : List ℕ) : List ℕ :=
  vsub q ((List.replicate q j).foldl (fun u j' => XlC q c XC j' u) v) (XlC q c XC j v)

def ClC (j k : ℕ) (v : List ℕ) : List ℕ :=
  vsub q (XlC q c XC j (XlC q c XC k v)) (XlC q c XC k (XlC q c XC j v))

def gens0C : List (List ℕ) := (VR c).flatMap (fun t =>
    let v := unitVL (VR c) t
    (c.nR.flatMap (fun j => c.nR.filterMap (fun k =>
      if j < k then some (ClC q c XC j k v) else none))) ++
    c.nR.map (fun j => HlC q c XC j v) ++
    c.mR.map (fun i => FlC q c XC i v))

def B0C : List Row := insertAll q [] ((gens0C q c XC).map (fun v => (v, v)))

def stepBC (B : List Row) : List Row :=
  insertAll q B (B.flatMap (fun r => c.nR.map (fun j => (XlC q c XC j r.2.1, XlC q c XC j r.2.1))))

/-- Rounds of the closure, truncated to `dim V` rows (a no-op on echelon forms). -/
def BkC (k : List ℕ) : List Row := k.foldl (fun B _ => (stepBC q c XC B).take c.MV.length) (B0C q c XC)

def outTestC (B : List Row) (j c' : ℕ) : Bool :=
  let v := vlin q (negq q c') (unitVL (VR c) (idxOf c.MV (unitVL c.nR j)))
    (unitVL (VR c) (idxOf c.MV (zeroVL c.nR)))
  (reduce q B (v, v)).1.all (fun a => a % q == 0)

def readOutC (B : List Row) : List ℕ :=
  c.nR.map (fun j => (List.range q).findIdx (fun c' => outTestC q c B j c'))

end

/-- The main decoder over a context. -/
def mainDecC (c : Ctx) : List ℕ :=
  let BP := BphiC q c
  let RV := rvecsC q c BP
  let XC := XcolsC q c RV
  readOutC q c (BkC q c XC (List.range (c.MV.length + 1)))

end T17M

end File_T17M_AlgoC

section File_T17M_PolyC1

/-! # `Poly` for the arithmetic and echelon routines -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

section Size

theorem enc_nat (a : ℕ) : (enc a).length = a.size := Nat.size_eq_bits_len a

theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.2 (Nat.lt_two_pow_self)

theorem size_add (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.2
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h1 : 2 ^ a.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ b.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem enc_list_nat_le (l : List ℕ) (S : ℕ) (h : ∀ a ∈ l, a.size ≤ S) :
    (enc l).length ≤ l.length * (2 * S + 1) :=
  EncodedList.length_bound _ l S (fun a ha => by rw [enc_nat]; exact h a ha)

theorem length_le_enc {β : Type} [Coding β] (l : List β) : l.length ≤ (enc l).length :=
  EncodedList.length_le _ l

theorem enc_pair (α β : Type) [Coding α] [Coding β] (x : α × β) :
    (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length := encodePair_length _ _ _

theorem enc_list_append {β : Type} [Coding β] (l l' : List β) :
    (enc (l ++ l')).length = (enc l).length + (enc l').length := by
  change (encodeList enc (l ++ l')).length = _
  rw [EncodedList.append, List.length_append]; rfl

theorem enc_list_cons {β : Type} [Coding β] (a : β) (l : List β) :
    (enc (a :: l)).length = 2 * (enc a).length + 1 + (enc l).length := EncodedList.cons_length _ _ _

theorem enc_mem_le {β : Type} [Coding β] (l : List β) (a : β) (h : a ∈ l) :
    (enc a).length ≤ (enc l).length := EncodedList.member_length _ l a h

end Size

variable (q : ℕ)

theorem addq_lt (hq : 0 < q) (a b : ℕ) : addq q a b < q := Nat.mod_lt _ hq
theorem mulq_lt (hq : 0 < q) (a b : ℕ) : mulq q a b < q := Nat.mod_lt _ hq
theorem negq_lt (hq : 0 < q) (a : ℕ) : negq q a < q := Nat.mod_lt _ hq

section Poly1
variable {α : Type} [Coding α]

@[fun_prop] theorem Poly.addq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => addq q (f x) (g x)) := by unfold addq; fun_prop
@[fun_prop] theorem Poly.mulq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => mulq q (f x) (g x)) := by unfold mulq; fun_prop
@[fun_prop] theorem Poly.negq_comp {f : α → ℕ} (hf : Poly f) :
    Poly (fun x => negq q (f x)) := by unfold negq; fun_prop

@[fun_prop] theorem Poly.sumq_comp [NeZero q] {l : α → List ℕ} (hl : Poly l) : Poly (fun x => sumq q (l x)) := by
  unfold sumq
  have hq : ∀ b a, (enc (addq q b a)).length ≤ (enc b).length + q.size := by
    intro b a
    rw [enc_nat, enc_nat]
    have := Nat.size_le_size (le_of_lt (addq_lt q (Nat.pos_of_ne_zero (NeZero.ne q)) b a)); omega
  exact Poly.list_foldl (f := fun _ b a => addq q b a) (by fun_prop) hl (Automatic.Poly.const 0)
    (Polynomial.C q.size) (fun x b a => by simpa using hq b a)

theorem list_sum_foldl (l : List ℕ) : l.sum = l.foldl (· + ·) 0 := by
  rw [List.sum_eq_foldl]

@[fun_prop] theorem Poly.list_sum_comp {l : α → List ℕ} (hl : Poly l) : Poly (fun x => (l x).sum) := by
  simp only [list_sum_foldl]
  exact Poly.list_foldl (f := fun _ b a => b + a) (by fun_prop) hl (Automatic.Poly.const 0) (X + 1)
    (fun x b a => by
      simp only [enc_nat, eval_add, eval_X, eval_one]
      have := size_add b a
      have : (enc a).length = a.size := enc_nat a
      omega)

end Poly1

end T17M

end File_T17M_PolyC1

section File_T17M_Fuel

/-! # The fuel stage: doubling a list `k` times -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

def dbl : ℕ → List ℕ → List ℕ
  | 0, l => l
  | k + 1, l => dbl k (l ++ l)

theorem length_dbl (k : ℕ) (l : List ℕ) : (dbl k l).length = 2 ^ k * l.length := by
  induction k generalizing l with
  | zero => simp [dbl]
  | succ k ih => simp only [dbl, ih, List.length_append, pow_succ]; ring

section
variable {α : Type} [Coding α] [Inhabited α]

def fbody (s : α × (ℕ × List ℕ)) : (α × List ℕ) ⊕ (α × (ℕ × List ℕ)) :=
  if s.2.1 == 0 then .inl (s.1, s.2.2) else .inr (s.1, (s.2.1 - 1, s.2.2 ++ s.2.2))

noncomputable def fbodyProgram : PolyProgram (enc : α × (ℕ × List ℕ) → List Bool)
    (encodeLoop (enc : α × (ℕ × List ℕ) → List Bool) (enc : α × List ℕ → List Bool)) fbody := by
  have hc : Poly (fun s : α × (ℕ × List ℕ) => s.2.1 == 0) := by fun_prop
  have hd : Poly (fun s : α × (ℕ × List ℕ) => (s.1, s.2.2)) := by fun_prop
  have hr : Poly (fun s : α × (ℕ × List ℕ) => (s.1, (s.2.1 - 1, s.2.2 ++ s.2.2))) := by fun_prop
  exact (PolyProgram.ite hc.program (hr.program.comp (PolyProgram.injectRight enc enc))
    (hd.program.comp (PolyProgram.injectLeft enc enc))).congr _ (fun s => by
      simp only [fbody, Function.comp_apply])

def fres (s : α × (ℕ × List ℕ)) : α × List ℕ := (s.1, dbl s.2.1 s.2.2)

def fsize (s : α × (ℕ × List ℕ)) : ℕ := 2 * (enc s.1).length + 3 + 2 * s.2.1.size + 2 ^ s.2.1 * (enc s.2.2).length

theorem enc_list_dup (l : List ℕ) : (enc (l ++ l)).length = 2 * (enc l).length := by
  rw [enc_list_append]; ring

theorem fuel_run (x : α) (k : ℕ) (fl : List ℕ) (S : ℕ)
    (hS : 2 * (enc x).length + 3 + 2 * k.size + 2 ^ k * (enc fl).length ≤ S) :
    BoundedRun (enc : α × (ℕ × List ℕ) → List Bool) fbody S (k + 1) (x, (k, fl)) (x, dbl k fl) := by
  induction k generalizing fl with
  | zero =>
    apply BoundedRun.stop
    · change (enc (x, ((0 : ℕ), fl))).length ≤ S
      simp only [enc_pair, enc_nat, Nat.size_zero]
      simp only [pow_zero, one_mul, Nat.size_zero, mul_zero, add_zero] at hS
      omega
    · simp [fbody, dbl]
  | succ k ih =>
    apply BoundedRun.step
    · change (enc (x, (k + 1, fl))).length ≤ S
      simp only [enc_pair, enc_nat]
      have : (enc fl).length ≤ 2 ^ (k + 1) * (enc fl).length := Nat.le_mul_of_pos_left _ (by positivity)
      omega
    · simp only [fbody, Nat.add_one_sub_one]; rfl
    · apply ih
      rw [enc_list_dup]
      have h1 : k.size ≤ (k + 1).size := Nat.size_le_size (Nat.le_succ k)
      have h2 : 2 ^ k * (2 * (enc fl).length) = 2 ^ (k + 1) * (enc fl).length := by ring
      omega

noncomputable def fuelTimed : Timed (enc : α × (ℕ × List ℕ) → List Bool) (enc : α × List ℕ → List Bool) fres
    (fun s => (s.2.1 + 1) * (fbodyProgram (α := α)).passTime (fsize s)) :=
  Timed.loop fbodyProgram fres (fun s => s.2.1 + 1) fsize (fun s => fuel_run s.1 s.2.1 s.2.2 _ le_rfl)

end

end T17M

end File_T17M_Fuel

section File_T17M_PolyC2

/-! # `Poly` for vectors and the echelon routines -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ) [NeZero q]

theorem q_pos' : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)

/-- Encoded size of a vector with entries below `q`. -/
theorem enc_vec_le (l : List ℕ) (h : ∀ a ∈ l, a < q) : (enc l).length ≤ l.length * (2 * q.size + 1) :=
  enc_list_nat_le l q.size (fun a ha => Nat.size_le_size (le_of_lt (h a ha)))

theorem axpy_lt (c : ℕ) (x y : List ℕ) : ∀ a ∈ axpy q c x y, a < q := by
  intro a ha
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  exact addq_lt q (q_pos' q) _ _

theorem smul_lt (c : ℕ) (x : List ℕ) : ∀ a ∈ smul q c x, a < q := by
  intro a ha
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  exact mulq_lt q (q_pos' q) _ _

theorem length_axpy_le (c : ℕ) (x y : List ℕ) : (axpy q c x y).length ≤ x.length ∧ (axpy q c x y).length ≤ y.length := by
  simp [axpy]

theorem length_reduce_le (B : List Row) (xw : List ℕ × List ℕ) :
    (reduce q B xw).1.length ≤ xw.1.length ∧ (reduce q B xw).2.length ≤ xw.2.length := by
  induction B generalizing xw with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons r B ih =>
    obtain ⟨h1, h2⟩ := ih (redStep q xw r)
    simp only [reduce, List.foldl_cons] at h1 h2 ⊢
    exact ⟨h1.trans (length_axpy_le q _ _ _).1, h2.trans (length_axpy_le q _ _ _).1⟩

section
variable {α : Type} [Coding α]

@[fun_prop] theorem Poly.smul_comp {c : α → ℕ} {x : α → List ℕ} (hc : Poly c) (hx : Poly x) :
    Poly (fun a => smul q (c a) (x a)) := by unfold smul mulq; fun_prop
@[fun_prop] theorem Poly.axpy_comp {c : α → ℕ} {x y : α → List ℕ} (hc : Poly c) (hx : Poly x) (hy : Poly y) :
    Poly (fun a => axpy q (c a) (x a) (y a)) := by unfold axpy addq mulq negq; fun_prop
@[fun_prop] theorem Poly.vlin_comp {c : α → ℕ} {x y : α → List ℕ} (hc : Poly c) (hx : Poly x) (hy : Poly y) :
    Poly (fun a => vlin q (c a) (x a) (y a)) := by unfold vlin addq mulq; fun_prop
@[fun_prop] theorem Poly.vsub_comp {x y : α → List ℕ} (hx : Poly x) (hy : Poly y) :
    Poly (fun a => vsub q (x a) (y a)) := by unfold vsub; fun_prop
@[fun_prop] theorem Poly.unitVL_comp {R : α → List ℕ} {t : α → ℕ} (hR : Poly R) (ht : Poly t) :
    Poly (fun a => unitVL (R a) (t a)) := by unfold unitVL; fun_prop
@[fun_prop] theorem Poly.zeroVL_comp {R : α → List ℕ} (hR : Poly R) : Poly (fun a => zeroVL (R a)) := by
  unfold zeroVL; fun_prop
@[fun_prop] theorem Poly.vsumL_comp {R : α → List ℕ} {vs : α → List (List ℕ)} (hR : Poly R) (hv : Poly vs) :
    Poly (fun a => vsumL q (R a) (vs a)) := by
  unfold vsumL
  have : Poly (fun a => (R a).map (fun r => sumq q ((vs a).map (fun v => v.getD r 0)))) := by fun_prop
  simpa only [sumq] using this
@[fun_prop] theorem Poly.matVecL_comp {R : α → List ℕ} {cols : α → List (List ℕ)} {v : α → List ℕ}
    (hR : Poly R) (hc : Poly cols) (hv : Poly v) :
    Poly (fun a => matVecL q (R a) (cols a) (v a)) := by unfold matVecL; fun_prop

theorem redStep_size (xw : List ℕ × List ℕ) (r : Row) :
    (enc (redStep q xw r)).length ≤ 3 * (2 * q.size + 1) * (enc r).length + 1 := by
  simp only [redStep]
  rw [enc_pair]
  have h1 := enc_vec_le q _ (axpy_lt q (xw.1.getD r.1 0) xw.1 r.2.1)
  have h2 := enc_vec_le q _ (axpy_lt q (xw.1.getD r.1 0) xw.2 r.2.2)
  have h3 := (length_axpy_le q (xw.1.getD r.1 0) xw.1 r.2.1).2
  have h4 := (length_axpy_le q (xw.1.getD r.1 0) xw.2 r.2.2).2
  have h5 := length_le_enc r.2.1
  have h6 := length_le_enc r.2.2
  have e1 : (enc r).length = 2 * (enc r.1).length + 1 + (2 * (enc r.2.1).length + 1 + (enc r.2.2).length) := by
    rw [enc_pair, enc_pair]
  have m1 : (axpy q (xw.1.getD r.1 0) xw.1 r.2.1).length * (2 * q.size + 1) ≤ (enc r).length * (2 * q.size + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  have m2 : (axpy q (xw.1.getD r.1 0) xw.2 r.2.2).length * (2 * q.size + 1) ≤ (enc r).length * (2 * q.size + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  nlinarith

@[fun_prop] theorem Poly.reduce_comp {B : α → List Row} {xw : α → List ℕ × List ℕ} (hB : Poly B) (hxw : Poly xw) :
    Poly (fun a => reduce q (B a) (xw a)) := by
  unfold reduce
  have hstep : Poly (fun y : (α × (List ℕ × List ℕ)) × Row => redStep q y.1.2 y.2) := by
    unfold redStep; fun_prop
  exact Poly.list_foldl (f := fun _ acc r => redStep q acc r) hstep hB hxw
    (Polynomial.C (3 * (2 * q.size + 1)) * X + 1) (fun x b r => by
      have := redStep_size q b r
      have hm := polynomial_eval_mono (Polynomial.C (3 * (2 * q.size + 1)) * X + 1)
        (show (enc r).length ≤ (enc x).length + (enc r).length by omega)
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_one] at hm ⊢
      omega)

theorem replicate_eq_map (k : ℕ) {β : Type} (a : β) : List.replicate k a = (List.replicate k (0 : ℕ)).map (fun _ => a) := by
  simp

@[fun_prop] theorem Poly.invq_comp {a : α → ℕ} (ha : Poly a) : Poly (fun x => invq q (a x)) := by
  unfold invq
  have he : (fun x => (List.replicate (q - 2) (a x)).foldl (mulq q) 1) =
      (fun x => ((List.replicate (q - 2) (0 : ℕ)).map (fun _ => a x)).foldl (fun b c => mulq q b c) 1) := by
    funext x; rw [← replicate_eq_map]
  rw [he]
  exact Poly.list_foldl (f := fun _ b c => mulq q b c) (by fun_prop) (by fun_prop) (Automatic.Poly.const 1)
    (Polynomial.C q.size) (fun x b c => by
      simp only [eval_C, enc_nat]
      have := Nat.size_le_size (le_of_lt (mulq_lt q (q_pos' q) b c)); omega)

@[fun_prop] theorem Poly.pivotOf_comp {x : α → List ℕ} (hx : Poly x) : Poly (fun a => pivotOf q (x a)) := by
  unfold pivotOf bne; fun_prop

@[fun_prop] theorem Poly.insertRow_comp {B : α → List Row} {xw : α → List ℕ × List ℕ} (hB : Poly B) (hxw : Poly xw) :
    Poly (fun a => insertRow q (B a) (xw a)) := by
  unfold insertRow; fun_prop

theorem insertRow_size (B : List Row) (xw : List ℕ × List ℕ) :
    (enc (insertRow q B xw)).length ≤ (enc B).length + 10 * (2 * q.size + 1) * (enc xw).length + 10 := by
  unfold insertRow
  simp only
  split_ifs with h
  · rw [enc_list_append, enc_list_cons, enc_pair, enc_pair]
    simp only [enc_nat]
    obtain ⟨l1, l2⟩ := length_reduce_le q B xw
    have hs1 := enc_vec_le q _ (smul_lt q (invq q ((reduce q B xw).1.getD (pivotOf q (reduce q B xw).1) 0)) (reduce q B xw).1)
    have hs2 := enc_vec_le q _ (smul_lt q (invq q ((reduce q B xw).1.getD (pivotOf q (reduce q B xw).1) 0)) (reduce q B xw).2)
    rw [length_smul] at hs1 hs2
    have hp := size_le_self (pivotOf q (reduce q B xw).1)
    have hx : (enc xw).length = 2 * (enc xw.1).length + 1 + (enc xw.2).length := enc_pair _ _ xw
    have hx1 := length_le_enc xw.1
    have hx2 := length_le_enc xw.2
    have hnil : (enc ([] : List Row)).length = 0 := rfl
    have m1 : (reduce q B xw).1.length * (2 * q.size + 1) ≤ (enc xw).length * (2 * q.size + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have m2 : (reduce q B xw).2.length * (2 * q.size + 1) ≤ (enc xw).length * (2 * q.size + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · omega

@[fun_prop] theorem Poly.insertAll_comp {B : α → List Row} {L : α → List (List ℕ × List ℕ)} (hB : Poly B) (hL : Poly L) :
    Poly (fun a => insertAll q (B a) (L a)) := by
  unfold insertAll
  exact Poly.list_foldl (f := fun _ b xw => insertRow q b xw) (by fun_prop) hL hB
    (Polynomial.C (10 * (2 * q.size + 1)) * X + 10) (fun x b xw => by
      have := insertRow_size q b xw
      have hm := polynomial_eval_mono (Polynomial.C (10 * (2 * q.size + 1)) * X + 10)
        (show (enc xw).length ≤ (enc x).length + (enc xw).length by omega)
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat] at hm ⊢
      omega)

end

end T17M

end File_T17M_PolyC2

section File_T17M_PolyC3

/-! # `Poly` for monomial helpers -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

theorem list_beq_eq (l1 l2 : List ℕ) :
    (l1 == l2) = (l1.length == l2.length && (l1.zip l2).all (fun p => p.1 == p.2)) := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp
  | cons a l1 ih =>
    cases l2 with
    | nil => simp
    | cons b l2 =>
      simp only [List.cons_beq_cons, List.length_cons, List.zip_cons_cons, List.all_cons, ih]
      cases h : (a == b) <;> simp_all

variable (q : ℕ) [NeZero q]

section
variable {α : Type} [Coding α]

@[fun_prop] theorem Poly.list_beq_comp {x y : α → List ℕ} (hx : Poly x) (hy : Poly y) :
    Poly (fun a => x a == y a) := by
  simp only [list_beq_eq]; fun_prop

@[fun_prop] theorem Poly.idxOf_comp {Ms : α → List (List ℕ)} {a : α → List ℕ} (hM : Poly Ms) (ha : Poly a) :
    Poly (fun x => idxOf (Ms x) (a x)) := by unfold idxOf; fun_prop

@[fun_prop] theorem Poly.bump_comp {β : α → List ℕ} {j : α → ℕ} (hb : Poly β) (hj : Poly j) :
    Poly (fun x => bump (β x) (j x)) := by unfold bump; fun_prop

@[fun_prop] theorem Poly.redM_comp {β : α → List ℕ} (hb : Poly β) : Poly (fun x => redM q (β x)) := by
  unfold redM redE; fun_prop

@[fun_prop] theorem Poly.colPhi_comp {MD : α → List (List ℕ)} {a β : α → List ℕ} (hM : Poly MD) (ha : Poly a)
    (hb : Poly β) : Poly (fun x => colPhi q (MD x) (a x) (β x)) := by
  unfold colPhi; dsimp only; fun_prop

@[fun_prop] theorem Poly.coefRed_comp {a : α → List ℕ} {bi : α → ℕ} {β δ : α → List ℕ} (ha : Poly a)
    (hbi : Poly bi) (hb : Poly β) (hd : Poly δ) : Poly (fun x => coefRed q (a x) (bi x) (β x) (δ x)) := by
  unfold coefRed; dsimp only; fun_prop

end

end T17M

end File_T17M_PolyC3

section File_T17M_PolyC4

/-! # `Poly` for the context decoder -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ) [NeZero q]

theorem foldl_addq_lt (l : List ℕ) (b : ℕ) (hb : b < q) : l.foldl (addq q) b < q := by
  induction l generalizing b with
  | nil => exact hb
  | cons a l ih => exact ih _ (addq_lt q (q_pos' q) _ _)

theorem vsumL_lt (R : List ℕ) (vs : List (List ℕ)) : ∀ a ∈ vsumL q R vs, a < q := by
  intro a ha
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha
  exact foldl_addq_lt q _ 0 (q_pos' q)

theorem length_vsumL (R : List ℕ) (vs : List (List ℕ)) : (vsumL q R vs).length = R.length := by
  simp [vsumL]

theorem ctx_MV_le (c : Ctx) : (enc c.MV).length ≤ (enc c).length := by
  simp only [Ctx.MV, enc_pair]; omega

theorem XlC_size (c : Ctx) (XC : List (List (List ℕ))) (j : ℕ) (v : List ℕ) :
    (enc (XlC q c XC j v)).length ≤ (2 * q.size + 1) * (enc c).length := by
  unfold XlC matVecL
  have h := enc_vec_le q (vsumL q (VR c) ((List.range (XC.getD j []).length).map
    (fun t => smul q (v.getD t 0) ((XC.getD j []).getD t [])))) (vsumL_lt q _ _)
  rw [length_vsumL] at h
  have h2 : (VR c).length ≤ (enc c).length := by
    simp only [VR, List.length_range]
    exact (length_le_enc c.MV).trans (ctx_MV_le c)
  nlinarith

section
variable {α : Type} [Coding α]

@[fun_prop] theorem Poly.XlC_comp {c : α → Ctx} {XC : α → List (List (List ℕ))} {j : α → ℕ} {v : α → List ℕ}
    (hc : Poly c) (hX : Poly XC) (hj : Poly j) (hv : Poly v) :
    Poly (fun x => XlC q (c x) (XC x) (j x) (v x)) := by
  unfold XlC VR; fun_prop

@[fun_prop] theorem Poly.LlC_comp {c : α → Ctx} {XC : α → List (List (List ℕ))} {i : α → ℕ} {v : α → List ℕ}
    (hc : Poly c) (hX : Poly XC) (hi : Poly i) (hv : Poly v) :
    Poly (fun x => LlC q (c x) (XC x) (i x) (v x)) := by
  unfold LlC VR; fun_prop

@[fun_prop] theorem Poly.FlC_comp {c : α → Ctx} {XC : α → List (List (List ℕ))} {i : α → ℕ} {v : α → List ℕ}
    (hc : Poly c) (hX : Poly XC) (hi : Poly i) (hv : Poly v) :
    Poly (fun x => FlC q (c x) (XC x) (i x) (v x)) := by
  unfold FlC; dsimp only; fun_prop

@[fun_prop] theorem Poly.ClC_comp {c : α → Ctx} {XC : α → List (List (List ℕ))} {j k : α → ℕ} {v : α → List ℕ}
    (hc : Poly c) (hX : Poly XC) (hj : Poly j) (hk : Poly k) (hv : Poly v) :
    Poly (fun x => ClC q (c x) (XC x) (j x) (k x) (v x)) := by
  unfold ClC; fun_prop

set_option maxHeartbeats 2000000 in
theorem Poly.Hfold : Poly (fun y : (Ctx × List (List (List ℕ))) × (ℕ × List ℕ) =>
    (List.replicate q y.2.1).foldl (fun u j' => XlC q y.1.1 y.1.2 j' u) y.2.2) := by
  have he : (fun y : (Ctx × List (List (List ℕ))) × (ℕ × List ℕ) =>
      (List.replicate q y.2.1).foldl (fun u j' => XlC q y.1.1 y.1.2 j' u) y.2.2) =
      (fun y => ((List.replicate q (0 : ℕ)).map (fun _ => y.2.1)).foldl
        (fun u j' => XlC q y.1.1 y.1.2 j' u) y.2.2) := by
    funext y; rw [← replicate_eq_map]
  rw [he]
  have hf : Poly (fun z : (((Ctx × List (List (List ℕ))) × (ℕ × List ℕ)) × List ℕ) × ℕ =>
      XlC q z.1.1.1.1 z.1.1.1.2 z.2 z.1.2) := by
    exact Poly.XlC_comp q (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have has : Poly (fun y : (Ctx × List (List (List ℕ))) × (ℕ × List ℕ) =>
      (List.replicate q (0 : ℕ)).map (fun _ => y.2.1)) := by fun_prop
  have hb : Poly (fun y : (Ctx × List (List (List ℕ))) × (ℕ × List ℕ) => y.2.2) := by fun_prop
  refine Poly.list_foldl (f := fun y u j' => XlC q y.1.1 y.1.2 j' u) hf has hb
    (Polynomial.C (2 * q.size + 1) * X) (fun y u j' => ?_)
  have h1 := XlC_size q y.1.1 y.1.2 j' u
  have h2 : (enc y.1.1).length ≤ (enc y).length := by
    have e1 := enc_pair _ _ y
    have e2 := enc_pair _ _ y.1
    omega
  have h3 : (2 * q.size + 1) * (enc y.1.1).length ≤ (2 * q.size + 1) * ((enc y).length + (enc j').length) :=
    Nat.mul_le_mul_left _ (by omega)
  simp only [eval_mul, eval_C, eval_X]
  omega

@[fun_prop] theorem Poly.HlC_comp {c : α → Ctx} {XC : α → List (List (List ℕ))} {j : α → ℕ} {v : α → List ℕ}
    (hc : Poly c) (hX : Poly XC) (hj : Poly j) (hv : Poly v) :
    Poly (fun x => HlC q (c x) (XC x) (j x) (v x)) := by
  unfold HlC
  have h := Automatic.Poly.comp (Poly.Hfold q) (show Poly (fun x => ((c x, XC x), (j x, v x))) by fun_prop)
  exact Poly.vsub_comp q h (by fun_prop)

end

/-! ## Size of `insertAll` -/

theorem rowBound_mono {M M' : ℕ} (h : M ≤ M') :
    3 * (2 * q.size + 1) * M + 2 * M + 2 ≤ 3 * (2 * q.size + 1) * M' + 2 * M' + 2 := by
  have := Nat.mul_le_mul_left (3 * (2 * q.size + 1)) h; omega

theorem insertRow_ext (B : List Row) (xw : List ℕ × List ℕ) (M : ℕ) (h1 : xw.1.length ≤ M)
    (h2 : xw.2.length ≤ M) : ∃ T, insertRow q B xw = B ++ T ∧
      ∀ r ∈ T, (enc r).length ≤ 3 * (2 * q.size + 1) * M + 2 * M + 2 := by
  unfold insertRow
  simp only
  split_ifs with h
  · refine ⟨_, rfl, ?_⟩
    intro r hr
    rw [List.mem_singleton] at hr
    subst hr
    rw [enc_pair, enc_pair, enc_nat]
    obtain ⟨l1, l2⟩ := length_reduce_le q B xw
    have hs1 := enc_vec_le q _ (smul_lt q (invq q ((reduce q B xw).1.getD (pivotOf q (reduce q B xw).1) 0)) (reduce q B xw).1)
    have hs2 := enc_vec_le q _ (smul_lt q (invq q ((reduce q B xw).1.getD (pivotOf q (reduce q B xw).1) 0)) (reduce q B xw).2)
    rw [length_smul] at hs1 hs2
    have hp := size_le_self (pivotOf q (reduce q B xw).1)
    have m1 : (reduce q B xw).1.length * (2 * q.size + 1) ≤ M * (2 * q.size + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have m2 : (reduce q B xw).2.length * (2 * q.size + 1) ≤ M * (2 * q.size + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · exact ⟨[], by simp, by simp⟩

theorem insertAll_ext (items : List (List ℕ × List ℕ)) (M : ℕ)
    (h : ∀ xw ∈ items, xw.1.length ≤ M ∧ xw.2.length ≤ M) (B : List Row) :
    ∃ T, insertAll q B items = B ++ T ∧ ∀ r ∈ T, (enc r).length ≤ 3 * (2 * q.size + 1) * M + 2 * M + 2 := by
  induction items generalizing B with
  | nil => exact ⟨[], by simp [insertAll], by simp⟩
  | cons xw items ih =>
    obtain ⟨T1, e1, h1⟩ := insertRow_ext q B xw M (h xw List.mem_cons_self).1 (h xw List.mem_cons_self).2
    obtain ⟨T2, e2, h2⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) (insertRow q B xw)
    refine ⟨T1 ++ T2, ?_, ?_⟩
    · simp only [insertAll, List.foldl_cons] at e2 ⊢
      rw [e2, e1, List.append_assoc]
    · intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact h1 r hr
      · exact h2 r hr

theorem enc_take_le {β : Type} [Coding β] (l : List β) (k : ℕ) : (enc (l.take k)).length ≤ (enc l).length := by
  conv_rhs => rw [← List.take_append_drop k l]
  rw [enc_list_append]; omega

theorem enc_take_append_le {β : Type} [Coding β] (B T : List β) (k g : ℕ) (hT : ∀ r ∈ T, (enc r).length ≤ g) :
    (enc ((B ++ T).take k)).length ≤ (enc B).length + k * (2 * g + 1) := by
  rw [List.take_append, enc_list_append]
  have h1 := enc_take_le B k
  have h2 := EncodedList.length_bound (enc : β → List Bool) (T.take (k - B.length)) g
    (fun r hr => hT r (List.mem_of_mem_take hr))
  have h3 : (T.take (k - B.length)).length ≤ k := by simp
  have h4 : (T.take (k - B.length)).length * (2 * g + 1) ≤ k * (2 * g + 1) := Nat.mul_le_mul_right _ h3
  change (enc (List.take k B)).length + (encodeList enc (List.take (k - B.length) T)).length ≤ _
  omega

end T17M

end File_T17M_PolyC4

section File_T17M_PolyC5

/-! # `Poly` for the whole context decoder -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ) [NeZero q]

theorem filterMap_ite {β γ : Type} (l : List β) (p : β → Bool) (f : β → γ) :
    l.filterMap (fun k => if p k then some (f k) else none) = (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, List.filter_cons]

theorem Poly.phiGensC_p : Poly (fun c : Ctx => phiGensC q c) := by unfold phiGensC; fun_prop
@[fun_prop] theorem Poly.phiGensC_comp {α : Type} [Coding α] {c : α → Ctx} (hc : Poly c) :
    Poly (fun x => phiGensC q (c x)) := Automatic.Poly.comp (Poly.phiGensC_p q) hc
theorem Poly.BphiC_p : Poly (fun c : Ctx => BphiC q c) := by unfold BphiC; fun_prop
@[fun_prop] theorem Poly.BphiC_comp {α : Type} [Coding α] {c : α → Ctx} (hc : Poly c) :
    Poly (fun x => BphiC q (c x)) := Automatic.Poly.comp (Poly.BphiC_p q) hc

set_option maxHeartbeats 4000000 in
theorem Poly.rvecsC_p : Poly (fun y : Ctx × List Row => rvecsC q y.1 y.2) := by
  unfold rvecsC rvecC QvecC; fun_prop

@[fun_prop] theorem Poly.rvecsC_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List Row} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => rvecsC q (a x) (b x)) :=
  Automatic.Poly.comp (f := fun y : Ctx × List Row => rvecsC q y.1 y.2) (Poly.rvecsC_p q) (g := fun x => (a x, b x)) (Automatic.Poly.pair ha hb)

theorem Poly.XcolsC_p : Poly (fun y : Ctx × List (List ℕ) => XcolsC q y.1 y.2) := by
  unfold XcolsC XcolC VR; dsimp only; fun_prop

@[fun_prop] theorem Poly.XcolsC_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List (List ℕ)} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => XcolsC q (a x) (b x)) :=
  Automatic.Poly.comp (f := fun y : Ctx × List (List ℕ) => XcolsC q y.1 y.2) (Poly.XcolsC_p q) (g := fun x => (a x, b x)) (Automatic.Poly.pair ha hb)

theorem Poly.gens0C_p : Poly (fun y : Ctx × List (List (List ℕ)) => gens0C q y.1 y.2) := by
  unfold gens0C VR
  dsimp only
  have he : ∀ (y : Ctx × List (List (List ℕ))) (t j : ℕ),
      y.1.nR.filterMap (fun k => if j < k then some (ClC q y.1 y.2 j k (unitVL (List.range y.1.MV.length) t))
        else none) = (y.1.nR.filter (fun k => decide (j < k))).map
          (fun k => ClC q y.1 y.2 j k (unitVL (List.range y.1.MV.length) t)) := by
    intro y t j
    rw [← filterMap_ite]
    congr 1; funext k; simp
  simp only [he]
  fun_prop

@[fun_prop] theorem Poly.gens0C_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List (List (List ℕ))} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => gens0C q (a x) (b x)) :=
  Automatic.Poly.comp (f := fun y : Ctx × List (List (List ℕ)) => gens0C q y.1 y.2) (Poly.gens0C_p q) (g := fun x => (a x, b x)) (Automatic.Poly.pair ha hb)

theorem Poly.B0C_p : Poly (fun y : Ctx × List (List (List ℕ)) => B0C q y.1 y.2) := by
  unfold B0C
  fun_prop

@[fun_prop] theorem Poly.B0C_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List (List (List ℕ))} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => B0C q (a x) (b x)) :=
  Automatic.Poly.comp (f := fun y : Ctx × List (List (List ℕ)) => B0C q y.1 y.2) (Poly.B0C_p q) (g := fun x => (a x, b x)) (Automatic.Poly.pair ha hb)

theorem Poly.stepBC_p : Poly (fun y : (Ctx × List (List (List ℕ))) × List Row => stepBC q y.1.1 y.1.2 y.2) := by
  unfold stepBC; fun_prop

@[fun_prop] theorem Poly.stepBC_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List (List (List ℕ))} {d : α → List Row} (ha : Poly a)
    (hb : Poly b) (hd : Poly d) :
    Poly (fun x => stepBC q (a x) (b x) (d x)) :=
  Automatic.Poly.comp (f := fun y : (Ctx × List (List (List ℕ))) × List Row => stepBC q y.1.1 y.1.2 y.2) (Poly.stepBC_p q)
    (g := fun x => ((a x, b x), d x)) (Automatic.Poly.pair (Automatic.Poly.pair ha hb) hd)

theorem stepBC_ext (c : Ctx) (XC : List (List (List ℕ))) (B : List Row) :
    ∃ T, stepBC q c XC B = B ++ T ∧ ∀ r ∈ T, (enc r).length ≤
      3 * (2 * q.size + 1) * c.MV.length + 2 * c.MV.length + 2 := by
  unfold stepBC
  apply insertAll_ext
  intro xw hxw
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hxw
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hr
  simp only [XlC, matVecL, length_vsumL, VR, List.length_range, le_refl, and_self]

set_option maxHeartbeats 2000000 in
theorem Poly.BkC_p : Poly (fun y : (Ctx × List (List (List ℕ))) × List ℕ => BkC q y.1.1 y.1.2 y.2) := by
  unfold BkC
  have hf : Poly (fun z : (((Ctx × List (List (List ℕ))) × List ℕ) × List Row) × ℕ =>
      (stepBC q z.1.1.1.1 z.1.1.1.2 z.1.2).take z.1.1.1.1.MV.length) := by
    fun_prop
  have hb : Poly (fun y : (Ctx × List (List (List ℕ))) × List ℕ => B0C q y.1.1 y.1.2) := by
    fun_prop
  refine Poly.list_foldl (f := fun y B _ => (stepBC q y.1.1 y.1.2 B).take y.1.1.MV.length) hf
    (by fun_prop) hb (X * (2 * (Polynomial.C (3 * (2 * q.size + 1)) * X + 2 * X + 2) + 1)) (fun y B k => ?_)
  obtain ⟨T, e, hT⟩ := stepBC_ext q y.1.1 y.1.2 B
  rw [e]
  have h := enc_take_append_le B T y.1.1.MV.length _ hT
  have hM : y.1.1.MV.length ≤ (enc y).length + (enc k).length := by
    have e1 := enc_pair _ _ y
    have e2 := enc_pair _ _ y.1
    have := (length_le_enc y.1.1.MV).trans (ctx_MV_le y.1.1)
    omega
  set L := (enc y).length + (enc k).length
  have hg := rowBound_mono q hM
  have hm : y.1.1.MV.length * (2 * (3 * (2 * q.size + 1) * y.1.1.MV.length + 2 * y.1.1.MV.length + 2) + 1) ≤
      L * (2 * (3 * (2 * q.size + 1) * L + 2 * L + 2) + 1) := Nat.mul_le_mul hM (by omega)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
  omega

@[fun_prop] theorem Poly.BkC_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List (List (List ℕ))} {d : α → List ℕ} (ha : Poly a)
    (hb : Poly b) (hd : Poly d) :
    Poly (fun x => BkC q (a x) (b x) (d x)) :=
  Automatic.Poly.comp (f := fun y : (Ctx × List (List (List ℕ))) × List ℕ => BkC q y.1.1 y.1.2 y.2) (Poly.BkC_p q)
    (g := fun x => ((a x, b x), d x)) (Automatic.Poly.pair (Automatic.Poly.pair ha hb) hd)

set_option maxHeartbeats 4000000 in
theorem Poly.readOutC_p : Poly (fun y : Ctx × List Row => readOutC q y.1 y.2) := by
  unfold readOutC outTestC VR; dsimp only; fun_prop

@[fun_prop] theorem Poly.readOutC_comp {α : Type} [Coding α] {a : α → Ctx} {b : α → List Row} (ha : Poly a) (hb : Poly b) :
    Poly (fun x => readOutC q (a x) (b x)) :=
  Automatic.Poly.comp (f := fun y : Ctx × List Row => readOutC q y.1 y.2) (Poly.readOutC_p q) (g := fun x => (a x, b x)) (Automatic.Poly.pair ha hb)

theorem Poly.mainDecC_p : Poly (fun c : Ctx => mainDecC q c) := by
  unfold mainDecC
  dsimp only
  have he : ∀ c : Ctx, List.range (c.MV.length + 1) = List.range (c.MV ++ [[]]).length := by
    intro c; simp
  simp only [he]
  fun_prop

end T17M

end File_T17M_PolyC5

section File_T17_Monos

/-! # Facts about the monomial enumerations -/

namespace T17

variable {q : ℕ}

theorem mem_monosEq (hq : 0 < q) (k d : ℕ) (α : List ℕ) :
    α ∈ monosEq q k d ↔ α.length = k ∧ (∀ e ∈ α, e < q) ∧ α.sum = d := by
  induction k generalizing d α with
  | zero =>
    simp only [monosEq]
    split_ifs with h
    · subst h; simp only [List.mem_singleton, List.length_eq_zero_iff]
      constructor
      · rintro rfl; simp
      · rintro ⟨rfl, -⟩; rfl
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hl _ hs
      rw [List.length_eq_zero_iff] at hl; subst hl; simp at hs; exact h hs.symm
  | succ k ih =>
    simp only [monosEq, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨e, he, t, ht, rfl⟩
      rw [ih] at ht
      refine ⟨by simp [ht.1], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact ht.2.1 x hx
      · simp only [List.sum_cons, ht.2.2]
        have : e ≤ d := le_trans (Nat.lt_succ_iff.mp he) (min_le_right _ _)
        omega
    · rintro ⟨hl, hlt, hs⟩
      match α, hl with
      | e :: t, hl =>
        refine ⟨e, ?_, t, ?_, rfl⟩
        · have := hlt e (List.mem_cons_self ..)
          simp only [List.sum_cons] at hs
          omega
        · rw [ih]
          refine ⟨by simpa using hl, fun x hx => hlt x (List.mem_cons_of_mem _ hx), ?_⟩
          simp only [List.sum_cons] at hs; omega

theorem nodup_monosEq (k d : ℕ) : (monosEq q k d).Nodup := by
  induction k generalizing d with
  | zero => simp only [monosEq]; split_ifs <;> simp
  | succ k ih =>
    simp only [monosEq]
    rw [List.nodup_flatMap]
    refine ⟨fun e _ => (ih _).map (fun a b h => List.cons_injective h), ?_⟩
    refine (List.nodup_range).pairwise_of_forall_ne ?_
    intro e₁ _ e₂ _ hne
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨t₁, -, rfl⟩ ⟨t₂, -, h⟩
    exact hne (List.cons.inj h).1.symm

theorem mem_monosLt (hq : 0 < q) (n D : ℕ) (α : List ℕ) :
    α ∈ monosLt q n D ↔ α.length = n ∧ (∀ e ∈ α, e < q) ∧ α.sum < D := by
  simp only [monosLt, List.mem_flatMap, List.mem_range, mem_monosEq hq]
  constructor
  · rintro ⟨d, hd, h1, h2, rfl⟩; exact ⟨h1, h2, hd⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨_, h3, h1, h2, rfl⟩

theorem nodup_monosLt (hq : 0 < q) (n D : ℕ) : (monosLt q n D).Nodup := by
  unfold monosLt
  rw [List.nodup_flatMap]
  refine ⟨fun d _ => nodup_monosEq n d, ?_⟩
  refine (List.nodup_range).pairwise_of_forall_ne ?_
  intro d₁ _ d₂ _ hne
  simp only [Function.onFun, List.disjoint_left]
  intro α h1 h2
  rw [mem_monosEq hq] at h1 h2
  exact hne (h1.2.2.symm.trans h2.2.2)

end T17

end File_T17_Monos

section File_T17M_MonoGen

/-! # Fuel-truncated generation of the monomial lists -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ)

def normM (K : List ℕ) (l : List ℕ) : List ℕ := (l.take K.length).map (· % q)

def tab0 (DR : List ℕ) : List (List (List ℕ)) := DR.map (fun d => if d = 0 then [[]] else [])

def tabStep (fl K DR : List ℕ) (T : List (List (List ℕ))) : List (List (List ℕ)) :=
  DR.map (fun d => (((List.range q).take (min (q - 1) d + 1)).flatMap (fun e =>
    (T.getD (d - e) []).map (fun t => normM q K (e :: t)))).take fl.length)

/-- The table after `L.length` rounds: entry `d` lists the reduced monomials of degree `d`. -/
def tabK (fl K DR L : List ℕ) : List (List (List ℕ)) := L.foldl (fun T _ => tabStep q fl K DR T) (tab0 DR)

theorem range_take_min (hq : 0 < q) (d : ℕ) :
    (List.range q).take (min (q - 1) d + 1) = List.range (min (q - 1) d + 1) := by
  rw [List.take_range]; congr 1; omega

theorem normM_id (K : List ℕ) (l : List ℕ) (hl : l.length ≤ K.length) (hq : ∀ e ∈ l, e < q) :
    normM q K l = l := by
  unfold normM
  rw [List.take_of_length_le hl]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro e he; exact Nat.mod_eq_of_lt (hq e he)

theorem tabK_eq (hq : 0 < q) (fl K : List ℕ) (D k : ℕ) (hK : k ≤ K.length)
    (hF : ∀ k' ≤ k, ∀ d ≤ D, (monosEq q k' d).length ≤ fl.length) :
    tabK q fl K (List.range (D + 1)) (List.range k) = (List.range (D + 1)).map (fun d => monosEq q k d) := by
  induction k with
  | zero =>
    simp only [tabK, List.range_zero, List.foldl_nil, tab0, monosEq]
  | succ k ih =>
    have ih' := ih (by omega) (fun k' hk' d hd => hF k' (by omega) d hd)
    unfold tabK at ih' ⊢
    rw [List.range_succ (n := k), List.foldl_append, ih']
    simp only [List.foldl_cons, List.foldl_nil, tabStep]
    apply List.map_congr_left
    intro d hd
    rw [List.mem_range] at hd
    rw [range_take_min q hq]
    have hget : ∀ e ∈ List.range (min (q - 1) d + 1),
        ((List.range (D + 1)).map (fun d => monosEq q k d)).getD (d - e) [] = monosEq q k (d - e) := by
      intro e _
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp
    rw [List.flatMap_congr (fun e he => by rw [hget e he])]
    have hnorm : ∀ e ∈ List.range (min (q - 1) d + 1),
        (monosEq q k (d - e)).map (fun t => normM q K (e :: t)) = (monosEq q k (d - e)).map (fun t => e :: t) := by
      intro e he
      apply List.map_congr_left
      intro t ht
      obtain ⟨hl, hlt, -⟩ := (mem_monosEq hq _ _ _).1 ht
      apply normM_id
      · simp [hl]; omega
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [List.mem_range] at he; omega
        · exact hlt x hx
    rw [List.flatMap_congr hnorm]
    rw [List.take_of_length_le]
    · rfl
    · have := hF (k + 1) le_rfl d (by omega)
      simpa [monosEq] using this

variable [NeZero q]

theorem normM_size (K l : List ℕ) : (enc (normM q K l)).length ≤ K.length * (2 * q.size + 1) := by
  have h := enc_vec_le q (normM q K l) (by
    intro a ha; unfold normM at ha
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
    exact Nat.mod_lt _ (q_pos' q))
  have hl : (normM q K l).length ≤ K.length := by simp [normM]
  have := Nat.mul_le_mul_right (2 * q.size + 1) hl
  omega

theorem tabStep_size (fl K DR : List ℕ) (T : List (List (List ℕ))) :
    (enc (tabStep q fl K DR T)).length ≤
      DR.length * (2 * (fl.length * (2 * (K.length * (2 * q.size + 1)) + 1)) + 1) := by
  unfold tabStep
  apply (EncodedList.length_bound _ _ _ _).trans
  · rw [List.length_map]
  · intro row hrow
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hrow
    apply (EncodedList.length_bound _ _ _ _).trans
    · exact Nat.mul_le_mul_right _ (by simp)
    · intro t ht
      have ht' := List.mem_of_mem_take ht
      obtain ⟨e, -, ht''⟩ := List.mem_flatMap.1 ht'
      obtain ⟨t0, -, rfl⟩ := List.mem_map.1 ht''
      exact normM_size q K _

@[fun_prop] theorem Poly.normM_comp {α : Type} [Coding α] {K l : α → List ℕ} (hK : Poly K) (hl : Poly l) :
    Poly (fun x => normM q (K x) (l x)) := by unfold normM; fun_prop

theorem Poly.tabStep_p : Poly (fun y : ((List ℕ × List ℕ × List ℕ) × List (List (List ℕ))) =>
    tabStep q y.1.1 y.1.2.1 y.1.2.2 y.2) := by
  unfold tabStep; fun_prop

set_option maxHeartbeats 1000000 in
theorem Poly.tabK_p : Poly (fun y : (List ℕ × List ℕ × List ℕ) × List ℕ => tabK q y.1.1 y.1.2.1 y.1.2.2 y.2) := by
  unfold tabK
  have hf : Poly (fun z : (((List ℕ × List ℕ × List ℕ) × List ℕ) × List (List (List ℕ))) × ℕ =>
      tabStep q z.1.1.1.1 z.1.1.1.2.1 z.1.1.1.2.2 z.1.2) :=
    Automatic.Poly.comp (f := fun y : ((List ℕ × List ℕ × List ℕ) × List (List (List ℕ))) =>
      tabStep q y.1.1 y.1.2.1 y.1.2.2 y.2)
      (g := fun z : (((List ℕ × List ℕ × List ℕ) × List ℕ) × List (List (List ℕ))) × ℕ => (z.1.1.1, z.1.2))
      (Poly.tabStep_p q) (by fun_prop)
  have hb : Poly (fun y : (List ℕ × List ℕ × List ℕ) × List ℕ => tab0 y.1.2.2) := by unfold tab0; fun_prop
  refine Poly.list_foldl (f := fun y T _ => tabStep q y.1.1 y.1.2.1 y.1.2.2 T) hf (by fun_prop) hb
    (X * (2 * (X * (2 * (X * (Polynomial.C (2 * q.size + 1))) + 1)) + 1)) (fun y T k => ?_)
  have h := tabStep_size q y.1.1 y.1.2.1 y.1.2.2 T
  set L := (enc y).length + (enc k).length
  have e1 := enc_pair _ _ y
  have e2 := enc_pair _ _ y.1
  have e3 := enc_pair _ _ y.1.2
  have l1 := length_le_enc y.1.1
  have l2 := length_le_enc y.1.2.1
  have l3 := length_le_enc y.1.2.2
  have hD : y.1.2.2.length ≤ L := by omega
  have hF : y.1.1.length ≤ L := by omega
  have hK : y.1.2.1.length ≤ L := by omega
  have m1 : y.1.2.1.length * (2 * q.size + 1) ≤ L * (2 * q.size + 1) := Nat.mul_le_mul_right _ hK
  have m2 : y.1.1.length * (2 * (y.1.2.1.length * (2 * q.size + 1)) + 1) ≤
      L * (2 * (L * (2 * q.size + 1)) + 1) := Nat.mul_le_mul hF (by omega)
  have m3 : y.1.2.2.length * (2 * (y.1.1.length * (2 * (y.1.2.1.length * (2 * q.size + 1)) + 1)) + 1) ≤
      L * (2 * (L * (2 * (L * (2 * q.size + 1)) + 1)) + 1) := Nat.mul_le_mul hD (by omega)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
  rw [mul_comm L (2 * q.size + 1)] at m1 ⊢
  nlinarith

end T17M

end File_T17M_MonoGen

section File_T17_Coords

/-! # Coordinates: lists of naturals ↔ polynomials -/

namespace T17

open MvPolynomial F3SubsetSum

variable {q : ℕ}

/-- Exponent list → finitely supported exponent. -/
noncomputable def monoOf (n : ℕ) (α : List ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => α.getD j 0)

@[simp] theorem monoOf_apply (n : ℕ) (α : List ℕ) (j : Fin n) : monoOf n α j = α.getD j 0 := rfl

theorem monoOf_inj {n : ℕ} {α β : List ℕ} (ha : α.length = n) (hb : β.length = n)
    (h : monoOf n α = monoOf n β) : α = β := by
  apply List.ext_getElem (ha.trans hb.symm)
  intro i h1 h2
  have := DFunLike.congr_fun h ⟨i, ha ▸ h1⟩
  simp only [monoOf_apply] at this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- The vector space of lists of length `d`. -/
def VecSup (q d : ℕ) : Submodule (ZMod q) (ℕ → ZMod q) where
  carrier := {f | ∀ t, d ≤ t → f t = 0}
  add_mem' := by intro a b ha hb t ht; simp [ha t ht, hb t ht]
  zero_mem' := by intro t _; rfl
  smul_mem' := by intro c a ha t ht; simp [ha t ht]

theorem toV_mem (x : List ℕ) : toV q x ∈ VecSup q x.length := by
  intro t ht; simp only [toV]; rw [List.getD_eq_default _ _ ht]; simp

/-- Vector → polynomial along a list of monomials. -/
noncomputable def pv (n : ℕ) (Ms : List (List ℕ)) : (ℕ → ZMod q) →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q) :=
  ∑ t ∈ Finset.range Ms.length, (monomial (monoOf n (Ms.getD t []))).comp (LinearMap.proj t)

theorem pv_apply (n : ℕ) (Ms : List (List ℕ)) (f : ℕ → ZMod q) :
    pv n Ms f = ∑ t ∈ Finset.range Ms.length, monomial (monoOf n (Ms.getD t [])) (f t) := by
  simp [pv]

/-- Monomial lists: nodup and all of length `n`. -/
def Good (n : ℕ) (Ms : List (List ℕ)) : Prop := Ms.Nodup ∧ ∀ α ∈ Ms, α.length = n

theorem pv_coeff {n : ℕ} {Ms : List (List ℕ)} (hM : Good n Ms) (f : ℕ → ZMod q) (t : ℕ)
    (ht : t < Ms.length) : (pv n Ms f).coeff (monoOf n (Ms.getD t [])) = f t := by
  rw [pv_apply, coeff_sum]
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' ht' hne
    rw [coeff_monomial, if_neg]
    intro h
    apply hne
    have h1 : t' < Ms.length := Finset.mem_range.1 ht'
    have := monoOf_inj (hM.2 _ (by rw [List.getD_eq_getElem _ _ h1]; exact List.getElem_mem _))
      (hM.2 _ (by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _)) h
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ ht] at this
    exact (hM.1.getElem_inj_iff).1 this
  · intro h; exact absurd (Finset.mem_range.2 ht) h

theorem pv_coeff_other {n : ℕ} {Ms : List (List ℕ)} (f : ℕ → ZMod q) (s : Fin n →₀ ℕ)
    (hs : ∀ α ∈ Ms, monoOf n α ≠ s) : (pv n Ms f).coeff s = 0 := by
  rw [pv_apply, coeff_sum]
  apply Finset.sum_eq_zero
  intro t ht
  rw [coeff_monomial, if_neg]
  have h1 : t < Ms.length := Finset.mem_range.1 ht
  rw [List.getD_eq_getElem _ _ h1]
  exact hs _ (List.getElem_mem _)

theorem pv_inj {n : ℕ} {Ms : List (List ℕ)} (hM : Good n Ms) (f g : ℕ → ZMod q)
    (hf : f ∈ VecSup q Ms.length) (hg : g ∈ VecSup q Ms.length) (h : pv n Ms f = pv n Ms g) : f = g := by
  funext t
  by_cases ht : t < Ms.length
  · rw [← pv_coeff hM f t ht, ← pv_coeff hM g t ht, h]
  · rw [hf t (by omega), hg t (by omega)]

/-- The coordinates of a polynomial along `Ms`. -/
noncomputable def coordsOf (n : ℕ) (Ms : List (List ℕ)) (p : MvPolynomial (Fin n) (ZMod q)) : ℕ → ZMod q :=
  fun t => if t < Ms.length then p.coeff (monoOf n (Ms.getD t [])) else 0

theorem coordsOf_mem (n : ℕ) (Ms : List (List ℕ)) (p : MvPolynomial (Fin n) (ZMod q)) :
    coordsOf n Ms p ∈ VecSup q Ms.length := by
  intro t ht; simp [coordsOf, show ¬ t < Ms.length by omega]

/-- A polynomial supported on the monomials of `Ms` is `pv` of its coordinates. -/
theorem pv_coordsOf {n : ℕ} {Ms : List (List ℕ)} (hM : Good n Ms) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : ∀ s ∈ p.support, ∃ α ∈ Ms, monoOf n α = s) : pv n Ms (coordsOf n Ms p) = p := by
  ext s
  by_cases hs : ∃ α ∈ Ms, monoOf n α = s
  · obtain ⟨α, hα, rfl⟩ := hs
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hα
    have := pv_coeff hM (coordsOf n Ms p) t ht
    rw [List.getD_eq_getElem _ _ ht] at this
    rw [this]
    simp [coordsOf, ht, List.getD_eq_getElem _ _ ht]
  · push Not at hs
    rw [pv_coeff_other _ _ hs]
    by_contra h
    obtain ⟨α, hα, he⟩ := hp s (mem_support_iff.2 (Ne.symm h))
    exact hs α hα he

end T17

end File_T17_Coords

section File_T17_VecOps

/-! # Semantics of the list vector operations -/

namespace T17

variable {q : ℕ} [NeZero q]

theorem length_unitV (d t : ℕ) : (unitV d t).length = d := by simp [unitV]
theorem length_zeroV (d : ℕ) : (zeroV d).length = d := by simp [zeroV]
theorem length_vsum (d : ℕ) (vs : List (List ℕ)) : (vsum q d vs).length = d := by simp [vsum]
theorem length_matVec (d : ℕ) (cols : List (List ℕ)) (v : List ℕ) :
    (matVec q d cols v).length = d := by simp [matVec, length_vsum]
theorem length_vlin (c : ℕ) (x y : List ℕ) (h : x.length = y.length) :
    (vlin q c x y).length = x.length := by simp [vlin, h]
theorem length_vsub (x y : List ℕ) (h : x.length = y.length) :
    (vsub q x y).length = x.length := length_axpy _ _ _ h

theorem toV_unitV (d t : ℕ) (ht : t < d) : toV q (unitV d t) = Pi.single t 1 := by
  funext r
  simp only [toV, unitV]
  by_cases hr : r < d
  · rw [List.getD_eq_getElem _ _ (by simp [hr])]
    simp only [List.getElem_map, List.getElem_range]
    by_cases h : r = t
    · subst h; simp
    · simp [h, Pi.single_apply]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    have : r ≠ t := by omega
    simp [Pi.single_apply, this]

theorem toV_zeroV (d : ℕ) : toV q (zeroV d) = 0 := by
  funext r; simp [toV, zeroV]

theorem toV_vlin (c : ℕ) (x y : List ℕ) (h : x.length = y.length) :
    toV q (vlin q c x y) = toV q x + (c : ZMod q) • toV q y := by
  unfold vlin
  rw [toV_zip_map x y h (fun a b => addq q a (mulq q c b)) (fun a b => a + (c : ZMod q) * b)
    (fun a b => by rw [cast_addq, cast_mulq]) (by simp)]
  funext i; simp [smul_eq_mul]

theorem toV_vsub (x y : List ℕ) (h : x.length = y.length) :
    toV q (vsub q x y) = toV q x - toV q y := by
  unfold vsub; rw [toV_axpy _ _ _ h]; simp

theorem cast_foldl_addq (xs : List ℕ) (b : ℕ) :
    ((xs.foldl (addq q) b : ℕ) : ZMod q) = (b : ZMod q) + (xs.map (Nat.cast : ℕ → ZMod q)).sum := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, cast_addq]; simp; ring

theorem cast_sumq (xs : List ℕ) : ((sumq q xs : ℕ) : ZMod q) = (xs.map (Nat.cast : ℕ → ZMod q)).sum := by
  unfold sumq; rw [cast_foldl_addq]; simp

theorem list_sum_apply (vs : List (ℕ → ZMod q)) (r : ℕ) : vs.sum r = (vs.map (fun v => v r)).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [ih]

theorem toV_vsum (d : ℕ) (vs : List (List ℕ)) (hvs : ∀ v ∈ vs, v.length ≤ d) :
    toV q (vsum q d vs) = (vs.map (toV q)).sum := by
  funext r
  rw [list_sum_apply, List.map_map]
  show (((vsum q d vs).getD r 0 : ℕ) : ZMod q) = (vs.map (fun v => toV q v r)).sum
  unfold vsum
  by_cases hr : r < d
  · rw [List.getD_eq_getElem _ _ (by simp [hr])]
    simp only [List.getElem_map, List.getElem_range]
    rw [cast_foldl_addq, List.map_map]
    simp only [Nat.cast_zero, zero_add]
    rfl
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp only [Nat.cast_zero]
    symm
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    simp only [toV]
    rw [List.getD_eq_default _ _ (by have := hvs v hv; omega)]
    simp

theorem list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem toV_matVec (d : ℕ) (cols : List (List ℕ)) (v : List ℕ) (hc : ∀ c ∈ cols, c.length ≤ d) :
    toV q (matVec q d cols v) = ∑ t ∈ Finset.range cols.length, toV q v t • toV q (cols.getD t []) := by
  unfold matVec
  rw [toV_vsum, List.map_map, list_sum_range]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Function.comp_apply, toV_smul]
    rfl
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    rw [length_smul]
    rw [List.mem_range] at ht
    rw [List.getD_eq_getElem _ _ ht]
    exact hc _ (List.getElem_mem _)

end T17

end File_T17_VecOps

section File_T17_P49Lib

open F3SubsetSum MvPolynomial
open scoped BigOperators

namespace Prop49Proof

section
variable {q n m : ℕ} [Fact q.Prime]

noncomputable def rIndex (q : ℕ) (s : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => redExp q (s j)

lemma rIndex_apply (s : Fin n →₀ ℕ) (j : Fin n) :
    rIndex q s j = redExp q (s j) := by simp [rIndex]

lemma redExp_le (q e : ℕ) (hq : 2 ≤ q) : redExp q e ≤ e := by
  unfold redExp
  split_ifs with h
  · exact le_rfl
  · have hh := Nat.mod_le (e - 1) (q - 1)
    omega

lemma redExp_lt (hq : 2 ≤ q) (e : ℕ) : redExp q e < q := by
  unfold redExp
  split_ifs with h
  · exact h
  · have hh := Nat.mod_lt (e - 1) (show 0 < q - 1 by omega)
    omega

lemma rIndex_reduced (hq : 2 ≤ q) (s : Fin n →₀ ℕ) :
    ∀ j, rIndex q s j < q := by
  intro j
  rw [rIndex_apply]
  exact redExp_lt hq _

lemma rIndex_le (s : Fin n →₀ ℕ) : rIndex q s ≤ s := by
  intro j
  rw [rIndex_apply]
  exact redExp_le _ _ (Fact.out : q.Prime).two_le

lemma rIndex_self (s : Fin n →₀ ℕ) (hs : ∀ j, s j < q) :
    rIndex q s = s := by
  ext j
  simp [rIndex_apply, redExp, hs j]

noncomputable def redL (q n : ℕ) :
    MvPolynomial (Fin n) (ZMod q) →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q) :=
  (Finsupp.lsum (ZMod q) (fun s : Fin n →₀ ℕ =>
    (monomial (rIndex q s) : ZMod q →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q)))).comp
    (AddMonoidAlgebra.coeffLinearEquiv (ZMod q)).toLinearMap

lemma redL_apply (p : MvPolynomial (Fin n) (ZMod q)) :
    redL q n p = red q p := rfl

lemma red_monomial (s : Fin n →₀ ℕ) (c : ZMod q) :
    red q (monomial s c) = monomial (rIndex q s) c := by
  change (Finsupp.lsum (ZMod q) (fun s : Fin n →₀ ℕ =>
    (monomial (rIndex q s) : ZMod q →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q))))
      (Finsupp.single s c) = _
  exact Finsupp.lsum_single _ _ _ _

lemma low_mem (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q)) :
    p ∈ lowSpan q n D ↔
      ∀ s ∈ p.support, (∀ j, s j < q) ∧ ∑ j, s j < D := by
  classical
  let E : Set (Fin n →₀ ℕ) := {s | (∀ j, s j < q) ∧ ∑ j, s j < D}
  have hE : lowSpan q n D = MvPolynomial.restrictSupport (ZMod q) E := by
    rw [MvPolynomial.restrictSupport_eq_span]
    unfold lowSpan
    congr 1
    ext v
    constructor
    · rintro ⟨s, hs, hd, rfl⟩
      exact ⟨s, ⟨hs, hd⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hd⟩, rfl⟩
      exact ⟨s, hs, hd, rfl⟩
  rw [hE, MvPolynomial.mem_restrictSupport_iff]
  rfl

lemma monomial_low (D : ℕ) (s : Fin n →₀ ℕ) (c : ZMod q)
    (hs : ∀ j, s j < q) (hd : ∑ j, s j < D) :
    monomial s c ∈ lowSpan q n D := by
  have h : monomial s (1 : ZMod q) ∈ lowSpan q n D :=
    Submodule.subset_span ⟨s, hs, hd, rfl⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using (lowSpan q n D).smul_mem c h

noncomputable def tauL (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) :
    MvPolynomial (Fin n) (ZMod q) →ₗ[ZMod q] MvPolynomial (Fin n) (ZMod q) := by
  classical
  exact (Finsupp.lsum (ZMod q) (fun s =>
    if ∑ j, s j < D then monomial s
    else if h : (∀ j, s j < q) ∧ ∑ j, s j = D then
      LinearMap.toSpanSingleton (ZMod q) _
        (remainder A b D Q ⟨fun j => ⟨s j, h.1 j⟩, h.2⟩)
    else 0)).comp (AddMonoidAlgebra.coeffLinearEquiv (ZMod q)).toLinearMap

lemma tauL_apply (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (p : MvPolynomial (Fin n) (ZMod q)) :
    tauL A b D Q p = tau A b D Q p := by
  classical
  unfold tauL tau
  simp only [LinearMap.comp_apply, AddMonoidAlgebra.coeffLinearEquiv_apply, Finsupp.lsum_apply, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> rfl


lemma degree_of_support (p : MvPolynomial (Fin n) (ZMod q))
    (s : Fin n →₀ ℕ) (hs : s ∈ p.support) : ∑ j, s j ≤ p.totalDegree := by
  simpa [Finsupp.sum_fintype] using (MvPolynomial.le_totalDegree hs)

lemma rIndex_top (s t : Fin n →₀ ℕ)
    (hdeg : ∑ j, s j ≤ ∑ j, t j) (heq : rIndex q s = t) : s = t := by
  classical
  ext j
  have hle : ∀ i, t i ≤ s i := by intro i; rw [← heq]; exact rIndex_le s i
  by_contra hj
  have hjlt : t j < s j := lt_of_le_of_ne (hle j) (Ne.symm hj)
  have hsum := Finset.sum_lt_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
    ⟨j, Finset.mem_univ _, hjlt⟩
  omega

lemma red_supported (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p.totalDegree ≤ D) :
    red q p ∈ MvPolynomial.restrictSupport (ZMod q)
      {s : Fin n →₀ ℕ | (∀ j, s j < q) ∧ ∑ j, s j ≤ D} := by
  classical
  have hexp : red q p = ∑ s ∈ p.support, red q (monomial s (coeff s p)) := by
    change redL q n p = ∑ s ∈ p.support, redL q n (monomial s (coeff s p))
    rw [← map_sum, ← as_sum p]
  rw [hexp]
  apply Submodule.sum_mem
  intro s hs
  rw [red_monomial, monomial_mem_restrictSupport]
  left
  exact ⟨rIndex_reduced (Fact.out : q.Prime).two_le s,
    (Finset.sum_le_sum (fun j _ => rIndex_le s j)).trans ((degree_of_support p s hs).trans hp)⟩

lemma red_coeff_top (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p.totalDegree ≤ D) (t : Fin n →₀ ℕ)
    (ht : ∀ j, t j < q) (htD : ∑ j, t j = D) :
    coeff t (red q p) = coeff t p := by
  classical
  have hexp : red q p = ∑ s ∈ p.support, red q (monomial s (coeff s p)) := by
    change redL q n p = ∑ s ∈ p.support, redL q n (monomial s (coeff s p))
    rw [← map_sum, ← as_sum p]
  rw [hexp, coeff_sum]
  calc
    _ = coeff t (red q (monomial t (coeff t p))) := Finset.sum_eq_single (s := p.support)
      (f := fun s => coeff t (red q (monomial s (coeff s p)))) t (by
      intro s hs hst
      rw [red_monomial, coeff_monomial]
      have hne : rIndex q s ≠ t := by
        intro he
        exact hst (rIndex_top s t (by rw [htD]; exact (degree_of_support p s hs).trans hp) he)
      simp [hne]) (by
      intro ht'
      rw [notMem_support_iff.mp ht']
      simp [red])
    _ = coeff t p := by rw [red_monomial, rIndex_self t ht]; simp

lemma toPoly_degree (d : ℕ) (v : Rd (ZMod q) n q d) :
    (Rd.toPoly (ZMod q) n q d v).totalDegree ≤ d := by
  classical
  simp only [Rd.toPoly, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply totalDegree_finsetSum_le
  intro α _
  have h := totalDegree_monomial_le α.toFinsupp (v α)
  simpa [ReducedMono.toFinsupp, Finsupp.sum_fintype, α.property] using h

lemma linForm_degree (a : Fin n → ZMod q) : (linForm a).totalDegree ≤ 1 := by
  classical
  unfold linForm
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

lemma fPoly_degree (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (i : Fin m) : (fPoly A b i).totalDegree ≤ 2 := by
  have hL := linForm_degree (cols A i)
  unfold fPoly
  apply (totalDegree_mul _ _).trans
  have h₁ := (totalDegree_sub_C_le (linForm (cols A i)) (b i)).trans hL
  have h₂ := totalDegree_add (linForm (cols A i) - C (b i)) 1
  simp only [totalDegree_one, Nat.max_zero] at h₂
  exact (Nat.add_le_add h₁ (h₂.trans h₁)).trans (by decide)

lemma fPoly_error_degree (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (i : Fin m) :
    (fPoly A b i - linForm (cols A i) ^ 2).totalDegree ≤ 1 := by
  have he : fPoly A b i - linForm (cols A i) ^ 2 =
      (1 - C (2 * b i)) * linForm (cols A i) + C ((b i) ^ 2 - b i) := by
    unfold fPoly
    simp only [map_sub, map_mul, map_ofNat, map_pow]
    ring
  rw [he]
  apply (totalDegree_add _ _).trans
  have hc : (1 - C (2 * b i) : MvPolynomial (Fin n) (ZMod q)).totalDegree = 0 := by
    rw [← map_one C, ← map_sub, totalDegree_C]
  have hm := totalDegree_mul (1 - C (2 * b i)) (linForm (cols A i))
  rw [hc, zero_add] at hm
  exact max_le (hm.trans (linForm_degree _)) (by rw [totalDegree_C]; omega)

lemma remainder_low (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (α : ReducedMono n q D) : remainder A b D Q α ∈ lowSpan q n D := by
  classical
  let p := ∑ i, fPoly A b i * Rd.toPoly (ZMod q) n q (D - 2) (Q α i)
  let p₂ := ∑ i, linForm (cols A i) ^ 2 * Rd.toPoly (ZMod q) n q (D - 2) (Q α i)
  have hp : p.totalDegree ≤ D := by
    apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add (fPoly_degree A b i)
      (toPoly_degree _ _)).trans (by omega))
  have herror : (p - p₂).totalDegree < D := by
    have he : p - p₂ = ∑ i, (fPoly A b i - linForm (cols A i) ^ 2) *
        Rd.toPoly (ZMod q) n q (D - 2) (Q α i) := by
      simp [p, p₂, Finset.sum_sub_distrib, sub_mul]
    rw [he]
    apply lt_of_le_of_lt (totalDegree_finsetSum_le (d := D - 1) ?_) (by omega)
    intro i _
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add (fPoly_error_degree A b i)
      (toPoly_degree _ _)).trans (by omega))
  have htop (β : ReducedMono n q D) : coeff β.toFinsupp p = (Pi.single α (1 : ZMod q) : Rd (ZMod q) n q D) β := by
    have he : coeff β.toFinsupp (p - p₂) = 0 :=
      coeff_eq_zero_of_totalDegree_lt (by
        change (p - p₂).totalDegree < β.toFinsupp.sum (fun _ e => e)
        rw [Finsupp.sum_fintype]
        simpa [ReducedMono.toFinsupp, β.property] using herror
        intro j; rfl)
    have hh := congrFun (hQ α) β
    rw [coeff_sub] at he
    apply (sub_eq_zero.mp he).trans
    simpa [Phi, mulMap, Rd.ofPoly, p₂, coeff_sum] using hh
  apply (low_mem D _).mpr
  intro s hs
  have hsnon : coeff s (remainder A b D Q α) ≠ 0 := mem_support_iff.mp hs
  have hsr : coeff s (monomial α.toFinsupp (1 : ZMod q)) ≠ 0 ∨ coeff s (red q p) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hsnon
    change coeff s (monomial α.toFinsupp 1 - red q p) = 0
    rw [coeff_sub, hn.1, hn.2, sub_self]
  have hsbound : (∀ j, s j < q) ∧ ∑ j, s j ≤ D := by
    rcases hsr with ha | ha
    · have he : α.toFinsupp = s := by simpa only [coeff_monomial, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] using ha
      subst s
      exact ⟨fun j => by simpa [ReducedMono.toFinsupp] using (α.val j).isLt,
        by simp [ReducedMono.toFinsupp, Finsupp.sum_fintype, α.property]⟩
    · exact ((mem_restrictSupport_iff (ZMod q)).mp (red_supported D p hp)) (mem_support_iff.mpr ha)
  refine ⟨hsbound.1, lt_of_le_of_ne hsbound.2 ?_⟩
  intro hsd
  let β : ReducedMono n q D := ⟨fun j => ⟨s j, hsbound.1 j⟩, hsd⟩
  have hb : β.toFinsupp = s := by ext j; simp [β, ReducedMono.toFinsupp]
  apply hsnon
  change coeff s (monomial α.toFinsupp 1 - red q p) = 0
  rw [coeff_sub, red_coeff_top D p hp s hsbound.1 hsd, ← hb, htop β]
  have hi : α.toFinsupp = β.toFinsupp ↔ α = β := by
    constructor
    · intro h; apply Subtype.ext; funext j; apply Fin.ext
      simpa [ReducedMono.toFinsupp] using congrArg (fun t => t j) h
    · rintro rfl; rfl
  simp [coeff_monomial, Pi.single_apply, hi, eq_comm]


lemma red_fixed (p : MvPolynomial (Fin n) (ZMod q))
    (hp : ∀ s ∈ p.support, ∀ j, s j < q) : red q p = p := by
  classical
  unfold red
  conv_rhs => rw [as_sum p]
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun t => monomial t (coeff s p)) (rIndex_self s (hp s hs))

lemma tau_fixed (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ lowSpan q n D) : tau A b D Q p = p := by
  classical
  unfold tau
  conv_rhs => rw [as_sum p]
  apply Finset.sum_congr rfl
  intro s hs
  rw [if_pos (((low_mem D p).mp hp s hs).2)]

lemma low_degree (D : ℕ) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ lowSpan q n D) : p.totalDegree ≤ D - 1 := by
  classical
  unfold totalDegree
  apply Finset.sup_le
  intro s hs
  have h := ((low_mem D p).mp hp s hs).2
  simpa [Finsupp.sum_fintype] using (show ∑ j, s j ≤ D - 1 by omega)

lemma tau_low (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ MvPolynomial.restrictSupport (ZMod q)
      {s : Fin n →₀ ℕ | (∀ j, s j < q) ∧ ∑ j, s j ≤ D}) :
    tau A b D Q p ∈ lowSpan q n D := by
  classical
  unfold tau
  apply Submodule.sum_mem
  intro s hs
  have hsp := (mem_restrictSupport_iff (ZMod q)).mp hp hs
  split_ifs with hlt heq
  · exact monomial_low D s _ hsp.1 hlt
  · exact (lowSpan q n D).smul_mem _ (remainder_low A b D hD Q hQ _)
  · exact (lowSpan q n D).zero_mem

noncomputable def XL (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) (j : Fin n) :
    Module.End (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  (tauL A b D Q).comp ((redL q n).comp (LinearMap.mulLeft (ZMod q) (X j)))

lemma XL_apply (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q)) : XL A b D Q j p = Xop A b D Q j p := by
  simp [XL, Xop, redL_apply, tauL_apply]

lemma Xop_low (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D) :
    Xop A b D Q j p ∈ lowSpan q n D := by
  apply tau_low A b D hD Q hQ
  apply red_supported
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have hh := low_degree D p hp
    omega)

lemma Xop_fixed (A : Matrix (Fin n) (Fin m) (ZMod q))
    (b : Fin m → ZMod q) (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q))
    (hp : X j * p ∈ lowSpan q n D) : Xop A b D Q j p = X j * p := by
  unfold Xop
  rw [red_fixed _ (fun s hs => ((low_mem D _).mp hp s hs).1)]
  exact tau_fixed A b D Q _ hp

end

section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

lemma field_product (j : Fin n) :
    (∏ a : K, (X j - C a : MvPolynomial (Fin n) K)) =
      X j ^ Fintype.card K - X j := by
  classical
  have hc : (1 : ℕ) < Fintype.card K := Fintype.one_lt_card
  have hp : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).Monic :=
    Polynomial.monic_X_pow_sub (by simpa using hc)
  have hr : (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).roots.card =
      (Polynomial.X ^ Fintype.card K - Polynomial.X : Polynomial K).natDegree := by
    rw [FiniteField.roots_X_pow_card_sub_X]
    simp [FiniteField.X_pow_card_sub_X_natDegree_eq K hc]
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hr
  rw [FiniteField.roots_X_pow_card_sub_X] at h
  have he := congrArg (Polynomial.aeval (X j : MvPolynomial (Fin n) K)) h
  simpa using he

-- Alon's grid Nullstellensatz identifies polynomials vanishing on the full grid.
lemma vanishes_grid_mem (I : Ideal (MvPolynomial (Fin n) K))
    (hI : ∀ j, X j ^ Fintype.card K - X j ∈ I)
    (p : MvPolynomial (Fin n) K) (hp : ∀ u : Fin n → K, eval u p = 0) : p ∈ I := by
  classical
  obtain ⟨h, _, heq⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ : Fin n => (Finset.univ : Finset K)) (fun _ => Finset.univ_nonempty) p (fun u _ => hp u)
  rw [heq, Finsupp.linearCombination_apply]
  apply I.sum_mem
  intro j _
  change h j * (∏ a : K, (X j - C a)) ∈ I
  rw [field_product]
  exact I.mul_mem_left _ (hI j)

end

section
variable {q n m : ℕ} [Fact q.Prime]
variable (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q)

omit [Fact q.Prime] in
lemma sample_mem (i : Fin m) : fPoly A b i ∈ idealJ A b :=
  Ideal.subset_span (Or.inl ⟨i, rfl⟩)

lemma eval_zero_of_mem {u : Fin n → ZMod q} (hu : u ∈ candidates A b)
    {p : MvPolynomial (Fin n) (ZMod q)} (hp : p ∈ idealJ A b) : eval u p = 0 := by
  have h : idealJ A b ≤ RingHom.ker (eval u) := by
    apply Ideal.span_le.mpr
    rintro p (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hu i
    · simp [RingHom.mem_ker, ZMod.pow_card]
  exact h hp

lemma grid_vanish_mem {p : MvPolynomial (Fin n) (ZMod q)}
    (hp : ∀ u, eval u p = 0) : p ∈ idealJ A b := by
  apply vanishes_grid_mem (idealJ A b) _ p hp
  intro j
  rw [ZMod.card]
  exact Ideal.subset_span (Or.inr ⟨j, rfl⟩)

lemma interpolation_mem (p : MvPolynomial (Fin n) (ZMod q)) :
    p - ∑ u : Fin n → ZMod q, C (eval u p) * indicator u ∈ idealJ A b := by
  classical
  apply grid_vanish_mem A b
  intro u
  simp only [map_sub, map_sum, map_mul, eval_C]
  rw [Finset.sum_eq_single u]
  · simp [eval_indicator_apply_eq_one]
  · intro v _ hv
    rw [eval_indicator_apply_eq_zero u v hv.symm, mul_zero]
  · simp

-- An indicator outside the candidate set is killed by one sample equation.
lemma indicator_mem_of_not_candidate (u : Fin n → ZMod q)
    (hu : u ∉ candidates A b) : indicator u ∈ idealJ A b := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, eval u (fPoly A b i) ≠ 0 := by
    simpa only [candidates, Set.mem_ofPred_eq, not_forall] using hu
  let c := eval u (fPoly A b i)
  have h : C c * indicator u - fPoly A b i * indicator u ∈ idealJ A b := by
    apply grid_vanish_mem A b
    intro v
    by_cases hv : v = u
    · subst v
      simp [c]
    · simp [eval_indicator_apply_eq_zero v u hv]
  have hprod : C c * indicator u ∈ idealJ A b :=
    by simpa only [sub_add_cancel] using
      (idealJ A b).add_mem h ((idealJ A b).mul_mem_right (indicator u) (sample_mem A b i))
  have hc : c ≠ 0 := hi
  have hscaled := (idealJ A b).mul_mem_left (C c⁻¹) hprod
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hscaled

-- Interpolation now identifies J with the kernel of evaluation on candidates.
lemma mem_ideal_iff (p : MvPolynomial (Fin n) (ZMod q)) :
    p ∈ idealJ A b ↔ ∀ u ∈ candidates A b, eval u p = 0 := by
  classical
  constructor
  · exact fun hp u hu => eval_zero_of_mem A b hu hp
  · intro hp
    have hsum : (∑ u : Fin n → ZMod q, C (eval u p) * indicator u) ∈ idealJ A b := by
      apply (idealJ A b).sum_mem
      intro u _
      by_cases hu : u ∈ candidates A b
      · simp [hp u hu]
      · exact (idealJ A b).mul_mem_left _ (indicator_mem_of_not_candidate A b u hu)
    have h := (idealJ A b).add_mem (interpolation_mem A b p) hsum
    simpa only [sub_add_cancel] using h



lemma pow_redExp (x : ZMod q) (e : ℕ) : x ^ redExp q e = x ^ e := by
  unfold redExp
  split_ifs with he
  · rfl
  · have hepos : 0 < e := by have := (Fact.out : q.Prime).two_le; omega
    by_cases hx : x = 0
    · subst x
      simp [Nat.ne_of_gt hepos]
    · rw [pow_add, pow_one, ← pow_eq_pow_mod (e - 1) (ZMod.pow_card_sub_one_eq_one hx),
        pow_sub_one_mul (Nat.ne_of_gt hepos)]

lemma eval_red (p : MvPolynomial (Fin n) (ZMod q)) (u : Fin n → ZMod q) :
    eval u (red q p) = eval u p := by
  classical
  unfold red
  rw [map_sum]
  conv_rhs => rw [as_sum p, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [eval_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by intro j; simp),
    Finsupp.prod_fintype _ _ (by intro j; simp)]
  apply Finset.prod_congr rfl
  intro j _
  simp [pow_redExp]

lemma red_mod (p : MvPolynomial (Fin n) (ZMod q)) :
    Ideal.Quotient.mk (idealJ A b) (red q p) = Ideal.Quotient.mk (idealJ A b) p := by
  apply (sub_eq_zero.mp ?_)
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply grid_vanish_mem A b
  intro u
  simp [eval_red]

lemma remainder_mod (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (α : ReducedMono n q D) :
    Ideal.Quotient.mk (idealJ A b) (remainder A b D Q α) =
      Ideal.Quotient.mk (idealJ A b) (monomial α.toFinsupp 1) := by
  unfold remainder
  rw [map_sub, red_mod A b]
  have hz : (∑ i, fPoly A b i * Rd.toPoly (ZMod q) n q (D - 2) (Q α i)) ∈ idealJ A b := by
    apply (idealJ A b).sum_mem
    intro i _
    exact (idealJ A b).mul_mem_right _ (sample_mem A b i)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, sub_zero]

lemma tau_mod (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (p : MvPolynomial (Fin n) (ZMod q))
    (hp : p ∈ MvPolynomial.restrictSupport (ZMod q)
      {s : Fin n →₀ ℕ | (∀ j, s j < q) ∧ ∑ j, s j ≤ D}) :
    Ideal.Quotient.mk (idealJ A b) (tau A b D Q p) = Ideal.Quotient.mk (idealJ A b) p := by
  classical
  unfold tau
  rw [map_sum]
  conv_rhs => rw [as_sum p, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsp := (mem_restrictSupport_iff (ZMod q)).mp hp hs
  split_ifs with hlt heq
  · rfl
  · let α : ReducedMono n q D := ⟨fun j => ⟨s j, heq.1 j⟩, heq.2⟩
    have hi : α.toFinsupp = s := by ext j; simp [α, ReducedMono.toFinsupp]
    change Ideal.Quotient.mk (idealJ A b) (coeff s p • remainder A b D Q α) = _
    change (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) _ = _
    have hh : (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (remainder A b D Q α) =
        (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (monomial α.toFinsupp 1) := remainder_mod A b D Q α
    rw [map_smul, hh, hi, ← map_smul]
    simp only [smul_monomial, smul_eq_mul, mul_one]
    rfl
  · have hsle : ∑ j, s j ≤ D := hsp.2
    exact False.elim (heq ⟨hsp.1, by omega⟩)

lemma Xop_mod (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D) :
    Ideal.Quotient.mk (idealJ A b) (Xop A b D Q j p) =
      Ideal.Quotient.mk (idealJ A b) (X j * p) := by
  unfold Xop
  rw [tau_mod A b D Q, red_mod A b]
  apply red_supported
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have hh := low_degree D p hp
    omega)


lemma relSpace_le (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (T : Submodule (ZMod q) (MvPolynomial (Fin n) (ZMod q)))
    (h₀ : relN0 A b D Q ≤ T)
    (hX : ∀ j, ∀ v ∈ T, Xop A b D Q j v ∈ T) : relSpace A b D Q ≤ T := by
  apply iSup_le
  intro r
  induction r with
  | zero => exact h₀
  | succ r ih =>
    change relNr A b D Q r ⊔ _ ≤ T
    refine sup_le ih (Submodule.span_le.mpr ?_)
    rintro w ⟨j, v, hv, rfl⟩
    exact hX j v (ih hv)

lemma relNr_mono (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) :
    Monotone (relNr A b D Q) := by
  apply monotone_nat_of_le_succ
  intro r
  exact le_sup_left

lemma Xop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ relSpace A b D Q) :
    Xop A b D Q j v ∈ relSpace A b D Q := by
  obtain ⟨r, hr⟩ := (Submodule.mem_iSup_of_directed _ (relNr_mono A b D Q).directed_le).mp hv
  apply (le_iSup (relNr A b D Q) (r + 1))
  apply (show Submodule.span (ZMod q) {w | ∃ j, ∃ v ∈ relNr A b D Q r,
      w = Xop A b D Q j v} ≤ relNr A b D Q (r + 1) from le_sup_right)
  exact Submodule.subset_span ⟨j, v, hr, rfl⟩

lemma relN0_le_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) :
    relN0 A b D Q ≤ relSpace A b D Q := le_iSup (relNr A b D Q) 0

lemma iterate_low (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (j : Fin n) (r : ℕ) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Xop A b D Q j)^[r] v ∈ lowSpan q n D := by
  induction r with
  | zero => exact hv
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact Xop_low A b D hD Q hQ j _ ih

lemma Lop_low (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Lop A b D Q i v ∈ lowSpan q n D := by
  apply Submodule.sum_mem
  intro j _
  exact (lowSpan q n D).smul_mem _ (Xop_low A b D hD Q hQ j v hv)

lemma relSpace_low (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    relSpace A b D Q ≤ lowSpan q n D := by
  apply relSpace_le A b D Q
  · apply Submodule.span_le.mpr
    rintro w ((⟨j, k, _, v, hv, rfl⟩ | ⟨j, v, hv, rfl⟩) | ⟨i, v, hv, rfl⟩)
    · exact (lowSpan q n D).sub_mem
        (Xop_low A b D hD Q hQ j _ (Xop_low A b D hD Q hQ k v hv))
        (Xop_low A b D hD Q hQ k _ (Xop_low A b D hD Q hQ j v hv))
    · exact (lowSpan q n D).sub_mem (iterate_low A b D hD Q hQ j q v hv)
        (Xop_low A b D hD Q hQ j v hv)
    · let w := Lop A b D Q i v - b i • v + v
      have hw : w ∈ lowSpan q n D := (lowSpan q n D).add_mem
        ((lowSpan q n D).sub_mem (Lop_low A b D hD Q hQ i v hv)
          ((lowSpan q n D).smul_mem _ hv)) hv
      exact (lowSpan q n D).sub_mem (Lop_low A b D hD Q hQ i w hw)
        ((lowSpan q n D).smul_mem _ hw)
  · exact Xop_low A b D hD Q hQ

lemma quot_Xop (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (Xop A b D Q j v) =
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (X j) *
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) v := by
  change Ideal.Quotient.mk _ (Xop A b D Q j v) = _
  rw [Xop_mod A b D hD Q j v hv, map_mul]
  rfl

lemma quot_iterate (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (j : Fin n) (r : ℕ) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) ((Xop A b D Q j)^[r] v) =
      ((Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (X j)) ^ r *
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', quot_Xop A b D hD Q j _ (iterate_low A b D hD Q hQ j r v hv), ih]
    rw [pow_succ']; ring

lemma quot_Lop (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (Lop A b D Q i v) =
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) (linForm (cols A i)) *
      (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)) v := by
  classical
  let f := Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)
  change f (∑ j, A j i • Xop A b D Q j v) = f (∑ j, C (A j i) * X j) * f v
  rw [map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul]
  change A j i • f (Xop A b D Q j v) = f (C (A j i) * X j) * f v
  rw [map_mul, show f (Xop A b D Q j v) = f (X j) * f v from quot_Xop A b D hD Q j v hv]
  rw [show f (C (A j i)) = algebraMap (ZMod q) _ (A j i) from f.commutes _]
  exact (Algebra.smul_def (R := ZMod q) _ _).trans (mul_assoc _ _ _).symm


lemma relSpace_mod (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    relSpace A b D Q ≤ LinearMap.ker (Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)).toLinearMap := by
  classical
  let f := Ideal.Quotient.mkₐ (ZMod q) (idealJ A b)
  have h₀ : relN0 A b D Q ≤ LinearMap.ker f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro w ((⟨j, k, _, v, hv, rfl⟩ | ⟨j, v, hv, rfl⟩) | ⟨i, v, hv, rfl⟩)
    · change f (Cop A b D Q j k v) = 0
      simp only [Cop, map_sub]
      rw [quot_Xop A b D hD Q j _ (Xop_low A b D hD Q hQ k v hv),
        quot_Xop A b D hD Q k _ (Xop_low A b D hD Q hQ j v hv),
        quot_Xop A b D hD Q k v hv, quot_Xop A b D hD Q j v hv]
      ring
    · change f (Hop A b D Q j v) = 0
      simp only [Hop, map_sub]
      rw [quot_iterate A b D hD Q hQ j q v hv, quot_Xop A b D hD Q j v hv]
      have he : f (X j ^ q - X j) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      rw [map_sub, map_pow] at he
      rw [sub_eq_zero.mp he, sub_self]
    · let w := Lop A b D Q i v - b i • v + v
      have hw : w ∈ lowSpan q n D := (lowSpan q n D).add_mem
        ((lowSpan q n D).sub_mem (Lop_low A b D hD Q hQ i v hv)
          ((lowSpan q n D).smul_mem _ hv)) hv
      change f (Lop A b D Q i w - b i • w) = 0
      have he : f (fPoly A b i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (sample_mem A b i)
      have hL (u : MvPolynomial (Fin n) (ZMod q)) (hu : u ∈ lowSpan q n D) :
          f (Lop A b D Q i u) = f (linForm (cols A i)) * f u := quot_Lop A b D hD Q i u hu
      have hc (c : ZMod q) : f (C c) = algebraMap (ZMod q) _ c := f.commutes c
      calc
        _ = f (fPoly A b i) * f v := by
          rw [map_sub, map_smul, hL w hw]
          simp only [w, map_add, map_sub, map_smul, hL v hv, fPoly, map_mul, map_one, hc]
          have hsmul (z : MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b) :
              b i • z = algebraMap (ZMod q) _ (b i) * z := Algebra.smul_def (b i) z
          simp only [hsmul]
          ring
        _ = 0 := by rw [he, zero_mul]
  have h : relSpace A b D Q ≤ lowSpan q n D ⊓ LinearMap.ker f.toLinearMap := by
    apply relSpace_le A b D Q
    · exact le_inf ((relN0_le_relSpace A b D Q).trans (relSpace_low A b D hD Q hQ)) h₀
    · intro j v hv
      refine ⟨Xop_low A b D hD Q hQ j v hv.1, ?_⟩
      change f (Xop A b D Q j v) = 0
      rw [quot_Xop A b D hD Q j v hv.1]
      change f (X j) * f v = 0
      rw [show f v = 0 from hv.2, mul_zero]
  exact h.trans inf_le_right

lemma quotient_surj (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    ∀ y : MvPolynomial (Fin n) (ZMod q) ⧸ idealJ A b,
      ∃ v ∈ lowSpan q n D, Ideal.Quotient.mk (idealJ A b) v = y := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨C c, ?_, rfl⟩
    exact monomial_low D 0 c (by intro j; simp; exact (Fact.out : q.Prime).pos)
      (by simp; omega)
  | add p r hp hr =>
    obtain ⟨v, hv, he⟩ := hp
    obtain ⟨w, hw, he'⟩ := hr
    exact ⟨v + w, (lowSpan q n D).add_mem hv hw, by simp only [map_add, he, he']⟩
  | mul_X p j hp =>
    obtain ⟨v, hv, he⟩ := hp
    refine ⟨Xop A b D Q j v, Xop_low A b D hD Q hQ j v hv, ?_⟩
    rw [Xop_mod A b D hD Q j v hv, map_mul, he, map_mul, mul_comm]


lemma Cop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j k : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Cop A b D Q j k v ∈ relSpace A b D Q := by
  rcases lt_trichotomy j k with hj | rfl | hk
  · exact relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inl (Or.inl ⟨j, k, hj, v, hv, rfl⟩)))
  · simp only [Cop, sub_self]; exact Submodule.zero_mem _
  · have hh : Cop A b D Q k j v ∈ relSpace A b D Q :=
      relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inl (Or.inl ⟨k, j, hk, v, hv, rfl⟩)))
    simpa only [Cop, neg_sub] using (relSpace A b D Q).neg_mem hh

lemma Hop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Hop A b D Q j v ∈ relSpace A b D Q :=
  relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inl (Or.inr ⟨j, v, hv, rfl⟩)))

lemma Fop_relSpace (D : ℕ)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) (hv : v ∈ lowSpan q n D) :
    Fop A b D Q i v ∈ relSpace A b D Q :=
  relN0_le_relSpace A b D Q (Submodule.subset_span (Or.inr ⟨i, v, hv, rfl⟩))

set_option maxRecDepth 3000 in
set_option maxHeartbeats 0 in
open scoped IsMulCommutative in
lemma kernel_reverse (D : ℕ) (hD : 2 ≤ D)
    (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D)
    (hpJ : p ∈ idealJ A b) : p ∈ relSpace A b D Q := by
  classical
  let V := lowSpan q n D
  let N : Submodule (ZMod q) V := (relSpace A b D Q).comap V.subtype
  let Xv : Fin n → Module.End (ZMod q) V := fun j => (XL A b D Q j).restrict
    (fun v hv => by rw [XL_apply]; exact Xop_low A b D hD Q hQ j v hv)
  have hXval (j : Fin n) (v : V) : (Xv j v).val = Xop A b D Q j v.val := by
    change XL A b D Q j v.val = _
    exact XL_apply A b D Q j v.val
  have hNv (j : Fin n) : N ≤ N.comap (Xv j) := by
    intro v hv
    change (Xv j v).val ∈ relSpace A b D Q
    rw [hXval]
    exact Xop_relSpace A b D Q j v.val hv
  let x : Fin n → Module.End (ZMod q) (V ⧸ N) := fun j => N.mapQ N (Xv j) (hNv j)
  have hx (j : Fin n) (v : V) : x j (N.mkQ v) = N.mkQ (Xv j v) := rfl
  have hcomm (j k : Fin n) : x j * x k = x k * x j := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [Module.End.mul_apply, hx]
    apply (Submodule.Quotient.eq N).mpr
    change (Xv j (Xv k v)).val - (Xv k (Xv j v)).val ∈ relSpace A b D Q
    simp only [hXval]
    exact Cop_relSpace A b D Q j k v.val v.property
  let B := Algebra.adjoin (ZMod q) (Set.range x)
  letI : IsMulCommutative B := Algebra.isMulCommutative_adjoin (ZMod q) (by
    rintro a ⟨j, rfl⟩ b ⟨k, rfl⟩
    exact hcomm j k)
  let y : Fin n → B := fun j => ⟨x j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  let ev : MvPolynomial (Fin n) (ZMod q) →ₐ[ZMod q] Module.End (ZMod q) (V ⧸ N) :=
    B.val.comp (aeval y)
  have hevX (j : Fin n) : ev (X j) = x j := by simp [ev, y]
  have hevC (c : ZMod q) : ev (C c) = c • (1 : Module.End (ZMod q) (V ⧸ N)) := by
    exact (ev.commutes c).trans (Algebra.algebraMap_eq_smul_one c)
  have hxpow (j : Fin n) (r : ℕ) (v : V) :
      (x j ^ r) (N.mkQ v) = N.mkQ ((Xv j ^ r) v) := by
    induction r with
    | zero => rfl
    | succ r ih => simp only [pow_succ', Module.End.mul_apply, ih, hx]
  have hpowval (j : Fin n) (r : ℕ) (v : V) :
      ((Xv j ^ r) v).val = (Xop A b D Q j)^[r] v.val := by
    induction r with
    | zero => rfl
    | succ r ih =>
      simp only [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      rw [hXval, ih]
  have hfield (j : Fin n) : ev (X j ^ q - X j) = 0 := by
    rw [map_sub, map_pow, hevX]
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    simp only [LinearMap.sub_apply, hxpow, hx, LinearMap.zero_apply]
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change (((Xv j ^ q) v).val - (Xv j v).val) ∈ relSpace A b D Q
    rw [hpowval, hXval]
    exact Hop_relSpace A b D Q j v.val v.property
  have hevL (i : Fin m) : ev (linForm (cols A i)) = ∑ j, A j i • x j := by
    simp only [linForm, cols, map_sum, map_mul, hevC, hevX, smul_mul_assoc, one_mul]
  have hLmk (i : Fin m) (v : V) :
      ev (linForm (cols A i)) (N.mkQ v) = N.mkQ
        ⟨Lop A b D Q i v.val, Lop_low A b D hD Q hQ i v.val v.property⟩ := by
    rw [hevL]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, ← map_smul, ← map_sum]
    congr 1
    apply Subtype.ext
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, hXval]
    rfl
  have hsample (i : Fin m) : ev (fPoly A b i) = 0 := by
    unfold fPoly
    rw [map_mul, map_sub, map_add, map_sub, map_one, hevC]
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := N.mkQ_surjective w
    let wv : V := ⟨Lop A b D Q i v.val - b i • v.val + v.val,
      V.add_mem (V.sub_mem (Lop_low A b D hD Q hQ i v.val v.property)
        (V.smul_mem _ v.property)) v.property⟩
    have hwv : (ev (linForm (cols A i)) - b i • 1 + 1) (N.mkQ v) = N.mkQ wv := by
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        Module.End.one_apply, hLmk, ← map_smul, ← map_sub, ← map_add]
      rfl
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, LinearMap.zero_apply] at hwv ⊢
    rw [hwv, hLmk, ← map_smul, ← map_sub]
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    change (Lop A b D Q i wv.val - b i • wv.val) ∈ relSpace A b D Q
    exact Fop_relSpace A b D Q i v.val v.property
  have hJ : idealJ A b ≤ RingHom.ker ev.toRingHom := by
    apply Ideal.span_le.mpr
    rintro f (⟨i, rfl⟩ | ⟨j, rfl⟩)
    · exact hsample i
    · exact hfield j
  have hevzero : ev p = 0 := hJ hpJ
  have hone : (1 : MvPolynomial (Fin n) (ZMod q)) ∈ V := by
    simpa [V] using
      monomial_low (q := q) D 0 (1 : ZMod q) (by intro j; simpa using (Fact.out : q.Prime).pos)
        (by simp; omega)
  let v1 : V := ⟨1, hone⟩
  have hmono (d : ℕ) : ∀ (s : Fin n →₀ ℕ) (hsd : (∑ j, s j) = d)
      (hs : ∀ j, s j < q) (hd : d < D),
      ev (monomial s 1) (N.mkQ v1) = N.mkQ
        ⟨monomial s 1, monomial_low D s 1 hs (hsd.trans_lt hd)⟩ := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro s hsd hs hd
      by_cases hz : s = 0
      · subst s
        simp only [monomial_zero', map_one, Module.End.one_apply]
        rfl
      · obtain ⟨j, hj⟩ : ∃ j, 0 < s j := by
          by_contra hn
          push_neg at hn
          apply hz
          ext j
          exact Nat.eq_zero_of_le_zero (hn j)
        let t := s - Finsupp.single j 1
        have hdecomp : Finsupp.single j 1 + t = s := by
          ext k
          by_cases hk : j = k
          · subst k; simp [t]; omega
          · simp [t, Finsupp.single_apply, hk]
        have hsum : 1 + (∑ k, t k) = d := by
          rw [← hsd, ← hdecomp]
          simp [Finset.sum_add_distrib]
        have ht : ∀ k, t k < q := by
          intro k
          exact lt_of_le_of_lt (by simp only [t, Finsupp.sub_apply]; exact Nat.sub_le _ _) (hs k)
        have htd : ∑ k, t k < D := by omega
        have hi := ih (∑ k, t k) (by omega) t rfl ht htd
        have hm : (monomial s 1 : MvPolynomial (Fin n) (ZMod q)) = X j * monomial t 1 := by
          rw [← hdecomp]
          simp [X, monomial_mul]
        conv_lhs => rw [hm, map_mul, hevX, Module.End.mul_apply, hi, hx]
        congr 1
        apply Subtype.ext
        rw [hXval]
        change Xop A b D Q j (monomial t 1) = monomial s 1
        rw [Xop_fixed A b D Q j (monomial t 1) (by
          rw [← hm]; exact monomial_low D s 1 hs (by omega)), ← hm]
  have hrep : ∀ (r : MvPolynomial (Fin n) (ZMod q)) (hr : r ∈ V),
      ev r (N.mkQ v1) = N.mkQ ⟨r, hr⟩ := by
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨s, hs, hd, rfl⟩ := hr
      exact hmono (∑ j, s j) s rfl hs hd
    | zero =>
      change ev 0 (N.mkQ v1) = N.mkQ (0 : V)
      rw [map_zero, LinearMap.zero_apply, map_zero]
    | add r s hr hs ihr ihs =>
      calc
        _ = ev r (N.mkQ v1) + ev s (N.mkQ v1) := by rw [map_add, LinearMap.add_apply]
        _ = N.mkQ ⟨r, hr⟩ + N.mkQ ⟨s, hs⟩ := congrArg₂ (· + ·) ihr ihs
        _ = N.mkQ (⟨r, hr⟩ + ⟨s, hs⟩) := (N.mkQ.map_add _ _).symm
    | smul c r hr ihr =>
      calc
        _ = c • ev r (N.mkQ v1) := by rw [map_smul, LinearMap.smul_apply]
        _ = c • N.mkQ ⟨r, hr⟩ := congrArg (c • ·) ihr
        _ = N.mkQ (c • ⟨r, hr⟩) := (N.mkQ.map_smul c _).symm
  have hz : N.mkQ ⟨p, hp⟩ = 0 := by
    rw [← hrep p hp, hevzero]
    rfl
  exact (Submodule.Quotient.mk_eq_zero N).mp hz

end
end Prop49Proof

end File_T17_P49Lib

section File_T17_SemPhi

/-! # Semantics of the `Φ` columns -/

namespace T17

open MvPolynomial F3SubsetSum

variable {q : ℕ} [NeZero q]

theorem length_bump (β : List ℕ) (j : ℕ) : (bump β j).length = β.length := by simp [bump]

theorem getD_bump (β : List ℕ) (j t : ℕ) (ht : t < β.length) :
    (bump β j).getD t 0 = β.getD t 0 + if t = j then 1 else 0 := by
  unfold bump
  rw [List.getD_eq_getElem _ _ (by simp [ht])]
  simp

theorem monoOf_bump {n : ℕ} (β : List ℕ) (hβ : β.length = n) (j : Fin n) :
    monoOf n (bump β j) = monoOf n β + Finsupp.single j 1 := by
  ext t
  simp only [monoOf_apply, Finsupp.coe_add, Pi.add_apply]
  rw [getD_bump _ _ _ (by rw [hβ]; exact t.isLt)]
  simp [Finsupp.single_apply, Fin.ext_iff, eq_comm]

theorem list_flatMap_sum {M : Type*} [AddCommMonoid M] (L : List ℕ) (f : ℕ → List M) :
    (L.flatMap f).sum = (L.map (fun j => (f j).sum)).sum := by
  induction L with
  | nil => simp
  | cons j L ih => simp [List.flatMap_cons, ih]

theorem sum_range_fin {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ j : Fin n, f j := by
  rw [list_sum_range, Fin.sum_univ_eq_sum_range]

/-- The column list of an instance. -/
def colL {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (i : Fin m) : List ℕ :=
  List.ofFn (fun j => (A j i).val)

theorem colL_length {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (i : Fin m) :
    (colL A i).length = n := by simp [colL]

theorem colL_getD {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (i : Fin m) (j : Fin n) :
    (((colL A i).getD j 0 : ℕ) : ZMod q) = A j i := by
  unfold colL
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem linForm_sq_mul {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (i : Fin m) (s : Fin n →₀ ℕ) :
    linForm (cols A i) ^ 2 * monomial s (1 : ZMod q) =
      ∑ j : Fin n, ∑ k : Fin n, monomial (s + Finsupp.single j 1 + Finsupp.single k 1) (A j i * A k i) := by
  unfold linForm
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [cols, X, C_mul_monomial, monomial_mul, mul_one]
  congr 1
  abel

/-- Entries of a `Φ` column. -/
theorem toV_colPhi {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (i : Fin m)
    (MD : List (List ℕ)) (hMD : ∀ α ∈ MD, α.length = n) (β : List ℕ) (hβ : β.length = n) (t : ℕ)
    (ht : t < MD.length) :
    toV q (colPhi q MD (colL A i) β) t =
      (linForm (cols A i) ^ 2 * monomial (monoOf n β) (1 : ZMod q)).coeff (monoOf n (MD.getD t [])) := by
  have hα : (MD.getD t []).length = n := by
    rw [List.getD_eq_getElem _ _ ht]; exact hMD _ (List.getElem_mem _)
  simp only [toV, colPhi, colL_length]
  rw [List.getD_eq_getElem _ _ (by simp [ht])]
  simp only [List.getElem_map]
  rw [cast_sumq, List.map_flatMap, list_flatMap_sum, sum_range_fin, linForm_sq_mul, coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [List.map_map, sum_range_fin, coeff_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Function.comp_apply, coeff_monomial]
  have hb : monoOf n (bump (bump β j) k) = monoOf n β + Finsupp.single j 1 + Finsupp.single k 1 := by
    rw [monoOf_bump _ (by rw [length_bump, hβ]) k, monoOf_bump _ hβ j]
  have hiff : (bump (bump β j) k == MD[t]) = true ↔
      monoOf n β + Finsupp.single j 1 + Finsupp.single k 1 = monoOf n (MD.getD t []) := by
    rw [beq_iff_eq, ← hb, List.getD_eq_getElem _ _ ht]
    constructor
    · rintro h; rw [h]
    · intro h
      exact monoOf_inj (by rw [length_bump, length_bump, hβ]) (by rw [← List.getD_eq_getElem _ _ ht]; exact hα) h
  by_cases h : monoOf n β + Finsupp.single j 1 + Finsupp.single k 1 = monoOf n (MD.getD t [])
  · rw [if_pos (hiff.2 h), if_pos h, cast_mulq, colL_getD, colL_getD]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]; simp

end T17

end File_T17_SemPhi

section File_T17_RM

/-! # Reduced monomials ↔ exponent lists -/

namespace T17

open MvPolynomial F3SubsetSum

variable {q : ℕ}

theorem idxOf_lt {Ms : List (List ℕ)} {a : List ℕ} (h : a ∈ Ms) : idxOf Ms a < Ms.length := by
  unfold idxOf
  exact List.findIdx_lt_length_of_exists ⟨a, h, by simp⟩

theorem getD_idxOf {Ms : List (List ℕ)} {a : List ℕ} (h : a ∈ Ms) : Ms.getD (idxOf Ms a) [] = a := by
  have hlt := idxOf_lt h
  rw [List.getD_eq_getElem _ _ hlt]
  have := List.findIdx_getElem (w := hlt)
  exact beq_iff_eq.1 this

theorem idxOf_getD {Ms : List (List ℕ)} (hM : Ms.Nodup) (t : ℕ) (ht : t < Ms.length) :
    idxOf Ms (Ms.getD t []) = t := by
  have hmem : Ms.getD t [] ∈ Ms := by rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
  have hlt := idxOf_lt hmem
  have h1 := getD_idxOf hmem
  rw [List.getD_eq_getElem _ _ hlt] at h1
  have h2 : Ms[idxOf Ms (Ms.getD t [])] = Ms[t] := by rw [h1, List.getD_eq_getElem _ _ ht]
  exact (hM.getElem_inj_iff).1 h2

/-- The exponent list of a reduced monomial. -/
def rl {n d : ℕ} (β : ReducedMono n q d) : List ℕ := List.ofFn (fun j => (β.1 j : ℕ))

theorem rl_length {n d : ℕ} (β : ReducedMono n q d) : (rl β).length = n := by simp [rl]

theorem rl_getD {n d : ℕ} (β : ReducedMono n q d) (j : Fin n) : (rl β).getD j 0 = β.1 j := by
  unfold rl; rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem monoOf_rl {n d : ℕ} (β : ReducedMono n q d) : monoOf n (rl β) = β.toFinsupp := by
  ext j
  rw [monoOf_apply, rl_getD]
  simp [ReducedMono.toFinsupp]

theorem rl_mem (hq : 0 < q) {n d : ℕ} (β : ReducedMono n q d) : rl β ∈ monosEq q n d := by
  rw [mem_monosEq hq]
  refine ⟨rl_length β, ?_, ?_⟩
  · intro e he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he
    exact (β.1 j).isLt
  · have h2 := β.2
    simp only [rl, List.sum_ofFn]
    exact h2

theorem rl_inj {n d : ℕ} {β γ : ReducedMono n q d} (h : rl β = rl γ) : β = γ := by
  apply Subtype.ext; funext j
  have := congrArg (fun l => l.getD j 0) h
  simp only [rl_getD] at this
  exact Fin.ext this

theorem sum_getD_fin {n : ℕ} (α : List ℕ) (hl : α.length = n) :
    ∑ j : Fin n, α.getD j 0 = α.sum := by
  subst hl
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem _ _ h2]

/-- The reduced monomial of a list in `monosEq`. -/
def rmOf (hq : 0 < q) {n d : ℕ} (α : List ℕ) (h : α ∈ monosEq q n d) : ReducedMono n q d :=
  ⟨fun j => ⟨α.getD j 0, by
      rw [mem_monosEq hq] at h
      exact h.2.1 _ (by rw [List.getD_eq_getElem _ _ (by rw [h.1]; exact j.isLt)]; exact List.getElem_mem _)⟩,
    by
      have h' := (mem_monosEq hq _ _ _).1 h
      show ∑ j : Fin n, α.getD j 0 = d
      exact (sum_getD_fin α h'.1).trans h'.2.2⟩

theorem rl_rmOf (hq : 0 < q) {n d : ℕ} (α : List ℕ) (h : α ∈ monosEq q n d) : rl (rmOf hq α h) = α := by
  have hl := ((mem_monosEq hq _ _ _).1 h).1
  apply List.ext_getElem (by simp [rl, hl])
  intro i h1 h2
  simp [rl, rmOf, List.getElem?_eq_getElem h2]

end T17

end File_T17_RM

section File_T17_Abs

/-! # Abstract layer: from the semantics of `X_j` to `L_i, F_i, H_j, C_{jk}` -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q))
  (b : Fin m → ZMod q) (D : ℕ) (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2))
  (I : Inst) (XC : List (List (List ℕ)))

/-- Semantics of the list operators `X_j`. -/
def XSem : Prop :=
  ∀ j : Fin n, ∀ v : List ℕ, v.length = dVl q I D →
    pv n (MVl q I D) (toV q (Xl q I D XC j v)) = Xop A b D Q j (pv n (MVl q I D) (toV q v))

/-- `I` represents `(A, b)`. -/
structure Rep : Prop where
  hn : I.n = n
  hm : I.m = m
  hcol : ∀ i : Fin m, I.cols.getD i [] = colL A i
  hb : ∀ i : Fin m, ((I.b.getD i 0 : ℕ) : ZMod q) = b i

variable {A b D Q I XC}

theorem length_Xl (j : ℕ) (v : List ℕ) : (Xl q I D XC j v).length = dVl q I D := length_matVec _ _ _

theorem length_Ll (i : ℕ) (v : List ℕ) : (Ll q I D XC i v).length = dVl q I D := length_vsum _ _

theorem Ll_sem (hR : Rep A b I) (hX : XSem A b D Q I XC) (i : Fin m) (v : List ℕ)
    (hv : v.length = dVl q I D) :
    pv n (MVl q I D) (toV q (Ll q I D XC i v)) = Lop A b D Q i (pv n (MVl q I D) (toV q v)) := by
  unfold Ll
  rw [toV_vsum _ _ (by
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hw
    rw [length_smul, length_Xl])]
  rw [List.map_map, list_sum_range, map_sum, hR.hn, ← Fin.sum_univ_eq_sum_range]
  unfold Lop
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, toV_smul, map_smul]
  rw [hR.hcol i, colL_getD, hX j v hv]

theorem length_vlin' {d : ℕ} (c : ℕ) (x y : List ℕ) (hx : x.length = d) (hy : y.length = d) :
    (vlin q c x y).length = d := by rw [length_vlin _ _ _ (hx.trans hy.symm), hx]

theorem Fl_sem (hR : Rep A b I) (hX : XSem A b D Q I XC) (i : Fin m) (v : List ℕ)
    (hv : v.length = dVl q I D) :
    pv n (MVl q I D) (toV q (Fl q I D XC i v)) = Fop A b D Q i (pv n (MVl q I D) (toV q v)) := by
  unfold Fl Fop
  simp only
  have hw1 : (vlin q (negq q (I.b.getD i 0)) (Ll q I D XC i v) v).length = dVl q I D :=
    length_vlin' _ _ _ (length_Ll _ _) hv
  have hw : (vlin q 1 (vlin q (negq q (I.b.getD i 0)) (Ll q I D XC i v) v) v).length = dVl q I D :=
    length_vlin' _ _ _ hw1 hv
  have hsw : pv n (MVl q I D) (toV q (vlin q 1 (vlin q (negq q (I.b.getD i 0)) (Ll q I D XC i v) v) v)) =
      Lop A b D Q i (pv n (MVl q I D) (toV q v)) - b i • pv n (MVl q I D) (toV q v) +
        pv n (MVl q I D) (toV q v) := by
    rw [toV_vlin _ _ _ (hw1.trans hv.symm), toV_vlin _ _ _ ((length_Ll _ _).trans hv.symm)]
    simp only [map_add, map_smul, cast_negq, hR.hb i, Ll_sem hR hX i v hv, Nat.cast_one, one_smul,
      neg_smul, sub_eq_add_neg, map_neg]
  rw [toV_vlin _ _ _ ((length_Ll _ _).trans hw.symm)]
  simp only [map_add, map_smul, cast_negq, hR.hb i, Ll_sem hR hX i _ hw, hsw, neg_smul,
    sub_eq_add_neg, map_neg]

theorem foldl_Xl_sem (hX : XSem A b D Q I XC) (j : Fin n) (k : ℕ) (v : List ℕ)
    (hv : v.length = dVl q I D) :
    ((List.replicate k (j : ℕ)).foldl (fun u j' => Xl q I D XC j' u) v).length = dVl q I D ∧
    pv n (MVl q I D) (toV q ((List.replicate k (j : ℕ)).foldl (fun u j' => Xl q I D XC j' u) v)) =
      (Xop A b D Q j)^[k] (pv n (MVl q I D) (toV q v)) := by
  induction k generalizing v with
  | zero => exact ⟨hv, rfl⟩
  | succ k ih =>
    rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := ih (Xl q I D XC j v) (length_Xl _ _)
    exact ⟨h1, by rw [h2, hX j v hv]⟩

theorem Hl_sem (hX : XSem A b D Q I XC) (j : Fin n) (v : List ℕ) (hv : v.length = dVl q I D) :
    pv n (MVl q I D) (toV q (Hl q I D XC j v)) = Hop A b D Q j (pv n (MVl q I D) (toV q v)) := by
  unfold Hl Hop
  obtain ⟨h1, h2⟩ := foldl_Xl_sem hX j q v hv
  rw [toV_vsub _ _ (h1.trans (length_Xl _ _).symm), map_sub, h2, hX j v hv]

theorem Cl_sem (hX : XSem A b D Q I XC) (j k : Fin n) (v : List ℕ) (hv : v.length = dVl q I D) :
    pv n (MVl q I D) (toV q (Cl q I D XC j k v)) = Cop A b D Q j k (pv n (MVl q I D) (toV q v)) := by
  unfold Cl Cop
  rw [toV_vsub _ _ ((length_Xl _ _).trans (length_Xl _ _).symm), map_sub,
    hX j _ (length_Xl _ _), hX k v hv, hX k _ (length_Xl _ _), hX j v hv]

theorem length_Fl (i : ℕ) (v : List ℕ) (hv : v.length = dVl q I D) :
    (Fl q I D XC i v).length = dVl q I D := by
  unfold Fl; simp only
  exact length_vlin' _ _ _ (length_Ll _ _)
    (length_vlin' _ _ _ (length_vlin' _ _ _ (length_Ll _ _) hv) hv)

theorem length_foldl_Xl (L : List ℕ) (v : List ℕ) (hv : v.length = dVl q I D) :
    (L.foldl (fun u j' => Xl q I D XC j' u) v).length = dVl q I D := by
  induction L generalizing v with
  | nil => exact hv
  | cons j L ih => exact ih _ (length_Xl _ _)

theorem length_Hl (j : ℕ) (v : List ℕ) (hv : v.length = dVl q I D) :
    (Hl q I D XC j v).length = dVl q I D := by
  unfold Hl
  rw [length_vsub _ _ ((length_foldl_Xl _ _ hv).trans (length_Xl _ _).symm), length_foldl_Xl _ _ hv]

theorem length_Cl (j k : ℕ) (v : List ℕ) : (Cl q I D XC j k v).length = dVl q I D := by
  unfold Cl
  rw [length_vsub _ _ ((length_Xl _ _).trans (length_Xl _ _).symm), length_Xl]

end T17

end File_T17_Abs

section File_T17_Abs2

/-! # Abstract layer II: `N_0`, the closure, stabilisation -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

section Gen
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- Images of a span under a linear map lie in the span of the images of generators. -/
theorem map_mem_span_image (f : M →ₗ[K] M) (S U : Set M) (h : ∀ v ∈ S, f v ∈ Submodule.span K U)
    (v : M) (hv : v ∈ Submodule.span K S) : f v ∈ Submodule.span K U := by
  have : f v ∈ (Submodule.span K S).map f := Submodule.mem_map_of_mem hv
  rw [Submodule.map_span] at this
  exact (Submodule.span_le.2 (by rintro _ ⟨w, hw, rfl⟩; exact h w hw)) this

/-- Stabilisation of a chain inside a finite-dimensional space. -/
theorem chain_stable (N : ℕ → Submodule K M) (W : Submodule K M) [FiniteDimensional K W]
    (hmono : Monotone N) (hW : ∀ r, N r ≤ W)
    (hstep : ∀ r, N r = N (r + 1) → N (r + 1) = N (r + 2)) (d : ℕ)
    (hd : Module.finrank K W ≤ d) : ⨆ r, N r = N (d + 1) := by
  -- some step in `0..d` is stationary
  have hex : ∃ r ≤ d, N r = N (r + 1) := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ r ≤ d, Module.finrank K (N r) < Module.finrank K (N (r + 1)) := by
      intro r hr
      haveI : FiniteDimensional K (N (r + 1)) := Submodule.finiteDimensional_of_le (hW _)
      exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono (Nat.le_succ r)) (hcon r hr))
    have hge : ∀ r ≤ d + 1, r ≤ Module.finrank K (N r) := by
      intro r hr
      induction r with
      | zero => exact Nat.zero_le _
      | succ r ih => exact lt_of_le_of_lt (ih (by omega)) (hlt r (by omega))
    have h1 := hge (d + 1) le_rfl
    have h2 : Module.finrank K (N (d + 1)) ≤ Module.finrank K W := Submodule.finrank_mono (hW _)
    omega
  obtain ⟨r, hr, hrr⟩ := hex
  have hsucc : ∀ k, N (r + k) = N (r + k + 1) := by
    intro k
    induction k with
    | zero => exact hrr
    | succ k ih => exact hstep (r + k) ih
  have hconst : ∀ k, N (r + k) = N r := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [← add_assoc, ← hsucc k, ih]
  have hfin : N (d + 1) = N r := by
    rw [show d + 1 = r + (d + 1 - r) by omega, hconst]
  rw [hfin]
  apply le_antisymm
  · apply iSup_le
    intro s
    calc N s ≤ N (r + s) := hmono (by omega)
      _ = N r := hconst s
  · exact le_iSup N r

end Gen

section Main
variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
  {b : Fin m → ZMod q} {D : ℕ} {Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)}
  {I : Inst} {XC : List (List (List ℕ))}

theorem pv_single {Ms : List (List ℕ)} (t : ℕ) (ht : t < Ms.length) :
    pv n Ms (Pi.single t 1 : ℕ → ZMod q) = monomial (monoOf n (Ms.getD t [])) 1 := by
  rw [pv_apply, Finset.sum_eq_single t]
  · simp
  · intro u _ hu; simp [Pi.single_apply, hu]
  · intro h; exact absurd (Finset.mem_range.2 ht) h

theorem q_pos : 0 < q := (Fact.out : q.Prime).pos

theorem good_MV (hn : I.n = n) : Good n (MVl q I D) :=
  ⟨nodup_monosLt q_pos _ _, fun α h => ((mem_monosLt q_pos _ _ _).1 h).1.trans hn⟩

/-- The `t`-th low monomial. -/
noncomputable def monoT (q n : ℕ) (I : Inst) (D t : ℕ) : MvPolynomial (Fin n) (ZMod q) :=
  pv n (MVl q I D) (toV q (unitV (dVl q I D) t))

theorem monoT_eq (t : ℕ) (ht : t < dVl q I D) :
    monoT q n I D t = monomial (monoOf n ((MVl q I D).getD t [])) 1 := by
  unfold monoT; rw [toV_unitV _ _ ht, pv_single _ ht]

theorem monoOf_ofFn (s : Fin n →₀ ℕ) : monoOf n (List.ofFn (fun j => s j)) = s := by
  ext j; simp [List.getD_eq_getElem?_getD]

theorem monoT_low (hn : I.n = n) (t : ℕ) (ht : t < dVl q I D) : monoT q n I D t ∈ lowSpan q n D := by
  rw [monoT_eq t ht]
  have hmem : (MVl q I D).getD t [] ∈ monosLt q I.n D := by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
  obtain ⟨hl, hlt, hs⟩ := (mem_monosLt q_pos _ _ _).1 hmem
  rw [hn] at hl
  apply monomial_low
  · intro j
    rw [monoOf_apply, List.getD_eq_getElem _ _ (by rw [hl]; exact j.isLt)]
    exact hlt _ (List.getElem_mem _)
  · simp only [monoOf_apply]
    rw [sum_getD_fin _ hl]; exact hs

theorem lowSpan_eq (hn : I.n = n) :
    lowSpan q n D = Submodule.span (ZMod q) (Set.range fun t : Fin (dVl q I D) => monoT q n I D t) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro p ⟨s, hsq, hsD, rfl⟩
    have hmem : List.ofFn (fun j => s j) ∈ MVl q I D := by
      unfold MVl
      rw [mem_monosLt q_pos]
      refine ⟨by simp [hn], ?_, ?_⟩
      · intro e he; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he; exact hsq j
      · rw [List.sum_ofFn]; exact hsD
    apply Submodule.subset_span
    refine ⟨⟨idxOf (MVl q I D) _, idxOf_lt hmem⟩, ?_⟩
    simp only
    rw [monoT_eq _ (idxOf_lt hmem), getD_idxOf hmem, monoOf_ofFn]
  · apply Submodule.span_le.2
    rintro _ ⟨t, rfl⟩
    exact monoT_low hn t t.isLt

variable (A b D Q) in
noncomputable def CL (j k : Fin n) : Module.End (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  XL A b D Q j * XL A b D Q k - XL A b D Q k * XL A b D Q j

theorem CL_apply (j k : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) : CL A b D Q j k v = Cop A b D Q j k v := by
  simp [CL, Cop, XL_apply]

theorem XL_coe (j : Fin n) : ⇑(XL A b D Q j) = Xop A b D Q j := funext (XL_apply A b D Q j)

variable (A b D Q) in
noncomputable def HL (j : Fin n) : Module.End (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  XL A b D Q j ^ q - XL A b D Q j

theorem HL_apply (j : Fin n) (v : MvPolynomial (Fin n) (ZMod q)) : HL A b D Q j v = Hop A b D Q j v := by
  simp [HL, Hop, Module.End.pow_apply, XL_coe]

variable (A b D Q) in
noncomputable def LLin (i : Fin m) : Module.End (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  ∑ j, A j i • XL A b D Q j

theorem LLin_apply (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) : LLin A b D Q i v = Lop A b D Q i v := by
  simp [LLin, Lop, XL_coe]

variable (A b D Q) in
noncomputable def FL (i : Fin m) : Module.End (ZMod q) (MvPolynomial (Fin n) (ZMod q)) :=
  (LLin A b D Q i - b i • 1) * (LLin A b D Q i - b i • 1 + 1)

theorem FL_apply (i : Fin m) (v : MvPolynomial (Fin n) (ZMod q)) : FL A b D Q i v = Fop A b D Q i v := by
  simp [FL, Fop, LLin_apply]

theorem length_gens0 (g : List ℕ) (hg : g ∈ gens0 q I D XC) : g.length = dVl q I D := by
  unfold gens0 at hg
  simp only [List.mem_flatMap, List.mem_range, List.mem_append, List.mem_map, List.mem_filterMap] at hg
  obtain ⟨t, -, (⟨j, -, k, -, hk⟩ | ⟨j, -, rfl⟩) | ⟨i, -, rfl⟩⟩ := hg
  · split_ifs at hk; cases hk; exact length_Cl _ _ _
  · exact length_Hl _ _ (length_unitV _ _)
  · exact length_Fl _ _ (length_unitV _ _)

/-- The span of the images of `gens0` is `N_0`. -/
theorem relN0_eq (hR : Rep A b I) (hX : XSem A b D Q I XC) :
    relN0 A b D Q = Submodule.span (ZMod q) ((fun g => pv n (MVl q I D) (toV q g)) '' {g | g ∈ gens0 q I D XC}) := by
  have hU : ∀ t, (unitV (dVl q I D) t).length = dVl q I D := fun t => length_unitV _ _
  apply le_antisymm
  · unfold relN0
    apply Submodule.span_le.2
    rintro w ((⟨j, k, hjk, v, hv, rfl⟩ | ⟨j, v, hv, rfl⟩) | ⟨i, v, hv, rfl⟩)
    · rw [← CL_apply]
      rw [lowSpan_eq hR.hn] at hv
      refine map_mem_span_image _ _ _ ?_ v hv
      rintro _ ⟨t, rfl⟩
      dsimp only [monoT]; rw [CL_apply, ← Cl_sem hX j k _ (hU t)]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, gens0, List.mem_flatMap, List.mem_range, List.mem_append,
        List.mem_map, List.mem_filterMap]
      exact ⟨t, t.isLt, Or.inl (Or.inl ⟨j, by rw [hR.hn]; exact j.isLt, k, by rw [hR.hn]; exact k.isLt,
        by rw [if_pos (Fin.lt_def.1 hjk)]⟩)⟩
    · rw [← HL_apply]
      rw [lowSpan_eq hR.hn] at hv
      refine map_mem_span_image _ _ _ ?_ v hv
      rintro _ ⟨t, rfl⟩
      dsimp only [monoT]; rw [HL_apply, ← Hl_sem hX j _ (hU t)]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, gens0, List.mem_flatMap, List.mem_range, List.mem_append,
        List.mem_map, List.mem_filterMap]
      exact ⟨t, t.isLt, Or.inl (Or.inr ⟨j, by rw [hR.hn]; exact j.isLt, rfl⟩)⟩
    · rw [← FL_apply]
      rw [lowSpan_eq hR.hn] at hv
      refine map_mem_span_image _ _ _ ?_ v hv
      rintro _ ⟨t, rfl⟩
      dsimp only [monoT]; rw [FL_apply, ← Fl_sem hR hX i _ (hU t)]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, gens0, List.mem_flatMap, List.mem_range, List.mem_append,
        List.mem_map, List.mem_filterMap]
      exact ⟨t, t.isLt, Or.inr ⟨i, by rw [hR.hm]; exact i.isLt, rfl⟩⟩
  · apply Submodule.span_le.2
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_ofPred_eq, gens0, List.mem_flatMap, List.mem_range, List.mem_append,
      List.mem_map, List.mem_filterMap] at hg
    obtain ⟨t, ht, (⟨j, hj, k, hk, hjk⟩ | ⟨j, hj, rfl⟩) | ⟨i, hi, rfl⟩⟩ := hg
    · split_ifs at hjk with h; cases hjk
      rw [hR.hn] at hj hk
      have := Cl_sem hX ⟨j, hj⟩ ⟨k, hk⟩ _ (hU t)
      simp only at this
      dsimp only
      rw [this]
      exact Submodule.subset_span (Or.inl (Or.inl ⟨⟨j, hj⟩, ⟨k, hk⟩, h, _, monoT_low hR.hn t ht, rfl⟩))
    · rw [hR.hn] at hj
      have := Hl_sem hX ⟨j, hj⟩ _ (hU t)
      simp only at this
      dsimp only
      rw [this]
      exact Submodule.subset_span (Or.inl (Or.inr ⟨⟨j, hj⟩, _, monoT_low hR.hn t ht, rfl⟩))
    · rw [hR.hm] at hi
      have := Fl_sem hR hX ⟨i, hi⟩ _ (hU t)
      simp only at this
      dsimp only
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨⟨i, hi⟩, _, monoT_low hR.hn t ht, rfl⟩)

theorem Bk_succ (k : ℕ) : Bk q I D XC (k + 1) = stepB q I D XC (Bk q I D XC k) := by
  simp [Bk, List.range_succ, List.foldl_append]

theorem map_span_pv (S : Set (ℕ → ZMod q)) :
    (Submodule.span (ZMod q) S).map (pv n (MVl q I D)) = Submodule.span (ZMod q) (pv n (MVl q I D) '' S) :=
  Submodule.map_span _ _

/-- The closure invariant. -/
theorem Bk_spec (hR : Rep A b I) (hX : XSem A b D Q I XC) (k : ℕ) :
    Shape (dVl q I D) (dVl q I D) (Bk q I D XC k) ∧ Echelon (q := q) (Bk q I D XC k) ∧
      PayOK (LinearMap.id : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) (Bk q I D XC k) ∧
      (Submodule.span (ZMod q) (vecs (q := q) (Bk q I D XC k))).map (pv n (MVl q I D)) = relNr A b D Q k := by
  have hq : q.Prime := Fact.out
  induction k with
  | zero =>
    obtain ⟨h1, h2, h3, h4⟩ := insertAll_spec hq LinearMap.id ((gens0 q I D XC).map (fun v => (v, v)))
      (by
        intro xw hxw
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hxw
        exact ⟨length_gens0 g hg, length_gens0 g hg, rfl⟩) []
      (by intro r hr; simp at hr) trivial (by intro r hr; simp at hr)
    refine ⟨h1, h2, h3, ?_⟩
    change _ = relN0 A b D Q
    rw [Bk, List.range_zero, List.foldl_nil, B0, h4, relN0_eq hR hX, Submodule.map_sup, map_span_pv,
      map_span_pv]
    have : vecs (q := q) ([] : List Row) = ∅ := by ext; simp [vecs]
    rw [this, Set.image_empty, Submodule.span_empty, bot_sup_eq]
    congr 1
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩; exact ⟨g, hg, rfl⟩
    · rintro ⟨g, hg, rfl⟩; exact ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
  | succ k ih =>
    obtain ⟨s1, s2, s3, s4⟩ := ih
    set B := Bk q I D XC k
    have hLs : ∀ xw ∈ B.flatMap (fun r => (List.range I.n).map (fun j =>
        (Xl q I D XC j r.2.1, Xl q I D XC j r.2.1))),
        xw.1.length = dVl q I D ∧ xw.2.length = dVl q I D ∧
          toV q xw.1 = (LinearMap.id : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) (toV q xw.2) := by
      intro xw hxw
      obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hxw
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hr
      exact ⟨length_Xl _ _, length_Xl _ _, rfl⟩
    obtain ⟨h1, h2, h3, h4⟩ := insertAll_spec hq LinearMap.id _ hLs B s1 s2 s3
    rw [Bk_succ]
    refine ⟨h1, h2, h3, ?_⟩
    change _ = relNr A b D Q k ⊔ _
    rw [stepB, h4, Submodule.map_sup, s4, map_span_pv]
    congr 1
    have hrel : relNr A b D Q k = Submodule.span (ZMod q) (pv n (MVl q I D) '' vecs (q := q) B) := by
      rw [← s4, map_span_pv]
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨_, ⟨xw, hxw, rfl⟩, rfl⟩
      obtain ⟨r, hrB, hr⟩ := List.mem_flatMap.1 hxw
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
      rw [List.mem_range, hR.hn] at hj
      apply Submodule.subset_span
      refine ⟨⟨j, hj⟩, _, ?_, hX ⟨j, hj⟩ r.2.1 (s1 r hrB).1⟩
      rw [hrel]
      exact Submodule.subset_span ⟨_, ⟨r, hrB, rfl⟩, rfl⟩
    · apply Submodule.span_le.2
      rintro _ ⟨j, v, hv, rfl⟩
      rw [← XL_apply]
      rw [hrel] at hv
      refine map_mem_span_image _ _ _ ?_ v hv
      rintro _ ⟨_, ⟨r, hrB, rfl⟩, rfl⟩
      rw [XL_apply, ← hX j r.2.1 (s1 r hrB).1]
      apply Submodule.subset_span
      refine ⟨_, ⟨(Xl q I D XC j r.2.1, Xl q I D XC j r.2.1), ?_, rfl⟩, rfl⟩
      exact List.mem_flatMap.2 ⟨r, hrB, List.mem_map.2 ⟨j, by rw [List.mem_range, hR.hn]; exact j.isLt, rfl⟩⟩

end Main

end T17

end File_T17_Abs2

section File_T17M_Equiv

/-! # The context decoder agrees with `mainDec` -/

namespace T17M

open T17

variable {q : ℕ} [Fact q.Prime] [NeZero q]

theorem echelon_one (B : List Row) (hE : Echelon (q := q) B) : ∀ r ∈ B, toV q r.2.1 r.1 = 1 := by
  induction B with
  | nil => simp
  | cons r B ih =>
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | h
    · exact hE.1
    · exact ih hE.2.2 r' h

theorem echelon_nodup (B : List Row) (hE : Echelon (q := q) B) : (B.map Prod.fst).Nodup := by
  induction B with
  | nil => simp
  | cons r B ih =>
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, ih hE.2.2⟩
    obtain ⟨r', hr', he⟩ := List.mem_map.1 h
    have h1 := echelon_one B hE.2.2 r' hr'
    have h0 := hE.2.1 r' hr'
    rw [← he] at h0
    rw [h0] at h1
    exact zero_ne_one h1

theorem echelon_length {d e : ℕ} (B : List Row) (hS : Shape d e B) (hE : Echelon (q := q) B) :
    B.length ≤ d := by
  have hnd := echelon_nodup B hE
  have hsub : (B.map Prod.fst).toFinset ⊆ Finset.range d := by
    intro p hp
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    exact Finset.mem_range.2 (hS r hr).2.2
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_range] at this
  exact this

/-- Shape and echelon form of the closure rounds (unconditional). -/
theorem Bk_shape (I : Inst) (D : ℕ) (XC : List (List (List ℕ))) (k : ℕ) :
    Shape (dVl q I D) (dVl q I D) (Bk q I D XC k) ∧ Echelon (q := q) (Bk q I D XC k) ∧
      PayOK (LinearMap.id : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) (Bk q I D XC k) := by
  have hq : q.Prime := Fact.out
  induction k with
  | zero =>
    obtain ⟨h1, h2, h3, -⟩ := insertAll_spec hq (LinearMap.id : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q))
      ((gens0 q I D XC).map (fun v => (v, v)))
      (by
        intro xw hxw
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hxw
        exact ⟨length_gens0 g hg, length_gens0 g hg, rfl⟩) []
      (by intro r hr; simp at hr) trivial (by intro r hr; simp at hr)
    exact ⟨h1, h2, h3⟩
  | succ k ih =>
    rw [Bk_succ]
    obtain ⟨h1, h2, h3, -⟩ := insertAll_spec hq (LinearMap.id : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q))
      ((Bk q I D XC k).flatMap (fun r => (List.range I.n).map (fun j =>
        (Xl q I D XC j r.2.1, Xl q I D XC j r.2.1))))
      (by
        intro xw hxw
        obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hxw
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hr
        exact ⟨length_Xl _ _, length_Xl _ _, rfl⟩) (Bk q I D XC k) ih.1 ih.2.1 ih.2.2
    exact ⟨h1, h2, h3⟩

section
variable (I : Inst) (D : ℕ)

theorem BphiC_eq : BphiC q (ctxOf q I D) = Bphi q I D := rfl

theorem QvecC_eq (BP : List Row) (t : ℕ) : QvecC q (ctxOf q I D) BP t = Qvec q I D BP t := by
  simp only [QvecC, Qvec, ctxOf, Ctx.ER, Ctx.MD, zeroVL_range]; rfl

theorem rvecsC_eq (BP : List Row) : rvecsC q (ctxOf q I D) BP = rvecs q I D BP := by
  unfold rvecsC rvecs
  simp only [QvecC_eq]
  rfl

theorem XcolsC_eq (RV : List (List ℕ)) : XcolsC q (ctxOf q I D) RV = Xcols q I D RV := by
  unfold XcolsC Xcols XcolC Xcol
  simp only [VR, ctxOf, Ctx.ER, Ctx.MD, Ctx.MV, Ctx.nR, zeroVL_range]
  rfl

theorem stepBC_eq (XC : List (List (List ℕ))) (B : List Row) :
    stepBC q (ctxOf q I D) XC B = stepB q I D XC B := rfl

theorem B0C_eq (XC : List (List (List ℕ))) : B0C q (ctxOf q I D) XC = B0 q I D XC := rfl

theorem BkC_eq (XC : List (List (List ℕ))) (k : ℕ) :
    BkC q (ctxOf q I D) XC (List.range k) = Bk q I D XC k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold BkC at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [stepBC_eq, ← Bk_succ]
    obtain ⟨h1, h2, -⟩ := Bk_shape (q := q) I D XC (k + 1)
    exact List.take_of_length_le (echelon_length _ h1 h2)

theorem readOutC_eq (B : List Row) : readOutC q (ctxOf q I D) B = readOut q I D B := by
  unfold readOutC readOut outTestC outTest
  simp only [VR, ctxOf, Ctx.ER, Ctx.MD, Ctx.MV, Ctx.nR, zeroVL_range]
  rfl

theorem mainDecC_eq : mainDecC q (ctxOf q I D) = mainDec q I D := by
  unfold mainDecC mainDec
  simp only [BphiC_eq, rvecsC_eq, XcolsC_eq]
  rw [show (ctxOf q I D).MV.length + 1 = dVl q I D + 1 from rfl, BkC_eq, readOutC_eq]

end

end T17M

end File_T17M_Equiv

section File_T17_Out

/-! # Stabilisation and the read-out -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
  {b : Fin m → ZMod q} {D : ℕ} {Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)}
  {I : Inst} {XC : List (List (List ℕ))}

theorem lowSpan_fd (hn : I.n = n) : FiniteDimensional (ZMod q) (lowSpan q n D) := by
  rw [lowSpan_eq (I := I) hn]
  exact FiniteDimensional.span_of_finite _ (Set.finite_range _)

theorem lowSpan_finrank (hn : I.n = n) : Module.finrank (ZMod q) (lowSpan q n D) ≤ dVl q I D := by
  rw [lowSpan_eq (I := I) hn]
  exact (finrank_range_le_card _).trans (by simp)

/-- After `dV + 1` rounds the closure is the whole relation space. -/
theorem BN_span (hR : Rep A b I) (hX : XSem A b D Q I XC) (hD : 2 ≤ D)
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1) :
    (Submodule.span (ZMod q) (vecs (q := q) (Bk q I D XC (dVl q I D + 1)))).map (pv n (MVl q I D)) =
      relSpace A b D Q := by
  rw [(Bk_spec (q := q) hR hX _).2.2.2]
  haveI := lowSpan_fd (q := q) (D := D) hR.hn
  symm
  apply chain_stable (relNr A b D Q) (lowSpan q n D) (relNr_mono A b D Q)
  · intro r
    exact (le_iSup (relNr A b D Q) r).trans (relSpace_low A b D hD Q hQ)
  · intro r hr
    change relNr A b D Q (r + 1) = relNr A b D Q (r + 1) ⊔ _
    rw [← hr]
    exact hr
  · exact lowSpan_finrank (q := q) hR.hn

theorem toV_eq_zero_iff (x : List ℕ) : toV q x = 0 ↔ x.all (fun a => a % q == 0) = true := by
  rw [List.all_eq_true]
  constructor
  · intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := congrFun h i
    simp only [toV, Pi.zero_apply, List.getD_eq_getElem _ _ hi, ZMod.natCast_eq_zero_iff] at this
    simpa using Nat.mod_eq_zero_of_dvd this
  · intro h
    funext i
    simp only [toV, Pi.zero_apply]
    by_cases hi : i < x.length
    · rw [List.getD_eq_getElem _ _ hi, ZMod.natCast_eq_zero_iff]
      have := h _ (List.getElem_mem hi)
      simp only [beq_iff_eq] at this
      exact Nat.dvd_of_mod_eq_zero this
    · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem sum_unitV (d t : ℕ) (ht : t < d) : (unitV d t).sum = 1 := by
  unfold unitV
  rw [list_sum_range, Finset.sum_ite_eq' (Finset.range d) t, if_pos (Finset.mem_range.2 ht)]

theorem mem_unitV_lt (d t e : ℕ) (he : e ∈ unitV d t) : e ≤ 1 := by
  unfold unitV at he
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 he
  split_ifs <;> omega

theorem monoOf_unitV (j : Fin n) : monoOf n (unitV n j) = Finsupp.single j 1 := by
  ext k
  rw [monoOf_apply, Finsupp.single_apply]
  unfold unitV
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp [Fin.ext_iff, eq_comm]

theorem monoOf_zeroV : monoOf n (zeroV n) = 0 := by
  ext k; simp [zeroV, List.getD_eq_getElem?_getD]

theorem two_le_q : 2 ≤ q := (Fact.out : q.Prime).two_le

theorem unitV_mem_MV (hn : I.n = n) (hD : 2 ≤ D) (j : Fin n) : unitV I.n j ∈ MVl q I D := by
  unfold MVl
  rw [mem_monosLt q_pos]
  refine ⟨length_unitV _ _, fun e he => ?_, ?_⟩
  · have := mem_unitV_lt _ _ _ he; have := two_le_q (q := q); omega
  · rw [sum_unitV _ _ (by rw [hn]; exact j.isLt)]; omega

theorem zeroV_mem_MV (hD : 2 ≤ D) : zeroV I.n ∈ MVl q I D := by
  unfold MVl
  rw [mem_monosLt q_pos]
  refine ⟨by simp [zeroV], fun e he => ?_, ?_⟩
  · simp only [zeroV, List.mem_replicate] at he; rw [he.2]; exact q_pos
  · simp [zeroV]; omega

theorem vecs_sup (B : List Row) (hB : Shape (dVl q I D) (dVl q I D) B) :
    Submodule.span (ZMod q) (vecs (q := q) B) ≤ VecSup q (dVl q I D) := by
  apply Submodule.span_le.2
  rintro _ ⟨r, hr, rfl⟩
  have := toV_mem (q := q) r.2.1
  rwa [(hB r hr).1] at this

/-- The read-out test for one coordinate. -/
theorem outTest_iff (hR : Rep A b I) (hD : 2 ≤ D) (B : List Row)
    (hB : Shape (dVl q I D) (dVl q I D) B) (hE : Echelon (q := q) B)
    (hP : PayOK (LinearMap.id : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q)) B)
    (hspan : (Submodule.span (ZMod q) (vecs (q := q) B)).map (pv n (MVl q I D)) = relSpace A b D Q)
    (h49 : ∀ v, v ∈ relSpace A b D Q ↔ (v ∈ lowSpan q n D ∧ Ideal.Quotient.mk (idealJ A b) v = 0))
    (s : Fin n → ZMod q) (hs : candidates A b = {s}) (j : Fin n) (c : ℕ) :
    outTest q I D B j c = true ↔ (c : ZMod q) = s j := by
  have hjm := unitV_mem_MV (q := q) hR.hn hD j
  have h0m := zeroV_mem_MV (q := q) (I := I) hD
  set ix := idxOf (MVl q I D) (unitV I.n j)
  set i0 := idxOf (MVl q I D) (zeroV I.n)
  have hix : ix < dVl q I D := idxOf_lt hjm
  have hi0 : i0 < dVl q I D := idxOf_lt h0m
  set v := vlin q (negq q c) (unitV (dVl q I D) ix) (unitV (dVl q I D) i0) with hvdef
  have hvl : v.length = dVl q I D := length_vlin' _ _ _ (length_unitV _ _) (length_unitV _ _)
  have hPv : pv n (MVl q I D) (toV q v) = X j + (-(c : ZMod q)) • (1 : MvPolynomial (Fin n) (ZMod q)) := by
    rw [hvdef, toV_vlin _ _ _ (by rw [length_unitV, length_unitV]), map_add, map_smul, cast_negq,
      toV_unitV _ _ hix, toV_unitV _ _ hi0, pv_single _ hix, pv_single _ hi0, getD_idxOf hjm,
      getD_idxOf h0m, hR.hn, monoOf_unitV, monoOf_zeroV]
    simp [X]
  unfold outTest
  simp only
  rw [← hvdef, ← toV_eq_zero_iff, ← mem_span_iff_reduce LinearMap.id B hB hE hP (v, v) hvl hvl]
  have hiff : toV q v ∈ Submodule.span (ZMod q) (vecs (q := q) B) ↔
      pv n (MVl q I D) (toV q v) ∈ relSpace A b D Q := by
    rw [← hspan]
    constructor
    · intro h; exact Submodule.mem_map_of_mem h
    · rintro ⟨u, hu, he⟩
      have := pv_inj (good_MV hR.hn) u (toV q v) (vecs_sup B hB hu) (by have h := toV_mem (q := q) v; rw [hvl] at h; exact h) he
      rwa [← this]
  rw [hiff, h49, hPv]
  have hlow : X j + (-(c : ZMod q)) • (1 : MvPolynomial (Fin n) (ZMod q)) ∈ lowSpan q n D := by
    apply Submodule.add_mem
    · exact monomial_low D _ 1 (fun k => by
        rw [Finsupp.single_apply]; split_ifs <;> have := two_le_q (q := q) <;> omega)
        (by rw [Finset.sum_eq_single j (fun k _ hk => by simp [Finsupp.single_apply, Ne.symm hk]) (by simp)]
            simp; omega)
    · apply Submodule.smul_mem
      exact monomial_low D 0 1 (fun k => by simp; exact q_pos) (by simp; omega)
  rw [and_iff_right hlow, Ideal.Quotient.eq_zero_iff_mem, mem_ideal_iff A b, hs]
  simp only [Set.mem_singleton_iff, forall_eq, map_add, smul_eval, eval_X, map_one, smul_eq_mul, mul_one]
  constructor
  · intro h; rw [← sub_eq_zero, ← neg_sub, neg_eq_zero, sub_eq_add_neg]; exact h
  · intro h; rw [h]; ring

theorem findIdx_range (k : ℕ) (P : ℕ → Bool) (x : ZMod k) [NeZero k] (hP : ∀ c < k, P c = true ↔ (c : ZMod k) = x) :
    (List.range k).findIdx P = x.val := by
  have hv : x.val < (List.range k).length := by rw [List.length_range]; exact ZMod.val_lt x
  rw [List.findIdx_eq hv]
  simp only [List.getElem_range]
  refine ⟨(hP _ (ZMod.val_lt x)).2 (ZMod.natCast_zmod_val x), fun c hc => ?_⟩
  by_contra h
  have h' := (hP c (by have := ZMod.val_lt x; omega)).1 (by simpa using h)
  have : x.val = c := by rw [← h', ZMod.val_natCast, Nat.mod_eq_of_lt (by have := ZMod.val_lt x; omega)]
  omega

/-- The read-out returns the secret. -/
theorem readOut_correct (hR : Rep A b I) (hX : XSem A b D Q I XC) (hD : 2 ≤ D)
    (hQ : ∀ α, Phi (ZMod q) q (cols A) D (Q α) = Pi.single α 1)
    (h49 : ∀ v, v ∈ relSpace A b D Q ↔ (v ∈ lowSpan q n D ∧ Ideal.Quotient.mk (idealJ A b) v = 0))
    (s : Fin n → ZMod q) (hs : candidates A b = {s}) :
    readOut q I D (Bk q I D XC (dVl q I D + 1)) = List.ofFn (fun j => (s j).val) := by
  obtain ⟨h1, h2, h3, -⟩ := Bk_spec (q := q) hR hX (dVl q I D + 1)
  have hsp := BN_span hR hX hD hQ
  unfold readOut
  apply List.ext_getElem (by simp [hR.hn])
  intro j hj1 hj2
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [List.length_ofFn] at hj2
  exact findIdx_range q _ _ (fun c _ => outTest_iff hR hD _ h1 h2 h3 hsp h49 s hs ⟨j, hj2⟩ c)

end T17

end File_T17_Out

section File_T17_SemQ

/-! # The computed `Q` satisfies `Φ(Q_α) = x^α` -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

section Coord
variable {q : ℕ} [Fact q.Prime] {n : ℕ}

/-- Coordinates of an element of `R_d` along a list of exponent lists. -/
noncomputable def cRd (Ms : List (List ℕ)) (d : ℕ) : Rd (ZMod q) n q d →ₗ[ZMod q] (ℕ → ZMod q) where
  toFun f t := if h : t < Ms.length ∧ ∃ β : ReducedMono n q d, rl β = Ms.getD t [] then f h.2.choose else 0
  map_add' f g := by
    funext t; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by
    funext t; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]; split_ifs <;> simp

theorem cRd_idx {Ms : List (List ℕ)} {d : ℕ} (f : Rd (ZMod q) n q d) (β : ReducedMono n q d)
    (hβ : rl β ∈ Ms) : cRd Ms d f (idxOf Ms (rl β)) = f β := by
  have hlt := idxOf_lt hβ
  have hg := getD_idxOf hβ
  have hex : idxOf Ms (rl β) < Ms.length ∧ ∃ β' : ReducedMono n q d, rl β' = Ms.getD (idxOf Ms (rl β)) [] :=
    ⟨hlt, β, hg.symm⟩
  simp only [cRd, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hex]
  congr 1
  apply rl_inj
  rw [hex.2.choose_spec, hg]

theorem cRd_out {Ms : List (List ℕ)} {d : ℕ} (f : Rd (ZMod q) n q d) (t : ℕ) (ht : Ms.length ≤ t) :
    cRd Ms d f t = 0 := by
  simp only [cRd, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_neg (fun h => by omega)]

theorem cRd_at {Ms : List (List ℕ)} {d : ℕ} (f : Rd (ZMod q) n q d) (t : ℕ) (β : ReducedMono n q d)
    (ht : t < Ms.length) (hβ : rl β = Ms.getD t []) : cRd Ms d f t = f β := by
  have hex : t < Ms.length ∧ ∃ β' : ReducedMono n q d, rl β' = Ms.getD t [] := ⟨ht, β, hβ⟩
  simp only [cRd, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hex]
  congr 1
  apply rl_inj
  rw [hex.2.choose_spec, hβ]

theorem cRd_inj {Ms : List (List ℕ)} {d : ℕ} (hall : ∀ β : ReducedMono n q d, rl β ∈ Ms)
    {f g : Rd (ZMod q) n q d} (h : cRd Ms d f = cRd Ms d g) : f = g := by
  funext β
  rw [← cRd_idx f β (hall β), ← cRd_idx g β (hall β), h]

theorem cRd_single {Ms : List (List ℕ)} {d : ℕ} (hM : Ms.Nodup) (β : ReducedMono n q d)
    (hβ : rl β ∈ Ms) : cRd Ms d (Pi.single β 1) = Pi.single (idxOf Ms (rl β)) 1 := by
  funext t
  by_cases h : t < Ms.length ∧ ∃ β' : ReducedMono n q d, rl β' = Ms.getD t []
  · obtain ⟨ht, β', hβ'⟩ := h
    rw [cRd_at _ t β' ht hβ']
    by_cases he : β' = β
    · subst he
      have : t = idxOf Ms (rl β') := by rw [hβ', idxOf_getD hM t ht]
      rw [← this]; simp
    · have : t ≠ idxOf Ms (rl β) := by
        intro htt
        apply he
        apply rl_inj
        rw [hβ', htt, getD_idxOf hβ]
      simp [Pi.single_apply, he, this]
  · simp only [cRd, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h]
    have : t ≠ idxOf Ms (rl β) := by
      rintro rfl
      exact h ⟨idxOf_lt hβ, β, (getD_idxOf hβ).symm⟩
    simp [Pi.single_apply, this]

end Coord

section Phi
variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ}

/-- Payload → family `(Q_i)_i`. -/
noncomputable def Qof (K : ℕ) (M2 : List (List ℕ)) (d : ℕ) :
    (ℕ → ZMod q) →ₗ[ZMod q] (Fin m → Rd (ZMod q) n q d) where
  toFun u i β := u (i * K + idxOf M2 (rl β))
  map_add' u v := by funext i β; simp
  map_smul' c u := by funext i β; simp

theorem idx_split {K i i' t t' : ℕ} (ht : t < K) (ht' : t' < K) (h : i * K + t = i' * K + t') :
    i = i' ∧ t = t' := by
  have h1 := congrArg (· % K) h
  have h2 := congrArg (· / K) h
  have hK : 0 < K := by omega
  simp only [Nat.mul_comm i K, Nat.mul_comm i' K, Nat.mul_add_mod, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt ht'] at h1
  simp only [Nat.mul_comm i K, Nat.mul_comm i' K, Nat.mul_add_div hK, Nat.div_eq_of_lt ht,
    Nat.div_eq_of_lt ht'] at h2
  omega

theorem Qof_single {K : ℕ} {M2 : List (List ℕ)} {d : ℕ} (hK : M2.length = K)
    (hall : ∀ β : ReducedMono n q d, rl β ∈ M2) (i : Fin m) (β0 : ReducedMono n q d) :
    Qof (q := q) (m := m) (n := n) K M2 d (Pi.single (i * K + idxOf M2 (rl β0)) 1) =
      Pi.single i (Pi.single β0 1) := by
  funext i' β
  simp only [Qof, LinearMap.coe_mk, AddHom.coe_mk]
  have hrl := hall β
  have hβ0 := hall β0
  · have h1 := idxOf_lt hrl
    have h0 := idxOf_lt hβ0
    rw [hK] at h1 h0
    by_cases hiβ : i' = i ∧ β = β0
    · obtain ⟨rfl, rfl⟩ := hiβ; simp
    · have hne : (i' : ℕ) * K + idxOf M2 (rl β) ≠ i * K + idxOf M2 (rl β0) := by
        intro h
        obtain ⟨hi, ht⟩ := idx_split h1 h0 h
        apply hiβ
        refine ⟨Fin.ext hi, rl_inj ?_⟩
        rw [← getD_idxOf hrl, ← getD_idxOf hβ0, ht]
      rw [Pi.single_apply, if_neg hne]
      by_cases hi : i' = i
      · subst hi
        have : β ≠ β0 := fun h => hiβ ⟨rfl, h⟩
        simp [this]
      · simp [Pi.single_apply, hi]

theorem toPoly_single {d : ℕ} (β : ReducedMono n q d) :
    Rd.toPoly (ZMod q) n q d (Pi.single β 1) = monomial β.toFinsupp 1 := by
  simp only [Rd.toPoly, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval]
  rw [Finset.sum_eq_single β]
  · simp
  · intro β' _ h; simp [Pi.single_apply, h]
  · simp

theorem Phi_single (A : Matrix (Fin n) (Fin m) (ZMod q)) (D : ℕ) (i : Fin m)
    (β0 : ReducedMono n q (D - 2)) (α : ReducedMono n q D) :
    Phi (ZMod q) q (cols A) D (Pi.single i (Pi.single β0 1)) α =
      (linForm (cols A i) ^ 2 * monomial β0.toFinsupp (1 : ZMod q)).coeff α.toFinsupp := by
  simp only [Phi, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval]
  rw [Finset.sum_eq_single i]
  · simp [mulMap, Rd.ofPoly, toPoly_single]
  · intro i' _ h; simp [Pi.single_apply, h]
  · simp

end Phi

/-- The `Q` computed by the algorithm. -/
noncomputable def Qalg (q : ℕ) [Fact q.Prime] [NeZero q] (n m : ℕ) (I : Inst) (D : ℕ) (BP : List Row) :
    ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2) :=
  fun α => Qof (M2l q I D).length (M2l q I D) (D - 2) (toV q (Qvec q I D BP (idxOf (MDl q I D) (rl α))))

section Alg
variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
  {b : Fin m → ZMod q} {D : ℕ} {I : Inst}

variable (A I D) in
/-- The payload map: payload ↦ coordinates of `Φ(Q)`. -/
noncomputable def Lpay : (ℕ → ZMod q) →ₗ[ZMod q] (ℕ → ZMod q) :=
  (cRd (n := n) (MDl q I D) D).comp ((Phi (ZMod q) q (cols A) D).comp
    (Qof (m := m) (M2l q I D).length (M2l q I D) (D - 2)))

theorem MDl_eq (hn : I.n = n) : MDl q I D = monosEq q n D := by unfold MDl; rw [hn]
theorem M2l_eq (hn : I.n = n) : M2l q I D = monosEq q n (D - 2) := by unfold M2l; rw [hn]

theorem rl_mem_MD (hn : I.n = n) (α : ReducedMono n q D) : rl α ∈ MDl q I D := by
  rw [MDl_eq hn]; exact rl_mem q_pos α
theorem rl_mem_M2 (hn : I.n = n) (α : ReducedMono n q (D - 2)) : rl α ∈ M2l q I D := by
  rw [M2l_eq hn]; exact rl_mem q_pos α

theorem toFinsupp_rmOf {d : ℕ} (α : List ℕ) (h : α ∈ monosEq q n d) :
    (rmOf q_pos α h).toFinsupp = monoOf n α := by
  rw [← monoOf_rl, rl_rmOf]

theorem lt_mul_of {i t K m' : ℕ} (hi : i < m') (ht : t < K) : i * K + t < m' * K := by
  have : (i + 1) * K ≤ m' * K := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, one_mul] at this
  omega

theorem toV_colPhi_out (MD : List (List ℕ)) (a β : List ℕ) (t : ℕ) (ht : MD.length ≤ t) :
    toV q (colPhi q MD a β) t = 0 := by
  simp only [toV]
  rw [List.getD_eq_default _ _ (by simp [colPhi]; omega)]; simp

theorem phiGens_ok (hR : Rep A b I) :
    ∀ xw ∈ phiGens q I D, xw.1.length = dDl q I D ∧ xw.2.length = El q I D ∧
      toV q xw.1 = Lpay A D I (toV q xw.2) := by
  intro xw hxw
  simp only [phiGens, List.mem_flatMap, List.mem_range, List.mem_map] at hxw
  obtain ⟨i, hi, t, ht, rfl⟩ := hxw
  refine ⟨by simp [colPhi, dDl], length_unitV _ _, ?_⟩
  rw [hR.hm] at hi
  have htm : (M2l q I D).getD t [] ∈ monosEq q n (D - 2) := by
    rw [← M2l_eq hR.hn, List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
  set β0 := rmOf q_pos _ htm
  have hrl0 : rl β0 = (M2l q I D).getD t [] := rl_rmOf _ _ _
  have hidx : idxOf (M2l q I D) (rl β0) = t := by
    rw [hrl0, idxOf_getD (by rw [M2l_eq hR.hn]; exact nodup_monosEq _ _) t ht]
  have hlt : i * (M2l q I D).length + t < El q I D := lt_mul_of (by rw [hR.hm]; exact hi) ht
  simp only
  rw [toV_unitV _ _ hlt, Lpay, LinearMap.comp_apply, LinearMap.comp_apply, ← hidx]
  rw [show i = ((⟨i, hi⟩ : Fin m) : ℕ) from rfl,
    Qof_single rfl (rl_mem_M2 hR.hn) ⟨i, hi⟩ β0, hidx]
  funext t'
  by_cases ht' : t' < (MDl q I D).length
  · have htm' : (MDl q I D).getD t' [] ∈ monosEq q n D := by
      rw [← MDl_eq hR.hn, List.getD_eq_getElem _ _ ht']; exact List.getElem_mem _
    rw [cRd_at _ t' (rmOf q_pos _ htm') ht' (rl_rmOf _ _ _), Phi_single, toFinsupp_rmOf,
      toFinsupp_rmOf, hR.hcol ⟨i, hi⟩]
    exact toV_colPhi A ⟨i, hi⟩ _ (fun α hα => by
        rw [MDl_eq hR.hn] at hα; exact ((mem_monosEq q_pos _ _ _).1 hα).1) _
      ((mem_monosEq q_pos _ _ _).1 htm).1 t' ht'
  · rw [cRd_out _ _ (by omega), toV_colPhi_out _ _ _ _ (by omega)]

theorem Bphi_spec (hR : Rep A b I) :
    Shape (dDl q I D) (El q I D) (Bphi q I D) ∧ Echelon (q := q) (Bphi q I D) ∧
      PayOK (Lpay A D I) (Bphi q I D) ∧
      Submodule.span (ZMod q) (vecs (q := q) (Bphi q I D)) =
        Submodule.span (ZMod q) {v | ∃ xw ∈ phiGens q I D, v = toV q xw.1} := by
  obtain ⟨h1, h2, h3, h4⟩ := insertAll_spec (Fact.out : q.Prime) (Lpay A D I) (phiGens q I D)
    (phiGens_ok (b := b) hR) [] (by intro r hr; simp at hr) trivial (by intro r hr; simp at hr)
  refine ⟨h1, h2, h3, ?_⟩
  rw [Bphi, h4]
  have : vecs (q := q) ([] : List Row) = ∅ := by ext; simp [vecs]
  rw [this, Submodule.span_empty, bot_sup_eq]

theorem Rd_decomp {d : ℕ} (Qs : Fin m → Rd (ZMod q) n q d) :
    Qs = ∑ i, ∑ β, Qs i β • Pi.single i (Pi.single β (1 : ZMod q)) := by
  funext i' β'
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single β'] <;> simp (config := { contextual := true })
  · intro i _ h; simp [Ne.symm h]
  · simp

theorem unit_mem_span (hR : Rep A b I) (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D))
    (t : ℕ) (ht : t < dDl q I D) :
    toV q (unitV (dDl q I D) t) ∈ Submodule.span (ZMod q) (vecs (q := q) (Bphi q I D)) := by
  rw [(Bphi_spec (D := D) hR).2.2.2]
  have htm : (MDl q I D).getD t [] ∈ monosEq q n D := by
    rw [← MDl_eq hR.hn, List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
  set α := rmOf q_pos _ htm
  have hidx : idxOf (MDl q I D) (rl α) = t := by
    rw [rl_rmOf, idxOf_getD (by rw [MDl_eq hR.hn]; exact nodup_monosEq _ _) t ht]
  obtain ⟨Qs, hQs⟩ := hsurj (Pi.single α 1)
  rw [toV_unitV _ _ ht, ← hidx, ← cRd_single (by rw [MDl_eq hR.hn]; exact nodup_monosEq _ _) α
    (rl_mem_MD hR.hn α), ← hQs, Rd_decomp Qs, map_sum, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_sum, map_sum]
  apply Submodule.sum_mem
  intro β _
  rw [map_smul, map_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hβm := rl_mem_M2 (D := D) hR.hn β
  have hiI : (i : ℕ) < I.m := by rw [hR.hm]; exact i.isLt
  refine ⟨_, List.mem_flatMap.2 ⟨i, List.mem_range.2 hiI, List.mem_map.2
    ⟨idxOf (M2l q I D) (rl β), List.mem_range.2 (idxOf_lt hβm), rfl⟩⟩, ?_⟩
  rw [(phiGens_ok (b := b) hR _ (List.mem_flatMap.2 ⟨i, List.mem_range.2 hiI, List.mem_map.2
    ⟨idxOf (M2l q I D) (rl β), List.mem_range.2 (idxOf_lt hβm), rfl⟩⟩)).2.2]
  simp only
  rw [toV_unitV _ _ (show _ < El q I D from lt_mul_of (by rw [hR.hm]; exact i.isLt) (idxOf_lt hβm)), Lpay,
    LinearMap.comp_apply, LinearMap.comp_apply, Qof_single rfl (rl_mem_M2 hR.hn) i β]

theorem cast_q_sub_one : (((q - 1 : ℕ) : ℕ) : ZMod q) = -1 := by
  rw [Nat.cast_sub (Fact.out : q.Prime).one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- If `Φ` is surjective, the algorithm's `Q` satisfies (30). -/
theorem Qalg_spec (hR : Rep A b I) (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D)) :
    ∀ α, Phi (ZMod q) q (cols A) D (Qalg q n m I D (Bphi q I D) α) = Pi.single α 1 := by
  intro α
  obtain ⟨h1, h2, h3, -⟩ := Bphi_spec (D := D) hR
  have hαm := rl_mem_MD (D := D) hR.hn α
  set t := idxOf (MDl q I D) (rl α)
  have ht : t < dDl q I D := idxOf_lt hαm
  have hx : (unitV (dDl q I D) t, zeroV (El q I D)).1.length = dDl q I D := length_unitV _ _
  have hw : (unitV (dDl q I D) t, zeroV (El q I D)).2.length = El q I D := length_zeroV _
  obtain ⟨-, hr2⟩ := reduce_spec (Lpay A D I) _ h1 h3 _ hx hw
  have hz := (mem_span_iff_reduce (Lpay A D I) _ h1 h2 h3 _ hx hw).1 (unit_mem_span hR hsurj t ht)
  rw [hz, toV_zeroV, map_zero, sub_zero, zero_sub] at hr2
  apply cRd_inj (Ms := MDl q I D) (rl_mem_MD hR.hn)
  rw [cRd_single (by rw [MDl_eq hR.hn]; exact nodup_monosEq _ _) α hαm]
  have : cRd (MDl q I D) D (Phi (ZMod q) q (cols A) D (Qalg q n m I D (Bphi q I D) α)) =
      Lpay A D I (toV q (Qvec q I D (Bphi q I D) t)) := rfl
  rw [this, Qvec, toV_smul, cast_q_sub_one, neg_one_smul, map_neg, hr2]
  exact toV_unitV _ _ ht

end Alg

end T17

end File_T17_SemQ

section File_T17_SemR

/-! # Semantics of reduction, `τ` on monomials and `coefRed` -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ}

theorem length_redM (l : List ℕ) : (redM q l).length = l.length := by simp [redM]

theorem monoOf_redM (l : List ℕ) (hl : l.length = n) : monoOf n (redM q l) = rIndex q (monoOf n l) := by
  ext k
  rw [rIndex_apply, monoOf_apply, monoOf_apply]
  unfold redM
  rw [List.getD_eq_getElem _ _ (by simp [hl]), List.getD_eq_getElem _ _ (by simp [hl])]
  simp [redE, redExp]

theorem redM_eq_iff (l δ : List ℕ) (hl : l.length = n) (hδ : δ.length = n) :
    redM q l = δ ↔ rIndex q (monoOf n l) = monoOf n δ := by
  rw [← monoOf_redM l hl]
  constructor
  · rintro rfl; rfl
  · intro h; exact monoOf_inj (by rw [length_redM, hl]) hδ h

theorem linForm_mul_mono (a : Fin n → ZMod q) (s : Fin n →₀ ℕ) :
    linForm a * monomial s (1 : ZMod q) = ∑ j, monomial (s + Finsupp.single j 1) (a j) := by
  unfold linForm
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [X, C_mul_monomial, monomial_mul, mul_one]
  congr 1; abel

theorem fPoly_expand (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (i : Fin m) :
    fPoly A b i = linForm (cols A i) ^ 2 + C (1 - 2 * b i) * linForm (cols A i) + C (b i * b i - b i) := by
  unfold fPoly
  simp only [map_sub, map_mul, map_one, map_ofNat]
  ring

theorem red_add (p p' : MvPolynomial (Fin n) (ZMod q)) : red q (p + p') = red q p + red q p' := by
  rw [← redL_apply, ← redL_apply, ← redL_apply, map_add]

theorem red_C_mul (c : ZMod q) (p : MvPolynomial (Fin n) (ZMod q)) : red q (C c * p) = c • red q p := by
  rw [C_mul', ← redL_apply, ← redL_apply, map_smul]

theorem red_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) (ZMod q)) :
    red q (∑ i ∈ s, f i) = ∑ i ∈ s, red q (f i) := by
  rw [← redL_apply, map_sum]; rfl

theorem sum_range_fin' {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ((List.range k).map f).sum = ∑ j : Fin k, f j := sum_range_fin k f

theorem coefRed_sem (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (i : Fin m) (bi : ℕ)
    (hbi : (bi : ZMod q) = b i) (β δ : List ℕ) (hβ : β.length = n) (hδ : δ.length = n)
    (hβq : ∀ e ∈ β, e < q) :
    ((coefRed q (colL A i) bi β δ : ℕ) : ZMod q) =
      (red q (fPoly A b i * monomial (monoOf n β) 1)).coeff (monoOf n δ) := by
  have hβr : rIndex q (monoOf n β) = monoOf n β := by
    apply rIndex_self
    intro k
    rw [monoOf_apply, List.getD_eq_getElem _ _ (by rw [hβ]; exact k.isLt)]
    exact hβq _ (List.getElem_mem _)
  rw [fPoly_expand, add_mul, add_mul, mul_assoc, red_add, red_add, red_C_mul, red_C_mul,
    linForm_sq_mul, linForm_mul_mono]
  simp only [red_sum, red_monomial, coeff_add, coeff_smul, coeff_sum, coeff_monomial, smul_eq_mul]
  unfold coefRed
  simp only [colL_length]
  rw [cast_addq, cast_addq, cast_mulq, cast_sumq, cast_sumq, ← add_assoc]
  congr 1
  · congr 1
    · rw [List.map_flatMap, list_flatMap_sum, sum_range_fin]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [List.map_map, sum_range_fin]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Function.comp_apply]
      have hb : monoOf n (bump (bump β j) k) = monoOf n β + Finsupp.single j 1 + Finsupp.single k 1 := by
        rw [monoOf_bump _ (by rw [length_bump, hβ]) k, monoOf_bump _ hβ j]
      have hiff := redM_eq_iff (q := q) (bump (bump β j) k) δ (by rw [length_bump, length_bump, hβ]) hδ
      rw [hb] at hiff
      by_cases h : rIndex q (monoOf n β + Finsupp.single j 1 + Finsupp.single k 1) = monoOf n δ
      · rw [if_pos (beq_iff_eq.2 (hiff.2 h)), if_pos h, cast_mulq, colL_getD, colL_getD]
      · rw [if_neg (fun h' => h (hiff.1 (beq_iff_eq.1 h'))), if_neg h]; simp
    · congr 1
      · rw [cast_addq, cast_mulq, cast_negq, hbi]; simp; ring
      · rw [List.map_map, sum_range_fin]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Function.comp_apply]
        have hiff := redM_eq_iff (q := q) (bump β j) δ (by rw [length_bump, hβ]) hδ
        rw [monoOf_bump _ hβ j] at hiff
        by_cases h : rIndex q (monoOf n β + Finsupp.single j 1) = monoOf n δ
        · rw [if_pos (beq_iff_eq.2 (hiff.2 h)), if_pos h, colL_getD]; rfl
        · rw [if_neg (fun h' => h (hiff.1 (beq_iff_eq.1 h'))), if_neg h]; simp
  · rw [hβr]
    by_cases h : monoOf n β = monoOf n δ
    · rw [if_pos (beq_iff_eq.2 (monoOf_inj hβ hδ h)), if_pos h, cast_addq, cast_mulq, cast_negq, hbi]; ring
    · rw [if_neg (fun h' => h (by rw [beq_iff_eq.1 h'])), if_neg h]; simp

end T17

end File_T17_SemR

section File_T17_SemX

/-! # Semantics of the remainders and of the columns of `X_j` -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
  {b : Fin m → ZMod q} {D : ℕ} {I : Inst}

theorem tau_monomial (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) (s : Fin n →₀ ℕ) :
    tau A b D Q (monomial s 1) =
      if ∑ j, s j < D then monomial s 1
      else if h : (∀ j, s j < q) ∧ ∑ j, s j = D then remainder A b D Q ⟨fun j => ⟨s j, h.1 j⟩, h.2⟩
      else 0 := by
  unfold tau
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl]
  split_ifs <;> simp

theorem sum_reindex {R : Type*} [AddCommMonoid R] {d : ℕ} (Ms : List (List ℕ)) (hM : Ms.Nodup)
    (hall : ∀ β : ReducedMono n q d, rl β ∈ Ms)
    (hmem : ∀ α ∈ Ms, ∃ β : ReducedMono n q d, rl β = α) (g : ℕ → List ℕ → R) :
    ∑ tt ∈ Finset.range Ms.length, g tt (Ms.getD tt []) =
      ∑ β : ReducedMono n q d, g (idxOf Ms (rl β)) (rl β) := by
  have hget : ∀ tt, tt < Ms.length → Ms.getD tt [] ∈ Ms := fun tt h => by
    rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem _
  refine Finset.sum_bij' (fun tt htt => (hmem _ (hget tt (Finset.mem_range.1 htt))).choose)
    (fun β _ => idxOf Ms (rl β)) (fun _ _ => Finset.mem_univ _)
    (fun β _ => Finset.mem_range.2 (idxOf_lt (hall β))) ?_ ?_ ?_
  · intro tt htt
    rw [(hmem _ (hget tt (Finset.mem_range.1 htt))).choose_spec, idxOf_getD hM _ (Finset.mem_range.1 htt)]
  · intro β _
    apply rl_inj
    rw [(hmem _ (hget _ (idxOf_lt (hall β)))).choose_spec, getD_idxOf (hall β)]
  · intro tt htt
    rw [(hmem _ (hget tt (Finset.mem_range.1 htt))).choose_spec, idxOf_getD hM _ (Finset.mem_range.1 htt)]

theorem mem_MV_iff (hn : I.n = n) (γ : List ℕ) :
    γ ∈ MVl q I D ↔ γ.length = n ∧ (∀ e ∈ γ, e < q) ∧ γ.sum < D := by
  unfold MVl; rw [mem_monosLt q_pos, hn]

theorem low_support_MV (hn : I.n = n) (p : MvPolynomial (Fin n) (ZMod q)) (hp : p ∈ lowSpan q n D) :
    ∀ s ∈ p.support, ∃ γ ∈ MVl q I D, monoOf n γ = s := by
  intro s hs
  obtain ⟨hsq, hsD⟩ := (low_mem D p).1 hp s hs
  refine ⟨List.ofFn (fun j => s j), ?_, monoOf_ofFn s⟩
  rw [mem_MV_iff hn]
  refine ⟨by simp, ?_, by rw [List.sum_ofFn]; exact hsD⟩
  intro e he; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he; exact hsq j

theorem sum_monoOf (γ : List ℕ) (hγ : γ.length = n) : ∑ j, monoOf n γ j = γ.sum := by
  simp only [monoOf_apply]; exact sum_getD_fin γ hγ

theorem toFinsupp_sum {d : ℕ} (α : ReducedMono n q d) : ∑ j, α.toFinsupp j = d := by
  rw [← monoOf_rl, sum_monoOf _ (rl_length α)]
  have := α.2
  simpa [rl, List.sum_ofFn] using this

theorem toPoly_eq {d : ℕ} (f : Rd (ZMod q) n q d) :
    Rd.toPoly (ZMod q) n q d f = ∑ β, C (f β) * monomial β.toFinsupp 1 := by
  simp only [Rd.toPoly, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_proj, Function.eval, C_mul_monomial, mul_one]

theorem rl_lt {d : ℕ} (β : ReducedMono n q d) : ∀ e ∈ rl β, e < q := by
  intro e he; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he; exact (β.1 j).isLt

theorem getD_map_lt {α β : Type*} (L : List α) (f : α → β) (t : ℕ) (ht : t < L.length) (d : β) (d' : α) :
    (L.map f).getD t d = f (L.getD t d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using ht), List.getD_eq_getElem _ _ ht, List.getElem_map]

/-- The computed coordinates of `r_α`. -/
theorem rvec_sem (hR : Rep A b I) (hD : 2 ≤ D) (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D))
    (α : ReducedMono n q D) :
    pv n (MVl q I D) (toV q (rvec q I D (Qvec q I D (Bphi q I D) (idxOf (MDl q I D) (rl α))))) =
      remainder A b D (Qalg q n m I D (Bphi q I D)) α := by
  have hQ := Qalg_spec (D := D) hR hsurj
  have hlow := remainder_low A b D hD _ hQ α
  rw [← pv_coordsOf (good_MV hR.hn) _ (low_support_MV hR.hn _ hlow)]
  congr 1
  funext t
  set Qα := Qvec q I D (Bphi q I D) (idxOf (MDl q I D) (rl α))
  by_cases ht : t < dVl q I D
  · simp only [coordsOf, if_pos (show t < (MVl q I D).length from ht)]
    have hδm : (MVl q I D).getD t [] ∈ MVl q I D := by
      rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
    set δ := (MVl q I D).getD t []
    obtain ⟨hδl, -, hδs⟩ := (mem_MV_iff hR.hn δ).1 hδm
    have hne : α.toFinsupp ≠ monoOf n δ := by
      intro h
      have h1 := toFinsupp_sum α
      rw [h, sum_monoOf _ hδl] at h1
      omega
    unfold remainder
    rw [coeff_sub, coeff_monomial, if_neg hne, zero_sub, red_sum, coeff_sum]
    simp only [toV, rvec]
    rw [getD_map_lt _ _ _ ht 0 []]
    rw [cast_negq, cast_sumq, List.map_flatMap, list_flatMap_sum, hR.hm, sum_range_fin]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have hM2n : (M2l q I D).Nodup := by rw [M2l_eq hR.hn]; exact nodup_monosEq _ _
    have hmem : ∀ γ ∈ M2l q I D, ∃ β : ReducedMono n q (D - 2), rl β = γ := by
      intro γ hγ
      rw [M2l_eq hR.hn] at hγ
      exact ⟨rmOf q_pos γ hγ, rl_rmOf _ _ _⟩
    have hre := sum_reindex (M2l q I D) hM2n (rl_mem_M2 hR.hn) hmem
      (fun tt γ => ((mulq q (Qα.getD (↑i * (M2l q I D).length + tt) 0)
        (coefRed q (I.cols.getD ↑i []) (I.b.getD (↑i) 0) γ δ) : ℕ) : ZMod q))
    rw [List.map_map, list_sum_range]
    refine Eq.trans hre ?_
    rw [toPoly_eq, Finset.mul_sum, red_sum, coeff_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [mul_left_comm, red_C_mul, coeff_smul, smul_eq_mul, cast_mulq, hR.hcol i,
      coefRed_sem A b i _ (hR.hb i) (rl β) δ (rl_length β) hδl (rl_lt β), monoOf_rl]
    rfl
  · simp only [coordsOf, if_neg (show ¬ t < (MVl q I D).length from ht)]
    have : (rvec q I D Qα).length ≤ t := by simp [rvec]; exact Nat.le_of_not_lt ht
    simp only [toV]
    rw [List.getD_eq_default _ _ this]; simp

theorem Xop_monomial (Q : ReducedMono n q D → Fin m → Rd (ZMod q) n q (D - 2)) (j : Fin n)
    (s : Fin n →₀ ℕ) : Xop A b D Q j (monomial s 1) = tau A b D Q (monomial (rIndex q (s + Finsupp.single j 1)) 1) := by
  unfold Xop
  rw [X, monomial_mul, one_mul, add_comm, red_monomial]

theorem length_Xcol (RV : List (List ℕ)) (hRV : ∀ r ∈ RV, r.length = dVl q I D) (j : ℕ) (β : List ℕ) :
    (Xcol q I D RV j β).length = dVl q I D := by
  unfold Xcol
  simp only
  split_ifs
  · exact length_unitV _ _
  · rcases Nat.lt_or_ge (idxOf (MDl q I D) (redM q (bump β j))) RV.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hRV _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ h]; exact length_zeroV _

theorem length_rvecs (BP : List Row) : ∀ r ∈ rvecs q I D BP, r.length = dVl q I D := by
  intro r hr
  simp only [rvecs, List.mem_map] at hr
  obtain ⟨t, -, rfl⟩ := hr
  simp [rvec, dVl]

/-- Columns of `X_j`. -/
theorem Xcol_sem (hR : Rep A b I) (hD : 2 ≤ D) (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D))
    (j : Fin n) (t : ℕ) (ht : t < dVl q I D) :
    pv n (MVl q I D) (toV q (Xcol q I D (rvecs q I D (Bphi q I D)) j ((MVl q I D).getD t []))) =
      Xop A b D (Qalg q n m I D (Bphi q I D)) j (monomial (monoOf n ((MVl q I D).getD t [])) 1) := by
  have hβm : (MVl q I D).getD t [] ∈ MVl q I D := by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem _
  set β := (MVl q I D).getD t []
  obtain ⟨hβl, hβq, hβs⟩ := (mem_MV_iff hR.hn β).1 hβm
  set γ := redM q (bump β j) with hγ
  have hγl : γ.length = n := by rw [hγ, length_redM, length_bump, hβl]
  have hmγ : monoOf n γ = rIndex q (monoOf n β + Finsupp.single j 1) := by
    rw [hγ, monoOf_redM _ (by rw [length_bump, hβl]), monoOf_bump _ hβl]
  rw [Xop_monomial, ← hmγ, tau_monomial]
  have hred : ∀ k, monoOf n γ k < q := by rw [hmγ]; exact rIndex_reduced two_le_q _
  unfold Xcol
  simp only [← hγ]
  by_cases hlt : γ.sum < D
  · rw [if_pos hlt, if_pos (show ∑ k, monoOf n γ k < D by rw [sum_monoOf _ hγl]; exact hlt)]
    have hγm : γ ∈ MVl q I D := by
      rw [mem_MV_iff hR.hn]
      refine ⟨hγl, fun e he => ?_, hlt⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
      have := hred ⟨k, by omega⟩
      rwa [monoOf_apply, List.getD_eq_getElem _ _ hk] at this
    rw [toV_unitV _ _ (show idxOf (MVl q I D) γ < dVl q I D from idxOf_lt hγm),
      pv_single _ (idxOf_lt hγm), getD_idxOf hγm]
  · rw [if_neg hlt, if_neg (show ¬ ∑ k, monoOf n γ k < D by rw [sum_monoOf _ hγl]; exact hlt)]
    have hle : γ.sum ≤ D := by
      have h1 : ∑ k, monoOf n γ k ≤ ∑ k, ((monoOf n β + Finsupp.single j 1 : Fin n →₀ ℕ) k) := by
        rw [hmγ]; exact Finset.sum_le_sum fun k _ => rIndex_le _ k
      rw [sum_monoOf _ hγl] at h1
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, Finsupp.single_apply] at h1
      rw [sum_monoOf _ hβl] at h1
      simp at h1
      omega
    have hD' : γ.sum = D := by omega
    have hcond : (∀ k, monoOf n γ k < q) ∧ ∑ k, monoOf n γ k = D := ⟨hred, by rw [sum_monoOf _ hγl]; exact hD'⟩
    rw [dif_pos hcond]
    set α : ReducedMono n q D := ⟨fun k => ⟨monoOf n γ k, hred k⟩, hcond.2⟩
    have hrlα : rl α = γ := by
      apply List.ext_getElem (by rw [rl_length, hγl])
      intro k h1 h2
      simp only [rl, List.getElem_ofFn]
      show monoOf n γ ⟨k, _⟩ = _
      rw [monoOf_apply, List.getD_eq_getElem _ _ h2]
    have hγD : γ ∈ MDl q I D := by rw [← hrlα]; exact rl_mem_MD hR.hn α
    have hix : idxOf (MDl q I D) γ < (rvecs q I D (Bphi q I D)).length := by
      simp only [rvecs, List.length_map, List.length_range]; exact idxOf_lt hγD
    unfold rvecs
    rw [getD_map_lt _ _ _ (show idxOf (MDl q I D) γ < (List.range (dDl q I D)).length by
      rw [List.length_range]; exact idxOf_lt hγD) _ 0, List.getD_eq_getElem _ _ (by
      rw [List.length_range]; exact idxOf_lt hγD), List.getElem_range, ← hrlα]
    exact rvec_sem hR hD hsurj α

theorem pv_eq_smul_sum (Ms : List (List ℕ)) (f : ℕ → ZMod q) :
    pv n Ms f = ∑ t ∈ Finset.range Ms.length, f t • monomial (monoOf n (Ms.getD t [])) (1 : ZMod q) := by
  rw [pv_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_monomial, smul_eq_mul, mul_one]

/-- The list operators `X_j` implement `Xop` for the computed `Q`. -/
theorem xsem_alg (hR : Rep A b I) (hD : 2 ≤ D) (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D)) :
    XSem A b D (Qalg q n m I D (Bphi q I D)) I (Xcols q I D (rvecs q I D (Bphi q I D))) := by
  intro j v hv
  have hj : (j : ℕ) < I.n := by rw [hR.hn]; exact j.isLt
  have hXC : (Xcols q I D (rvecs q I D (Bphi q I D))).getD j [] =
      (MVl q I D).map (Xcol q I D (rvecs q I D (Bphi q I D)) j) := by
    unfold Xcols
    rw [getD_map_lt _ _ _ (by rw [List.length_range]; exact hj) _ 0, List.getD_eq_getElem _ _
      (by rw [List.length_range]; exact hj), List.getElem_range]
  unfold Xl
  rw [hXC, toV_matVec _ _ _ (by
    intro c hc
    obtain ⟨β, -, rfl⟩ := List.mem_map.1 hc
    rw [length_Xcol _ (length_rvecs _)])]
  rw [map_sum, pv_eq_smul_sum (MVl q I D) (toV q v), ← XL_apply, map_sum, List.length_map]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_range] at ht
  rw [map_smul, map_smul, XL_apply, getD_map_lt _ _ _ ht _ [], Xcol_sem hR hD hsurj j t ht]

end T17

end File_T17_SemX

section File_T17_Correct

/-! # Correctness of the main decoder -/

namespace T17

open MvPolynomial F3SubsetSum Prop49Proof

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
  {b : Fin m → ZMod q} {D : ℕ} {I : Inst}

/-- **Main decoder correctness**: if `Φ_{m,D}` is surjective and the candidate is unique, then
`mainDec` outputs the secret. -/
theorem mainDec_correct (hq3 : 3 ≤ q) (hR : Rep A b I) (hD : 2 ≤ D)
    (hsurj : Function.Surjective (Phi (ZMod q) q (cols A) D))
    (s : Fin n → ZMod q) (hs : candidates A b = {s}) :
    mainDec q I D = List.ofFn (fun j => (s j).val) := by
  have hQ := Qalg_spec (D := D) hR hsurj
  have h49 := (proposition_4_9 q hq3 A b D hD hsurj _ hQ).2
  exact readOut_correct hR (xsem_alg hR hD hsurj) hD hQ h49 s hs

end T17

end File_T17_Correct

section File_T17_Brute

/-! # Instances from matrices; correctness of brute force -/

namespace T17

open MvPolynomial F3SubsetSum

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m : ℕ}

/-- The list instance of `(A, b)`. -/
def instOf (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) : Inst :=
  ⟨n, m, List.ofFn (fun i => colL A i), List.ofFn (fun i => (b i).val)⟩

theorem rep_instOf (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) : Rep A b (instOf A b) where
  hn := rfl
  hm := rfl
  hcol i := by
    simp only [instOf]
    rw [List.getD_eq_getElem _ _ (by simp)]; simp
  hb i := by
    simp only [instOf]
    rw [List.getD_eq_getElem _ _ (by simp)]; simp

theorem mem_allVecs (k : ℕ) (u : List ℕ) : u ∈ allVecs q k ↔ u.length = k ∧ ∀ e ∈ u, e < q := by
  induction k generalizing u with
  | zero =>
    simp only [allVecs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | succ k ih =>
    simp only [allVecs, List.mem_flatMap, List.mem_range, List.mem_map, ih]
    constructor
    · rintro ⟨e, he, t, ⟨ht, htq⟩, rfl⟩
      refine ⟨by simp [ht], ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact he
      · exact htq x hx
    · rintro ⟨hl, hq⟩
      cases u with
      | nil => simp at hl
      | cons e t =>
        exact ⟨e, hq e List.mem_cons_self, t, ⟨by simpa using hl, fun x hx => hq x (List.mem_cons_of_mem _ hx)⟩, rfl⟩

theorem length_allVecs (k : ℕ) : (allVecs q k).length = q ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [allVecs, List.length_flatMap, List.length_map, ih]
    rw [List.map_const', List.sum_replicate, List.length_range, smul_eq_mul, pow_succ, mul_comm]

/-- The vector of a list. -/
def vecOf (u : List ℕ) : Fin n → ZMod q := fun j => ((u.getD j 0 : ℕ) : ZMod q)

theorem addq_lt' (a b : ℕ) : addq q a b < q := Nat.mod_lt _ (Fact.out : q.Prime).pos

theorem small_iff (r : ℕ) (hr : r < q) : (r == 0 || r == 1) = true ↔ ((r : ZMod q) = 0 ∨ (r : ZMod q) = 1) := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  simp only [Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · left
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hr, ZMod.val_zero] at this
    · right
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hr, ZMod.val_one] at this

theorem eval_linForm (a : Fin n → ZMod q) (v : Fin n → ZMod q) : eval v (linForm a) = ∑ j, a j * v j := by
  simp [linForm]

theorem eval_fPoly_eq_zero (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (v : Fin n → ZMod q)
    (i : Fin m) : eval v (fPoly A b i) = 0 ↔ (b i - eval v (linForm (cols A i)) = 0 ∨
      b i - eval v (linForm (cols A i)) = 1) := by
  simp only [fPoly, map_mul, map_sub, map_add, eval_C, map_one, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left; rw [← neg_sub, h, neg_zero]
    · right; linear_combination -h
  · rintro (h | h)
    · left; linear_combination -h
    · right; linear_combination -h

theorem consistent_iff (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (u : List ℕ) :
    consistent q (instOf A b) u = true ↔ vecOf u ∈ candidates A b := by
  simp only [consistent, List.all_eq_true, List.mem_range, candidates, Set.mem_setOf_eq]
  have key : ∀ i : Fin m, (((addq q ((instOf A b).b.getD i 0) (negq q (sumq q ((List.range (instOf A b).n).map
      (fun j => mulq q (((instOf A b).cols.getD i []).getD j 0) (u.getD j 0)))))) : ℕ) : ZMod q) =
      b i - eval (vecOf u) (linForm (cols A i)) := by
    intro i
    rw [cast_addq, cast_negq, cast_sumq, (rep_instOf A b).hb i, eval_linForm, List.map_map,
      (rep_instOf A b).hcol i, show (instOf A b).n = n from rfl, sum_range_fin, sub_eq_add_neg]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, cast_mulq, colL_getD, cols, vecOf]
  constructor
  · intro h i
    have hi := h i i.isLt
    rw [small_iff _ (addq_lt' _ _), key i] at hi
    exact (eval_fPoly_eq_zero A b _ i).2 hi
  · intro h i hi
    rw [small_iff _ (addq_lt' _ _), key ⟨i, hi⟩]
    exact (eval_fPoly_eq_zero A b _ ⟨i, hi⟩).1 (h ⟨i, hi⟩)

theorem eq_ofFn_of_vecOf (u : List ℕ) (hl : u.length = n) (hq : ∀ e ∈ u, e < q) (s : Fin n → ZMod q)
    (h : vecOf u = s) : u = List.ofFn (fun j => (s j).val) := by
  apply List.ext_getElem (by simp [hl])
  intro j h1 h2
  subst h
  rw [List.getElem_ofFn]
  simp only [vecOf]
  rw [List.getD_eq_getElem _ _ h1, ZMod.val_natCast, Nat.mod_eq_of_lt (hq _ (List.getElem_mem _))]

theorem vecOf_ofFn (s : Fin n → ZMod q) : vecOf (n := n) (List.ofFn (fun j => (s j).val)) = s := by
  funext j
  simp only [vecOf]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Brute force returns the unique candidate. -/
theorem bruteDec_correct (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) (s : Fin n → ZMod q)
    (hs : candidates A b = {s}) : bruteDec q (instOf A b) = List.ofFn (fun j => (s j).val) := by
  have hmem : List.ofFn (fun j => (s j).val) ∈ allVecs q n := by
    rw [mem_allVecs]
    refine ⟨by simp, fun e he => ?_⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 he
    exact ZMod.val_lt _
  have hcons : consistent q (instOf A b) (List.ofFn (fun j => (s j).val)) = true := by
    rw [consistent_iff, vecOf_ofFn, hs]; rfl
  unfold bruteDec
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨_, hmem, hcons⟩)
  rw [show (instOf A b).n = n from rfl, hu, Option.getD_some]
  have hum := List.mem_of_find?_eq_some hu
  have huc := List.find?_some hu
  rw [mem_allVecs] at hum
  rw [consistent_iff, hs] at huc
  exact eq_ofFn_of_vecOf u hum.1 hum.2 s huc

end T17

end File_T17_Brute

section File_T17M_DecList

/-! # The full list decoder (instance + fuel) -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

/-- Parsed instance: `n, m, range n, range m, columns, b`. -/
abbrev Pin := ℕ × ℕ × List ℕ × List ℕ × List (List ℕ) × List ℕ

variable (q : ℕ)

def vecStep (fl K : List ℕ) (V : List (List ℕ)) : List (List ℕ) :=
  ((List.range q).flatMap (fun e => V.map (fun t => normM q K (e :: t)))).take fl.length

def vecsF (fl K L : List ℕ) : List (List ℕ) := L.foldl (fun V _ => vecStep q fl K V) [[]]

def consistentC (x : Pin) (u : List ℕ) : Bool :=
  x.2.2.2.1.all (fun i =>
    let r := addq q (x.2.2.2.2.2.getD i 0) (negq q (sumq q (x.2.2.1.map
      (fun j => mulq q ((x.2.2.2.2.1.getD i []).getD j 0) (u.getD j 0)))))
    r == 0 || r == 1)

def bruteC (x : Pin) (fl : List ℕ) : List ℕ :=
  let V := vecsF q fl x.2.2.1 x.2.2.1
  let i := V.findIdx (consistentC q x)
  if i < V.length then V.getD i [] else zeroVL x.2.2.1

def degD (n m : ℕ) : ℕ := max 500 ((500 * n * n + m - 1) / m)

def bigR (nR : List ℕ) : List ℕ := nR.flatMap (fun _ => List.range 500) ++ List.range 501

/-- The context built with fuel. -/
def ctxF (x : Pin) (fl : List ℕ) : Ctx :=
  let D := degD x.1 x.2.1
  let DR := (List.range (bigR x.2.2.1).length).take (D + 1)
  let T := tabK q fl x.2.2.1 DR x.2.2.1
  let M2 := T.getD (D - 2) []
  (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2, D, (DR.take D).flatMap (fun d => T.getD d []),
    T.getD D [], M2, List.range (x.2.2.2.1.flatMap (fun _ => M2)).length)

def decL (N0 : ℕ) (x : Pin) (fl : List ℕ) : List ℕ :=
  if x.1 < N0 || x.2.1 < 500 * x.1 then bruteC q x fl else mainDecC q (ctxF q x fl)

/-- The parsed form of an instance. -/
def pinOf (I : Inst) : Pin := (I.n, I.m, List.range I.n, List.range I.m, I.cols, I.b)

theorem vecsF_eq [Fact q.Prime] [NeZero q] (hq : 0 < q) (fl K : List ℕ) (k : ℕ) (hK : k ≤ K.length) (hF : q ^ k ≤ fl.length) :
    vecsF q fl K (List.range k) = allVecs q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hF' : q ^ k ≤ fl.length := (Nat.pow_le_pow_right hq (Nat.le_succ k)).trans hF
    unfold vecsF at ih ⊢
    rw [List.range_succ (n := k), List.foldl_append, ih (by omega) hF']
    simp only [List.foldl_cons, List.foldl_nil, vecStep]
    have hnorm : ∀ e ∈ List.range q, (allVecs q k).map (fun t => normM q K (e :: t)) =
        (allVecs q k).map (fun t => e :: t) := by
      intro e he
      apply List.map_congr_left
      intro t ht
      obtain ⟨hl, hlt⟩ := (mem_allVecs (q := q) k t).1 ht
      apply normM_id
      · simp [hl]; omega
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_range.1 he
        · exact hlt x hx
    rw [List.flatMap_congr hnorm, List.take_of_length_le]
    · rfl
    · have := length_allVecs (q := q) (k + 1)
      simp only [allVecs] at this
      omega

theorem find_getD_eq {β : Type} [Inhabited β] (l : List β) (p : β → Bool) (d : β) :
    (l.find? p).getD d = if l.findIdx p < l.length then l.getD (l.findIdx p) default else d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.find?_cons, List.findIdx_cons, List.length_cons]
    cases h : p a
    · simp only [cond_false, Nat.add_lt_add_iff_right]
      rw [ih]
      split_ifs <;> simp
    · simp

theorem bruteC_eq [Fact q.Prime] [NeZero q] (I : Inst) (fl : List ℕ) (hF : q ^ I.n ≤ fl.length) :
    bruteC q (pinOf I) fl = bruteDec q I := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hv : vecsF q fl (List.range I.n) (List.range I.n) = allVecs q I.n :=
    vecsF_eq q hq fl _ _ (by simp) hF
  unfold bruteC bruteDec
  simp only [pinOf, hv]
  rw [find_getD_eq, zeroVL_range]
  rfl

theorem degD_le (n m : ℕ) (hm : n ≤ m) : degD n m + 1 ≤ (bigR (List.range n)).length := by
  unfold degD bigR
  simp only [List.length_append, List.length_flatMap, List.length_range, List.map_const', List.sum_replicate,
    smul_eq_mul]
  have : (500 * n * n + m - 1) / m ≤ 500 * n + 1 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · apply Nat.div_le_of_le_mul
      have h1 := Nat.mul_le_mul_left (500 * n) hm
      have h2 : m * (500 * n + 1) = 500 * n * m + m := by ring
      rw [h2]
      omega
  omega

theorem ctxF_eq [Fact q.Prime] (I : Inst) (fl : List ℕ) (hm : I.n ≤ I.m)
    (hF : ∀ k ≤ I.n, ∀ d ≤ degD I.n I.m, (monosEq q k d).length ≤ fl.length) :
    ctxF q (pinOf I) fl = ctxOf q I (degD I.n I.m) := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  set D := degD I.n I.m
  have hDR : (List.range (bigR (List.range I.n)).length).take (D + 1) = List.range (D + 1) := by
    rw [List.take_range]; congr 1; have := degD_le I.n I.m hm; omega
  have hT : tabK q fl (List.range I.n) (List.range (D + 1)) (List.range I.n) =
      (List.range (D + 1)).map (fun d => monosEq q I.n d) :=
    tabK_eq q hq fl (List.range I.n) D I.n (by simp) hF
  have hget : ∀ d ≤ D, ((List.range (D + 1)).map (fun d => monosEq q I.n d)).getD d [] = monosEq q I.n d := by
    intro d hd
    rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  unfold ctxF ctxOf pinOf
  simp only
  rw [hDR, hT, hget D le_rfl, hget (D - 2) (by omega)]
  have hMV : ((List.range (D + 1)).take D).flatMap
      (fun d => ((List.range (D + 1)).map (fun d => monosEq q I.n d)).getD d []) = monosLt q I.n D := by
    rw [List.take_range, min_eq_left (by omega)]
    unfold monosLt
    apply List.flatMap_congr
    intro d hd
    exact hget d (by rw [List.mem_range] at hd; omega)
  rw [hMV]
  simp [List.length_flatMap, List.map_const', List.sum_replicate, D]

theorem decL_eq [Fact q.Prime] (N0 : ℕ) (I : Inst) (fl : List ℕ) :
    decL q N0 (pinOf I) fl = if I.n < N0 || I.m < 500 * I.n then bruteC q (pinOf I) fl
      else mainDecC q (ctxF q (pinOf I) fl) := rfl

end T17M

end File_T17M_DecList

section File_T17M_DecPoly

/-! # `Poly` for the full list decoder -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ) [NeZero q]

theorem vecStep_size (fl K : List ℕ) (V : List (List ℕ)) :
    (enc (vecStep q fl K V)).length ≤ fl.length * (2 * (K.length * (2 * q.size + 1)) + 1) := by
  unfold vecStep
  apply (EncodedList.length_bound _ _ _ _).trans
  · exact Nat.mul_le_mul_right _ (by simp)
  · intro t ht
    obtain ⟨e, -, ht'⟩ := List.mem_flatMap.1 (List.mem_of_mem_take ht)
    obtain ⟨t0, -, rfl⟩ := List.mem_map.1 ht'
    exact normM_size q K _

set_option maxHeartbeats 1000000 in
theorem Poly.vecsF_p : Poly (fun y : (List ℕ × List ℕ) × List ℕ => vecsF q y.1.1 y.1.2 y.2) := by
  unfold vecsF
  have hf : Poly (fun z : (((List ℕ × List ℕ) × List ℕ) × List (List ℕ)) × ℕ =>
      vecStep q z.1.1.1.1 z.1.1.1.2 z.1.2) := by unfold vecStep; fun_prop
  refine Poly.list_foldl (f := fun (y : (List ℕ × List ℕ) × List ℕ) (V : List (List ℕ)) (_ : ℕ) =>
      vecStep q y.1.1 y.1.2 V) (as := fun y => y.2) (b0 := fun _ => [[]]) hf (by fun_prop) (by fun_prop)
    (X * (2 * (X * Polynomial.C (2 * q.size + 1)) + 1)) (fun y V k => ?_)
  have h := vecStep_size q y.1.1 y.1.2 V
  set L := (enc y).length + (enc k).length
  have e1 := enc_pair _ _ y
  have e2 := enc_pair _ _ y.1
  have l1 := length_le_enc y.1.1
  have l2 := length_le_enc y.1.2
  have m1 : y.1.1.length * (2 * (y.1.2.length * (2 * q.size + 1)) + 1) ≤
      L * (2 * (L * (2 * q.size + 1)) + 1) := Nat.mul_le_mul (by omega)
        (by have := Nat.mul_le_mul_right (2 * q.size + 1) (show y.1.2.length ≤ L by omega); omega)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
  omega

@[fun_prop] theorem Poly.vecsF_comp {α : Type} [Coding α] {a b c : α → List ℕ} (ha : Poly a) (hb : Poly b)
    (hc : Poly c) : Poly (fun x => vecsF q (a x) (b x) (c x)) :=
  Automatic.Poly.comp (f := fun y : (List ℕ × List ℕ) × List ℕ => vecsF q y.1.1 y.1.2 y.2)
    (g := fun x => ((a x, b x), c x)) (Poly.vecsF_p q) (by fun_prop)

@[fun_prop] theorem Poly.tabK_comp {α : Type} [Coding α] {a b c d : α → List ℕ} (ha : Poly a) (hb : Poly b)
    (hc : Poly c) (hd : Poly d) : Poly (fun x => tabK q (a x) (b x) (c x) (d x)) :=
  Automatic.Poly.comp (f := fun y : (List ℕ × List ℕ × List ℕ) × List ℕ => tabK q y.1.1 y.1.2.1 y.1.2.2 y.2)
    (g := fun x => ((a x, b x, c x), d x)) (Poly.tabK_p q) (by fun_prop)

@[fun_prop] theorem Poly.mainDecC_comp {α : Type} [Coding α] {c : α → Ctx} (hc : Poly c) :
    Poly (fun x => mainDecC q (c x)) :=
  Automatic.Poly.comp (f := fun c : Ctx => mainDecC q c) (Poly.mainDecC_p q) hc

theorem Poly.bruteC_p : Poly (fun y : Pin × List ℕ => bruteC q y.1 y.2) := by
  unfold bruteC consistentC; dsimp only; fun_prop

theorem Poly.ctxF_p : Poly (fun y : Pin × List ℕ => ctxF q y.1 y.2) := by
  unfold ctxF degD bigR; dsimp only; fun_prop

theorem Poly.decL_p (N0 : ℕ) : Poly (fun y : Pin × List ℕ => decL q N0 y.1 y.2) := by
  unfold decL
  have h1 := Poly.bruteC_p q
  have h2 : Poly (fun y : Pin × List ℕ => mainDecC q (ctxF q y.1 y.2)) :=
    Poly.mainDecC_comp q (Poly.ctxF_p q)
  have h3 : Poly (fun y : Pin × List ℕ => (y.1.1 < N0 || y.1.2.1 < 500 * y.1.1)) := by fun_prop
  exact Automatic.Poly.ite h3 h1 h2

end T17M

end File_T17M_DecPoly

section File_T17M_Pipeline

/-! # The whole pipeline: parse, fuel, decode, print -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ)

def stepP (acc : ℕ × List ℕ) (bit : Bool) : ℕ × List ℕ :=
  if bit then (acc.1 + 1, acc.2) else (0, acc.2 ++ [acc.1])

def parseNums (w : List Bool) : List ℕ := (w.foldl stepP (0, [])).2

def pinOfBits (w : List Bool) : Pin :=
  let nums := parseNums w
  let n := nums.getD 0 0
  let m := nums.getD 1 0
  let ent := nums.drop 2
  let R := List.range w.length
  (n, m, R.take n, R.take m, (R.take m).map (fun i => (ent.drop (i * n)).take n), (ent.drop (m * n)).take m)

/-- The fuel exponent. -/
def tf (N0 n m : ℕ) : ℕ :=
  if n < N0 || m < 500 * n then n * q.size else degD n m * Nat.size (3 * (n + degD n m) / degD n m + 1)

def stage1 (N0 : ℕ) (w : List Bool) : Pin × (ℕ × List ℕ) :=
  (pinOfBits w, (tf q N0 (pinOfBits w).1 (pinOfBits w).2.1, [0]))

def finalList (N0 : ℕ) (x : Pin) (fl : List ℕ) : List ℕ := x.2.2.1.map (fun j => (decL q N0 x fl).getD j 0)

def outBits (l : List ℕ) : List Bool :=
  l.flatMap (fun x => ((List.range q).filter (fun e => decide (e < x % q))).map (fun _ => true) ++ [false])

def stage3 (N0 : ℕ) (y : Pin × List ℕ) : List Bool := outBits q (finalList q N0 y.1 y.2)

/-- The function computed by the machine on raw input bits. -/
def total (N0 : ℕ) (w : List Bool) : List Bool := stage3 q N0 (fres (stage1 q N0 w))

section Poly
variable [NeZero q]

@[fun_prop] theorem Poly.nat_size_comp {α : Type} [Coding α] {f : α → ℕ} (hf : Poly f) :
    Poly (fun x => (f x).size) := Automatic.Poly.comp (f := Nat.size) ⟨PolyProgram.natSize⟩ hf

theorem Poly.parseNums_p : Poly (fun w : List Bool => parseNums w) := by
  unfold parseNums
  refine Automatic.Poly.comp (f := Prod.snd) Automatic.Poly.snd ?_
  refine Poly.list_foldl (f := fun (_ : List Bool) (acc : ℕ × List ℕ) (bit : Bool) => stepP acc bit)
    (as := fun w => w) (b0 := fun _ => (0, [])) (by unfold stepP; fun_prop) (by fun_prop) (by fun_prop)
    (Polynomial.C 5) (fun w acc bit => ?_)
  unfold stepP
  split_ifs
  · simp only [enc_pair, enc_nat, eval_C]
    have := size_add acc.1 1
    have : (1 : ℕ).size = 1 := rfl
    omega
  · simp only [enc_pair, enc_nat, enc_list_append, enc_list_cons, eval_C, Nat.size_zero]
    have : (enc ([] : List ℕ)).length = 0 := rfl
    omega

theorem Poly.stage1_p (N0 : ℕ) : Poly (fun w : List Bool => stage1 q N0 w) := by
  have := Poly.parseNums_p
  unfold stage1 pinOfBits tf degD; dsimp only; fun_prop

theorem Poly.stage3_p (N0 : ℕ) : Poly (fun y : Pin × List ℕ => stage3 q N0 y) := by
  have h := Poly.decL_p q N0
  have h' : Poly (fun y : Pin × List ℕ => decL q N0 y.1 y.2) := h
  unfold stage3 finalList outBits
  fun_prop

end Poly

end T17M

end File_T17M_Pipeline

section File_T17M_TimeBound2

/-! # The running time is at most `(m/n)^(C⌈n²/m⌉)` -/

namespace T17M

open Polynomial

theorem two_pow_size_le (x : ℕ) (hx : 1 ≤ x) : 2 ^ x.size ≤ 2 * x := by
  have hs := Nat.size_pos.2 hx
  have h : x.size - 1 < x.size := by omega
  have := (Nat.lt_size).1 h
  calc 2 ^ x.size = 2 * 2 ^ (x.size - 1) := by rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * x := by omega

/-- `2^tf` is at most `max (2^(N0 q)) (r^(E3 h))`. -/
theorem fuel_rpow (q N0 n m : ℕ) (hq : 2 ≤ q) (κ : ℝ) (hκ : 1 < κ) (hn : 1 ≤ n) (hm : κ * n ≤ m) :
    ((2 ^ tf q N0 n m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N0 * q) +
      ((m : ℝ) / n) ^ (max (500 * q * Real.log 2 / Real.log κ) 1002 * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by nlinarith
  set r := (m : ℝ) / n with hr
  have hrκ : κ ≤ r := by rw [hr, le_div_iff₀ (by linarith)]; linarith
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set h := (⌈(n : ℝ) ^ 2 / m⌉ : ℝ) with hh
  have hhge : (n : ℝ) ^ 2 / m ≤ h := Int.le_ceil _
  have hnr : (n : ℝ) / r ≤ h := by
    rw [hr, div_div_eq_mul_div]; rw [sq] at hhge; exact hhge
  have hh1 : 1 ≤ h := by
    have : (0 : ℝ) < (n : ℝ) ^ 2 / m := by positivity
    have h0 : (0 : ℤ) < ⌈(n : ℝ) ^ 2 / m⌉ := Int.ceil_pos.2 this
    rw [hh]; exact_mod_cast h0
  have hlk : 0 < Real.log κ := Real.log_pos hκ
  have hlr : Real.log κ ≤ Real.log r := Real.log_le_log (by linarith) hrκ
  set E3 := max (500 * q * Real.log 2 / Real.log κ) 1002
  have hpos : 0 ≤ r ^ (E3 * h) := Real.rpow_nonneg hr0.le _
  unfold tf
  split_ifs with hreg
  · simp only [Bool.or_eq_true, decide_eq_true_eq] at hreg
    have hsz : n * q.size ≤ n * q := Nat.mul_le_mul_left _ (Nat.size_le.2 Nat.lt_two_pow_self)
    rcases hreg with h1 | h1
    · -- n < N0
      have : 2 ^ (n * q.size) ≤ 2 ^ (N0 * q) :=
        Nat.pow_le_pow_right (by norm_num) (hsz.trans (Nat.mul_le_mul_right _ h1.le))
      have : ((2 ^ (n * q.size) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (N0 * q) := by exact_mod_cast this
      linarith
    · -- m < 500 n: then n < 500 h
      have hr500 : r < 500 := by
        rw [hr, div_lt_iff₀ (by linarith)]; exact_mod_cast h1
      have hn500 : (n : ℝ) ≤ 500 * h := by
        have : (n : ℝ) / 500 ≤ (n : ℝ) / r := div_le_div_of_nonneg_left (by linarith) hr0 hr500.le
        linarith
      have e1 : ((2 ^ (n * q.size) : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((500 * q : ℝ) * h) := by
        have : ((2 ^ (n * q.size) : ℕ) : ℝ) = (2 : ℝ) ^ ((n * q.size : ℕ) : ℝ) := by
          rw [Real.rpow_natCast]; push_cast; ring_nf
        rw [this]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have : ((n * q.size : ℕ) : ℝ) ≤ (n : ℝ) * q := by exact_mod_cast hsz
        nlinarith
      have e2 : (2 : ℝ) ^ ((500 * q : ℝ) * h) ≤ r ^ (E3 * h) := by
        rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hr0]
        apply Real.exp_le_exp.2
        have : 500 * q * Real.log 2 / Real.log κ ≤ E3 := le_max_left _ _
        have h2 : 500 * q * Real.log 2 ≤ E3 * Real.log κ := by rwa [div_le_iff₀ hlk] at this
        have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have hE3 : 0 ≤ E3 := le_trans (by positivity) this
        nlinarith [mul_le_mul_of_nonneg_left hlr hE3]
      have : (0 : ℝ) ≤ 2 ^ (N0 * q) := by positivity
      linarith
  · -- main regime
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hreg
    obtain ⟨hN0, h500⟩ := hreg
    set D := degD n m
    have hD500 : 500 ≤ D := le_max_left _ _
    have hr500 : 500 ≤ r := by rw [hr, le_div_iff₀ (by linarith)]; exact_mod_cast h500
    -- D ≥ 500 n / r
    have hmN : 0 < m := by exact_mod_cast hmpos
    have hDm : 500 * n * n ≤ D * m := by
      have hD : (500 * n * n + m - 1) / m ≤ D := le_max_right _ _
      have h1 := Nat.div_add_mod (500 * n * n + m - 1) m
      have h2 := Nat.mod_lt (500 * n * n + m - 1) hmN
      have h3 : m * ((500 * n * n + m - 1) / m) ≤ m * D := Nat.mul_le_mul_left _ hD
      rw [mul_comm m D] at h3
      omega
    have hDR : (500 : ℝ) * n / r ≤ D := by
      rw [hr, div_div_eq_mul_div, div_le_iff₀ hmpos]
      have : ((500 * n * n : ℕ) : ℝ) ≤ ((D * m : ℕ) : ℝ) := by exact_mod_cast hDm
      push_cast at this; nlinarith
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    -- D ≤ 501 h
    have hD501 : (D : ℝ) ≤ 501 * h := by
      have hc : ((((500 * n * n + m - 1) / m : ℕ)) : ℝ) ≤ 500 * (n : ℝ) ^ 2 / m + 1 := by
        refine (Nat.cast_div_le).trans ?_
        rw [div_le_iff₀ hmpos, add_mul, one_mul, div_mul_cancel₀ _ hmpos.ne']
        have : ((500 * n * n + m - 1 : ℕ) : ℝ) ≤ ((500 * n * n + m : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
        push_cast at this; nlinarith
      have hDmax : (D : ℝ) ≤ max 500 (500 * (n : ℝ) ^ 2 / m + 1) := by
        simp only [D, degD, Nat.cast_max]
        exact max_le_max (by norm_num) hc
      have h2 : 500 * (n : ℝ) ^ 2 / m ≤ 500 * h := by
        rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hhge (by norm_num)
      refine hDmax.trans (max_le (by linarith) (by linarith))
    -- x ≤ r
    set x := 3 * (n + D) / D + 1
    have hx1 : 1 ≤ x := Nat.le_add_left 1 _
    have hxr : (x : ℝ) ≤ r := by
      have h1 : ((3 * (n + D) / D : ℕ) : ℝ) ≤ (3 * (n + D) : ℝ) / D := by
        have := (Nat.cast_div_le (m := 3 * (n + D)) (n := D) (α := ℝ)); push_cast at this ⊢; exact this
      have h2 : (3 * (n + D) : ℝ) / D = 3 * n / D + 3 := by field_simp
      have h3 : (3 * n : ℝ) / D ≤ 3 * r / 500 := by
        rw [div_le_div_iff₀ hD0 (by norm_num)]
        have := hDR; rw [div_le_iff₀ hr0] at this; nlinarith
      have : (x : ℝ) = ((3 * (n + D) / D : ℕ) : ℝ) + 1 := by simp [x]
      rw [this]; linarith
    have hpow : 2 ^ (D * x.size) ≤ (2 * x) ^ D := by
      rw [mul_comm, pow_mul]
      exact Nat.pow_le_pow_left (two_pow_size_le x hx1) D
    have e1 : ((2 ^ (D * x.size) : ℕ) : ℝ) ≤ ((2 * x : ℕ) : ℝ) ^ D := by exact_mod_cast hpow
    have e2 : ((2 * x : ℕ) : ℝ) ^ D ≤ (r ^ 2) ^ D := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast; nlinarith
    have e3 : (r ^ 2) ^ D = r ^ ((2 * D : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, ← pow_mul]
    have e4 : r ^ ((2 * D : ℕ) : ℝ) ≤ r ^ (E3 * h) := by
      apply Real.rpow_le_rpow_of_exponent_le hr1
      have : (1002 : ℝ) ≤ E3 := le_max_right _ _
      push_cast; nlinarith
    have : (0 : ℝ) ≤ 2 ^ (N0 * q) := by positivity
    linarith

end T17M

end File_T17M_TimeBound2

section File_T17M_TimeBound3

/-! # The final running-time inequality -/

namespace T17M

open Polynomial

theorem time_bound (q N0 : ℕ) (hq : 3 ≤ q) (κ : ℝ) (hκ : 1 < κ) (P : Polynomial ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m → ∀ N : ℕ, N ≤ n + m + 2 + q * (m * n + m) →
      P.eval (N + 2 ^ tf q N0 n m) ≤ ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ := by
  have hlk : 0 < Real.log κ := Real.log_pos hκ
  set δ := min (1 / 2 : ℝ) (Real.log κ / 2)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  set E3 := max (500 * q * Real.log 2 / Real.log κ) 1002
  set E := max (1 + 2 / δ) E3
  set K0 : ℝ := 6 * q + 2 ^ (N0 * q) + 2
  set a := P.eval 1
  set k := P.natDegree
  set L := Real.log (a * K0 ^ k + 1)
  have hK0 : 0 < K0 := by positivity
  have hL : 0 ≤ L := by
    have : (0 : ℝ) ≤ a * K0 ^ k := by positivity
    exact Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := le_trans (by norm_num : (0 : ℝ) ≤ 1002) ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨E * k + L / Real.log κ + 1, by positivity, ?_⟩
  intro n m hn hm N hN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmpos : (0 : ℝ) < m := by nlinarith
  have hm1 : 1 ≤ m := by exact_mod_cast (show (1 : ℝ) ≤ m by nlinarith)
  set r := (m : ℝ) / n with hr
  have hrκ : κ ≤ r := by rw [hr, le_div_iff₀ (by linarith)]; linarith
  have hr1 : 1 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set h := (⌈(n : ℝ) ^ 2 / m⌉ : ℝ) with hh
  have hhge : (n : ℝ) ^ 2 / m ≤ h := Int.le_ceil _
  have hnr : (n : ℝ) / r ≤ h := by
    rw [hr, div_div_eq_mul_div]; rw [sq] at hhge; exact hhge
  have hh1 : 1 ≤ h := by
    have : (0 : ℝ) < (n : ℝ) ^ 2 / m := by positivity
    have h0 : (0 : ℤ) < ⌈(n : ℝ) ^ 2 / m⌉ := Int.ceil_pos.2 this
    rw [hh]; exact_mod_cast h0
  have hR1 : 1 ≤ r ^ (E * h) := Real.one_le_rpow hr1 (by positivity)
  -- n ≤ r^(h/δ)
  have hnb := n_le_rpow κ r h n hκ hn hrκ hh1 hnr
  -- m n ≤ r^(E h)
  have hmn : (m : ℝ) * n ≤ r ^ (E * h) := by
    have e1 : (m : ℝ) * n = r * n * n := by rw [hr]; field_simp
    have hrh : r ≤ r ^ h := by
      calc r = r ^ (1 : ℝ) := (Real.rpow_one r).symm
        _ ≤ r ^ h := Real.rpow_le_rpow_of_exponent_le hr1 hh1
    calc (m : ℝ) * n = r * n * n := e1
      _ ≤ r ^ h * r ^ (h / δ) * r ^ (h / δ) := by
          have : (0 : ℝ) ≤ n := by linarith
          gcongr
      _ = r ^ ((1 + 2 / δ) * h) := by
          rw [← Real.rpow_add hr0, ← Real.rpow_add hr0]; congr 1; field_simp; ring
      _ ≤ r ^ (E * h) := Real.rpow_le_rpow_of_exponent_le hr1
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  -- N ≤ 6 q m n
  have hNb : (N : ℝ) ≤ 6 * q * r ^ (E * h) := by
    have : N ≤ 6 * q * (m * n) := by
      have h1 : n ≤ m * n := Nat.le_mul_of_pos_left n (by omega)
      have h2 : m ≤ m * n := Nat.le_mul_of_pos_right m (by omega)
      have h3 : 1 ≤ m * n := Nat.mul_pos (by omega) (by omega)
      have h4 : q * m ≤ q * (m * n) := Nat.mul_le_mul_left q h2
      have h5 : q * (m * n + m) = q * (m * n) + q * m := by ring
      have h6 : 6 * q * (m * n) = 6 * (q * (m * n)) := by ring
      have h7 : 3 * (m * n) ≤ q * (m * n) := Nat.mul_le_mul_right _ hq
      omega
    have : (N : ℝ) ≤ 6 * q * ((m : ℝ) * n) := by exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ 6 * q := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmn hq0]
  -- 2^tf
  have hfb := fuel_rpow q N0 n m (by omega) κ hκ hn hm
  have hE3 : r ^ (E3 * h) ≤ r ^ (E * h) := Real.rpow_le_rpow_of_exponent_le hr1
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
  -- X ≤ K0 r^(E h)
  have hX : ((N + 2 ^ tf q N0 n m + 1 : ℕ) : ℝ) ≤ K0 * r ^ (E * h) := by
    push_cast
    have h2 : (2 : ℝ) ^ (N0 * q) ≤ 2 ^ (N0 * q) * r ^ (E * h) := by
      have : (0 : ℝ) ≤ 2 ^ (N0 * q) := by positivity
      nlinarith
    have hfb' : ((2 ^ tf q N0 n m : ℕ) : ℝ) = (2 : ℝ) ^ tf q N0 n m := by push_cast; ring
    rw [hfb'] at hfb
    simp only [K0]
    nlinarith
  -- polynomial bound
  have hP := poly_bound P (N + 2 ^ tf q N0 n m)
  have hPR : ((P.eval (N + 2 ^ tf q N0 n m) : ℕ) : ℝ) ≤ a * (K0 * r ^ (E * h)) ^ k := by
    have : ((P.eval (N + 2 ^ tf q N0 n m) : ℕ) : ℝ) ≤ (a : ℝ) * ((N + 2 ^ tf q N0 n m + 1 : ℕ) : ℝ) ^ k := by
      exact_mod_cast hP
    refine this.trans ?_
    gcongr
  apply Nat.le_floor
  refine hPR.trans ?_
  rw [mul_pow, ← Real.rpow_natCast (r ^ (E * h)), ← Real.rpow_mul hr0.le]
  have hsplit : r ^ ((E * k + L / Real.log κ + 1) * h) =
      r ^ (E * h * k) * r ^ ((L / Real.log κ + 1) * h) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  rw [hsplit]
  have hbig : (a : ℝ) * K0 ^ k ≤ r ^ ((L / Real.log κ + 1) * h) := by
    have h1 : r ^ (L / Real.log κ) ≤ r ^ ((L / Real.log κ + 1) * h) :=
      Real.rpow_le_rpow_of_exponent_le hr1 (by
        have : 0 ≤ L / Real.log κ := div_nonneg hL hlk.le
        nlinarith)
    have h2 : κ ^ (L / Real.log κ) ≤ r ^ (L / Real.log κ) :=
      Real.rpow_le_rpow (by linarith) hrκ (div_nonneg hL hlk.le)
    have h3 : κ ^ (L / Real.log κ) = a * K0 ^ k + 1 := by
      rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hlk.ne', Real.exp_log (by positivity)]
    linarith
  have hpos : 0 ≤ r ^ (E * h * k) := Real.rpow_nonneg hr0.le _
  calc (a : ℝ) * (K0 ^ k * r ^ (E * h * k)) = (a * K0 ^ k) * r ^ (E * h * k) := by ring
    _ ≤ r ^ ((L / Real.log κ + 1) * h) * r ^ (E * h * k) := by gcongr
    _ = r ^ (E * h * k) * r ^ ((L / Real.log κ + 1) * h) := by ring

end T17M

end File_T17M_TimeBound3

section File_T17M_Machine

/-! # The composed machine and its running time -/

namespace T17M

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial T17

variable (q : ℕ) [NeZero q] (N0 : ℕ)

noncomputable def P1 : PolyProgram (enc : List Bool → List Bool) enc (stage1 q N0) := (Poly.stage1_p q N0).program
noncomputable def P3 : PolyProgram (enc : Pin × List ℕ → List Bool) enc (stage3 q N0) := (Poly.stage3_p q N0).program

noncomputable def machineT := ((((Timed.ofPoly BooleanLists.packProgram).comp (Timed.ofPoly (P1 q N0))).comp
  (fuelTimed (α := Pin))).comp (Timed.ofPoly (P3 q N0))).comp (Timed.ofPoly BooleanLists.unpackProgram)

theorem machineT_fun (w : List Bool) :
    (fun a => id (stage3 q N0 (fres (stage1 q N0 (id a))))) w = total q N0 w := rfl

noncomputable def PT : Polynomial ℕ := (fbodyProgram (α := Pin)).time + 2 * (fbodyProgram (α := Pin)).sizeBound + 3

theorem passTime_eq (S : ℕ) : (fbodyProgram (α := Pin)).passTime S = (PT).eval S := by
  simp [PT, PolyProgram.passTime]

noncomputable def B1 : Polynomial ℕ := (P1 q N0).sizeBound.comp (Polynomial.C 3 * X)
noncomputable def AA : Polynomial ℕ := 4 * B1 q N0 + X + 3

noncomputable def RR : Polynomial ℕ :=
  BooleanLists.packProgram.time + 2 * (Polynomial.C 3 * X) + 2 + (P1 q N0).time.comp (Polynomial.C 3 * X) +
  2 * B1 q N0 + 2 + (X + 1) * PT.comp (AA q N0) + 2 * AA q N0 + 2 + (P3 q N0).time.comp (AA q N0) +
  2 * (P3 q N0).sizeBound.comp (AA q N0) + 2 + BooleanLists.unpackProgram.time.comp ((P3 q N0).sizeBound.comp (AA q N0))

theorem enc_bool_list (w : List Bool) : (enc w).length = 3 * w.length := BooleanLists.length w

theorem mem_dbl (k : ℕ) (l : List ℕ) : ∀ a ∈ dbl k l, a ∈ l := by
  induction k generalizing l with
  | zero => intro a ha; exact ha
  | succ k ih =>
    intro a ha
    have := ih (l ++ l) a ha
    rcases List.mem_append.1 this with h | h <;> exact h

theorem enc_zeros (l : List ℕ) (hl : ∀ a ∈ l, a = 0) : (enc l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [enc_list_cons, enc_nat, hl a List.mem_cons_self, ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))]
    simp; omega

theorem enc_dbl (k : ℕ) : (enc (dbl k [0])).length = 2 ^ k := by
  rw [enc_zeros _ (fun a ha => by simpa using mem_dbl k [0] a ha), length_dbl]; simp

theorem machine_run (w : List Bool) :
    ∃ t ≤ (RR q N0).eval (w.length + 2 ^ (stage1 q N0 w).2.1),
      Trace (machineT q N0).machine.step t ((machineT q N0).machine.initialCfg w)
        ((machineT q N0).machine.finalCfg (total q N0 w)) := by
  obtain ⟨t, ht, tr⟩ := (machineT q N0).run w
  refine ⟨t, ht.trans ?_, tr⟩
  clear tr
  simp only [id] at ht ⊢
  clear ht
  set p := stage1 q N0 w with hp
  set XX := w.length + 2 ^ p.2.1 with hXX
  have hp2 : p.2.2 = [0] := rfl
  have e0 : (enc ([0] : List ℕ)).length = 1 := rfl
  have ep : (enc p).length = 2 * (enc p.1).length + 1 + (2 * p.2.1.size + 1 + 1) := by
    rw [enc_pair (Pin) (ℕ × List ℕ) p, enc_pair ℕ (List ℕ) p.2, enc_nat, hp2, e0]
  have efs : fsize p = 2 * (enc p.1).length + 3 + 2 * p.2.1.size + 2 ^ p.2.1 := by
    simp only [fsize, hp2, e0, mul_one]
  have efr : (enc (fres p)).length = 2 * (enc p.1).length + 1 + 2 ^ p.2.1 := by
    rw [show fres p = (p.1, dbl p.2.1 [0]) from rfl, enc_pair (Pin) (List ℕ), enc_dbl]
  have hw : (enc w).length = 3 * w.length := enc_bool_list w
  have hs1 : (enc p).length ≤ (B1 q N0).eval XX := by
    have := (P1 q N0).length_bound w
    refine this.trans ?_
    simp only [B1, eval_comp, eval_mul, eval_C, eval_X]
    exact polynomial_eval_mono _ (by rw [hw, hXX]; exact Nat.mul_le_mul_left 3 (Nat.le_add_right _ _))
  have hA : (enc (fres p)).length ≤ (AA q N0).eval XX := by
    simp only [AA, eval_add, eval_mul, eval_X, eval_ofNat]; omega
  have hF : fsize p ≤ (AA q N0).eval XX := by
    simp only [AA, eval_add, eval_mul, eval_X, eval_ofNat]; omega
  have ht1 : p.2.1 + 1 ≤ XX + 1 := by
    have := Nat.lt_two_pow_self (n := p.2.1); rw [hXX]; omega
  have hPT : (fbodyProgram (α := Pin)).passTime (fsize p) ≤ PT.eval ((AA q N0).eval XX) := by
    rw [passTime_eq]; exact polynomial_eval_mono _ hF
  have hloop : (p.2.1 + 1) * (fbodyProgram (α := Pin)).passTime (fsize p) ≤
      (XX + 1) * PT.eval ((AA q N0).eval XX) := Nat.mul_le_mul ht1 hPT
  have hs3 : (enc (stage3 q N0 (fres p))).length ≤ (P3 q N0).sizeBound.eval ((AA q N0).eval XX) :=
    ((P3 q N0).length_bound (fres p)).trans (polynomial_eval_mono _ hA)
  have hT0 : eval (id w).length BooleanLists.packProgram.time ≤ BooleanLists.packProgram.time.eval XX :=
    polynomial_eval_mono _ (by simp only [id]; rw [hXX]; exact Nat.le_add_right _ _)
  have hT1 : eval (enc (id w)).length (P1 q N0).time ≤ (P1 q N0).time.eval (3 * XX) :=
    polynomial_eval_mono _ (by simp only [id]; rw [hw, hXX]; exact Nat.mul_le_mul_left 3 (Nat.le_add_right _ _))
  have hT3 : eval (enc (fres p)).length (P3 q N0).time ≤ (P3 q N0).time.eval ((AA q N0).eval XX) :=
    polynomial_eval_mono _ hA
  have hT4 : eval (encodeList encodeBool (stage3 q N0 (fres p))).length BooleanLists.unpackProgram.time ≤
      BooleanLists.unpackProgram.time.eval ((P3 q N0).sizeBound.eval ((AA q N0).eval XX)) :=
    polynomial_eval_mono _ hs3
  have hpk : (encodeList encodeBool (id w)).length = 3 * w.length := BooleanLists.length w
  have hs3' : (enc (stage3 q N0 (fres p))).length = (encodeList encodeBool (stage3 q N0 (fres p))).length := rfl
  simp only [RR, eval_add, eval_mul, eval_comp, eval_C, eval_X, eval_ofNat, eval_one]
  simp only [id] at hT0 hT1 hpk ⊢
  have hB : (B1 q N0).eval XX = (P1 q N0).sizeBound.eval (3 * XX) := by simp [B1]
  clear_value XX
  generalize 2 ^ p.2.1 = E at *
  omega

end T17M

end File_T17M_Machine

section File_T17M_Parse

/-! # Parsing the input code -/

namespace T17M

open T17 F3SubsetSum

theorem foldl_stepP_unaryD (a : ℕ) (w : List Bool) (done : List ℕ) :
    (unaryD a ++ w).foldl stepP (0, done) = w.foldl stepP (0, done ++ [a]) := by
  have h : ∀ k c, (List.replicate k true).foldl stepP (c, done) = (c + k, done) := by
    intro k
    induction k with
    | zero => intro c; rfl
    | succ k ih =>
      intro c
      rw [List.replicate_succ, List.foldl_cons]
      simp only [stepP, if_true]
      rw [ih]; congr 1; omega
  simp only [unaryD, unary, List.append_assoc, List.foldl_append, h, List.foldl_cons, List.foldl_nil, stepP]
  simp

theorem foldl_stepP_flat (L : List ℕ) (w : List Bool) (done : List ℕ) :
    (L.flatMap unaryD ++ w).foldl stepP (0, done) = w.foldl stepP (0, done ++ L) := by
  induction L generalizing done with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.append_assoc, foldl_stepP_unaryD, ih]
    simp

variable {q : ℕ} {n m : ℕ}

/-- The numbers listed by the instance code. -/
def instNums (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) : List ℕ :=
  n :: m :: ((List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => (A j i).val)) ++
    (List.finRange m).map (fun i => (b i).val))

theorem parseNums_inst (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    parseNums (encodeInstance A b) = instNums A b := by
  unfold parseNums encodeInstance instNums
  have e1 : (List.finRange m).flatMap (fun i => (List.finRange n).flatMap (fun j => unaryD (A j i).val)) =
      ((List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => (A j i).val))).flatMap unaryD := by
    rw [List.flatMap_assoc]; congr 1; funext i; rw [List.flatMap_map]
  have e2 : (List.finRange m).flatMap (fun i => unaryD (b i).val) =
      ((List.finRange m).map (fun i => (b i).val)).flatMap unaryD := by
    rw [List.flatMap_map]
  rw [e1, e2]
  have := foldl_stepP_flat
    (n :: m :: ((List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => (A j i).val)) ++
      (List.finRange m).map (fun i => (b i).val))) [] []
  simp only [List.append_nil, List.nil_append, List.flatMap_cons, List.flatMap_append] at this
  simp only [List.append_assoc] at this ⊢
  rw [this]
  rfl

theorem drop_take_flatten {α : Type} (L : List (List α)) (k : ℕ) (hL : ∀ l ∈ L, l.length = k)
    (rest : List α) (i : ℕ) (hi : i < L.length) :
    ((L.flatten ++ rest).drop (i * k)).take k = L[i] := by
  induction L generalizing i with
  | nil => simp at hi
  | cons l L ih =>
    have hl := hL l List.mem_cons_self
    rcases i with _ | i
    · simp only [List.getElem_cons_zero, zero_mul, List.drop_zero, List.flatten_cons, List.append_assoc]
      rw [List.take_append_of_le_length (by rw [hl]), ← hl, List.take_length]
    · rw [List.flatten_cons, List.append_assoc, show (i + 1) * k = k + i * k by ring, ← List.drop_drop,
        List.drop_left' hl]
      exact ih (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) i (by simpa using hi)

theorem length_encodeInstance_ge (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    n + m ≤ (encodeInstance A b).length := by
  simp only [encodeInstance, unaryD, unary, List.length_append, List.length_replicate]; omega

theorem pinOfBits_inst [NeZero q] (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    pinOfBits (encodeInstance A b) = pinOf (instOf A b) := by
  have hlen := length_encodeInstance_ge A b
  unfold pinOfBits pinOf instOf
  rw [parseNums_inst]
  simp only [instNums, List.getD_cons_zero, List.getD_cons_succ, List.drop_succ_cons, List.drop_zero]
  have hR : ∀ k ≤ (encodeInstance A b).length, (List.range (encodeInstance A b).length).take k = List.range k := by
    intro k hk; rw [List.take_range, min_eq_left hk]
  rw [hR n (by omega), hR m (by omega)]
  set cl := (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => (A j i).val))
  have hcl : cl = (List.ofFn (fun i => colL A i)).flatten := by
    simp only [cl, colL, List.flatMap, List.ofFn_eq_map]
  have hcl_len : cl.length = m * n := by
    rw [hcl, List.length_flatten]; simp [colL, Function.comp_def, List.sum_ofFn]
  congr 1; congr 1; congr 1; congr 1; congr 1
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hcl]
    rw [drop_take_flatten _ n (by intro l hl; obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hl; simp [colL]) _ i (by simpa using h2)]
  · rw [← hcl_len, List.drop_left, List.take_of_length_le (by simp)]
    simp [List.ofFn_eq_map]

end T17M

end File_T17M_Parse

section File_T17M_Bridge

/-! # From the machine to `ComputesWithin` -/

namespace T17M

open OAI.MetricKMedian.Binary T17 F3SubsetSum

def TMof (M : Machine) : Turing.TM2ComputableAux Bool Bool := ⟨M.tm, Equiv.refl Bool, Equiv.refl Bool⟩

theorem outputsWithin_of_trace (M : Machine) (w o : List Bool) (t T : ℕ) (ht : t ≤ T)
    (tr : Trace M.step t (M.initialCfg w) (M.finalCfg o)) : HMBinPacking.OutputsWithin (TMof M) w o T := by
  have hw : List.map (⇑(Equiv.refl Bool).symm) w = w := List.map_id w
  have ho : List.map (⇑(Equiv.refl Bool).symm) o = o := List.map_id o
  have tr' : Trace M.step t (M.initialCfg (List.map (⇑(Equiv.refl Bool).symm) w))
      (M.finalCfg (List.map (⇑(Equiv.refl Bool).symm) o)) := by rw [hw, ho]; exact tr
  exact ⟨⟨⟨t, tr'.iterate_eq⟩, ht⟩⟩

variable (q : ℕ) [NeZero q] (N0 : ℕ)

/-- The decoder. -/
def DecF : DecoderFn q := fun n m A b j =>
  (((decL q N0 (pinOf (instOf A b)) (dbl (tf q N0 n m) [0])).getD j 0 : ℕ) : ZMod q)

theorem filter_lt_range (x : ℕ) (hx : x ≤ q) :
    ((List.range q).filter (fun e => decide (e < x))).map (fun _ => true) = List.replicate x true := by
  apply List.eq_replicate_iff.2
  refine ⟨?_, by simp⟩
  rw [List.length_map]
  have : (List.range q).filter (fun e => decide (e < x)) = List.range x := by
    induction q with
    | zero => simp at hx; subst hx; rfl
    | succ k ih =>
      rcases Nat.lt_or_ge x (k + 1) with h | h
      · rw [List.range_succ, List.filter_append]
        rw [ih (by omega)]
        simp [show ¬ k < x by omega]
      · have hx' : x = k + 1 := by omega
        subst hx'
        rw [List.filter_eq_self.2 (by intro a ha; simpa using ha)]
  rw [this, List.length_range]

theorem flatMap_finRange {β : Type} (n : ℕ) (h : ℕ → List β) :
    (List.finRange n).flatMap (fun j : Fin n => h j.val) = (List.range n).flatMap h := by
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]

theorem total_inst {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    total q N0 (encodeInstance A b) = encodeSecret (DecF q N0 n m A b) := by
  unfold total stage3 stage1 fres finalList outBits encodeSecret DecF
  simp only [pinOfBits_inst]
  simp only [pinOf, instOf]
  rw [← List.map_coe_finRange_eq_range (n := n), List.map_map, List.flatMap_map]
  congr 1
  funext j
  rw [filter_lt_range q _ (le_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))))]
  simp [unaryD, unary, ZMod.val_natCast]

theorem stage1_inst {n m : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    (stage1 q N0 (encodeInstance A b)).2.1 = tf q N0 n m := by
  simp only [stage1, pinOfBits_inst, pinOf, instOf]

/-- The machine computes `DecF` within `RR(N + 2^tf)` steps. -/
theorem computes (n m T : ℕ)
    (hT : ∀ (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q),
      (RR q N0).eval ((encodeInstance A b).length + 2 ^ tf q N0 n m) ≤ T) :
    ComputesWithin (TMof (machineT q N0).machine) (DecF q N0) n m T := by
  intro A b
  obtain ⟨t, ht, tr⟩ := machine_run q N0 (encodeInstance A b)
  rw [stage1_inst q N0, total_inst q N0] at *
  exact outputsWithin_of_trace _ _ _ t T (ht.trans (hT A b)) tr

end T17M

end File_T17M_Bridge

section File_T17M_Count

/-! # Counting monomials: fuel sufficiency -/

namespace T17M

open T17

theorem hockey (k d : ℕ) : ∑ j ∈ Finset.range (d + 1), (k + j).choose j = (k + 1 + d).choose d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, show k + 1 + (d + 1) = (k + 1 + d) + 1 by ring, Nat.choose_succ_succ',
      show k + (d + 1) = k + 1 + d by ring]

theorem len_monosEq (q k d : ℕ) : (monosEq q k d).length ≤ (k + d).choose d := by
  induction k generalizing d with
  | zero =>
    simp only [monosEq]
    split_ifs with h <;> simp [h]
  | succ k ih =>
    simp only [monosEq, List.length_flatMap, List.length_map]
    rw [list_sum_range]
    calc ∑ e ∈ Finset.range (min (q - 1) d + 1), (monosEq q k (d - e)).length
        ≤ ∑ e ∈ Finset.range (min (q - 1) d + 1), (k + (d - e)).choose (d - e) :=
          Finset.sum_le_sum fun e _ => ih (d - e)
      _ ≤ ∑ e ∈ Finset.range (d + 1), (k + (d - e)).choose (d - e) :=
          Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))
      _ = ∑ j ∈ Finset.range (d + 1), (k + j).choose j := by
          rw [← Finset.sum_range_reflect]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [Finset.mem_range] at hj
          congr 2 <;> omega
      _ = (k + 1 + d).choose d := hockey k d

theorem choose_mono (k d n D : ℕ) (hk : k ≤ n) (hd : d ≤ D) : (k + d).choose d ≤ (n + D).choose D := by
  calc (k + d).choose d ≤ (n + d).choose d := Nat.choose_le_choose _ (by omega)
    _ = (n + d).choose n := by rw [Nat.choose_symm_add]
    _ ≤ (n + D).choose n := Nat.choose_le_choose _ (by omega)
    _ = (n + D).choose D := by rw [Nat.choose_symm_add]

/-- `D^D ≤ 3^D · D!`. -/
theorem pow_le_three_pow_factorial (D : ℕ) : D ^ D ≤ 3 ^ D * D.factorial := by
  have h := Real.pow_div_factorial_le_exp (D : ℝ) (Nat.cast_nonneg _) D
  have he : Real.exp (D : ℝ) ≤ 3 ^ D := by
    rw [show (D : ℝ) = D * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le (by have := Real.exp_one_lt_d9; linarith) D
  have hf : (0 : ℝ) < D.factorial := by exact_mod_cast Nat.factorial_pos D
  rw [div_le_iff₀ hf] at h
  have : (D : ℝ) ^ D ≤ 3 ^ D * D.factorial := by nlinarith
  exact_mod_cast this

/-- `choose(N, D) ≤ (⌊3N/D⌋ + 1)^D`. -/
theorem choose_le_bound (N D : ℕ) (hD : 0 < D) : N.choose D ≤ (3 * N / D + 1) ^ D := by
  have h1 : N.choose D * D.factorial ≤ N ^ D := by
    have := Nat.descFactorial_eq_factorial_mul_choose N D
    rw [mul_comm, ← this]
    exact Nat.descFactorial_le_pow N D
  have h2 := pow_le_three_pow_factorial D
  have h3 : 3 * N < D * (3 * N / D + 1) := by
    have := Nat.lt_mul_div_succ (3 * N) hD; linarith
  have h4 : (3 * N) ^ D ≤ (D * (3 * N / D + 1)) ^ D := Nat.pow_le_pow_left h3.le D
  have hDD : 0 < D ^ D := by positivity
  have h5 : N.choose D * D ^ D ≤ (3 * N / D + 1) ^ D * D ^ D := by
    calc N.choose D * D ^ D ≤ N.choose D * (3 ^ D * D.factorial) := Nat.mul_le_mul_left _ h2
      _ = 3 ^ D * (N.choose D * D.factorial) := by ring
      _ ≤ 3 ^ D * N ^ D := Nat.mul_le_mul_left _ h1
      _ = (3 * N) ^ D := by rw [mul_pow]
      _ ≤ (D * (3 * N / D + 1)) ^ D := h4
      _ = (3 * N / D + 1) ^ D * D ^ D := by rw [mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right h5 hDD

theorem lt_two_pow_size (x : ℕ) : x < 2 ^ x.size := Nat.lt_size_self x

end T17M

end File_T17M_Count

section File_T17M_Correct2

/-! # Correctness of `DecF` on the good events -/

namespace T17M

open OAI.MetricKMedian.Binary T17 F3SubsetSum

variable {q : ℕ} [Fact q.Prime] [NeZero q] {n m N0 : ℕ}

theorem fuel_len (N0 n m : ℕ) : (dbl (tf q N0 n m) [0]).length = 2 ^ tf q N0 n m := by
  rw [length_dbl]; simp

theorem fuel_brute (h : n < N0 ∨ m < 500 * n) : q ^ n ≤ (dbl (tf q N0 n m) [0]).length := by
  rw [fuel_len]
  have ht : tf q N0 n m = n * q.size := by
    unfold tf; rw [if_pos (by rcases h with h | h <;> simp [h])]
  rw [ht]
  calc q ^ n ≤ (2 ^ q.size) ^ n := Nat.pow_le_pow_left (Nat.lt_size_self q).le n
    _ = 2 ^ (n * q.size) := by rw [← pow_mul, mul_comm]

theorem fuel_main (h : ¬ (n < N0 ∨ m < 500 * n)) :
    ∀ k ≤ n, ∀ d ≤ degD n m, (monosEq q k d).length ≤ (dbl (tf q N0 n m) [0]).length := by
  intro k hk d hd
  rw [fuel_len]
  have ht : tf q N0 n m = degD n m * Nat.size (3 * (n + degD n m) / degD n m + 1) := by
    unfold tf; rw [if_neg (by simpa using h)]
  have hD : 0 < degD n m := by unfold degD; omega
  rw [ht]
  calc (monosEq q k d).length ≤ (k + d).choose d := len_monosEq q k d
    _ ≤ (n + degD n m).choose (degD n m) := choose_mono k d n _ hk hd
    _ ≤ (3 * (n + degD n m) / degD n m + 1) ^ degD n m := choose_le_bound _ _ hD
    _ ≤ (2 ^ Nat.size (3 * (n + degD n m) / degD n m + 1)) ^ degD n m :=
        Nat.pow_le_pow_left (Nat.lt_size_self _).le _
    _ = 2 ^ (degD n m * Nat.size (3 * (n + degD n m) / degD n m + 1)) := by rw [← pow_mul, mul_comm]

/-- `DecF` returns the secret on the good events. -/
theorem DecF_correct (hq3 : 3 ≤ q) (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q)
    (s : Fin n → ZMod q) (hs : candidates A b = {s})
    (h : (n < N0 ∨ m < 500 * n) ∨ Function.Surjective (Phi (ZMod q) q (cols A) (degD n m))) :
    DecF q N0 n m A b = s := by
  have hout : decL q N0 (pinOf (instOf A b)) (dbl (tf q N0 n m) [0]) = List.ofFn (fun j => (s j).val) := by
    rw [decL_eq]
    by_cases hreg : n < N0 ∨ m < 500 * n
    · have hc : ((instOf A b).n < N0 || (instOf A b).m < 500 * (instOf A b).n) = true := by
        simp only [instOf]; rcases hreg with h' | h' <;> simp [h']
      have hb : bruteC q (pinOf (instOf A b)) (dbl (tf q N0 n m) [0]) = bruteDec q (instOf A b) :=
        bruteC_eq q (instOf A b) (dbl (tf q N0 n m) [0]) (fuel_brute hreg)
      rw [if_pos hc, hb, bruteDec_correct A b s hs]
    · have hc : ((instOf A b).n < N0 || (instOf A b).m < 500 * (instOf A b).n) = false := by
        simp only [instOf]; push_neg at hreg; simp [show ¬ n < N0 by omega, show ¬ m < 500 * n by omega]
      have hsurj := h.resolve_left hreg
      push_neg at hreg
      have hcx : ctxF q (pinOf (instOf A b)) (dbl (tf q N0 n m) [0]) = ctxOf q (instOf A b) (degD n m) :=
        ctxF_eq q (instOf A b) (dbl (tf q N0 n m) [0]) (show n ≤ m by nlinarith)
          (fuel_main (q := q) (n := n) (m := m) (N0 := N0) (by omega))
      rw [if_neg (by simp [hc]), hcx, mainDecC_eq]
      exact mainDec_correct hq3 (rep_instOf A b) (by unfold degD; omega) hsurj s hs
  funext j
  unfold DecF
  rw [hout, List.getD_eq_getElem _ _ (by simp)]
  simp

end T17M

end File_T17M_Correct2

section File_T17M_Prob1

/-! # Probability I: the degree, block surjectivity -/

namespace T17M

open T17 F3SubsetSum

theorem ceil_div_nat (a b : ℕ) (hb : 0 < b) : ⌈(a : ℝ) / b⌉₊ = (a + b - 1) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set k := (a + b - 1) / b
  have h1 : a ≤ k * b := by
    have h := Nat.lt_mul_div_succ (a + b - 1) hb
    have e : b * ((a + b - 1) / b + 1) = k * b + b := by simp only [k]; ring
    rw [e] at h
    omega
  have h3 : k * b ≤ a + b - 1 := Nat.div_mul_le_self _ _
  apply le_antisymm
  · apply Nat.ceil_le.2
    rw [div_le_iff₀ hbR]; exact_mod_cast h1
  · by_contra hcon
    push_neg at hcon
    have h4 : ⌈(a : ℝ) / b⌉₊ + 1 ≤ k := hcon
    have h5 : (a : ℝ) / b ≤ ⌈(a : ℝ) / b⌉₊ := Nat.le_ceil _
    have h6 : (a : ℝ) ≤ ⌈(a : ℝ) / b⌉₊ * b := by rwa [div_le_iff₀ hbR] at h5
    have h7 : ⌈(a : ℝ) / b⌉₊ * b + b ≤ k * b := by nlinarith
    have h8 : (a : ℝ) + b ≤ k * b := by
      have : ((⌈(a : ℝ) / b⌉₊ * b + b : ℕ) : ℝ) ≤ (k * b : ℕ) := by exact_mod_cast h7
      push_cast at this; linarith
    have h9 : (k * b : ℝ) ≤ a + b - 1 := by
      have : ((k * b : ℕ) : ℝ) ≤ ((a + b - 1 : ℕ) : ℝ) := by exact_mod_cast h3
      rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
    linarith

theorem degD_ceil (n m : ℕ) (hm : 0 < m) (hle : m ≤ n ^ 2) :
    degD n m = ⌈500 * (n : ℝ) ^ 2 / m⌉₊ := by
  have hc := ceil_div_nat (500 * n * n) m hm
  have e : ((500 * n * n : ℕ) : ℝ) = 500 * (n : ℝ) ^ 2 := by push_cast; ring
  rw [e] at hc
  rw [hc]
  unfold degD
  apply max_eq_right
  apply (Nat.le_div_iff_mul_le hm).2
  have : m * 500 ≤ 500 * n * n := by nlinarith
  omega

theorem degD_big (n m : ℕ) (hlt : n ^ 2 < m) : degD n m = 500 := by
  unfold degD
  apply max_eq_left
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega)).2
  have : 500 * n * n < 500 * m := by nlinarith
  omega

theorem phi_apply {K : Type*} [CommRing K] {n m : ℕ} (q : ℕ) (a : Fin m → Fin n → K) (D : ℕ)
    (Q : Fin m → Rd K n q (D - 2)) :
    Phi K q a D Q = ∑ i, mulMap K n q (linForm (a i) ^ 2) (D - 2) D (Q i) := by
  simp [Phi]

/-- Surjectivity on a set of columns implies surjectivity. -/
theorem surj_of_sub {K : Type*} [CommRing K] {n m B : ℕ} (q : ℕ) (A : Matrix (Fin n) (Fin m) K) (D : ℕ)
    (f : Fin B → Fin m) (hf : Function.Injective f)
    (h : Function.Surjective (Phi K q (cols (A.submatrix id f)) D)) :
    Function.Surjective (Phi K q (cols A) D) := by
  intro y
  obtain ⟨Q', hQ'⟩ := h y
  refine ⟨Function.extend f Q' 0, ?_⟩
  rw [phi_apply] at hQ' ⊢
  rw [← hQ']
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨f, hf⟩))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [Function.Embedding.coeFn_mk, hf.extend_apply]
    rfl
  · intro i _ hi
    have : ¬ ∃ i', f i' = i := by
      rintro ⟨i', rfl⟩; exact hi (Finset.mem_map_of_mem _ (Finset.mem_univ i'))
    rw [Function.extend_apply' _ _ _ this]
    simp

end T17M

end File_T17M_Prob1

section File_T17M_Prob2

/-! # Probability II: counting matrices whose blocks are all bad -/

namespace T17M

open T17 F3SubsetSum

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- Column of block `ℓ`. -/
def bcol {k B m : ℕ} (h : k * B ≤ m) (ℓ : Fin k) (i : Fin B) : Fin m :=
  ⟨ℓ * B + i, by
    have h1 : (ℓ : ℕ) * B + i < (ℓ + 1) * B := by rw [Nat.add_mul, one_mul]; exact Nat.add_lt_add_left i.isLt _
    have h2 : ((ℓ : ℕ) + 1) * B ≤ k * B := Nat.mul_le_mul_right _ ℓ.isLt
    omega⟩

def rcol {k B m : ℕ} (h : k * B ≤ m) (j : Fin (m - k * B)) : Fin m := ⟨k * B + j, by omega⟩

theorem bcol_inj {k B m : ℕ} (h : k * B ≤ m) (ℓ : Fin k) : Function.Injective (bcol h ℓ) := by
  intro i i' e
  simp only [bcol, Fin.mk.injEq, Nat.add_left_cancel_iff] at e
  exact Fin.ext e

theorem block_count {n m k B : ℕ} (h : k * B ≤ m) (Bad : Finset (Matrix (Fin n) (Fin B) R)) :
    (Finset.univ.filter (fun A : Matrix (Fin n) (Fin m) R =>
      ∀ ℓ : Fin k, A.submatrix id (bcol h ℓ) ∈ Bad)).card ≤
      Bad.card ^ k * Fintype.card R ^ (n * (m - k * B)) := by
  classical
  let φ : Matrix (Fin n) (Fin m) R → (Fin k → Matrix (Fin n) (Fin B) R) × Matrix (Fin n) (Fin (m - k * B)) R :=
    fun A => (fun ℓ => A.submatrix id (bcol h ℓ), A.submatrix id (rcol h))
  have hinj : Function.Injective φ := by
    intro A A' e
    simp only [φ, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    ext j c
    by_cases hc : (c : ℕ) < k * B
    · have hB : 0 < B := by
        rcases Nat.eq_zero_or_pos B with hB | hB
        · subst hB; simp at hc
        · exact hB
      have hl : (c : ℕ) / B < k := (Nat.div_lt_iff_lt_mul hB).2 hc
      have := congrFun (congrFun (congrFun e1 ⟨(c : ℕ) / B, hl⟩) j) ⟨(c : ℕ) % B, Nat.mod_lt _ hB⟩
      simp only [Matrix.submatrix_apply, id] at this
      have hcc : bcol h ⟨(c : ℕ) / B, hl⟩ ⟨(c : ℕ) % B, Nat.mod_lt _ hB⟩ = c := by
        apply Fin.ext; simp only [bcol]; exact Nat.div_add_mod' c B
      rwa [hcc] at this
    · have := congrFun (congrFun e2 j) ⟨(c : ℕ) - k * B, by omega⟩
      simp only [Matrix.submatrix_apply, id] at this
      have hcc : rcol h ⟨(c : ℕ) - k * B, by omega⟩ = c := by
        apply Fin.ext; simp only [rcol]; omega
      rwa [hcc] at this
  calc (Finset.univ.filter (fun A : Matrix (Fin n) (Fin m) R => ∀ ℓ : Fin k, A.submatrix id (bcol h ℓ) ∈ Bad)).card
      ≤ ((Fintype.piFinset (fun _ : Fin k => Bad)) ×ˢ (Finset.univ : Finset (Matrix (Fin n) (Fin (m - k * B)) R))).card := by
        apply Finset.card_le_card_of_injOn φ
        · intro A hA
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hA
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Fintype.mem_piFinset, Finset.coe_univ,
            Set.mem_univ, and_true]
          exact hA
        · exact hinj.injOn
    _ = Bad.card ^ k * Fintype.card R ^ (n * (m - k * B)) := by
        rw [Finset.card_product, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Finset.card_univ]
        congr 1
        have : Fintype.card (Matrix (Fin n) (Fin (m - k * B)) R) = Fintype.card (Fin n → Fin (m - k * B) → R) :=
          Fintype.card_congr (Equiv.refl _)
        rw [this]
        simp [← pow_mul, mul_comm]

end T17M

end File_T17M_Prob2

section File_T17M_Prob3

/-! # Probability III: the non-surjective event -/

namespace T17M

open T17 F3SubsetSum

variable {q : ℕ} [Fact q.Prime]

theorem ceil_sq (n : ℕ) (hn : 0 < n) : ⌈500 * (n : ℝ) ^ 2 / ((n ^ 2 : ℕ) : ℝ)⌉₊ = 500 := by
  have : ((n ^ 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_pow, mul_div_assoc, div_self (by positivity), mul_one]
  simp

open Classical in
/-- Fraction of `A` with `Φ_{m, degD n m}` not surjective, in the main regime. -/
theorem nonsurj_bound (hq3 : 3 ≤ q) (n m : ℕ) (hn : 500 ≤ n) (hm : 500 * n ≤ m) :
    ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
        ¬ Function.Surjective (Phi (ZMod q) q (cols A) (degD n m))).card : ℝ) / (q : ℝ) ^ (n * m) ≤
      Real.exp (-(m : ℝ) / 800) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  rcases le_or_gt m (n ^ 2) with hle | hlt
  · rw [degD_ceil n m (by omega) hle]
    refine (theorem_4_12 q hq3 n m hm hle).trans ?_
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · rw [degD_big n m hlt]
    set B := n ^ 2
    set k := m / B
    have hB : 0 < B := by positivity
    have hk : 1 ≤ k := (Nat.le_div_iff_mul_le hB).2 (by omega)
    have hkB : k * B ≤ m := Nat.div_mul_le_self m B
    have hm2 : m < 2 * (k * B) := by
      have h1 := Nat.lt_mul_div_succ m hB
      have e : B * (m / B + 1) = k * B + B := by simp only [k]; ring
      have h2 : B ≤ k * B := Nat.le_mul_of_pos_left B hk
      omega
    set Bad := Finset.univ.filter fun A' : Matrix (Fin n) (Fin B) (ZMod q) =>
      ¬ Function.Surjective (Phi (ZMod q) q (cols A') 500)
    have hsub : (Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
        ¬ Function.Surjective (Phi (ZMod q) q (cols A) 500)) ⊆
        Finset.univ.filter (fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
          ∀ ℓ : Fin k, A.submatrix id (bcol hkB ℓ) ∈ Bad) := by
      intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bad] at hA ⊢
      intro ℓ hs
      exact hA (surj_of_sub q A 500 _ (bcol_inj hkB ℓ) hs)
    have hcount := (Finset.card_le_card hsub).trans (block_count hkB Bad)
    rw [ZMod.card] at hcount
    have h412 := theorem_4_12 q hq3 n B (by simp only [B]; rw [sq]; exact Nat.mul_le_mul_right n hn) le_rfl
    rw [show ⌈500 * (n : ℝ) ^ 2 / (B : ℝ)⌉₊ = 500 from ceil_sq n (by omega)] at h412
    -- Bad.card / q^(nB) ≤ exp(-B/400)
    have hbad : (Bad.card : ℝ) ≤ Real.exp (-(B : ℝ) / 400) * (q : ℝ) ^ (n * B) := by
      rwa [div_le_iff₀ (by positivity)] at h412
    have hcR : ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
        ¬ Function.Surjective (Phi (ZMod q) q (cols A) 500)).card : ℝ) ≤
        (Bad.card : ℝ) ^ k * (q : ℝ) ^ (n * (m - k * B)) := by exact_mod_cast hcount
    rw [div_le_iff₀ (by positivity)]
    refine hcR.trans ?_
    have hexp : n * m = n * B * k + n * (m - k * B) := by
      have e : m = k * B + (m - k * B) := by omega
      conv_lhs => rw [e]
      ring
    calc (Bad.card : ℝ) ^ k * (q : ℝ) ^ (n * (m - k * B))
        ≤ (Real.exp (-(B : ℝ) / 400) * (q : ℝ) ^ (n * B)) ^ k * (q : ℝ) ^ (n * (m - k * B)) := by
          gcongr
      _ = Real.exp (-(B : ℝ) / 400) ^ k * (q : ℝ) ^ (n * m) := by
          rw [mul_pow, hexp, pow_add, pow_mul]; ring
      _ ≤ Real.exp (-(m : ℝ) / 800) * (q : ℝ) ^ (n * m) := by
          gcongr
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.2
          have : (m : ℝ) < 2 * ((k : ℝ) * B) := by exact_mod_cast hm2
          nlinarith

end T17M

end File_T17M_Prob3

section File_T17M_Prob4

/-! # Probability IV: the failure probability of `DecF` -/

namespace T17M

open T17 F3SubsetSum

variable {q : ℕ} [Fact q.Prime] [NeZero q]

open Classical in
theorem failure_le (hq3 : 3 ≤ q) (N0 : ℕ) (hN0 : 500 ≤ N0) (n m : ℕ) (s : Fin n → ZMod q) (e : Fin m → Bool)
    (c1 : ℝ)
    (h16 : 1 - (2 : ℝ) ^ (-(c1 * m)) ≤
      ((Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) =>
        candidates A (lweSample A s e) = {s}).card : ℝ) / (q : ℝ) ^ (n * m)) :
    pointwiseFailure (DecF q N0) n m s e ≤
      (2 : ℝ) ^ (-(c1 * m)) + (if n < N0 ∨ m < 500 * n then 0 else Real.exp (-(m : ℝ) / 800)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) ^ (n * m) := by
    have : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    positivity
  set U := Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) => candidates A (lweSample A s e) = {s}
  set S : Finset (Matrix (Fin n) (Fin m) (ZMod q)) := if n < N0 ∨ m < 500 * n then ∅ else
    Finset.univ.filter fun A => ¬ Function.Surjective (Phi (ZMod q) q (cols A) (degD n m))
  set F := Finset.univ.filter fun A : Matrix (Fin n) (Fin m) (ZMod q) => DecF q N0 n m A (lweSample A s e) ≠ s
  have hsub : F ⊆ Uᶜ ∪ S := by
    intro A hA
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    by_contra hc
    simp only [Finset.mem_union, Finset.mem_compl, not_or, not_not] at hc
    obtain ⟨hU, hS⟩ := hc
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hU
    apply hA
    apply DecF_correct hq3 A _ s hU
    by_cases hreg : n < N0 ∨ m < 500 * n
    · exact Or.inl hreg
    · right
      simp only [S, if_neg hreg, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hS
      exact hS
  have hcard : (F.card : ℝ) ≤ (Uᶜ.card : ℝ) + (S.card : ℝ) := by
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact_mod_cast this
  have hUc : (Uᶜ.card : ℝ) = (q : ℝ) ^ (n * m) - U.card := by
    rw [Finset.card_compl]
    have : U.card ≤ Fintype.card (Matrix (Fin n) (Fin m) (ZMod q)) := Finset.card_le_univ U
    rw [Nat.cast_sub this]
    congr 1
    have : Fintype.card (Matrix (Fin n) (Fin m) (ZMod q)) = Fintype.card (Fin n → Fin m → ZMod q) :=
      Fintype.card_congr (Equiv.refl _)
    rw [this]; simp [← pow_mul, mul_comm]
  have hS : (S.card : ℝ) / (q : ℝ) ^ (n * m) ≤ (if n < N0 ∨ m < 500 * n then 0 else Real.exp (-(m : ℝ) / 800)) := by
    by_cases hreg : n < N0 ∨ m < 500 * n
    · simp [S, hreg]
    · simp only [S, if_neg hreg]
      push_neg at hreg
      exact nonsurj_bound hq3 n m (by omega) hreg.2
  unfold pointwiseFailure
  change (F.card : ℝ) / (q : ℝ) ^ (n * m) ≤ _
  calc (F.card : ℝ) / (q : ℝ) ^ (n * m) ≤ ((Uᶜ.card : ℝ) + S.card) / (q : ℝ) ^ (n * m) := by gcongr
    _ = (1 - (U.card : ℝ) / (q : ℝ) ^ (n * m)) + (S.card : ℝ) / (q : ℝ) ^ (n * m) := by
        rw [hUc, add_div, sub_div, div_self (ne_of_gt hq0)]
    _ ≤ _ := by linarith

end T17M

end File_T17M_Prob4

section File_T17M_Final

/-! # Theorem 1.7 -/

namespace T17M

open T17 F3SubsetSum

theorem length_unaryD (v : ℕ) : (unaryD v).length = v + 1 := by
  simp [unaryD, unary]

theorem length_flatMap_le {β : Type} (l : List β) (f : β → List Bool) (B : ℕ) (h : ∀ x ∈ l, (f x).length ≤ B) :
    (l.flatMap f).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := h x List.mem_cons_self
    have := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem encodeInstance_length {q n m : ℕ} [NeZero q] (A : Matrix (Fin n) (Fin m) (ZMod q)) (b : Fin m → ZMod q) :
    (encodeInstance A b).length ≤ n + m + 2 + q * (m * n + m) := by
  unfold encodeInstance
  simp only [List.length_append, length_unaryD]
  have h1 : ((List.finRange m).flatMap (fun i => (List.finRange n).flatMap (fun j => unaryD (A j i).val))).length
      ≤ m * (n * q) := by
    have := length_flatMap_le (List.finRange m)
      (fun i => (List.finRange n).flatMap (fun j => unaryD (A j i).val)) (n * q) (fun i _ => by
      have := length_flatMap_le (List.finRange n) (fun j => unaryD (A j i).val) q (fun j _ => by
        rw [length_unaryD]; exact ZMod.val_lt _)
      rwa [List.length_finRange] at this)
    rwa [List.length_finRange] at this
  have h2 : ((List.finRange m).flatMap (fun i => unaryD (b i).val)).length ≤ m * q := by
    have := length_flatMap_le (List.finRange m) (fun i => unaryD (b i).val) q (fun i _ => by
      rw [length_unaryD]; exact ZMod.val_lt _)
    rwa [List.length_finRange] at this
  have e : q * (m * n + m) = m * (n * q) + m * q := by ring
  omega

theorem one_lt_logb (q : ℕ) (hq : 3 ≤ q) : 1 < Real.logb ((q : ℝ) / 2) q := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 0 < Real.log ((q : ℝ) / 2) := Real.log_pos (by linarith)
  have h2 : Real.log ((q : ℝ) / 2) < Real.log q := Real.log_lt_log (by linarith) (by linarith)
  rw [Real.logb, lt_div_iff₀ h1]; linarith

theorem main_1_7 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (κ : ℝ)
    (hκ : Real.logb ((q : ℝ) / 2) q < κ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (Dec : DecoderFn q) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m →
        ComputesWithin M Dec n m ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ ∧
        ∀ (s : Fin n → ZMod q) (e : Fin m → Bool),
          pointwiseFailure Dec n m s e ≤ (2 : ℝ) ^ (-(c * m)) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hκ1 : 1 < κ := (one_lt_logb q hq).trans hκ
  obtain ⟨c1, hc1, h16⟩ := fact_1_6 q hq (κ - Real.logb ((q : ℝ) / 2) q) (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a := min (c1 * Real.log 2) (1 / 800) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by norm_num)
  set N0 := max 500 ⌈2 / a⌉₊
  obtain ⟨C, hC, hT⟩ := time_bound q N0 hq κ hκ1 (RR q N0)
  refine ⟨TMof (machineT q N0).machine, DecF q N0, C, a / (2 * Real.log 2), hC, by positivity, ?_⟩
  intro n m hn hm
  refine ⟨?_, ?_⟩
  · apply computes
    intro A b
    exact hT n m hn hm _ (encodeInstance_length A b)
  · intro s e
    have h16' := (h16 n m s e).1 (by rw [add_sub_cancel]; exact hm)
    have hf := failure_le hq N0 (le_max_left _ _) n m s e c1 h16'
    refine hf.trans ?_
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have e1 : (2 : ℝ) ^ (-(c1 * m)) ≤ Real.exp (-(a * m)) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      apply Real.exp_le_exp.2
      have : a ≤ c1 * Real.log 2 := min_le_left _ _
      nlinarith
    have e2 : (2 : ℝ) ^ (-(a / (2 * Real.log 2) * m)) = Real.exp (-(a * m) / 2) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1; field_simp
    rw [e2]
    have e3 : Real.exp (-(a * m)) ≤ Real.exp (-(a * m) / 2) := Real.exp_le_exp.2 (by nlinarith)
    split_ifs with hreg
    · linarith
    · push_neg at hreg
      obtain ⟨hnN, hmn⟩ := hreg
      have hnN' : (2 : ℝ) / a ≤ n := by
        have h1 : ⌈2 / a⌉₊ ≤ n := (le_max_right _ _).trans hnN
        exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
      have hnm : (n : ℝ) ≤ m := by
        have : n ≤ m := by omega
        exact_mod_cast this
      have ham : 2 ≤ a * m := by
        have := (div_le_iff₀ ha0).1 (hnN'.trans hnm); linarith
      have e4 : Real.exp (-(m : ℝ) / 800) ≤ Real.exp (-(a * m)) := by
        apply Real.exp_le_exp.2
        have : a ≤ 1 / 800 := min_le_right _ _
        nlinarith
      -- 2 exp(-am) ≤ exp(-am/2)
      have e5 : 2 * Real.exp (-(a * m)) ≤ Real.exp (-(a * m) / 2) := by
        have h1 : Real.exp (-(a * m)) = Real.exp (-(a * m) / 2) * Real.exp (-(a * m) / 2) := by
          rw [← Real.exp_add]; ring_nf
        have h2 : Real.exp (-(a * m) / 2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
        have h3 : Real.exp (-1) < 1 / 2 := by
          rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
          have := Real.exp_one_gt_d9; norm_num; linarith
        have h4 : 0 < Real.exp (-(a * m) / 2) := Real.exp_pos _
        rw [h1]; nlinarith
      linarith

end T17M

end File_T17M_Final

theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (κ : ℝ)
    (hκ : Real.logb ((q : ℝ) / 2) q < κ) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (Dec : F3SubsetSum.DecoderFn q) (C c : ℝ), 0 < C ∧ 0 < c ∧
      ∀ n m : ℕ, 1 ≤ n → κ * n ≤ m →
        F3SubsetSum.ComputesWithin M Dec n m ⌊((m : ℝ) / n) ^ (C * (⌈(n : ℝ) ^ 2 / m⌉ : ℝ))⌋₊ ∧
        ∀ (s : Fin n → ZMod q) (e : Fin m → Bool),
          F3SubsetSum.pointwiseFailure Dec n m s e ≤ (2 : ℝ) ^ (-(c * m)) :=
  T17M.main_1_7 q hq κ hκ
