-- Prove2me | solution 1 for F3SubsetSum.exhaustive_search_circuit
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-15T05:33:17.872543+00:00
-- url     : https://prove2.me/submissions/2d81e0aa-55a3-4809-b088-000c24bb68ec

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_SubsetSum
import Definitions.Def_F3SubsetSum_QutritCircuit


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

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace F3Generate
open F3Tools F3Search OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

abbrev EnumState := (Env × ℕ) × List (List Bool)

def expand (ss : List (List Bool)) := ss.map (false :: ·) ++ ss.map (true :: ·)
def enumBody (s : EnumState) : (Env × List (List Bool)) ⊕ EnumState :=
  if s.1.2 == 0 then .inl (s.1.1,s.2) else .inr ((s.1.1,s.1.2-1),expand s.2)

@[fun_prop] theorem expand_poly : Poly expand := by unfold expand; fun_prop

noncomputable def enumProgram : PolyProgram enc (encodeLoop enc enc) enumBody := by
  have hp : Poly (fun s : EnumState => s.1.2 == 0) := by fun_prop
  have hd : Poly (fun s : EnumState => (s.1.1,s.2)) := by fun_prop
  have hc : Poly (fun s : EnumState => ((s.1.1,s.1.2-1),expand s.2)) := by fun_prop
  exact (PolyProgram.ite hp.program
    (hc.program.comp (PolyProgram.injectRight enc enc))
    (hd.program.comp (PolyProgram.injectLeft enc enc))).congr _ (fun _ => rfl)

theorem expand_length (ss : List (List Bool)) : (expand ss).length = 2*ss.length := by simp [expand]; omega

theorem expand_members (ss : List (List Bool)) (d : ℕ) (h : ∀ s ∈ ss, s.length  ≤  d) :
    ∀ s ∈ expand ss, s.length  ≤  d+1 := by
  intro s hs
  simp only [expand,List.mem_append,List.mem_map] at hs
  rcases hs with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩ <;> simp only [List.length_cons] <;> exact Nat.add_le_add_right (h s hs) 1

theorem enc_lists_bound (ss : List (List Bool)) (d : ℕ) (h : ∀ s ∈ ss, s.length  ≤  d) :
    (enc ss).length  ≤  ss.length*(6*d+1) := by
  have hh := EncodedList.length_bound (enc : List Bool → List Bool) ss (3*d) (fun s hs => by
    rw [L3.enc_bool_length]
    nlinarith [h s hs])
  change (encodeList (enc : List Bool → List Bool) ss).length  ≤  _
  simpa only [show 2*(3*d)+1 = 6*d+1 by omega] using hh

theorem enum_run (w : Env) (k d : ℕ) (ss : List (List Bool)) (S : ℕ)
    (hd : ∀ s ∈ ss, s.length  ≤  d)
    (hS : 4*(enc w).length+2*k.size+3+2^k*ss.length*(6*(d+k)+1)  ≤  S) :
    BoundedRun enc enumBody S (k+1) ((w,k),ss) (w,(expand^[k]) ss) := by
  induction k generalizing d ss with
  | zero =>
    apply BoundedRun.stop
    · have henc := enc_lists_bound ss d hd
      simp only [L3.enc_pair_length,L3.enc_nat_length,Nat.size_zero] at ⊢
      simp only [pow_zero,Nat.size_zero,Nat.add_zero,one_mul] at hS
      omega
    · rfl
  | succ k ih =>
    have henc := enc_lists_bound ss d hd
    have hpow : 1  ≤  2^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hsize : (enc ((w,k+1),ss)).length  ≤  S := by
      simp only [L3.enc_pair_length,L3.enc_nat_length]
      have : ss.length*(6*d+1)  ≤  2^(k+1)*ss.length*(6*(d+(k+1))+1) :=
        Nat.mul_le_mul (by nlinarith) (by omega)
      omega
    have hnext : 4*(enc w).length+2*k.size+3+2^k*(expand ss).length*(6*(d+1+k)+1)  ≤  S := by
      have hnat := Nat.size_le_size (Nat.le_succ k)
      change k.size  ≤  (k+1).size at hnat
      rw [expand_length]
      have he : 2^k*(2*ss.length)*(6*(d+1+k)+1) = 2^(k+1)*ss.length*(6*(d+(k+1))+1) := by
        rw [pow_succ]; ring
      rw [← he] at hS
      omega
    have hr := BoundedRun.step (ea := enc) (f := enumBody)
      (a := ((w,k+1),ss)) (a' := ((w,k),expand ss)) hsize (by simp [enumBody])
      (ih (d+1) (expand ss) (expand_members ss d hd) hnext)
    simpa only [Function.iterate_succ_apply] using hr

theorem iterate_expand (m : ℕ) : (expand^[m]) [[]] = bits m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply',ih]; rfl

end F3Generate

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

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Stages
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial

def budget (n m : ℕ) := n+m+2^m+1

structure Stage (ea eb : ℕ → ℕ → List Bool) where
  machine : Machine
  time : Polynomial ℕ
  outputSize : Polynomial ℕ
  length_bound : ∀ n m, (eb n m).length  ≤  outputSize.eval (budget n m)
  run : ∀ n m, ∃ t, t  ≤  time.eval (budget n m) ∧
    Trace machine.step t (machine.initialCfg (ea n m)) (machine.finalCfg (eb n m))

noncomputable def Stage.then {ea eb ec : ℕ → ℕ → List Bool} (A : Stage ea eb) (B : Stage eb ec) :
    Stage ea ec where
  machine := Compose.machine A.machine B.machine
  time := A.time+2*A.outputSize+2+B.time
  outputSize := B.outputSize
  length_bound := B.length_bound
  run n m := by
    obtain ⟨t,ht,tr⟩ := A.run n m
    obtain ⟨u,hu,ur⟩ := B.run n m
    refine ⟨_,?_,Compose.run A.machine B.machine tr ur⟩
    have hl := A.length_bound n m
    simp only [eval_add,eval_mul,eval_ofNat]
    omega

noncomputable def Stage.ofPoly {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) (a : ℕ → ℕ → α) (S : Polynomial ℕ)
    (hS : ∀ n m, (ea (a n m)).length  ≤  S.eval (budget n m)) :
    Stage (fun n m => ea (a n m)) (fun n m => eb (f (a n m))) where
  machine := P.machine
  time := P.time.comp S
  outputSize := P.sizeBound.comp S
  length_bound n m := by
    rw [eval_comp]
    exact (P.length_bound (a n m)).trans (polynomial_eval_mono _ (hS n m))
  run n m := by
    have hp := P.outputs (a n m)
    refine ⟨hp.steps,?_,Trace.of_iterate hp.evals_in_steps⟩
    rw [eval_comp]
    exact hp.steps_le_m.trans (polynomial_eval_mono _ (hS n m))

noncomputable def Stage.recode {ea eb ec ed : ℕ → ℕ → List Bool} (P : Stage ea eb)
    (ha : ∀ n m, ea n m = ec n m) (hb : ∀ n m, eb n m = ed n m) : Stage ec ed where
  machine := P.machine
  time := P.time
  outputSize := P.outputSize
  length_bound n m := by rw [← hb]; exact P.length_bound n m
  run n m := by rw [← ha,← hb]; exact P.run n m

noncomputable def Stage.ofLoop {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β ⊕ α} (P : PolyProgram ea (encodeLoop ea eb) f)
    (a : ℕ → ℕ → α) (b : ℕ → ℕ → β) (N S A : Polynomial ℕ)
    (ha : ∀ n m, (ea (a n m)).length  ≤  A.eval (budget n m))
    (hr : ∀ n m, ∃ k s, k  ≤  N.eval (budget n m) ∧ s  ≤  S.eval (budget n m) ∧
      BoundedRun ea f s k (a n m) (b n m)) :
    Stage (fun n m => ea (a n m)) (fun n m => eb (b n m)) := by
  let M := Loop.machine P.machine
  let R := N*(P.time.comp S+2*P.sizeBound.comp S+3)
  refine ⟨M,R,A+R*C M.growth,?_,?_⟩
  · intro n m
    obtain ⟨k,s,hk,hs,hrun⟩ := hr n m
    obtain ⟨t,ht,tr⟩ := P.run_loop hrun
    have hb : t  ≤  R.eval (budget n m) := by
      have hmono : P.passTime s  ≤  P.passTime (S.eval (budget n m)) := by
        unfold PolyProgram.passTime
        exact Nat.add_le_add_right (Nat.add_le_add (polynomial_eval_mono _ hs)
          (Nat.mul_le_mul_left 2 (polynomial_eval_mono _ hs))) 3
      have hbound := ht.trans (Nat.mul_le_mul hk hmono)
      simpa [R,PolyProgram.passTime] using hbound
    have hout := M.output_length (show Turing.TM2OutputsInTime M.tm (ea (a n m))
        (some (eb (b n m))) t from ⟨⟨t,tr.iterate_eq⟩,le_rfl⟩)
    have hinput := ha n m
    simp only [eval_add,eval_mul,eval_C]
    exact hout.trans (Nat.add_le_add hinput (Nat.mul_le_mul_right M.growth hb))
  · intro n m
    obtain ⟨k,s,hk,hs,hrun⟩ := hr n m
    obtain ⟨t,ht,tr⟩ := P.run_loop hrun
    refine ⟨t,?_,tr⟩
    have hmono : P.passTime s  ≤  P.passTime (S.eval (budget n m)) := by
      unfold PolyProgram.passTime
      exact Nat.add_le_add_right (Nat.add_le_add (polynomial_eval_mono _ hs)
        (Nat.mul_le_mul_left 2 (polynomial_eval_mono _ hs))) 3
    have hbound := ht.trans (Nat.mul_le_mul hk hmono)
    simpa [R,PolyProgram.passTime] using hbound

end F3Stages

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Generate
open F3Tools F3Search F3SubsetSum F3Stages OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic Polynomial

def enumStart (w : Env) : EnumState := ((w,L3.inputM w),[[]])
@[fun_prop] theorem enumStart_poly : Poly enumStart := by unfold enumStart; fun_prop
noncomputable def startProgram : PolyProgram id enc enumStart :=
  BooleanLists.packProgram.comp enumStart_poly.program

def enumInput (n m : ℕ) : List Bool := enc (((word n m,m),[[]]) : EnumState)
def enumOutput (n m : ℕ) : List Bool := enc (word n m,bits m)

theorem word_length (n m : ℕ) : (word n m).length = n+m+1 := by simp [word,unaryD,unary]; omega

theorem budget_bounds (n m : ℕ) : n  ≤  budget n m ∧ m  ≤  budget n m ∧ 2^m  ≤  budget n m ∧ 1  ≤  budget n m := by
  have hpow : 1  ≤  (2:ℕ)^m := Nat.one_le_pow m 2 (by decide)
  dsimp [budget]
  omega

theorem word_budget (n m : ℕ) : (word n m).length  ≤  budget n m := by
  rw [word_length]
  exact Nat.add_le_add_right (Nat.le_add_right (n+m) (2^m)) 1

noncomputable def stageStart : Stage word enumInput :=
  (Stage.ofPoly startProgram word X (fun n m => by rw [eval_X]; exact word_budget n m)).recode
    (fun _ _ => rfl) (fun n m => by simp only [enumStart,show L3.inputM (word n m) = m from L3.inputM_word n m]; rfl)

noncomputable def stageEnum : Stage enumInput enumOutput :=
  Stage.ofLoop enumProgram (fun n m => ((word n m,m),[[]])) (fun n m => (word n m,bits m))
    (X+1) (100*(X+1)^2) stageStart.outputSize stageStart.length_bound (by
      intro n m
      let S := 4*(enc (word n m)).length+2*m.size+3+2^m*(6*m+1)
      have hr := enum_run (word n m) m 0 [[]] S (by simp) (by dsimp [S]; simp)
      refine ⟨m+1,S,?_,?_,?_⟩
      · simp only [eval_add,eval_X,eval_one]
        have := (budget_bounds n m).2.1
        omega
      · have hb := budget_bounds n m
        have hm : m.size  ≤  m+1 := by simpa only [L3.enc_nat_length] using nat_enc_bound m m le_rfl
        have hw : (enc (word n m)).length  ≤  3*budget n m := by
          rw [L3.enc_bool_length]
          exact Nat.mul_le_mul_left 3 (word_budget n m)
        have hprod : 2^m*(6*m+1)  ≤  budget n m*(6*budget n m+1) :=
          Nat.mul_le_mul hb.2.2.1 (by nlinarith [hb.2.1])
        simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
        dsimp [S]
        nlinarith only [hm,hw,hprod,hb.2.1]
      · simpa only [Nat.zero_add,mul_one,iterate_expand] using hr)

noncomputable def enumeration : Stage word enumOutput := stageStart.then stageEnum

def codeInit (x : Env × List (List Bool)) : LoopState :=
  let c := outputCode x.1 x.2
  ((x.1,c),(c,(([],L3.inputN x.1*L3.inputM x.1+L3.inputM x.1+1),[])))

@[fun_prop] theorem codeInit_poly : Poly codeInit := by unfold codeInit; fun_prop

def compileInput (n m : ℕ) :=
  enc (((word n m,code n m),(code n m,(([],base n m),[]))) : LoopState)
def compileOutput (n m : ℕ) := enc ((word n m,code n m),compiled n m)

noncomputable def stageCode : Stage enumOutput compileInput :=
  (Stage.ofPoly codeInit_poly.program (fun n m => (word n m,bits m)) enumeration.outputSize
    enumeration.length_bound).recode (fun _ _ => rfl) (fun n m => by
      simp only [codeInit,outputCode_word,
        show L3.inputN (word n m) = n from L3.inputN_word n m,
        show L3.inputM (word n m) = m from L3.inputM_word n m]
      rfl)

/-- Bound the code length and the preserved environment by the actual machine input length. -/
theorem compile_input_bounds (n m : ℕ) :
    (code n m).length  ≤  (compileInput n m).length ∧
    (enc (word n m,code n m)).length  ≤  (compileInput n m).length := by
  have hc := EncodedList.length_le (enc : Token → List Bool) (code n m)
  change (code n m).length  ≤  (enc (code n m)).length at hc
  unfold compileInput
  simp only [L3.enc_pair_length]
  constructor <;> omega

noncomputable def compileM : Polynomial ℕ := (X+1)^2+2*stageCode.outputSize+5
noncomputable def compileS : Polynomial ℕ :=
  10*stageCode.outputSize+200*(compileM+1)*(stageCode.outputSize+1)

noncomputable def stageCompile : Stage compileInput compileOutput :=
  Stage.ofLoop compileProgram
    (fun n m => ((word n m,code n m),(code n m,(([],base n m),[]))))
    (fun n m => ((word n m,code n m),compiled n m))
    (stageCode.outputSize+1) compileS stageCode.outputSize stageCode.length_bound (by
      intro n m
      let L := (code n m).length
      let M := base n m+2*L+5
      let e := (word n m,code n m)
      let S := 10*(enc e).length+200*(M+1)*(L+1)
      have hI : L3.inputN e.1*L3.inputM e.1 = n*m := by
        change L3.inputN (word n m)*L3.inputM (word n m) = n*m
        rw [show L3.inputN (word n m) = n from L3.inputN_word n m,
          show L3.inputM (word n m) = m from L3.inputM_word n m]
      have hr := compile_run e (code n m) (([],base n m),[]) M L
        (by dsimp [M]; omega)
        (by rw [hI]; dsimp [base]; omega)
        (code_numbers n m M (by dsimp [M,base]; omega) (by dsimp [M]; omega))
        (by simp) (by simp) (by dsimp [M,L]; omega) (by dsimp [L]; simp) (by dsimp [L]; simp)
      rw [hI] at hr
      refine ⟨L+1,S,?_,?_,hr⟩
      · simp only [eval_add,eval_one]
        have hl := (compile_input_bounds n m).1.trans (stageCode.length_bound n m)
        dsimp [L]
        omega
      · have he := (compile_input_bounds n m).2.trans (stageCode.length_bound n m)
        have hl := (compile_input_bounds n m).1.trans (stageCode.length_bound n m)
        have hb := budget_bounds n m
        have hbase : base n m  ≤  (budget n m+1)^2 := by
          dsimp [base]
          have hp := Nat.mul_le_mul hb.1 hb.2.1
          nlinarith only [hp,hb.2.1]
        have hM : M  ≤  compileM.eval (budget n m) := by
          simp only [compileM,eval_add,eval_pow,eval_X,eval_one,eval_mul,eval_ofNat]
          dsimp [M,L]
          omega
        unfold compileS
        simp only [eval_add,eval_mul,eval_ofNat,eval_one]
        dsimp [S,e]
        exact Nat.add_le_add (Nat.mul_le_mul_left 10 he)
          (Nat.mul_le_mul (Nat.mul_le_mul_left 200 (Nat.add_le_add_right hM 1)) (Nat.add_le_add_right hl 1)))

noncomputable def finishProgram : PolyProgram enc id serialize :=
  serialize_poly.program.comp BooleanLists.unpackProgram

noncomputable def stageFinish : Stage compileOutput (fun n m => encodeCircuit (circuit n m)) :=
  (Stage.ofPoly finishProgram (fun n m => ((word n m,code n m),compiled n m)) stageCompile.outputSize
    stageCompile.length_bound).recode (fun _ _ => rfl) (fun n m => serialize_correct n m)

noncomputable def whole : Stage word (fun n m => encodeCircuit (circuit n m)) :=
  (((enumeration.then stageCode).then stageCompile).then stageFinish)

end F3Generate

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace F3Generate
open F3Tools F3Search F3SubsetSum F3Stages OAI.MetricKMedian.Binary Polynomial

theorem encodeGate_nonempty {W : ℕ} (g : Gate W) : 1  ≤  (encodeGate g).length := by
  cases g <;> simp [encodeGate] <;> omega

theorem gates_code_length {W : ℕ} (gs : List (Gate W)) : gs.length  ≤  (gs.flatMap encodeGate).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have := encodeGate_nonempty g
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    omega

theorem circuit_code_bounds (C : Circuit) :
    C.wires  ≤  (encodeCircuit C).length ∧ C.gates.length  ≤  (encodeCircuit C).length := by
  have hg := gates_code_length C.gates
  simp only [encodeCircuit,List.length_append,List.length_replicate,List.length_singleton]
  omega

theorem polynomial_power_bound (P : Polynomial ℕ) :
    ∃ C : ℕ, ∀ x : ℕ, 1  ≤  x → P.eval x  ≤  C*x^C := by
  have hP (x : ℕ) (hx : 1  ≤  x) : P.eval x  ≤  P.eval 1*x^P.natDegree := by
    rw [eval_eq_sum_range,eval_eq_sum_range,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [one_pow,mul_one]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by
      have := Finset.mem_range.mp hi
      omega))
  refine ⟨P.eval 1+P.natDegree+1,?_⟩
  intro x hx
  exact (hP x hx).trans
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hx (by omega)))

noncomputable def aux : Turing.TM2ComputableAux Bool Bool :=
  ⟨whole.machine.tm,Equiv.refl _,Equiv.refl _⟩

theorem generated (n m : ℕ) :
    HMBinPacking.OutputsWithin aux (word n m) (encodeCircuit (circuit n m))
      (whole.time.eval (budget n m)) := by
  obtain ⟨t,ht,tr⟩ := whole.run n m
  have hw : (word n m).map (⇑(Equiv.refl Bool).symm) = word n m := List.map_id _
  have ho : (encodeCircuit (circuit n m)).map (⇑(Equiv.refl Bool).symm) = encodeCircuit (circuit n m) := List.map_id _
  change Nonempty (Turing.TM2OutputsInTime whole.machine.tm
    ((word n m).map (⇑(Equiv.refl Bool).symm))
    (some ((encodeCircuit (circuit n m)).map (⇑(Equiv.refl Bool).symm))) _)
  rw [hw,ho]
  exact ⟨⟨⟨t,tr.iterate_eq⟩,ht⟩⟩

theorem outputs_mono {M : Turing.TM2ComputableAux Bool Bool} {w out : List Bool} {t u : ℕ}
    (h : HMBinPacking.OutputsWithin M w out t) (hle : t  ≤  u) :
    HMBinPacking.OutputsWithin M w out u := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo,h.steps_le_m.trans hle⟩⟩

end F3Generate

open F3SubsetSum in
theorem solution :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → Circuit) (C : ℕ),
      ∀ n m : ℕ,
        HMBinPacking.OutputsWithin G (unaryD n ++ unary m) (encodeCircuit (circ n m))
            (C * (n + m + 2 ^ m + 1) ^ C) ∧
          n * m + m  ≤  (circ n m).wires ∧
          (circ n m).gates.length  ≤  C * (n + m + 2 ^ m + 1) ^ C ∧
          (circ n m).wires  ≤  C * (n + m + 2 ^ m + 1) ^ C ∧
          probSolvable n m  ≤  successProb n m (circ n m) := by
  obtain ⟨C,hC⟩ := F3Generate.polynomial_power_bound (F3Generate.whole.time+F3Generate.whole.outputSize)
  refine ⟨F3Generate.aux,F3Search.circuit,C,?_⟩
  intro n m
  have hbound := hC (F3Stages.budget n m) (F3Generate.budget_bounds n m).2.2.2
  simp only [Polynomial.eval_add] at hbound
  have ht : F3Generate.whole.time.eval (F3Stages.budget n m)  ≤  C*(F3Stages.budget n m)^C := by omega
  have hs : F3Generate.whole.outputSize.eval (F3Stages.budget n m)  ≤  C*(F3Stages.budget n m)^C := by omega
  have hlen := (F3Generate.whole.length_bound n m).trans hs
  have hcodes := F3Generate.circuit_code_bounds (F3Search.circuit n m)
  have hwidth := (F3Search.compiled_shape n m).2.1
  refine ⟨F3Generate.outputs_mono (F3Generate.generated n m) ht,?_,hcodes.2.trans hlen,hcodes.1.trans hlen,F3Search.success_bound n m⟩
  change n*m+m  ≤  (F3Search.compiled n m).1.2
  dsimp [F3Search.base] at hwidth
  omega

#print axioms solution
