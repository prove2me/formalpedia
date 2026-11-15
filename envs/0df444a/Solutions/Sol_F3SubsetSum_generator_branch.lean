-- Prove2me | solution 1 for F3SubsetSum.generator_branch
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-15T04:20:28.595415+00:00
-- url     : https://prove2.me/submissions/e64a20d2-3caf-471d-82c2-88c67fb10f2d

/-
Proof of F3SubsetSum.generator_branch.
The construction preprocesses the unary dimensions, writes the clock only in the
large branch, dispatches to the chosen supplied machine, and restores a clean
halting configuration. The arbitrary-machine composition and growth lemmas
retain their original Prove2Me provenance below.
-/
import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_HMBinPacking_OutputsWithin



set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true


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

end L3





/-! # Machines with explicit (non-polynomial) running times -/

namespace L3

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

end L3


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true

-- General TM2 composition and output-length bounds reused from marwahaha,
-- Prove2Me submission 70c7eb16-aa64-45fc-9619-d6fd621972a7, Apache-2.0.
-- https://prove2.me/theorems/5b3ff7b0-a6cd-4c33-b40a-6fd6334ba249


set_option autoImplicit true

open Turing

/-!
# Core of a general composition lemma for `Turing.TM2ComputableInPolyTime`

Given two machines `tm₁`, `tm₂` we build the stack/key/state packaging in which `tm₁` and `tm₂` can
run inside one machine:

* `Key := tm₁.K ⊕ (tm₂.K ⊕ Unit)` — the two machines' stacks plus one temporary stack (used to
  reverse the copied word, because stacks are LIFO);
* `Gam` — the corresponding (dependent) stack alphabets;
* `Lab := tm₁.Λ ⊕ (Unit ⊕ tm₂.Λ)` — the two label sets plus a copy-phase label;
* `Sta := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))` — both internal states plus a one-symbol buffer.

`tr₁`/`tr₂` push each machine's statements through this packaging, and `stepAux_tr₁`/`stepAux_tr₂`
are the exact one-step commutation lemmas: one composite step simulates one step of the machine.
-/

namespace Turing

/-- Once a deterministic step function has halted, iterating it stays at `none`. -/
theorem iterate_none {α : Type*} (f : α → Option α) : ∀ m : ℕ,
    (flip bind f)^[m] (none : Option α) = none
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none f m

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Stack index type of the composite. -/
abbrev Key : Type := tm₁.K ⊕ (tm₂.K ⊕ Unit)

/-- Stack alphabets of the composite. -/
abbrev Gam : Key tm₁ tm₂ → Type
  | .inl a => tm₁.Γ a
  | .inr (.inl b) => tm₂.Γ b
  | .inr (.inr _) => tm₂.Γ tm₂.k₀

/-- Label type of the composite: machine 1's labels, machine 2's labels, and one copy-phase label
(stored as `Unit`). -/
abbrev Lab : Type := tm₁.Λ ⊕ (Fin 2 ⊕ tm₂.Λ)

/-- Internal state of the composite: both machines' states plus a one-symbol buffer. -/
abbrev Sta : Type := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))

/-- The stack contents of the composite as a dependent function. -/
def pack (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) : (k : Key tm₁ tm₂) → List (Gam tm₁ tm₂ k)
  | .inl a => S₁ a
  | .inr (.inl b) => S₂ b
  | .inr (.inr _) => T

theorem pack_update_left (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inl k) x
      = pack tm₁ tm₂ (Function.update S₁ k x) S₂ T := by
  funext j
  rcases j with a | (b | u)
  · by_cases h : a = k
    · subst h; simp [pack]
    · simp only [pack, Function.update_of_ne (by simp [h] : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inl k),
        Function.update_of_ne h]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inl k)]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inl k)]

theorem pack_update_right (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inl k)) x
      = pack tm₁ tm₂ S₁ (Function.update S₂ k x) T := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]
  · by_cases h : b = k
    · subst h; simp [pack]
    · have hne : ¬ ((Sum.inr (Sum.inl b) : Key tm₁ tm₂) = Sum.inr (Sum.inl k)) :=
        fun hh => h (by simpa using hh)
      rw [Function.update_of_ne (a := Sum.inr (Sum.inl b)) (a' := Sum.inr (Sum.inl k))
            (v := x) (f := pack tm₁ tm₂ S₁ S₂ T) hne]
      simp only [pack, Function.update_of_ne (a := b) (a' := k) (v := x) (f := S₂) h]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]

theorem pack_update_tmp (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : List (tm₂.Γ tm₂.k₀)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inr ())) x
      = pack tm₁ tm₂ S₁ S₂ x := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack]
    congr 1
    cases u
    rfl

/-- Label translation for machine 1: its own labels, and its halting label is turned into a jump to
the copy phase. -/
def lab₁ : Option tm₁.Λ → Option (Lab tm₁ tm₂)
  | none => some (Sum.inr (Sum.inl 0))
  | some l => some (Sum.inl l)

/-- Label translation for machine 2: its halting label stays a halting label. -/
def lab₂ : Option tm₂.Λ → Option (Lab tm₁ tm₂)
  | none => none
  | some l => some (Sum.inr (Sum.inr l))

/-- Reindex machine 1's statements into the composite. -/
def tr₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inl k) (fun s => g s.1) (tr₁ q)
  | .peek k g q => .peek (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .pop k g q => .pop (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .load g q => .load (fun s => (g s.1, s.2)) (tr₁ q)
  | .branch g q r => .branch (fun s => g s.1) (tr₁ q) (tr₁ r)
  | .goto g => .goto (fun s => Sum.inl (g s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inl 0))

/-- Reindex machine 2's statements into the composite. -/
def tr₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inr (Sum.inl k)) (fun s => g s.2.1) (tr₂ q)
  | .peek k g q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .pop k g q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .load g q => .load (fun s => (s.1, (g s.2.1, s.2.2))) (tr₂ q)
  | .branch g q r => .branch (fun s => g s.2.1) (tr₂ q) (tr₂ r)
  | .goto g => .goto (fun s => Sum.inr (Sum.inr (g s.2.1)))
  | .halt => .halt

theorem stepAux_tr₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₁ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₁ tm₁ tm₂ (TM2.stepAux q v₁ S₁).l,
          ((TM2.stepAux q v₁ S₁).var, v₂, b),
          pack tm₁ tm₂ (TM2.stepAux q v₁ S₁).stk S₂ T⟩ := by
  induction q generalizing v₁ S₁ with
  | push k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₁
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₁, TM2.stepAux, lab₁]
  | halt => simp only [tr₁, TM2.stepAux, lab₁]

theorem stepAux_tr₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₂ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₂ tm₁ tm₂ (TM2.stepAux q v₂ S₂).l,
          (v₁, ((TM2.stepAux q v₂ S₂).var, b)),
          pack tm₁ tm₂ S₁ (TM2.stepAux q v₂ S₂).stk T⟩ := by
  induction q generalizing v₂ S₂ with
  | push k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₂
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₂, TM2.stepAux, lab₂]
  | halt => simp only [tr₂, TM2.stepAux, lab₂]
end CompCore

end Turing


namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Program of the composite: machine 1's code, the copy phase, then machine 2's code. -/
def compCode (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl _) => copy
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

/-- The composite step function. -/
def compStep (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) →
      Option (TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :=
  TM2.step (compCode tm₁ tm₂ copy)

/-- Embed machine 1's configuration into the composite. -/
def cfg₁ (c : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₁ tm₁ tm₂ c.l, (c.var, v₂, b), pack tm₁ tm₂ c.stk S₂ T⟩

theorem step_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ}
    (h : tm₁.step c = some c') :
    TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T) := by
  obtain ⟨l, v₁, S₁⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₁.m l) v₁ S₁ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₁, lab₁, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₁]

/-- Run lifting for machine 1: any `m`-step run of `tm₁` is an `m`-step run of the composite. -/
theorem iterate_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ),
      (flip bind tm₁.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
        = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₁.step) (some c) = tm₁.step c from rfl] at h
      cases hstep : tm₁.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
                = TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) from rfl,
              step_cfg₁ tm₁ tm₂ M hM v₂ b S₂ T hstep]
          exact iterate_cfg₁ M hM v₂ b S₂ T m d c' h

/-- Embed machine 2's configuration into the composite. -/
def cfg₂ (c : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₂ tm₁ tm₂ c.l, (v₁, (c.var, b)), pack tm₁ tm₂ S₁ c.stk T⟩

theorem step_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ}
    (h : tm₂.step c = some c') :
    TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T) := by
  obtain ⟨l, v₂, S₂⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₂.m l) v₂ S₂ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₂, lab₂, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₂]

/-- Run lifting for machine 2. -/
theorem iterate_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ),
      (flip bind tm₂.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
        = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₂.step) (some c) = tm₂.step c from rfl] at h
      cases hstep : tm₂.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
                = TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) from rfl,
              step_cfg₂ tm₁ tm₂ M hM v₁ b S₁ T hstep]
          exact iterate_cfg₂ M hM v₁ b S₁ T m d c' h

end CompCore

end Turing


namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)
variable {βΓ : Type} [Inhabited βΓ]

/-- Copy pass 1: move `tm₁`'s output stack onto the temporary stack, through the two alphabets'
equivalences (this pass reverses the word, since stacks are LIFO). -/
def copyStmt₁ (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  .pop (Sum.inl tm₁.k₁) (fun v o => (v.1, (v.2.1, o.map (fun x => ia₂.invFun (oa₁ x)))))
    (.branch (fun v => v.2.2.isSome)
      (.push (Sum.inr (Sum.inr ()))
        (fun v => (v.2.2).getD (ia₂.invFun default))
        (.goto (fun _ => Sum.inr (Sum.inl 0))))
      (.goto (fun _ => Sum.inr (Sum.inl 1))))

/-- Copy pass 2: move the temporary stack onto `tm₂`'s input stack, restoring the order. -/
def copyStmt₂ (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  .pop (Sum.inr (Sum.inr ())) (fun v o => (v.1, (v.2.1, o)))
    (.branch (fun v => v.2.2.isSome)
      (.push (Sum.inr (Sum.inl tm₂.k₀))
        (fun v => (v.2.2).getD (ia₂.invFun default))
        (.goto (fun _ => Sum.inr (Sum.inl 1))))
      (.goto (fun _ => Sum.inr (Sum.inr tm₂.main))))

/-- The composite program: `tm₁`'s code, the two copy passes, `tm₂`'s code. -/
def compProg (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl 0) => copyStmt₁ tm₁ tm₂ oa₁ ia₂
  | .inr (.inl 1) => copyStmt₂ tm₁ tm₂ ia₂
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

theorem compProg_inl (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) (l : tm₁.Λ) :
    compProg tm₁ tm₂ oa₁ ia₂ (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l) := rfl

theorem compProg_inr_inr (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (l : tm₂.Λ) :
    compProg tm₁ tm₂ oa₁ ia₂ (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l) := rfl

/-- One step of copy pass 1 on a nonempty source stack. -/
theorem step_copy₁_some (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : tm₁.Γ tm₁.k₁) (xs : List (tm₁.Γ tm₁.k₁)) (hS₁ : S₁ tm₁.k₁ = x :: xs) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 0)), (v.1, (v.2.1, some (ia₂.invFun (oa₁ x)))),
          pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ xs) S₂
            (ia₂.invFun (oa₁ x) :: T)⟩ := by
  simp only [compProg, copyStmt₁, TM2.step, TM2.stepAux, hS₁, Option.map_some,
    Option.isSome_some, Option.getD_some, cond_true, List.head?_cons, List.tail_cons,
    pack, pack_update_left, pack_update_tmp, pack_update_right]

/-- One step of copy pass 1 on an empty source stack. -/
theorem step_copy₁_nil (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (hS₁ : S₁ tm₁.k₁ = []) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ S₂ T⟩ := by
  have hupd : Function.update S₁ tm₁.k₁ ([] : List (tm₁.Γ tm₁.k₁)) = S₁ := by
    rw [← hS₁]; exact Function.update_eq_self _ _
  rw [← hupd]
  simp [compProg, copyStmt₁, TM2.step, TM2.stepAux, pack, pack_update_tmp, pack_update_right,
    pack_update_left]

/-- One step of copy pass 2 on a nonempty temporary stack. -/
theorem step_copy₂_some (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : tm₂.Γ tm₂.k₀) (xs : List (tm₂.Γ tm₂.k₀)) (hT : T = x :: xs) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, some x)),
          pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀)) xs⟩ := by
  subst hT
  simp [compProg, copyStmt₂, TM2.step, TM2.stepAux, pack, pack_update_tmp, pack_update_right,
    pack_update_left]

/-- One step of copy pass 2 on an empty temporary stack: the composite enters `tm₂`. -/
theorem step_copy₂_nil (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (v : Sta tm₁ tm₂) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) (hT : T = []) :
    TM2.step (compProg tm₁ tm₂ oa₁ ia₂) ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ T⟩
      = some ⟨some (Sum.inr (Sum.inr tm₂.main)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ S₂ T⟩ := by
  subst hT
  simp only [compProg, copyStmt₂, TM2.step, TM2.stepAux, List.head?_nil, Option.map_none,
    Option.isSome_none, Bool.false_eq_true, cond_false, pack]
  rw [show ([] : List (tm₂.Γ tm₂.k₀)).tail = [] from rfl, pack_update_tmp]

end CompCore

end Turing

namespace Turing

namespace CompCore

variable (tm₁ : FinTM2) (tm₂ : FinTM2)
variable {βΓ : Type} [Inhabited βΓ]



end CompCore

end Turing




open StateTransition
namespace QMCExit
variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ σ : Type*}
def EvalsToInTime.trans' {α : Type*} {f : α → Option α} {a b : α} {c : Option α} {m₁ m₂ : ℕ}
    (h₁ : EvalsToInTime f a (some b) m₁) (h₂ : EvalsToInTime f b c m₂) :
    EvalsToInTime f a c (m₂ + m₁) :=
  EvalsToInTime.trans f m₁ m₂ a b c h₁ h₂

def EvalsToInTime.mono {α : Type*} {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

def EvalsToInTime.congr_cfg {α : Type*} {f : α → Option α} {a a' : α} {b b' : Option α} {m : ℕ}
    (ha : a = a') (hb : b = b') (h : EvalsToInTime f a b m) : EvalsToInTime f a' b' m := by
  subst ha; subst hb; exact h

theorem flip_bind_step (M : Λ → Turing.TM2.Stmt Γ Λ σ) (c : Turing.TM2.Cfg Γ Λ σ) :
    (flip bind (Turing.TM2.step M)) c = Turing.TM2.step M c := by
  rcases c with ⟨l, v, S⟩
  cases l <;> rfl

def tm2OutputsInTime_of_cfg {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {out : List (tm.Γ tm.k₁)} {n : ℕ} {c : tm.Cfg}
    (h : EvalsToInTime (Turing.TM2.step tm.m) (Turing.initList tm l) (some c) n)
    (hc : c = Turing.haltList tm out) : Turing.TM2OutputsInTime tm l (some out) n := by
  subst c
  unfold Turing.TM2OutputsInTime
  exact h

def initStacks (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) : ∀ k, List (tm.Γ k) :=
  fun k => @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀)
    (fun h => by rw [h]; exact l) fun _ => []

def haltStacks (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) : ∀ k, List (tm.Γ k) :=
  fun k => @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁)
    (fun h => by rw [h]; exact out) fun _ => []

@[simp] theorem initStacks_k0 (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) :
    initStacks tm l tm.k₀ = l := by
  simp [initStacks]

@[simp] theorem haltStacks_k1 (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) :
    haltStacks tm out tm.k₁ = out := by
  simp [haltStacks]

@[simp] theorem initList_stk (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀)) (k : tm.K) :
    (Turing.initList tm l).stk k = initStacks tm l k := rfl

@[simp] theorem haltList_stk (tm : Turing.FinTM2) (out : List (tm.Γ tm.k₁)) (k : tm.K) :
    (Turing.haltList tm out).stk k = haltStacks tm out k := rfl


end QMCExit
namespace Turing

namespace CompCore

variable {tm₁ : FinTM2} {tm₂ : FinTM2}
variable {βΓ : Type} [Inhabited βΓ]
/-- **Copy pass 1, whole word** (`EvalsToInTime` form): moves `L` from `tm₁`'s output stack onto the
temporary stack through the two alphabets' equivalences (reversing it) in `|L| + 1` steps. -/
noncomputable def copy₁_trace (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    ∀ (L : List (tm₁.Γ tm₁.k₁)) (v : Sta tm₁ tm₂)
      (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
      (T : List (tm₂.Γ tm₂.k₀)), S₁ tm₁.k₁ = L →
      EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
        ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
        (some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ []) S₂
            ((L.map (fun x => ia₂.invFun (oa₁ x))).reverse ++ T)⟩) (L.length + 1)
  | [], v, S₁, S₂, T, hL => by
      have hupd : Function.update S₁ tm₁.k₁ ([] : List (tm₁.Γ tm₁.k₁)) = S₁ := by
        rw [← hL]; exact Function.update_eq_self _ _
      rw [hupd]
      have hstep := step_copy₁_nil tm₁ tm₂ oa₁ ia₂ v S₁ S₂ T hL
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      refine ⟨⟨1, ?_⟩, by simp⟩
      rw [Function.iterate_one, this]
      exact hstep
  | x :: xs, v, S₁, S₂, T, hL => by
      have hstep := step_copy₁_some tm₁ tm₂ oa₁ ia₂ v S₁ S₂ T x xs hL
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have e1 : EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
          ⟨some (Sum.inr (Sum.inl 0)), v, pack tm₁ tm₂ S₁ S₂ T⟩
          (some ⟨some (Sum.inr (Sum.inl 0)), (v.1, (v.2.1, some (ia₂.invFun (oa₁ x)))),
            pack tm₁ tm₂ (Function.update S₁ tm₁.k₁ xs) S₂ (ia₂.invFun (oa₁ x) :: T)⟩) 1 := by
        refine ⟨⟨1, ?_⟩, by simp⟩
        rw [Function.iterate_one, this]
        exact hstep
      refine (QMCExit.EvalsToInTime.trans' e1 (copy₁_trace oa₁ ia₂ xs (v.1, (v.2.1, some (ia₂.invFun (oa₁ x))))
        (Function.update S₁ tm₁.k₁ xs) S₂ (ia₂.invFun (oa₁ x) :: T) (by simp)))
        |> QMCExit.EvalsToInTime.congr_cfg rfl (by
            simp only [List.map_cons, List.reverse_cons, List.map_append, List.append_assoc,
              List.singleton_append, List.append_nil, List.nil_append, Function.update_idem])
        |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

/-- **Copy pass 2, whole word** (`EvalsToInTime` form). -/
noncomputable def copy₂_trace (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) :
    ∀ (L : List (tm₂.Γ tm₂.k₀)) (v : Sta tm₁ tm₂)
      (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k)),
      EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
        ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ L⟩
        (some ⟨some (Sum.inr (Sum.inr tm₂.main)), (v.1, (v.2.1, none)),
          pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (L.reverse ++ S₂ tm₂.k₀)) []⟩) (L.length + 1)
  | [], v, S₁, S₂ => by
      have hstep := step_copy₂_nil tm₁ tm₂ oa₁ ia₂ v S₁ S₂ [] rfl
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ []⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have hupd : Function.update S₂ tm₂.k₀ (([] : List (tm₂.Γ tm₂.k₀)).reverse ++ S₂ tm₂.k₀)
          = S₂ := by simp
      rw [hupd]
      refine ⟨⟨1, ?_⟩, by simp⟩
      rw [Function.iterate_one, this]
      exact hstep
  | x :: xs, v, S₁, S₂ => by
      have hstep := step_copy₂_some tm₁ tm₂ oa₁ ia₂ v S₁ S₂ (x :: xs) x xs rfl
      have this := QMCExit.flip_bind_step (compProg tm₁ tm₂ oa₁ ia₂)
        (⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ (x :: xs)⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      have e1 : EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
          ⟨some (Sum.inr (Sum.inl 1)), v, pack tm₁ tm₂ S₁ S₂ (x :: xs)⟩
          (some ⟨some (Sum.inr (Sum.inl 1)), (v.1, (v.2.1, some x)),
            pack tm₁ tm₂ S₁ (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀)) xs⟩) 1 := by
        refine ⟨⟨1, ?_⟩, by simp⟩
        rw [Function.iterate_one, this]
        exact hstep
      refine (QMCExit.EvalsToInTime.trans' e1 (copy₂_trace oa₁ ia₂ xs (v.1, (v.2.1, some x)) S₁
        (Function.update S₂ tm₂.k₀ (x :: S₂ tm₂.k₀))))
        |> QMCExit.EvalsToInTime.congr_cfg rfl (by
            simp only [List.reverse_cons, List.append_assoc, List.singleton_append,
              Function.update_idem, Function.update_self])
        |> fun h => QMCExit.EvalsToInTime.mono h (by simp only [List.length_cons]; omega)

end CompCore

end Turing


attribute [instance] Turing.FinTM2.kDecidableEq Turing.FinTM2.kFin Turing.FinTM2.ΛFin
  Turing.FinTM2.σFin Turing.FinTM2.Γk₀Fin

namespace Turing

namespace TM2

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*}

/-- The number of `push` statements executed inside a single statement chain.

A single `TM2.step` runs a whole chain (`push`/`peek`/`pop`/`load`/`branch` continue within the
same step), ending at `goto` or `halt`; `pushes` therefore bounds the number of symbols that a step
can add to the stacks. -/
def pushes : Stmt Γ Λ σ → ℕ
  | .push _ _ q => 1 + pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

variable [Fintype K] [DecidableEq K]

/-- Total number of symbols stored on all stacks. -/
def volume (s : (k : K) → List (Γ k)) : ℕ := ∑ k, (s k).length

theorem length_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    (fun j => (Function.update s k v j).length) =
      Function.update (fun j => (s j).length) k v.length := by
  funext j
  by_cases h : j = k
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem volume_update (s : (k : K) → List (Γ k)) (k : K) (v : List (Γ k)) :
    volume (Function.update s k v) + (s k).length = volume s + v.length := by
  classical
  unfold volume
  rw [length_update, Finset.sum_update_of_mem (Finset.mem_univ k)]
  have hh := Finset.sum_erase_add (Finset.univ : Finset K) (fun j => (s j).length)
    (Finset.mem_univ k)
  rw [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : Stmt Γ Λ σ) (v : σ) (s : (k : K) → List (Γ k)) :
    volume (TM2.stepAux q v s).stk ≤ volume s + pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have hv := volume_update s k (g v :: s k)
      simp only [List.length_cons] at hv
      have hq := ih v (Function.update s k (g v :: s k))
      simp only [TM2.stepAux, pushes]
      omega
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      have hq := ih (g v (s k).head?) (Function.update s k (s k).tail)
      simp only [TM2.stepAux, pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simp only [TM2.stepAux, hg, Bool.cond_false, pushes]
        exact (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simp only [TM2.stepAux, hg, Bool.cond_true, pushes]
        exact (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _
  | halt => simp only [TM2.stepAux, pushes, Nat.add_zero]; exact le_refl _

end TM2

open TM2 in
/-- Number of symbols a machine can add to all of its stacks in one step, summed over its program. -/
noncomputable def FinTM2.growth (tm : FinTM2) : ℕ := ∑ l, TM2.pushes (tm.m l)

namespace FinTM2

variable (tm : FinTM2)

theorem flip_bind_none : (flip bind tm.step) (none : Option tm.Cfg) = none := rfl

theorem flip_bind_some (c : tm.Cfg) : (flip bind tm.step) (some c) = tm.step c := rfl

theorem step_volume {a b : tm.Cfg} (h : tm.step a = some b) :
    TM2.volume b.stk ≤ TM2.volume a.stk + tm.growth := by
  classical
  obtain ⟨l, v, s⟩ := a
  cases l with
  | none => exact absurd h (by simp [FinTM2.step, TM2.step])
  | some l =>
      have hb : b = TM2.stepAux (tm.m l) v s := (Option.some.inj h).symm
      rw [hb, FinTM2.growth]
      refine (TM2.stepAux_volume _ _ _).trans (Nat.add_le_add_left ?_ _)
      exact Finset.single_le_sum (f := fun x => TM2.pushes (tm.m x))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)

theorem iterate_volume (tm : FinTM2) : ∀ (m : ℕ) (a b : tm.Cfg),
    (flip bind tm.step)^[m] (some a) = some b →
      TM2.volume b.stk ≤ TM2.volume a.stk + m * tm.growth
  | 0, a, b, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst h; simp
  | m + 1, a, b, h => by
      rw [Function.iterate_succ_apply'] at h
      cases hprev : (flip bind tm.step)^[m] (some a) with
      | none => rw [hprev, tm.flip_bind_none] at h; exact absurd h (by simp)
      | some c =>
          rw [hprev, tm.flip_bind_some] at h
          have ih := iterate_volume tm m a c hprev
          have hs := tm.step_volume h
          have hmul : (m + 1) * tm.growth = m * tm.growth + tm.growth := Nat.succ_mul _ _
          rw [hmul]
          omega

theorem volume_initList (s : List (tm.Γ tm.k₀)) : TM2.volume (initList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk
    simp only [initList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem volume_haltList (s : List (tm.Γ tm.k₁)) : TM2.volume (haltList tm s).stk = s.length := by
  classical
  unfold TM2.volume
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk
    simp only [haltList, dif_neg hk, List.length_nil]
  · intro h; exact absurd (Finset.mem_univ _) h

end FinTM2

end Turing

namespace StateTransition

variable {α : Type*}

/-- A step bound may always be weakened. -/
def EvalsToInTime.mono {f : α → Option α} {a : α} {b : Option α} {m m' : ℕ}
    (h : EvalsToInTime f a b m) (hm : m ≤ m') : EvalsToInTime f a b m' :=
  ⟨h.toEvalsTo, le_trans h.steps_le_m hm⟩

end StateTransition

namespace Turing

/-- **Output length bound for an arbitrary `FinTM2`.** If `tm` outputs `t` on input `s` within `n`
steps, then `t` has at most `s.length + n * growth` symbols. -/
theorem TM2OutputsInTime.output_length_le {tm : FinTM2} {s : List (tm.Γ tm.k₀)}
    {t : List (tm.Γ tm.k₁)} {n : ℕ}
    (h : TM2OutputsInTime tm s (some t) n) : t.length ≤ s.length + n * tm.growth := by
  have hvol := tm.iterate_volume h.steps (initList tm s) (haltList tm t) h.evals_in_steps
  rw [tm.volume_initList, tm.volume_haltList] at hvol
  exact hvol.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Turing

namespace Turing

namespace CompCore

open Polynomial

/-- `initStacks` is "put `l` on the input stack, nothing elsewhere". -/
theorem initStacks_eq_update (tm : FinTM2) (l : List (tm.Γ tm.k₀)) :
    QMCExit.initStacks tm l = Function.update (fun k => ([] : List (tm.Γ k))) tm.k₀ l := by
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp [QMCExit.initStacks]
  · simp [QMCExit.initStacks, Function.update, h]

/-- Internal initial state of the composite. -/
def compInit (tm₁ tm₂ : FinTM2) : Sta tm₁ tm₂ :=
  (tm₁.initialState, (tm₂.initialState, none))

variable {tm₁ : FinTM2} {tm₂ : FinTM2}
variable {βΓ : Type} [Inhabited βΓ]

/-- **The composite machine**: run `tm₁`, copy its output onto `tm₂`'s input, run `tm₂`.
(An `abbrev`, so that its stack indices reduce definitionally.) -/
noncomputable abbrev compTM (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ) : FinTM2 where
  K := Key tm₁ tm₂
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := Sum.inl tm₁.k₀
  k₁ := Sum.inr (Sum.inl tm₂.k₁)
  Γ := Gam tm₁ tm₂
  Λ := Lab tm₁ tm₂
  main := Sum.inl tm₁.main
  ΛFin := inferInstance
  σ := Sta tm₁ tm₂
  initialState := compInit tm₁ tm₂
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := compProg tm₁ tm₂ oa₁ ia₂

/-- The composite's input stack family is `pack` of `tm₁`'s. -/
theorem pack_initStacks (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (l : List (tm₁.Γ tm₁.k₀)) :
    pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []
      = QMCExit.initStacks (compTM oa₁ ia₂) l := by
  funext k
  rcases k with a | (b | u)
  · show QMCExit.initStacks tm₁ l a = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inl a)
    unfold QMCExit.initStacks
    by_cases h : a = tm₁.k₀
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inl b))))
        = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inr (Sum.inl b))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₀ from
      by intro e; cases e)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr u))))
        = QMCExit.initStacks (compTM oa₁ ia₂) l (Sum.inr (Sum.inr u))
    unfold QMCExit.initStacks
    rw [dif_neg (show (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₀ from
      by intro e; cases e)]

/-- The composite's halting stack family is `pack` of `tm₂`'s. -/
theorem pack_haltStacks (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    (u : List (tm₂.Γ tm₂.k₁)) :
    pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []
      = QMCExit.haltStacks (compTM oa₁ ia₂) u := by
  funext k
  rcases k with a | (b | uu)
  · show ([] : List (Gam tm₁ tm₂ (Sum.inl a)))
        = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inl a)
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inl a : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₁ from
      by intro e; cases e)]
  · show QMCExit.haltStacks tm₂ u b = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inr (Sum.inl b))
    unfold QMCExit.haltStacks
    by_cases h : b = tm₂.k₁
    · subst h
      rw [dif_pos rfl, dif_pos rfl]
    · rw [dif_neg h, dif_neg (by simpa using h)]
  · show ([] : List (Gam tm₁ tm₂ (Sum.inr (Sum.inr uu))))
        = QMCExit.haltStacks (compTM oa₁ ia₂) u (Sum.inr (Sum.inr uu))
    unfold QMCExit.haltStacks
    rw [dif_neg (show (Sum.inr (Sum.inr uu) : Key tm₁ tm₂) ≠ (compTM oa₁ ia₂).k₁ from
      by intro e; cases e)]

/-- The stack that copy pass 1 leaves behind is empty. -/
theorem update_haltStacks_self (t : List (tm₁.Γ tm₁.k₁)) :
    Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = tm₁.k₁
  · subst h; simp
  · rw [Function.update_of_ne h]
    simp [QMCExit.haltStacks, h]

/-- **Phase 1**: machine 1's run, lifted into the composite. -/
noncomputable def phase₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {N : ℕ}
    (h : TM2OutputsInTime tm₁ l (some t) N) :
    EvalsToInTime (TM2.step M)
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨some (Sum.inr (Sum.inl 0)), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.haltStacks tm₁ t) (fun _ => []) []⟩) N := by
  have h1 := iterate_cfg₁ (tm₁ := tm₁) (tm₂ := tm₂) (M := M) hM tm₂.initialState
    (none : Option (tm₂.Γ tm₂.k₀)) (fun _ => []) [] h.steps
    (Turing.initList tm₁ l) (Turing.haltList tm₁ t) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

/-- **Phase 2**: machine 2's run, lifted into the composite. -/
noncomputable def phase₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    {S₁ : (k : tm₁.K) → List (tm₁.Γ k)}
    {l : List (tm₂.Γ tm₂.k₀)} {u : List (tm₂.Γ tm₂.k₁)} {M' : ℕ}
    (h : TM2OutputsInTime tm₂ l (some u) M') :
    EvalsToInTime (TM2.step M)
      ⟨some (Sum.inr (Sum.inr tm₂.main)), compInit tm₁ tm₂,
        pack tm₁ tm₂ S₁ (QMCExit.initStacks tm₂ l) []⟩
      (some ⟨none, compInit tm₁ tm₂, pack tm₁ tm₂ S₁ (QMCExit.haltStacks tm₂ u) []⟩) M' := by
  have h1 := iterate_cfg₂ (tm₁ := tm₁) (tm₂ := tm₂) (M := M) hM tm₁.initialState
    (none : Option (tm₂.Γ tm₂.k₀)) S₁ [] h.steps
    (Turing.initList tm₂ l) (Turing.haltList tm₂ u) h.evals_in_steps
  exact ⟨⟨h.steps, h1⟩, h.steps_le_m⟩

/-- **The composite run**: machine 1, the two copy passes, machine 2. -/
noncomputable def comp_run (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ) (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {u : List (tm₂.Γ tm₂.k₁)}
    {N M' : ℕ} (h₁ : TM2OutputsInTime tm₁ l (some t) N)
    (h₂ : TM2OutputsInTime tm₂ (t.map (fun x => ia₂.invFun (oa₁ x))) (some u) M') :
    EvalsToInTime (TM2.step (compProg tm₁ tm₂ oa₁ ia₂))
      ⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩
      (some ⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []⟩)
      (M' + ((t.length + 1) + ((t.length + 1) + N))) := by
  have hP1 := phase₁ (tm₁ := tm₁) (tm₂ := tm₂) (compProg tm₁ tm₂ oa₁ ia₂) (fun _ => rfl) h₁
  have hC1 := copy₁_trace (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂ t (compInit tm₁ tm₂)
    (QMCExit.haltStacks tm₁ t) (fun _ => []) [] (QMCExit.haltStacks_k1 tm₁ t)
  have hC2 := copy₂_trace (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂
    ((t.map (fun x => ia₂.invFun (oa₁ x))).reverse) (compInit tm₁ tm₂)
    (Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ []) (fun _ => [])
  have hP2 := phase₂ (tm₁ := tm₁) (tm₂ := tm₂) (compProg tm₁ tm₂ oa₁ ia₂) (fun _ => rfl)
    (S₁ := Function.update (QMCExit.haltStacks tm₁ t) tm₁.k₁ []) h₂
  -- copy pass 1, with its endpoint written for copy pass 2
  have hC1' := hC1
  simp only [compInit, List.append_nil] at hC1'
  -- copy pass 2, with its endpoint written for machine 2
  have hC2' := hC2
  simp only [compInit, ← initStacks_eq_update, List.reverse_reverse, List.append_nil] at hC2'
  have hchain := QMCExit.EvalsToInTime.trans'
    (QMCExit.EvalsToInTime.trans' (QMCExit.EvalsToInTime.trans' hP1 hC1') hC2') hP2
  simpa only [update_haltStacks_self, List.length_reverse, List.length_map] using hchain

/-- The composite run, packaged as `TM2OutputsInTime` for `compTM`. -/
noncomputable def tm2OutputsInTime_comp (oa₁ : tm₁.Γ tm₁.k₁ ≃ βΓ)
    (ia₂ : tm₂.Γ tm₂.k₀ ≃ βΓ)
    {l : List (tm₁.Γ tm₁.k₀)} {t : List (tm₁.Γ tm₁.k₁)} {u : List (tm₂.Γ tm₂.k₁)}
    {N M' : ℕ} (h₁ : TM2OutputsInTime tm₁ l (some t) N)
    (h₂ : TM2OutputsInTime tm₂ (t.map (fun x => ia₂.invFun (oa₁ x))) (some u) M') :
    TM2OutputsInTime (compTM oa₁ ia₂) l (some u)
      (M' + ((t.length + 1) + ((t.length + 1) + N))) := by
  have hrun := comp_run (tm₁ := tm₁) (tm₂ := tm₂) oa₁ ia₂ h₁ h₂
  have hstart : Turing.initList (compTM oa₁ ia₂) l =
      (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
        pack tm₁ tm₂ (QMCExit.initStacks tm₁ l) (fun _ => []) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := by
    have h1 : Turing.initList (compTM oa₁ ia₂) l =
        (⟨some (Sum.inl tm₁.main), compInit tm₁ tm₂,
          QMCExit.initStacks (compTM oa₁ ia₂) l⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_initStacks]
  have hend : (⟨none, compInit tm₁ tm₂,
        pack tm₁ tm₂ (fun _ => []) (QMCExit.haltStacks tm₂ u) []⟩ :
        TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
      = Turing.haltList (compTM oa₁ ia₂) u := by
    have h1 : Turing.haltList (compTM oa₁ ia₂) u =
        (⟨none, compInit tm₁ tm₂, QMCExit.haltStacks (compTM oa₁ ia₂) u⟩ :
          TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) := rfl
    rw [h1, ← pack_haltStacks]
  have h := hrun
  rw [← hstart, hend] at h
  exact QMCExit.tm2OutputsInTime_of_cfg h rfl


end CompCore
end Turing

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true


set_option maxHeartbeats 1000000

namespace L3
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic Polynomial F3SubsetSum

def inputN (w : List Bool) : ℕ := w.findIdx (! ·)
def inputM (w : List Bool) : ℕ := w.length - inputN w - 1

def base (n m : ℕ) : ℕ := (m + n - 1) / n
def exponent (d n m : ℕ) : ℕ := d * ((n * n + m - 1) / m)
def clock (d n m : ℕ) : ℕ := base n m ^ exponent d n m

def large (K : ℕ) (w : List Bool) : Bool := decide (K * inputN w ≤ inputM w)
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
      max 1 (p.2.length ^ k) * (enc xs).length ≤ S) :
    BoundedRun enc powerBody S (k+1) (p,(k,xs)) (p,powerList p.2 k xs) := by
  induction k generalizing xs with
  | zero =>
    apply BoundedRun.stop
    · simp only [enc_pair_length,enc_nat_length,Nat.size_zero,pow_zero,max_self,one_mul] at hS ⊢
      omega
    · simp [powerBody,powerList]
  | succ k ih =>
    apply BoundedRun.step (a' := (p,(k,copies p.2 xs)))
    · change (enc (p,(k+1,xs))).length ≤ S
      simp only [enc_pair_length,enc_nat_length] at hS ⊢
      have hpow : 1 ≤ max 1 (p.2.length^(k+1)) := le_max_left _ _
      nlinarith
    · simp [powerBody,copies]
    · apply ih
      have hk : k.size ≤ (k+1).size := Nat.size_le_size (Nat.le_succ k)
      have hlen : (enc (copies p.2 xs)).length = p.2.length * (enc xs).length := by
        simp only [enc_bool_length,copies_length]; ring
      have hprod : max 1 (p.2.length^k) * p.2.length ≤ max 1 (p.2.length^(k+1)) := by
        by_cases hb : p.2.length = 0
        · simp [hb]
        · have hb1 : 1 ≤ p.2.length := by omega
          have hk1 : 1 ≤ p.2.length^k := one_le_pow₀ hb1
          have hk2 : 1 ≤ p.2.length^(k+1) := one_le_pow₀ hb1
          rw [max_eq_right hk1,max_eq_right hk2,pow_succ]
      change 2*(enc p).length+3+2*k.size+
        max 1 (p.2.length^k)*(enc (copies p.2 xs)).length ≤ S
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

theorem base_bound (n m : ℕ) : base n m ≤ n+m+1 := by
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
    large K (unaryD n ++ unary m) = decide (K*n ≤ m) := by
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
      if K*n ≤ m then
        true :: (unaryD n ++ unaryD m ++ unary (clock d n m))
      else false :: (unaryD n ++ unary m) := by
  by_cases h : K*n ≤ m
  · simp only [start,large_word,inputN_word,inputM_word]
    simp only [h,decide_true,if_true]
    simp only [powerResult,finish,powerList_true,bases_length_word,clock,if_true]
    simp [unaryD,unary,List.append_assoc]
  · simp only [start,large_word,inputN_word,inputM_word]
    simp [h,powerResult,finish,powerList]

theorem powerSize_result (s : PowerState) :
    (enc (powerResult s)).length ≤ powerSize s := by
  unfold powerResult powerSize
  simp only [enc_pair_length,enc_bool_length,powerList_length]
  have hh : s.1.2.length^s.2.1 ≤ max 1 (s.1.2.length^s.2.1) := le_max_right _ _
  nlinarith

theorem exponent_bound (d n m : ℕ) :
    exponent d n m + 1 ≤ (d+1)*(n+m+1)^2 := by
  have h := Nat.div_le_self (n*n+m-1) m
  have he : (n*n+m-1)/m ≤ n*n+m := h.trans (Nat.sub_le _ _)
  have hd := Nat.mul_le_mul_left d he
  have hn : n*n+m+1 ≤ (n+m+1)^2 := by nlinarith
  have hb : ∀ u : ℕ, d*u+1 ≤ (d+1)*(u+1) := by intro u; nlinarith
  unfold exponent
  exact (Nat.add_le_add_right hd 1).trans ((hb _).trans (Nat.mul_le_mul_left (d+1) hn))

theorem start_size_word (K d n m : ℕ) :
    powerSize (start K d (unaryD n ++ unary m)) ≤ 
      (start_poly K d).program.sizeBound.eval (3*(n+m+1)) + 3*(if K*n ≤ m then clock d n m else 0)+4 := by
  set w := unaryD n ++ unary m
  have hs := (start_poly K d).program.length_bound w
  have hw : (enc w).length = 3*(n+m+1) := by simp [enc_bool_length,w,unaryD,unary,Nat.add_assoc]
  rw [hw] at hs
  unfold powerSize
  have hparts : 2*(enc (start K d w).1).length + 3 + 2*(start K d w).2.1.size ≤ 
      (enc (start K d w)).length + 1 := by
    simp only [enc_pair_length,enc_nat_length]
    omega
  have hpow : max 1 ((start K d w).1.2.length^(start K d w).2.1) *
      (enc (start K d w).2.2).length ≤ 3*(if K*n ≤ m then clock d n m else 0)+3 := by
    simp only [start]
    rw [show large K w = decide (K*n ≤ m) from large_word K n m,
      show inputN w = n from inputN_word n m,
      show inputM w = m from inputM_word n m]
    by_cases h : K*n ≤ m
    · simp only [if_pos h] at ⊢
      simp only [h,decide_true,ite_true,enc_bool_length,List.length_singleton,
        show (bases w).length = base n m from bases_length_word n m]
      change max 1 (clock d n m)*3 ≤ _
      have : max 1 (clock d n m) ≤ clock d n m+1 := max_le (by omega) (by omega)
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

def budget (K d n m : ℕ) : ℕ := n+m+(if K*n ≤ m then clock d n m else 0)+1

theorem prepare_run (K d n m : ℕ) :
    ∃ t ≤ (RPrepare K d).eval (budget K d n m),
      Trace (prepare K d).machine.step t
        ((prepare K d).machine.initialCfg (unaryD n ++ unary m))
        ((prepare K d).machine.finalCfg
          (if K*n ≤ m then true :: (unaryD n ++ unaryD m ++ unary (clock d n m))
            else false :: (unaryD n ++ unary m))) := by
  set w := unaryD n ++ unary m
  set s := start K d w
  set r := powerResult s
  set Z := budget K d n m
  obtain ⟨t,ht,tr⟩ := (prepare K d).run w
  refine ⟨t,?_,?_⟩
  · have hw : w.length = n+m+1 := by simp [w,unaryD,unary,Nat.add_assoc]
    have hZ : n+m+1 ≤ Z := by unfold Z budget; omega
    have hwe : (enc w).length ≤ 3*Z := by rw [enc_bool_length,hw]; omega
    have hs : (enc s).length ≤ (RStart K d).eval Z := by
      have h := (start_poly K d).program.length_bound w
      exact h.trans (by
        simp only [RStart,eval_comp,eval_mul,eval_ofNat,eval_X]
        exact polynomial_eval_mono _ hwe)
    have hsize : powerSize s ≤ (RSize K d).eval Z := by
      have h := start_size_word K d n m
      change powerSize s ≤ _ at h
      have hmono := polynomial_eval_mono (start_poly K d).program.sizeBound
        (Nat.mul_le_mul_left 3 hZ)
      have hclock : (if K*n ≤ m then clock d n m else 0) ≤ Z := by unfold Z budget; omega
      simp only [RSize,RStart,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X] at ⊢
      omega
    have hr : (enc r).length ≤ (RSize K d).eval Z := (powerSize_result s).trans hsize
    have hfin : (enc (finish r)).length ≤ finish_poly.program.sizeBound.eval ((RSize K d).eval Z) :=
      (finish_poly.program.length_bound r).trans (polynomial_eval_mono _ hr)
    have hk : s.2.1+1 ≤ (d+1)*(Z+1)^2 := by
      have he := exponent_bound d n m
      have hm : (d+1)*(n+m+1)^2 ≤ (d+1)*(Z+1)^2 := by gcongr; omega
      change (if large K w then exponent d (inputN w) (inputM w) else 0)+1 ≤ _
      rw [show inputN w = n from inputN_word n m,show inputM w = m from inputM_word n m]
      split_ifs
      · omega
      · nlinarith
    have hloop : (s.2.1+1)*powerProgram.passTime (powerSize s) ≤ 
        (d+1)*(Z+1)^2 * loopTime.eval ((RSize K d).eval Z) := by
      rw [loopTime_eq]
      exact Nat.mul_le_mul hk (polynomial_eval_mono _ hsize)
    have hpt := polynomial_eval_mono BooleanLists.packProgram.time (hw ▸ hZ)
    have hst := polynomial_eval_mono (start_poly K d).program.time hwe
    have hft := polynomial_eval_mono finish_poly.program.time hr
    have hut := polynomial_eval_mono BooleanLists.unpackProgram.time hfin
    change t ≤ 
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

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
open Turing
namespace L3.Dispatch

/-- Once a deterministic step function has halted, iterating it stays at `none`. -/
theorem iterate_none {α : Type*} (f : α → Option α) : ∀ m : ℕ,
    (flip bind f)^[m] (none : Option α) = none
  | 0 => rfl
  | m + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none f m

namespace Core

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Stack index type of the composite. -/
abbrev Key : Type := tm₁.K ⊕ (tm₂.K ⊕ Unit)

/-- Stack alphabets of the composite. -/
abbrev Gam : Key tm₁ tm₂ → Type
  | .inl a => tm₁.Γ a
  | .inr (.inl b) => tm₂.Γ b
  | .inr (.inr _) => tm₂.Γ tm₂.k₀

/-- Label type of the composite: machine 1's labels, machine 2's labels, and one copy-phase label
(stored as `Unit`). -/
abbrev Lab : Type := tm₁.Λ ⊕ (Fin 5 ⊕ tm₂.Λ)

/-- Internal state of the composite: both machines' states plus a one-symbol buffer. -/
abbrev Sta : Type := tm₁.σ × (tm₂.σ × Option (tm₂.Γ tm₂.k₀))

/-- The stack contents of the composite as a dependent function. -/
def pack (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) : (k : Key tm₁ tm₂) → List (Gam tm₁ tm₂ k)
  | .inl a => S₁ a
  | .inr (.inl b) => S₂ b
  | .inr (.inr _) => T

theorem pack_update_left (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₁.K) (x : List (tm₁.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inl k) x
      = pack tm₁ tm₂ (Function.update S₁ k x) S₂ T := by
  funext j
  rcases j with a | (b | u)
  · by_cases h : a = k
    · subst h; simp [pack]
    · simp only [pack, Function.update_of_ne (by simp [h] : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inl k),
        Function.update_of_ne h]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inl k)]
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inl k)]

theorem pack_update_right (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (k : tm₂.K) (x : List (tm₂.Γ k)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inl k)) x
      = pack tm₁ tm₂ S₁ (Function.update S₂ k x) T := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack, Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]
  · by_cases h : b = k
    · subst h; simp [pack]
    · have hne : ¬ ((Sum.inr (Sum.inl b) : Key tm₁ tm₂) = Sum.inr (Sum.inl k)) :=
        fun hh => h (by simpa using hh)
      rw [Function.update_of_ne (a := Sum.inr (Sum.inl b)) (a' := Sum.inr (Sum.inl k))
            (v := x) (f := pack tm₁ tm₂ S₁ S₂ T) hne]
      simp only [pack, Function.update_of_ne (a := b) (a' := k) (v := x) (f := S₂) h]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inr u) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inl k))]

theorem pack_update_tmp (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀))
    (x : List (tm₂.Γ tm₂.k₀)) :
    Function.update (pack tm₁ tm₂ S₁ S₂ T) (Sum.inr (Sum.inr ())) x
      = pack tm₁ tm₂ S₁ S₂ x := by
  funext j
  rcases j with a | (b | u)
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inl a : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack,
      Function.update_of_ne (by simp : (Sum.inr (Sum.inl b) : Key tm₁ tm₂) ≠ Sum.inr (Sum.inr ()))]
  · simp only [pack]
    congr 1
    cases u
    rfl

/-- Label translation for machine 1: its own labels, and its halting label is turned into a jump to
the copy phase. -/
def lab₁ : Option tm₁.Λ → Option (Lab tm₁ tm₂)
  | none => some (Sum.inr (Sum.inl 0))
  | some l => some (Sum.inl l)

/-- Label translation for machine 2: its halting label stays a halting label. -/
def lab₂ : Option tm₂.Λ → Option (Lab tm₁ tm₂)
  | none => none
  | some l => some (Sum.inr (Sum.inr l))

/-- Reindex machine 1's statements into the composite. -/
def tr₁ : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inl k) (fun s => g s.1) (tr₁ q)
  | .peek k g q => .peek (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .pop k g q => .pop (Sum.inl k) (fun s o => (g s.1 o, s.2)) (tr₁ q)
  | .load g q => .load (fun s => (g s.1, s.2)) (tr₁ q)
  | .branch g q r => .branch (fun s => g s.1) (tr₁ q) (tr₁ r)
  | .goto g => .goto (fun s => Sum.inl (g s.1))
  | .halt => .goto (fun _ => Sum.inr (Sum.inl 0))

/-- Reindex machine 2's statements into the composite. -/
def tr₂ : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .push k g q => .push (Sum.inr (Sum.inl k)) (fun s => g s.2.1) (tr₂ q)
  | .peek k g q => .peek (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .pop k g q => .pop (Sum.inr (Sum.inl k)) (fun s o => (s.1, (g s.2.1 o, s.2.2))) (tr₂ q)
  | .load g q => .load (fun s => (s.1, (g s.2.1, s.2.2))) (tr₂ q)
  | .branch g q r => .branch (fun s => g s.2.1) (tr₂ q) (tr₂ r)
  | .goto g => .goto (fun s => Sum.inr (Sum.inr (g s.2.1)))
  | .halt => .halt

theorem stepAux_tr₁ (q : TM2.Stmt tm₁.Γ tm₁.Λ tm₁.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₁ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₁ tm₁ tm₂ (TM2.stepAux q v₁ S₁).l,
          ((TM2.stepAux q v₁ S₁).var, v₂, b),
          pack tm₁ tm₂ (TM2.stepAux q v₁ S₁).stk S₂ T⟩ := by
  induction q generalizing v₁ S₁ with
  | push k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₁, TM2.stepAux, pack_update_left tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₁, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₁
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₁, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₁, TM2.stepAux, lab₁]
  | halt => simp only [tr₁, TM2.stepAux, lab₁]

theorem stepAux_tr₂ (q : TM2.Stmt tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (v₂ : tm₂.σ)
    (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.stepAux (tr₂ tm₁ tm₂ q) (v₁, v₂, b) (pack tm₁ tm₂ S₁ S₂ T)
      = ⟨lab₂ tm₁ tm₂ (TM2.stepAux q v₂ S₂).l,
          (v₁, ((TM2.stepAux q v₂ S₂).var, b)),
          pack tm₁ tm₂ S₁ (TM2.stepAux q v₂ S₂).stk T⟩ := by
  induction q generalizing v₂ S₂ with
  | push k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | peek k g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | pop k g q ih =>
      simp only [tr₂, TM2.stepAux, pack_update_right tm₁ tm₂]
      exact ih _ _
  | load g q ih =>
      simp only [tr₂, TM2.stepAux]
      exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v₂
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_false]
        exact ihr _ _
      · simp only [tr₂, TM2.stepAux, hg, Bool.cond_true]
        exact ihq _ _
  | goto g => simp only [tr₂, TM2.stepAux, lab₂]
  | halt => simp only [tr₂, TM2.stepAux, lab₂]
end Core

end L3.Dispatch


namespace L3.Dispatch

namespace Core

variable (tm₁ : FinTM2) (tm₂ : FinTM2)

/-- Program of the composite: machine 1's code, the copy phase, then machine 2's code. -/
def compCode (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)
  | .inl l => tr₁ tm₁ tm₂ (tm₁.m l)
  | .inr (.inl _) => copy
  | .inr (.inr l) => tr₂ tm₁ tm₂ (tm₂.m l)

/-- The composite step function. -/
def compStep (copy : TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) →
      Option (TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂)) :=
  TM2.step (compCode tm₁ tm₂ copy)

/-- Embed machine 1's configuration into the composite. -/
def cfg₁ (c : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ) (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₂ : (k : tm₂.K) → List (tm₂.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₁ tm₁ tm₂ c.l, (c.var, v₂, b), pack tm₁ tm₂ c.stk S₂ T⟩

theorem step_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ}
    (h : tm₁.step c = some c') :
    TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T) := by
  obtain ⟨l, v₁, S₁⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₁.m l) v₁ S₁ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₁, lab₁, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₁]

/-- Run lifting for machine 1: any `m`-step run of `tm₁` is an `m`-step run of the composite. -/
theorem iterate_cfg₁ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₁.Λ, M (Sum.inl l) = tr₁ tm₁ tm₂ (tm₁.m l))
    (v₂ : tm₂.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₂ : (k : tm₂.K) → List (tm₂.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₁.Γ tm₁.Λ tm₁.σ),
      (flip bind tm₁.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
        = some (cfg₁ tm₁ tm₂ c' v₂ b S₂ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₁.step) (some c) = tm₁.step c from rfl] at h
      cases hstep : tm₁.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₁ tm₁ tm₂ c v₂ b S₂ T))
                = TM2.step M (cfg₁ tm₁ tm₂ c v₂ b S₂ T) from rfl,
              step_cfg₁ tm₁ tm₂ M hM v₂ b S₂ T hstep]
          exact iterate_cfg₁ M hM v₂ b S₂ T m d c' h

/-- Embed machine 2's configuration into the composite. -/
def cfg₂ (c : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ) (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀))
    (S₁ : (k : tm₁.K) → List (tm₁.Γ k)) (T : List (tm₂.Γ tm₂.k₀)) :
    TM2.Cfg (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂) :=
  ⟨lab₂ tm₁ tm₂ c.l, (v₁, (c.var, b)), pack tm₁ tm₂ S₁ c.stk T⟩

theorem step_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) {c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ}
    (h : tm₂.step c = some c') :
    TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T) := by
  obtain ⟨l, v₂, S₂⟩ := c
  cases l with
  | none => simp [FinTM2.step, TM2.step] at h
  | some l =>
      have hh : c' = TM2.stepAux (tm₂.m l) v₂ S₂ := (Option.some.inj h).symm
      subst hh
      simp only [cfg₂, lab₂, hM, TM2.step.eq_2, FinTM2.step, stepAux_tr₂]

/-- Run lifting for machine 2. -/
theorem iterate_cfg₂ (M : Lab tm₁ tm₂ → TM2.Stmt (Gam tm₁ tm₂) (Lab tm₁ tm₂) (Sta tm₁ tm₂))
    (hM : ∀ l : tm₂.Λ, M (Sum.inr (Sum.inr l)) = tr₂ tm₁ tm₂ (tm₂.m l))
    (v₁ : tm₁.σ) (b : Option (tm₂.Γ tm₂.k₀)) (S₁ : (k : tm₁.K) → List (tm₁.Γ k))
    (T : List (tm₂.Γ tm₂.k₀)) :
    ∀ (m : ℕ) (c c' : TM2.Cfg tm₂.Γ tm₂.Λ tm₂.σ),
      (flip bind tm₂.step)^[m] (some c) = some c' →
      (flip bind (TM2.step M))^[m] (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
        = some (cfg₂ tm₁ tm₂ c' v₁ b S₁ T)
  | 0, c, c', h => by
      simp only [Function.iterate_zero, id_eq] at h
      have h' : c = c' := Option.some.inj h
      subst h'; rfl
  | m + 1, c, c', h => by
      rw [Function.iterate_succ_apply] at h ⊢
      rw [show (flip bind tm₂.step) (some c) = tm₂.step c from rfl] at h
      cases hstep : tm₂.step c with
      | none => rw [hstep] at h; exact absurd h (by rw [iterate_none]; simp)
      | some d =>
          rw [hstep] at h
          rw [show (flip bind (TM2.step M)) (some (cfg₂ tm₁ tm₂ c v₁ b S₁ T))
                = TM2.step M (cfg₂ tm₁ tm₂ c v₁ b S₁ T) from rfl,
              step_cfg₂ tm₁ tm₂ M hM v₁ b S₁ T hstep]
          exact iterate_cfg₂ M hM v₁ b S₁ T m d c' h

end Core

end L3.Dispatch

namespace L3.Dispatch
open OAI.MetricKMedian.Binary Function
open Core

theorem state_ext {K : Type} {Γ : K → Type} {Λ σ : Type}
    {x y : TM2.Cfg Γ Λ σ} (hl : x.l = y.l) (hv : x.var = y.var) (hs : x.stk = y.stk) : x = y := by
  cases x
  cases y
  simp_all

variable (A B : Turing.TM2ComputableAux Bool Bool)
local notation "a" => A.tm
local notation "b" => B.tm

abbrev SKey := Key a b
abbrev SLabel := Lab a b
abbrev SGamma := Gam a b
abbrev SState := Sta a b

def initial : SState A B := (A.tm.initialState,B.tm.initialState,none)
def clear (s : SState A B) : SState A B := (s.1,s.2.1,none)
def phase (i : Fin 5) : SLabel A B := .inr (.inl i)
def temp : SKey A B := .inr (.inr ())
def leftInput : SKey A B := .inl A.tm.k₀
def leftOutput : SKey A B := .inl A.tm.k₁
def rightInput : SKey A B := .inr (.inl B.tm.k₀)
def rightOutput : SKey A B := .inr (.inl B.tm.k₁)

def jump (l : Option (SLabel A B)) : TM2.Stmt (SGamma A B) (SLabel A B) (SState A B) :=
  l.elim .halt (fun q => .goto (fun _ => q))

def moveStmt (src dst : SKey A B)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (self : SLabel A B) (next : Option (SLabel A B)) :
    TM2.Stmt (SGamma A B) (SLabel A B) (SState A B) :=
  .pop src (fun s x => (s.1,s.2.1,x.map es))
    (.branch (fun s => s.2.2.isSome)
      (.push dst (fun s => ed.symm (s.2.2.getD (B.inputAlphabet.symm false)))
        (.load (clear A B) (.goto (fun _ => self))))
      (.load (clear A B) (jump A B next)))

def code : SLabel A B → TM2.Stmt (SGamma A B) (SLabel A B) (SState A B)
  | .inl l => tr₁ a b (A.tm.m l)
  | .inr (.inr l) => tr₂ a b (B.tm.m l)
  | .inr (.inl 0) =>
      moveStmt A B (leftOutput A B) (temp A B)
        (A.outputAlphabet.trans B.inputAlphabet.symm) (Equiv.refl _)
        (phase A B 0) (some (phase A B 1))
  | .inr (.inl 1) =>
      moveStmt A B (temp A B) (rightOutput A B)
        (Equiv.refl _) (B.outputAlphabet.trans B.inputAlphabet.symm)
        (phase A B 1) none
  | .inr (.inl 2) =>
      .pop (rightInput A B) (fun s x => (s.1,s.2.1,x))
        (.branch (fun s => (s.2.2.map B.inputAlphabet).getD false)
          (.load (clear A B) (.goto (fun _ => phase A B 3)))
          (.load (clear A B) (.goto (fun _ => .inr (.inr B.tm.main)))))
  | .inr (.inl 3) =>
      moveStmt A B (rightInput A B) (temp A B) (Equiv.refl _) (Equiv.refl _)
        (phase A B 3) (some (phase A B 4))
  | .inr (.inl 4) =>
      moveStmt A B (temp A B) (leftInput A B)
        (Equiv.refl _) (A.inputAlphabet.trans B.inputAlphabet.symm)
        (phase A B 4) (some (.inl A.tm.main))

noncomputable abbrev machine : FinTM2 where
  K := SKey A B
  k₀ := rightInput A B
  k₁ := rightOutput A B
  Γ := SGamma A B
  Λ := SLabel A B
  main := phase A B 2
  σ := SState A B
  initialState := initial A B
  m := code A B
  Γk₀Fin := B.tm.Γk₀Fin

noncomputable def aux : TM2ComputableAux Bool Bool :=
  ⟨machine A B,B.inputAlphabet,B.outputAlphabet⟩

def empty : ∀ k : SKey A B, List (SGamma A B k) := fun _ => []

def single (k : SKey A B) (xs : List (SGamma A B k)) : ∀ j, List (SGamma A B j) :=
  update (empty A B) k xs

def pairStacks (src dst : SKey A B)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (xs ys : List (B.tm.Γ B.tm.k₀)) : ∀ j, List (SGamma A B j) :=
  update (single A B src (xs.map es.symm)) dst (ys.map ed.symm)

def moveCfg (src dst : SKey A B)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (lab : Option (SLabel A B)) (xs ys : List (B.tm.Γ B.tm.k₀)) : (machine A B).Cfg :=
  ⟨lab,initial A B,pairStacks A B src dst es ed xs ys⟩

theorem pair_source (src dst : SKey A B) (h : src ≠ dst)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (xs ys : List (B.tm.Γ B.tm.k₀)) :
    pairStacks A B src dst es ed xs ys src = xs.map es.symm := by
  simp [pairStacks,single,update_of_ne h]

theorem pair_target (src dst : SKey A B)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (xs ys : List (B.tm.Γ B.tm.k₀)) :
    pairStacks A B src dst es ed xs ys dst = ys.map ed.symm := by
  simp [pairStacks]

theorem pair_left_empty (src dst : SKey A B)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (ys : List (B.tm.Γ B.tm.k₀)) :
    pairStacks A B src dst es ed [] ys = single A B dst (ys.map ed.symm) := by
  unfold pairStacks single
  simp only [List.map_nil]
  have he : update (empty A B) src ([] : List (SGamma A B src)) = empty A B :=
    update_eq_self src (empty A B)
  rw [he]

theorem pair_right_empty (src dst : SKey A B) (h : src ≠ dst)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (xs : List (B.tm.Γ B.tm.k₀)) :
    pairStacks A B src dst es ed xs [] = single A B src (xs.map es.symm) := by
  unfold pairStacks
  rw [List.map_nil]
  have hd : single A B src (xs.map es.symm) dst = [] := by
    simp [single,empty,h.symm]
  rw [← hd,update_eq_self]

theorem move_cons (src dst : SKey A B) (h : src ≠ dst)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (self : SLabel A B) (next : Option (SLabel A B))
    (hc : code A B self = moveStmt A B src dst es ed self next)
    (x : B.tm.Γ B.tm.k₀) (xs ys : List (B.tm.Γ B.tm.k₀)) :
    (machine A B).step (moveCfg A B src dst es ed (some self) (x::xs) ys) =
      some (moveCfg A B src dst es ed (some self) xs (x::ys)) := by
  simp only [FinTM2.step,TM2.step,moveCfg,hc,moveStmt,TM2.stepAux,
    pair_source A B src dst h es ed,List.map_cons,List.head?_cons,List.tail_cons,
    Option.map_some,Equiv.apply_symm_apply,Option.isSome_some,Bool.cond_true,Option.getD_some]
  congr 1
  apply state_ext <;> try rfl
  simp only [pairStacks,single,List.map_cons]
  rw [update_comm h,update_idem,update_comm h.symm,update_idem]
  simp only [update_of_ne h.symm,update_self]

theorem move_nil (src dst : SKey A B) (h : src ≠ dst)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (self : SLabel A B) (next : Option (SLabel A B))
    (hc : code A B self = moveStmt A B src dst es ed self next)
    (ys : List (B.tm.Γ B.tm.k₀)) :
    (machine A B).step (moveCfg A B src dst es ed (some self) [] ys) =
      some (moveCfg A B src dst es ed next [] ys) := by
  simp only [FinTM2.step,TM2.step,moveCfg,hc,moveStmt,TM2.stepAux,
    pair_source A B src dst h es ed,List.map_nil,List.head?_nil,List.tail_nil,
    Option.map_none,Option.isSome_none,Bool.false_eq_true,Bool.cond_false]
  have hup : update (pairStacks A B src dst es ed [] ys) src [] =
      pairStacks A B src dst es ed [] ys := by
    have hz : pairStacks A B src dst es ed [] ys src = [] := by
      simp only [pair_source A B src dst h es ed,List.map_nil]
    exact hz ▸ update_eq_self src (pairStacks A B src dst es ed [] ys)
  cases next <;> simp [jump,TM2.stepAux,clear,initial,hup]

theorem move_run (src dst : SKey A B) (h : src ≠ dst)
    (es : SGamma A B src ≃ B.tm.Γ B.tm.k₀) (ed : SGamma A B dst ≃ B.tm.Γ B.tm.k₀)
    (self : SLabel A B) (next : Option (SLabel A B))
    (hc : code A B self = moveStmt A B src dst es ed self next)
    (xs ys : List (B.tm.Γ B.tm.k₀)) :
    Trace (machine A B).step (xs.length+1)
      (moveCfg A B src dst es ed (some self) xs ys)
      (moveCfg A B src dst es ed next [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.cons (move_nil A B src dst h es ed self next hc ys) (Trace.refl _)
  | cons x xs ih =>
    have tr := Trace.cons (move_cons A B src dst h es ed self next hc x xs ys) (ih (x::ys))
    simpa [List.reverse_cons,List.append_assoc] using tr

end L3.Dispatch

namespace L3.Dispatch
open Core OAI.MetricKMedian.Binary Function
variable (A B : TM2ComputableAux Bool Bool)
local notation "a" => A.tm
local notation "b" => B.tm

theorem single_left (k : A.tm.K) (xs : List (A.tm.Γ k)) :
    pack a b (Function.update (fun j => ([] : List (A.tm.Γ j))) k xs) (fun _ => []) [] =
      single A B (.inl k) xs := by
  funext j
  rcases j with j | (j | j)
  · by_cases hj : j = k
    · subst j; simp [single,empty,update,pack]
    · simp [single,empty,update,pack,hj]
  · simp [single,empty,update,pack]
  · simp [single,empty,update,pack]

theorem single_right (k : B.tm.K) (xs : List (B.tm.Γ k)) :
    pack a b (fun _ => []) (Function.update (fun j => ([] : List (B.tm.Γ j))) k xs) [] =
      single A B (.inr (.inl k)) xs := by
  funext j
  rcases j with j | (j | j)
  · simp [single,empty,update,pack]
  · by_cases hj : j = k
    · subst j; simp [single,empty,update,pack]
    · simp [single,empty,update,pack,hj]
  · simp [single,empty,update,pack]

theorem init_single (xs : List (B.tm.Γ B.tm.k₀)) :
    Turing.initList (machine A B) xs =
      ⟨some (phase A B 2),initial A B,single A B (rightInput A B) xs⟩ := by
  apply state_ext <;> try rfl
  change (Turing.initList (machine A B) xs).stk = _
  funext j
  by_cases h : j = rightInput A B
  · subst j; simp [Turing.initList,single,empty,update]
  · simp [Turing.initList,single,empty,update,h]

theorem halt_single (xs : List (B.tm.Γ B.tm.k₁)) :
    Turing.haltList (machine A B) xs =
      ⟨none,initial A B,single A B (rightOutput A B) xs⟩ := by
  apply state_ext <;> try rfl
  change (Turing.haltList (machine A B) xs).stk = _
  funext j
  by_cases h : j = rightOutput A B
  · subst j; simp [Turing.haltList,single,empty,update]
  · simp [Turing.haltList,single,empty,update,h]

theorem init_stacks (tm : FinTM2) (xs : List (tm.Γ tm.k₀)) :
    (Turing.initList tm xs).stk = Function.update (fun j => ([] : List (tm.Γ j))) tm.k₀ xs := by
  funext j
  by_cases h : j = tm.k₀
  · subst j; simp [Turing.initList,Function.update]
  · simp [Turing.initList,Function.update,h]

theorem halt_stacks (tm : FinTM2) (xs : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm xs).stk = Function.update (fun j => ([] : List (tm.Γ j))) tm.k₁ xs := by
  funext j
  by_cases h : j = tm.k₁
  · subst j; simp [Turing.haltList,Function.update]
  · simp [Turing.haltList,Function.update,h]

theorem cfg1_init (xs : List (A.tm.Γ A.tm.k₀)) :
    cfg₁ a b (Turing.initList a xs) B.tm.initialState none (fun _ => []) [] =
      ⟨some (.inl A.tm.main),initial A B,single A B (leftInput A B) xs⟩ := by
  apply state_ext <;> try rfl
  simpa only [cfg₁,init_stacks,leftInput] using single_left A B A.tm.k₀ xs

theorem cfg1_halt (xs : List (A.tm.Γ A.tm.k₁)) :
    cfg₁ a b (Turing.haltList a xs) B.tm.initialState none (fun _ => []) [] =
      ⟨some (phase A B 0),initial A B,single A B (leftOutput A B) xs⟩ := by
  apply state_ext <;> try rfl
  simpa only [cfg₁,halt_stacks,leftOutput] using single_left A B A.tm.k₁ xs

theorem cfg2_init (xs : List (B.tm.Γ B.tm.k₀)) :
    cfg₂ a b (Turing.initList b xs) A.tm.initialState none (fun _ => []) [] =
      ⟨some (.inr (.inr B.tm.main)),initial A B,single A B (rightInput A B) xs⟩ := by
  apply state_ext <;> try rfl
  simpa only [cfg₂,init_stacks,rightInput] using single_right A B B.tm.k₀ xs

theorem cfg2_halt (xs : List (B.tm.Γ B.tm.k₁)) :
    cfg₂ a b (Turing.haltList b xs) A.tm.initialState none (fun _ => []) [] =
      Turing.haltList (machine A B) xs := by
  rw [halt_single]
  apply state_ext <;> try rfl
  simpa only [cfg₂,halt_stacks,rightOutput] using single_right A B B.tm.k₁ xs

theorem select_false (w : List Bool) :
    (machine A B).step (Turing.initList (machine A B) ((false::w).map B.inputAlphabet.symm)) =
      some (cfg₂ a b (Turing.initList b (w.map B.inputAlphabet.symm))
        A.tm.initialState none (fun _ => []) []) := by
  rw [init_single,cfg2_init]
  simp [FinTM2.step,TM2.step,phase,code,rightInput,single,empty,TM2.stepAux,
    clear,initial,List.map_cons]

theorem select_true (w : List Bool) :
    (machine A B).step (Turing.initList (machine A B) ((true::w).map B.inputAlphabet.symm)) =
      some (moveCfg A B (rightInput A B) (temp A B)
        (Equiv.refl _) (Equiv.refl _) (some (phase A B 3))
        (w.map B.inputAlphabet.symm) []) := by
  rw [init_single]
  simp only [moveCfg]
  rw [pair_right_empty A B (rightInput A B) (temp A B) (by simp [rightInput,temp])]
  simp [FinTM2.step,TM2.step,phase,code,rightInput,single,empty,TM2.stepAux,
    clear,initial,List.map_cons]

theorem run_false (w out : List Bool) (t : ℕ)
    (h : HMBinPacking.OutputsWithin B w out t) :
    HMBinPacking.OutputsWithin (aux A B) (false::w) out (t+1) := by
  obtain ⟨h⟩ := h
  have tr : Trace B.tm.step h.steps (Turing.initList b (w.map B.inputAlphabet.symm))
      (Turing.haltList b (out.map B.outputAlphabet.symm)) := Trace.of_iterate h.evals_in_steps
  have tr' := tr.map (fun c => cfg₂ a b c A.tm.initialState none (fun _ => []) [])
    (fun _ _ hh => step_cfg₂ a b (code A B) (fun _ => rfl)
      A.tm.initialState none (fun _ => []) [] hh)
  rw [cfg2_halt] at tr'
  have all := Trace.cons (select_false A B w) tr'
  exact ⟨⟨⟨_,all.iterate_eq⟩,by
    change h.steps+1 ≤ t+1
    have := h.steps_le_m
    omega⟩⟩

theorem input_transfer (w : List Bool) :
    Trace (machine A B).step (2*w.length+2)
      (moveCfg A B (rightInput A B) (temp A B)
        (Equiv.refl _) (Equiv.refl _) (some (phase A B 3)) (w.map B.inputAlphabet.symm) [])
      (cfg₁ a b (Turing.initList a (w.map A.inputAlphabet.symm))
        B.tm.initialState none (fun _ => []) []) := by
  have h1 := move_run A B (rightInput A B) (temp A B) (by intro h; cases h)
    (Equiv.refl _) (Equiv.refl _) (phase A B 3) (some (phase A B 4)) rfl
    (w.map B.inputAlphabet.symm) []
  have h2 := move_run A B (temp A B) (leftInput A B) (by intro h; cases h)
    (Equiv.refl _) (A.inputAlphabet.trans B.inputAlphabet.symm)
    (phase A B 4) (some (.inl A.tm.main)) rfl
    (w.map B.inputAlphabet.symm).reverse []
  have he : moveCfg A B (rightInput A B) (temp A B) (Equiv.refl _) (Equiv.refl _)
      (some (phase A B 4)) [] ((w.map B.inputAlphabet.symm).reverse++[]) =
      moveCfg A B (temp A B) (leftInput A B) (Equiv.refl _)
        (A.inputAlphabet.trans B.inputAlphabet.symm) (some (phase A B 4))
        (w.map B.inputAlphabet.symm).reverse [] := by
    simp [moveCfg,pair_left_empty,pair_right_empty,rightInput,rightOutput,leftInput,leftOutput,temp]
  rw [he] at h1
  have tr := h1.trans h2
  rw [cfg1_init]
  simpa [moveCfg,pair_left_empty,pair_right_empty,rightInput,rightOutput,leftInput,leftOutput,temp,List.map_map,
    Equiv.trans_apply,Function.comp_def,two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tr

theorem output_transfer (out : List Bool) :
    Trace (machine A B).step (2*out.length+2)
      (cfg₁ a b (Turing.haltList a (out.map A.outputAlphabet.symm))
        B.tm.initialState none (fun _ => []) [])
      (Turing.haltList (machine A B) (out.map B.outputAlphabet.symm)) := by
  have h1 := move_run A B (leftOutput A B) (temp A B) (by intro h; cases h)
    (A.outputAlphabet.trans B.inputAlphabet.symm) (Equiv.refl _)
    (phase A B 0) (some (phase A B 1)) rfl
    (out.map B.inputAlphabet.symm) []
  have h2 := move_run A B (temp A B) (rightOutput A B) (by intro h; cases h)
    (Equiv.refl _) (B.outputAlphabet.trans B.inputAlphabet.symm)
    (phase A B 1) none rfl (out.map B.inputAlphabet.symm).reverse []
  have he : moveCfg A B (leftOutput A B) (temp A B)
      (A.outputAlphabet.trans B.inputAlphabet.symm) (Equiv.refl _)
      (some (phase A B 1)) [] ((out.map B.inputAlphabet.symm).reverse++[]) =
      moveCfg A B (temp A B) (rightOutput A B) (Equiv.refl _)
        (B.outputAlphabet.trans B.inputAlphabet.symm) (some (phase A B 1))
        (out.map B.inputAlphabet.symm).reverse [] := by
    simp [moveCfg,pair_left_empty,pair_right_empty,rightInput,rightOutput,leftInput,leftOutput,temp]
  rw [he] at h1
  have tr := h1.trans h2
  rw [cfg1_halt,halt_single]
  simpa [moveCfg,pair_left_empty,pair_right_empty,rightInput,rightOutput,leftInput,leftOutput,temp,List.map_map,
    Equiv.trans_apply,Function.comp_def,two_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using tr

theorem run_true (w out : List Bool) (t : ℕ)
    (h : HMBinPacking.OutputsWithin A w out t) :
    HMBinPacking.OutputsWithin (aux A B) (true::w) out
      (t+2*w.length+2*out.length+5) := by
  obtain ⟨h⟩ := h
  have tr : Trace A.tm.step h.steps (Turing.initList a (w.map A.inputAlphabet.symm))
      (Turing.haltList a (out.map A.outputAlphabet.symm)) := Trace.of_iterate h.evals_in_steps
  have tr' := tr.map (fun c => cfg₁ a b c B.tm.initialState none (fun _ => []) [])
    (fun _ _ hh => step_cfg₁ a b (code A B) (fun _ => rfl)
      B.tm.initialState none (fun _ => []) [] hh)
  have all := Trace.cons (select_true A B w)
    (((input_transfer A B w).trans tr').trans (output_transfer A B out))
  exact ⟨⟨⟨_,all.iterate_eq⟩,by
    change (2*w.length+2+h.steps+(2*out.length+2))+1 ≤ _
    have := h.steps_le_m
    omega⟩⟩

end L3.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true


set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace L3
open OAI.MetricKMedian.Binary F3SubsetSum Turing Polynomial

def toAux (M : Machine) : TM2ComputableAux Bool Bool := ⟨M.tm,Equiv.refl _,Equiv.refl _⟩

theorem outputs_mono {M : TM2ComputableAux Bool Bool} {w out : List Bool} {t u : ℕ}
    (h : HMBinPacking.OutputsWithin M w out t) (hle : t ≤ u) :
    HMBinPacking.OutputsWithin M w out u := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo,h.steps_le_m.trans hle⟩⟩

theorem trace_outputs (M : Machine) (w out : List Bool) (t : ℕ)
    (h : Trace M.step t (M.initialCfg w) (M.finalCfg out)) :
    HMBinPacking.OutputsWithin (toAux M) w out t := by
  have hw : List.map (⇑(Equiv.refl Bool).symm) w = w := List.map_id w
  have ho : List.map (⇑(Equiv.refl Bool).symm) out = out := List.map_id out
  unfold HMBinPacking.OutputsWithin toAux
  change Nonempty (TM2OutputsInTime M.tm
    (w.map (⇑(Equiv.refl Bool).symm)) (some (out.map (⇑(Equiv.refl Bool).symm))) t)
  rw [hw,ho]
  exact ⟨⟨⟨t,h.iterate_eq⟩,le_rfl⟩⟩

noncomputable def composeAux (P Q : TM2ComputableAux Bool Bool) : TM2ComputableAux Bool Bool :=
  ⟨CompCore.compTM P.outputAlphabet Q.inputAlphabet,P.inputAlphabet,Q.outputAlphabet⟩

theorem compose_outputs (P Q : TM2ComputableAux Bool Bool) (w mid out : List Bool) (t u : ℕ)
    (hp : HMBinPacking.OutputsWithin P w mid t)
    (hq : HMBinPacking.OutputsWithin Q mid out u) :
    HMBinPacking.OutputsWithin (composeAux P Q) w out (t+2*mid.length+2+u) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  have hq' : TM2OutputsInTime Q.tm
      ((mid.map P.outputAlphabet.symm).map (fun x => Q.inputAlphabet.symm (P.outputAlphabet x)))
      (some (out.map Q.outputAlphabet.symm)) u := by
    simpa only [List.map_map,Function.comp_def,Equiv.apply_symm_apply] using hq
  have h := CompCore.tm2OutputsInTime_comp P.outputAlphabet Q.inputAlphabet hp hq'
  exact ⟨⟨h.toEvalsTo,by
    have ht := h.steps_le_m
    simp only [List.length_map] at ht
    omega⟩⟩

theorem output_length {M : TM2ComputableAux Bool Bool} {w out : List Bool} {t : ℕ}
    (h : HMBinPacking.OutputsWithin M w out t) :
    out.length ≤ w.length+t*M.tm.growth := by
  obtain ⟨h⟩ := h
  simpa using Turing.TM2OutputsInTime.output_length_le h

theorem poly_bound (P : Polynomial ℕ) (x : ℕ) (hx : 1 ≤ x) :
    P.eval x ≤ P.eval 1*x^P.natDegree := by
  rw [eval_eq_sum_range,eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simp only [one_pow,mul_one]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (by
    have := Finset.mem_range.mp hi
    omega))

theorem poly_power_bound (P : Polynomial ℕ) :
    ∃ C : ℕ, ∀ x : ℕ, 1 ≤ x → P.eval x ≤ C*x^C := by
  refine ⟨P.eval 1+P.natDegree+1,?_⟩
  intro x hx
  exact (poly_bound P x hx).trans
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right hx (by omega)))

noncomputable def generator (G₁ G₂ : TM2ComputableAux Bool Bool) (K d : ℕ) :
    TM2ComputableAux Bool Bool :=
  composeAux (toAux (prepare K d).machine) (Dispatch.aux G₁ G₂)

noncomputable def RTotal (G₁ : TM2ComputableAux Bool Bool) (K d : ℕ) : Polynomial ℕ :=
  RPrepare K d + C (2*G₁.tm.growth+10)*X+20

theorem generator_large (G₁ G₂ : TM2ComputableAux Bool Bool) (K d n m t : ℕ) (out : List Bool)
    (hreg : K*n ≤ m)
    (h : HMBinPacking.OutputsWithin G₁
      (unaryD n++unaryD m++unary (clock d n m)) out t) :
    HMBinPacking.OutputsWithin (generator G₁ G₂ K d) (unaryD n++unary m) out
      ((RTotal G₁ K d).eval (t+n+m+clock d n m+1)) := by
  obtain ⟨p,hp,tr⟩ := prepare_run K d n m
  simp only [if_pos hreg] at tr
  have hpre := trace_outputs (prepare K d).machine _ _ p tr
  have hdispatch := Dispatch.run_true G₁ G₂ _ out t h
  have hc := compose_outputs (toAux (prepare K d).machine) (Dispatch.aux G₁ G₂)
    _ _ _ p _ hpre hdispatch
  have hl := output_length h
  have hlen : (unaryD n++unaryD m++unary (clock d n m)).length = n+m+clock d n m+2 := by
    simp [unaryD,unary]; omega
  have htaglen : (true::(unaryD n++unaryD m++unary (clock d n m))).length =
      n+m+clock d n m+3 := by rw [List.length_cons,hlen]
  have hmono := polynomial_eval_mono (RPrepare K d)
    (show budget K d n m ≤ t+n+m+clock d n m+1 by
      unfold budget; rw [if_pos hreg]; omega)
  apply outputs_mono hc
  simp only [RTotal,eval_add,eval_mul,eval_C,eval_X,eval_ofNat]
  rw [hlen,htaglen] at ⊢
  rw [hlen] at hl
  nlinarith

theorem generator_small (G₁ G₂ : TM2ComputableAux Bool Bool) (K d n m t : ℕ) (out : List Bool)
    (hreg : m<K*n)
    (h : HMBinPacking.OutputsWithin G₂ (unaryD n++unary m) out t) :
    HMBinPacking.OutputsWithin (generator G₁ G₂ K d) (unaryD n++unary m) out
      ((RTotal G₁ K d).eval (t+n+m+1)) := by
  obtain ⟨p,hp,tr⟩ := prepare_run K d n m
  simp only [if_neg (not_le.mpr hreg)] at tr
  have hpre := trace_outputs (prepare K d).machine _ _ p tr
  have hdispatch := Dispatch.run_false G₁ G₂ _ out t h
  have hc := compose_outputs (toAux (prepare K d).machine) (Dispatch.aux G₁ G₂)
    _ _ _ p _ hpre hdispatch
  have hlen : (false::(unaryD n++unary m)).length = n+m+2 := by
    simp [unaryD,unary]; omega
  have hmono := polynomial_eval_mono (RPrepare K d)
    (show budget K d n m ≤ t+n+m+1 by
      unfold budget; rw [if_neg (not_le.mpr hreg)]; omega)
  apply outputs_mono hc
  simp only [RTotal,eval_add,eval_mul,eval_C,eval_X,eval_ofNat]
  rw [hlen]
  nlinarith

end L3

open F3SubsetSum in
theorem solution (G₁ G₂ : Turing.TM2ComputableAux Bool Bool) (K d : ℕ) :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (C : ℕ), ∀ (n m t : ℕ) (out : List Bool),
      (K * n ≤ m →
        HMBinPacking.OutputsWithin G₁
          (unaryD n ++ unaryD m ++ unary (((m + n - 1) / n) ^ (d * ((n ^ 2 + m - 1) / m)))) out t →
        HMBinPacking.OutputsWithin G (unaryD n ++ unary m) out
          (C * (t + n + m + ((m + n - 1) / n) ^ (d * ((n ^ 2 + m - 1) / m)) + 1) ^ C)) ∧
      (m < K * n →
        HMBinPacking.OutputsWithin G₂ (unaryD n ++ unary m) out t →
        HMBinPacking.OutputsWithin G (unaryD n ++ unary m) out (C * (t + n + m + 1) ^ C)) := by
  obtain ⟨C,hC⟩ := L3.poly_power_bound (L3.RTotal G₁ K d)
  refine ⟨L3.generator G₁ G₂ K d,C,?_⟩
  intro n m t out
  constructor
  · intro hreg h
    have h' := L3.generator_large G₁ G₂ K d n m t out hreg (by
      simpa only [L3.clock,L3.base,L3.exponent,pow_two] using h)
    exact L3.outputs_mono h' (by simpa only [L3.clock,L3.base,L3.exponent,pow_two] using
      (hC (t+n+m+L3.clock d n m+1) (by omega)))
  · intro hreg h
    exact L3.outputs_mono (L3.generator_small G₁ G₂ K d n m t out hreg h)
      (hC _ (by omega))
