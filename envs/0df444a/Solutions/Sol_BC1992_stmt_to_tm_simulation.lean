-- Prove2me | solution 1 for BC1992.stmt_to_tm_simulation
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:16:59.18752+00:00
-- url     : https://prove2.me/submissions/4d82644d-82bb-4cb5-b42c-27a18e5b4123

import Definitions.Def_BC1992_Syntax
import Definitions.Def_BC1992_Machines

/-
  FeasibleUnivalence/BC/Poly.lean

  Syntactic univariate polynomials with natural-number coefficients, used as explicit
  time and size certificates throughout the Bellantoni–Cook library.  Polynomials are
  *syntax*; certificates are computed from program syntax by structural recursion and
  only evaluated afterwards.
-/

namespace BC1992





namespace Poly



@[simp] theorem eval_const (c n : Nat) : (Poly.const c).eval n = c := rfl
@[simp] theorem eval_var (n : Nat) : Poly.var.eval n = n := rfl
@[simp] theorem eval_add (p q : Poly) (n : Nat) :
    (Poly.add p q).eval n = p.eval n + q.eval n := rfl
@[simp] theorem eval_mul (p q : Poly) (n : Nat) :
    (Poly.mul p q).eval n = p.eval n * q.eval n := rfl
@[simp] theorem eval_comp (p q : Poly) (n : Nat) :
    (Poly.comp p q).eval n = p.eval (q.eval n) := rfl





/-- Every `Poly` has natural-number coefficients and is therefore monotone. -/
theorem eval_mono (p : Poly) {n m : Nat} (h : n ≤ m) : p.eval n ≤ p.eval m := by
  induction p generalizing n m with
  | const c => exact Nat.le_refl c
  | var => exact h
  | add p q ihp ihq => exact Nat.add_le_add (ihp h) (ihq h)
  | mul p q ihp ihq => exact Nat.mul_le_mul (ihp h) (ihq h)
  | comp p q ihp ihq => exact ihp (ihq h)

theorem le_refl (p : Poly) : p.le p :=
  fun _ ↦ Nat.le_refl _

theorem le_trans {p q r : Poly} (h₁ : p.le q) (h₂ : q.le r) : p.le r :=
  fun n ↦ Nat.le_trans (h₁ n) (h₂ n)



theorem le_eval_sumFin : {k : Nat} → (ps : Fin k → Poly) → (i : Fin k) → (n : Nat) →
    (ps i).eval n ≤ (sumFin ps).eval n
  | _ + 1, ps, ⟨0, _⟩, n => by
    simp only [sumFin, eval_add]
    exact Nat.le_add_right _ _
  | _ + 1, ps, ⟨i + 1, hi⟩, n => by
    simp only [sumFin, eval_add]
    have ih := le_eval_sumFin (fun j => ps j.succ) ⟨i, Nat.lt_of_succ_lt_succ hi⟩ n
    exact Nat.le_trans ih (Nat.le_add_left _ _)

end Poly

end BC1992

/-
  FeasibleUnivalence/BC/Syntax.lean

  Syntax and denotational semantics of the Bellantoni–Cook function algebra
  (S. Bellantoni and S. Cook, "A new recursion-theoretic characterization of the
  polytime functions", Computational Complexity 2 (1992) 97–110), over binary words.

  A program `f : Fn n m` denotes a function `f(x₁,…,xₙ ; y₁,…,yₘ)` with `n` *normal*
  and `m` *safe* arguments.  The constructors are exactly the BC base functions and the
  two BC schemes:

  * `zero`              : the constant `0` (the empty word `ε`), arity `(0;0)`;
  * `projN i`, `projS j` : the projections `π^{n,m}_j` onto a normal resp. safe argument;
  * `s0`, `s1`          : the successors `s₀(;a) = a0`, `s₁(;a) = a1`, arity `(0;1)`;
  * `pred`              : the predecessor `p(;a)` (drop the last bit), arity `(0;1)`;
  * `cond`              : the conditional `C(;a,b,c,d)`, arity `(0;4)`;
  * `comp h r t`        : safe composition
                          `f(x̄;ȳ) = h(r₁(x̄;),…,r_k(x̄;) ; t₁(x̄;ȳ),…,t_l(x̄;ȳ))`;
  * `srec g h₀ h₁`      : predicative (safe) recursion on notation
                          `f(ε,x̄;ȳ) = g(x̄;ȳ)`,
                          `f(sᵢ(w),x̄;ȳ) = hᵢ(w,x̄; f(w,x̄;ȳ), ȳ)`.

  **Representation conventions** (the only deviations from the 1992 paper, both standard
  for the word presentation of BC, cf. Heraud–Nowak ITP 2011):
  * The carrier is `Word = List Bool` rather than `ℕ` in binary.  The head of the list is
    the *last* (least significant) bit, so `sᵢ` is `cons` and `p` is `tail`.
  * Since words have no "leading zero" identification, the conditional has three
    branches: `C(;ε,b,c,d) = b`, `C(;a0,b,c,d) = c`, `C(;a1,b,c,d) = d`.
  * In `srec`, the recursive value is passed as the *first* safe argument of `hᵢ`.

  Arguments are passed as lists; `Fn n m` guarantees that every projection index is in
  range when the lists have the declared lengths.  The `Fin k → Fn n 0` arguments of
  `comp` are *finite tuples of BC subprograms* (syntax), not semantic functions: no
  constructor of `Fn` takes a Lean function on words.
-/


namespace BC1992





@[simp] theorem recIter_nil (g : Word) (h : Bool → Word → Word → Word) :
    recIter g h [] = g := rfl
@[simp] theorem recIter_cons (g : Word) (h : Bool → Word → Word → Word) (b : Bool) (w : Word) :
    recIter g h (b :: w) = h b w (recIter g h w) := rfl



namespace Fn



@[simp] theorem eval_zero (xs ys : List Word) : Fn.zero.eval xs ys = [] := by
  simp [eval]
@[simp] theorem eval_projN {n m : Nat} (i : Fin n) (xs ys : List Word) :
    (Fn.projN (m := m) i).eval xs ys = xs.getD i.val [] := by simp [eval]
@[simp] theorem eval_projS {n m : Nat} (j : Fin m) (xs ys : List Word) :
    (Fn.projS (n := n) j).eval xs ys = ys.getD j.val [] := by simp [eval]
@[simp] theorem eval_s0 (xs ys : List Word) : Fn.s0.eval xs ys = false :: ys.getD 0 [] := by
  simp [eval]
@[simp] theorem eval_s1 (xs ys : List Word) : Fn.s1.eval xs ys = true :: ys.getD 0 [] := by
  simp [eval]
@[simp] theorem eval_pred (xs ys : List Word) : Fn.pred.eval xs ys = (ys.getD 0 []).tail := by
  simp [eval]
@[simp] theorem eval_cond (xs ys : List Word) :
    Fn.cond.eval xs ys = condW (ys.getD 0 []) (ys.getD 1 []) (ys.getD 2 []) (ys.getD 3 []) := by
  simp [eval]
@[simp] theorem eval_comp {n m k l : Nat} (h : Fn k l) (rs : Fin k → Fn n 0)
    (ts : Fin l → Fn n m) (xs ys : List Word) :
    (Fn.comp h rs ts).eval xs ys =
      h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys) := by
  simp [eval]
theorem eval_srec {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1)) (xs ys : List Word) :
    (Fn.srec g h0 h1).eval xs ys =
      recIter (g.eval xs.tail ys)
        (fun b w r => if b then h1.eval (w :: xs.tail) (r :: ys) else h0.eval (w :: xs.tail) (r :: ys))
        (xs.headD []) := by
  simp [eval]

/-- Unfolding of `rec` on an explicit recursion argument `ε`. -/
@[simp] theorem eval_srec_nil {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1))
    (xs ys : List Word) :
    (Fn.srec g h0 h1).eval ([] :: xs) ys = g.eval xs ys := by
  simp [eval_srec]

/-- Unfolding of `rec` on an explicit recursion argument `s_b(w)`. -/
@[simp] theorem eval_srec_cons {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1))
    (b : Bool) (w : Word) (xs ys : List Word) :
    (Fn.srec g h0 h1).eval ((b :: w) :: xs) ys =
      (if b then h1 else h0).eval (w :: xs) ((Fn.srec g h0 h1).eval (w :: xs) ys :: ys) := by
  cases b <;> simp [eval_srec]

/-! ## Syntactic Polynomial Max-Output-Length Bound (Bellantoni–Cook Lemma 2.1) -/



@[simp] theorem maxLen_nil : maxLen [] = 0 := rfl
@[simp] theorem maxLen_cons (y : Word) (ys : List Word) :
    maxLen (y :: ys) = max y.length (maxLen ys) := rfl

theorem length_getD_le_maxLen (ys : List Word) (j : Nat) :
    (ys.getD j []).length ≤ maxLen ys := by
  induction ys generalizing j with
  | nil => simp [List.getD]
  | cons y ys ih =>
    cases j with
    | zero =>
      simp only [List.getD, maxLen_cons]
      exact Nat.le_max_left y.length (maxLen ys)
    | succ j' =>
      simp only [List.getD, maxLen_cons]
      exact Nat.le_trans (ih j') (Nat.le_max_right y.length (maxLen ys))

theorem maxLen_le_of_forall {ys : List Word} {B : Nat} (h : ∀ y ∈ ys, y.length ≤ B) :
    maxLen ys ≤ B := by
  induction ys with
  | nil => exact Nat.zero_le B
  | cons y ys ih =>
    simp only [maxLen_cons]
    have hy : y.length ≤ B := h y (.head ys)
    have hys : maxLen ys ≤ B := ih (fun z hz => h z (.tail y hz))
    omega

theorem maxLen_ofFn_le {l : Nat} (f : Fin l → Word) {B : Nat}
    (h : ∀ j : Fin l, (f j).length ≤ B) :
    maxLen (List.ofFn f) ≤ B := by
  apply maxLen_le_of_forall
  intro y hy
  rcases List.mem_ofFn.mp hy with ⟨j, rfl⟩
  exact h j

theorem length_condW_le (a b c d : Word) {B : Nat}
    (hb : b.length ≤ B) (hc : c.length ≤ B) (hd : d.length ≤ B) :
    (condW a b c d).length ≤ B := by
  cases a with
  | nil => exact hb
  | cons bit _ =>
    cases bit
    · exact hc
    · exact hd





/-- Helper lemma for the `srec` case of `eval_length_le_sizePoly`. -/
theorem recIter_length_le {n m : Nat} (g : Fn n m) (h0 h1 : Fn (n + 1) (m + 1))
    (w : Word) (xs ys : List Word) {N : Nat}
    (hw : w.length ≤ N) (hxs : ∀ x ∈ xs, x.length ≤ N)
    (ihg : (g.eval xs ys).length ≤ g.sizePoly.eval N + maxLen ys)
    (ih0 : ∀ (xs' ys' : List Word), (∀ x ∈ xs', x.length ≤ N) →
      (h0.eval xs' ys').length ≤ h0.sizePoly.eval N + maxLen ys')
    (ih1 : ∀ (xs' ys' : List Word), (∀ x ∈ xs', x.length ≤ N) →
      (h1.eval xs' ys').length ≤ h1.sizePoly.eval N + maxLen ys') :
    (recIter (g.eval xs ys)
      (fun b u r => if b then h1.eval (u :: xs) (r :: ys) else h0.eval (u :: xs) (r :: ys))
      w).length ≤
      w.length * (h0.sizePoly.eval N + h1.sizePoly.eval N) + g.sizePoly.eval N + maxLen ys := by
  induction w with
  | nil =>
    simp only [recIter_nil, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact ihg
  | cons b u ih =>
    simp only [recIter_cons, List.length_cons]
    have hu : u.length ≤ N := by
      simp only [List.length_cons] at hw
      omega
    have huxs : ∀ x ∈ (u :: xs), x.length ≤ N := by
      intro x hx
      cases hx with
      | head => exact hu
      | tail _ hmem => exact hxs x hmem
    have ih_u := ih hu
    have hmax : maxLen (recIter (g.eval xs ys)
        (fun b' u' r' => if b' then h1.eval (u' :: xs) (r' :: ys) else h0.eval (u' :: xs) (r' :: ys)) u :: ys) ≤
        u.length * (h0.sizePoly.eval N + h1.sizePoly.eval N) + g.sizePoly.eval N + maxLen ys := by
      simp only [maxLen_cons]
      omega
    have hmul : (u.length + 1) * (h0.sizePoly.eval N + h1.sizePoly.eval N) =
        u.length * (h0.sizePoly.eval N + h1.sizePoly.eval N) + (h0.sizePoly.eval N + h1.sizePoly.eval N) :=
      Nat.succ_mul u.length _
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hstep := ih0 (u :: xs)
        (recIter (g.eval xs ys) (fun b' u' r' => if b' then h1.eval (u' :: xs) (r' :: ys) else h0.eval (u' :: xs) (r' :: ys)) u :: ys)
        huxs
      omega
    · simp only [↓reduceIte]
      have hstep := ih1 (u :: xs)
        (recIter (g.eval xs ys) (fun b' u' r' => if b' then h1.eval (u' :: xs) (r' :: ys) else h0.eval (u' :: xs) (r' :: ys)) u :: ys)
        huxs
      omega

/-- **Bellantoni–Cook Max-Output-Length Bound (Lemma 2.1)**:
    For every BC program `f : Fn n m`, normal arguments `xs` with `∀ x ∈ xs, x.length ≤ N`,
    and safe arguments `ys`:
    $$|f(\vec{x}; \vec{y})| \le q_f(N) + \max_{y \in \vec{y}} |y|.$$ -/
theorem eval_length_le_sizePoly {n m : Nat} (f : Fn n m) (xs ys : List Word)
    {N : Nat} (hxs : ∀ x ∈ xs, x.length ≤ N) :
    (f.eval xs ys).length ≤ f.sizePoly.eval N + maxLen ys := by
  induction f generalizing xs ys N with
  | zero =>
    simp [eval, sizePoly]
  | projN i =>
    simp only [eval_projN, sizePoly, Poly.eval_var]
    have h1 := length_getD_le_maxLen xs i.val
    have h2 : maxLen xs ≤ N := maxLen_le_of_forall hxs
    omega
  | projS j =>
    simp only [eval_projS, sizePoly, Poly.eval_const, Nat.zero_add]
    exact length_getD_le_maxLen ys j.val
  | s0 =>
    simp only [eval_s0, List.length_cons, sizePoly, Poly.eval_const]
    have h1 := length_getD_le_maxLen ys 0
    omega
  | s1 =>
    simp only [eval_s1, List.length_cons, sizePoly, Poly.eval_const]
    have h1 := length_getD_le_maxLen ys 0
    omega
  | pred =>
    simp only [eval_pred, List.length_tail, sizePoly, Poly.eval_const, Nat.zero_add]
    have h1 := length_getD_le_maxLen ys 0
    omega
  | cond =>
    simp only [eval_cond, sizePoly, Poly.eval_const, Nat.zero_add]
    exact length_condW_le _ _ _ _
      (length_getD_le_maxLen ys 1)
      (length_getD_le_maxLen ys 2)
      (length_getD_le_maxLen ys 3)
  | comp h rs ts ihh ihrs ihts =>
    simp only [eval_comp, sizePoly, Poly.eval_add, Poly.eval_comp]
    have hrs_bound : ∀ x ∈ List.ofFn (fun i => (rs i).eval xs []),
        x.length ≤ (Poly.sumFin fun i => (rs i).sizePoly).eval N := by
      intro x hx
      rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
      have h_i := ihrs i xs [] hxs
      simp only [maxLen_nil, Nat.add_zero] at h_i
      exact Nat.le_trans h_i (Poly.le_eval_sumFin (fun i' => (rs i').sizePoly) i N)
    have hts_bound : maxLen (List.ofFn (fun j => (ts j).eval xs ys)) ≤
        (Poly.sumFin fun j => (ts j).sizePoly).eval N + maxLen ys := by
      apply maxLen_ofFn_le
      intro j
      have h_j := ihts j xs ys hxs
      have h_le := Poly.le_eval_sumFin (fun j' => (ts j').sizePoly) j N
      omega
    have hh := ihh (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys) hrs_bound
    omega
  | srec g h0 h1 ihg ih0 ih1 =>
    simp only [eval_srec, sizePoly, Poly.eval_add, Poly.eval_mul, Poly.eval_var]
    have hhead : (xs.headD []).length ≤ N := by
      cases xs with
      | nil => exact Nat.zero_le N
      | cons x xs' => exact hxs x (.head xs')
    have htail : ∀ x ∈ xs.tail, x.length ≤ N := by
      cases xs with
      | nil => intro _ h; cases h
      | cons x xs' => intro z hz; exact hxs z (.tail x hz)
    have hrec := recIter_length_le g h0 h1 (xs.headD []) xs.tail ys hhead htail
      (ihg xs.tail ys htail)
      (fun xs' ys' hxs' => ih0 xs' ys' hxs')
      (fun xs' ys' hxs' => ih1 xs' ys' hxs')
    have hmul : (xs.headD []).length * (h0.sizePoly.eval N + h1.sizePoly.eval N) ≤
        N * (h0.sizePoly.eval N + h1.sizePoly.eval N) :=
      Nat.mul_le_mul_right _ hhead
    omega

/-- When `f : Fn n 0` has no safe arguments (`ys = []`), its output length is bounded by
    `f.sizePoly.eval N` alone. -/
theorem eval_normal_length_le {n : Nat} (f : Fn n 0) (xs : List Word)
    {N : Nat} (hxs : ∀ x ∈ xs, x.length ≤ N) :
    (f.eval xs []).length ≤ f.sizePoly.eval N := by
  have h := f.eval_length_le_sizePoly xs [] hxs
  simpa using h

/-- For a unary BC function `f : Fn 1 0`, `|f(x;)| ≤ q_f(|x|)`. -/
theorem eval_one_length_le (f : Fn 1 0) (x : Word) :
    (f.eval [x] []).length ≤ f.sizePoly.eval x.length := by
  apply f.eval_normal_length_le [x]
  intro z hz
  cases hz with
  | head => exact Nat.le_refl _
  | tail _ h => cases h

/-- When all normal and safe arguments have length at most `K`, `(f.eval xs ys).length ≤ f.fullSizePoly.eval K`. -/
theorem eval_length_le_fullSizePoly {n m : Nat} (f : Fn n m) (xs ys : List Word)
    {K : Nat} (hxs : ∀ x ∈ xs, x.length ≤ K) (hys : ∀ y ∈ ys, y.length ≤ K) :
    (f.eval xs ys).length ≤ f.fullSizePoly.eval K := by
  simp only [fullSizePoly, Poly.eval_add, Poly.eval_var]
  exact Nat.le_trans (f.eval_length_le_sizePoly xs ys hxs) (Nat.add_le_add_left (maxLen_le_of_forall hys) _)

end Fn



end BC1992

/-
  FeasibleUnivalence/BC/StackProg.lean

  Structured stack programs: an *intermediate compilation language* between
  Bellantoni–Cook programs and Turing machines (it is **not** used to define `FP`).

  A program manipulates finitely many stacks of bits (`Stacks := Nat → Word`, the head of
  a word being the top of the stack) with unit-cost `push`/`pop`, a three-way test on the
  top of a stack, sequencing, and a `while`-loop that runs while a stack is nonempty.
  The big-step judgment `Exec P σ c σ'` says that `P` started on `σ` terminates in `σ'`
  with cost `c`.
-/


namespace BC1992





@[simp] theorem Stacks.set_same (σ : Stacks) (i : Nat) (w : Word) : σ.set i w i = w := by
  simp [Stacks.set]

theorem Stacks.set_other (σ : Stacks) {i j : Nat} (w : Word) (h : j ≠ i) :
    σ.set i w j = σ j := by
  simp [Stacks.set, h]







end BC1992

/-
  FeasibleUnivalence/BC/TM.lean

  An independent machine model for `FP`: deterministic multi-tape Turing machines over a
  finite tape alphabet, with binary input and output.

  * A machine has `k ≥ 1` tapes (tape `0` is the input/output tape), `Q ≥ 1` states
    (state `0` is initial) and tape alphabet `Fin G` with `G ≥ 3`; symbol `0` is the blank,
    symbols `1` and `2` encode the bits `0` and `1`.
  * The transition function `δ q (a₀,…,a_{k-1})` either halts (`none`) or yields a new
    state, a symbol to write on every tape, and a head move `L`/`R`/`S` for every tape.
    Since its domain `Fin Q × (Fin k → Fin G)` is finite, `δ` is a finite table.
  * Tapes are zippers `⟨left, head, right⟩` (with `left` and `right` listed outwards from
    the head).  Moving keeps the representation canonical: a blank is never stored at the
    outer end of `left`/`right`, so a tape is exactly a finitely supported map `ℤ → Fin G`
    together with a head position.
  * Input convention: tape `0` holds the input bits with the head on the first one (or on
    a blank if the input is empty); all other tapes are blank.
  * Output convention: when `M` halts, the output is the maximal word of bit symbols
    read on tape `0` from the head cell rightwards.
  * Time is the number of transitions taken until `δ` returns `none`.

  `FP f` holds iff some machine computes `f` and halts within `p(|x|)` steps for an
  explicit syntactic polynomial `p : Poly`.
-/


namespace BC1992





namespace Tape

variable {Γ : Type} [DecidableEq Γ]







end Tape





namespace TM

variable (M : TM)

























end TM



end BC1992

/-
  FeasibleUnivalence/BC/CompileStmt.lean

  Compilation of structured stack programs (`Stmt` in `StackProg.lean`) to deterministic
  multi-tape Turing machines (`TM` in `TM.lean`), together with the big-step-to-TM
  simulation theorem showing that every `Exec s σ c σ'` is simulated in at most `2 * c`
  TM transitions.
-/


namespace BC1992

/-! ## 1. Basic `TM.run` and `Cfg` Lemmas -/

theorem Cfg.ext {k Q G : Nat} {c₁ c₂ : Cfg k Q G}
    (hs : c₁.state.val = c₂.state.val)
    (ht : ∀ j : Fin k, c₁.tapes j = c₂.tapes j) : c₁ = c₂ := by
  cases c₁
  cases c₂
  simp only [Cfg.mk.injEq] at hs ht ⊢
  exact ⟨Fin.ext hs, funext ht⟩

namespace TM

variable (M : TM)

theorem run_of_step_none {c : Cfg M.k M.Q M.G} (h : M.step c = none) :
    ∀ n : Nat, M.run n c = c
  | 0 => rfl
  | n + 1 => by simp [run, h]

theorem run_add (a b : Nat) (c : Cfg M.k M.Q M.G) :
    M.run (a + b) c = M.run b (M.run a c) := by
  induction a generalizing c with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [run]
    cases h : M.step c with
    | none => exact (M.run_of_step_none h b).symm
    | some c' => exact ih c'

theorem run_one_of_step_some {c c' : Cfg M.k M.Q M.G} (h : M.step c = some c') :
    M.run 1 c = c' := by
  simp [run, h]

@[simp] theorem blank_val : M.blank.val = 0 := rfl

@[simp] theorem bitSym_val (b : Bool) : (M.bitSym b).val = if b then 2 else 1 := rfl

@[simp] theorem decodeBit_blank : M.decodeBit M.blank = none := by
  simp [decodeBit, blank]

@[simp] theorem decodeBit_bitSym (b : Bool) : M.decodeBit (M.bitSym b) = some b := by
  cases b <;> simp [decodeBit, bitSym]

@[simp] theorem readBits_map_bitSym : ∀ w : Word, M.readBits (w.map M.bitSym) = w
  | [] => rfl
  | b :: w => by simp [readBits, readBits_map_bitSym w]

theorem output_of_inputTape (c : Cfg M.k M.Q M.G) (w : Word)
    (h0 : c.tapes ⟨0, M.hk⟩ = M.inputTape w) :
    M.output c = w := by
  unfold output
  rw [h0]
  cases w with
  | nil => simp [inputTape, readBits]
  | cons b w => simp [inputTape, readBits, readBits_map_bitSym]

theorem inputTape_nil : M.inputTape [] = M.blankTape := rfl

theorem write_head_move_S (t : Tape (Fin M.G)) :
    (t.write t.head).move M.blank .S = t := by
  cases t
  rfl

theorem write_head_move_L_inputTape (w : Word) :
    ((M.inputTape w).write (M.inputTape w).head).move M.blank .L =
      ⟨[], M.blank, w.map M.bitSym⟩ := by
  cases w with
  | nil =>
    simp [inputTape, Tape.write, Tape.move, Tape.consB]
  | cons b w =>
    cases w with
    | nil =>
      have hne : M.bitSym b ≠ M.blank := by
        intro h
        have hv := congrArg Fin.val h
        cases b <;> simp [bitSym, blank] at hv
      simp [inputTape, Tape.write, Tape.move, Tape.consB, hne]
    | cons b' w' =>
      simp [inputTape, Tape.write, Tape.move, Tape.consB]

theorem write_bitSym_move_S_after_L (b : Bool) (w : Word) :
    ((⟨[], M.blank, w.map M.bitSym⟩ : Tape (Fin M.G)).write (M.bitSym b)).move M.blank .S =
      M.inputTape (b :: w) := rfl

theorem write_blank_move_R_inputTape (w : Word) :
    ((M.inputTape w).write M.blank).move M.blank .R = M.inputTape w.tail := by
  cases w with
  | nil =>
    simp [inputTape, Tape.write, Tape.move, Tape.consB]
  | cons b w =>
    cases w with
    | nil =>
      simp [inputTape, Tape.write, Tape.move, Tape.consB]
    | cons b' w' =>
      simp [inputTape, Tape.write, Tape.move, Tape.consB]

end TM

/-! ## 2. Stack Bounds & Flat TM Instruction Code (`TMInstr`) -/











@[simp] theorem clampPC_val_of_le {len pc : Nat} (h : pc ≤ len) :
    (clampPC len pc).val = pc := by
  unfold clampPC
  have hlt : pc < len + 1 := Nat.lt_succ_of_le h
  simp [hlt]

@[simp] theorem clampPC_self (len : Nat) :
    clampPC len len = ⟨len, Nat.lt_succ_self len⟩ := by
  ext
  exact clampPC_val_of_le (Nat.le_refl len)







@[simp] theorem codeTM_bitSym (k : Nat) (hk : 0 < k) (code : List TMInstr) (b : Bool) :
    (codeTM k hk code).bitSym b = bitFin3 b := by
  cases b <;> rfl

@[simp] theorem codeTM_blank (k : Nat) (hk : 0 < k) (code : List TMInstr) :
    (codeTM k hk code).blank = blankFin3 := rfl

/-- Canonical `TM` configuration corresponding to program counter `pc` and stack assignment `σ`. -/
def cfgOf (k : Nat) (hk : 0 < k) (code : List TMInstr) (pc : Nat) (σ : Stacks) :
    Cfg (codeTM k hk code).k (codeTM k hk code).Q (codeTM k hk code).G where
  state := clampPC code.length pc
  tapes := fun j => (codeTM k hk code).inputTape (σ j.val)

theorem cfgOf_eq {k : Nat} {hk : 0 < k} {code : List TMInstr}
    {pc₁ pc₂ : Nat} {σ₁ σ₂ : Stacks} (hpc : pc₁ = pc₂) (hσ : ∀ j : Fin k, σ₁ j.val = σ₂ j.val) :
    cfgOf k hk code pc₁ σ₁ = cfgOf k hk code pc₂ σ₂ := by
  subst hpc
  apply Cfg.ext
  · rfl
  · intro j
    simp only [cfgOf]
    rw [hσ j]

theorem init_eq_cfgOf (k : Nat) (hk : 0 < k) (code : List TMInstr) (x : Word) :
    (codeTM k hk code).init x = cfgOf k hk code 0 (initStacks x) := by
  apply Cfg.ext
  · simp [TM.init, cfgOf]
  · intro j
    simp only [TM.init, cfgOf, initStacks]
    by_cases hj : j.val = 0
    · simp [hj]
    · simp [hj, TM.inputTape_nil]

theorem step_cfgOf_end (k : Nat) (hk : 0 < k) (code : List TMInstr) (σ : Stacks) :
    (codeTM k hk code).step (cfgOf k hk code code.length σ) = none := by
  simp [TM.step, codeTM, cfgOf]

/-! ## 3. Subcode Slice Predicate & Single-Instruction Stepping Lemmas -/

/-- `sub` occurs as a contiguous slice of `code` starting at index `pc`. -/
def SubcodeAt (code sub : List TMInstr) (pc : Nat) : Prop :=
  pc + sub.length ≤ code.length ∧
  ∀ j : Nat, j < sub.length → code[pc + j]? = sub[j]?

theorem subcodeAt_self (code : List TMInstr) : SubcodeAt code code 0 := by
  refine ⟨by omega, fun j _ => by simp⟩

theorem subcodeAt_append_left {code s1 s2 : List TMInstr} {pc : Nat}
    (h : SubcodeAt code (s1 ++ s2) pc) : SubcodeAt code s1 pc := by
  rcases h with ⟨hlen, hget⟩
  rw [List.length_append] at hlen
  refine ⟨by omega, fun j hj => ?_⟩
  rw [hget j (by rw [List.length_append]; omega)]
  exact List.getElem?_append_left hj

theorem subcodeAt_append_right {code s1 s2 : List TMInstr} {pc : Nat}
    (h : SubcodeAt code (s1 ++ s2) pc) : SubcodeAt code s2 (pc + s1.length) := by
  rcases h with ⟨hlen, hget⟩
  rw [List.length_append] at hlen
  refine ⟨by omega, fun j hj => ?_⟩
  have h1 := hget (s1.length + j) (by rw [List.length_append]; omega)
  rw [← Nat.add_assoc] at h1
  rw [h1, List.getElem?_append_right (Nat.le_add_right s1.length j)]
  simp [Nat.add_sub_cancel_left]

theorem subcodeAt_singleton {code : List TMInstr} {instr : TMInstr} {pc : Nat}
    (h : SubcodeAt code [instr] pc) :
    pc + 1 ≤ code.length ∧ code[pc]? = some instr := by
  rcases h with ⟨hlen, hget⟩
  have h0 := hget 0 Nat.zero_lt_one
  simp only [Nat.add_zero, List.length_singleton] at h0 hlen
  exact ⟨hlen, h0⟩

theorem step_push_pair {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {i : Nat} (b : Bool) {pc : Nat} (σ : Stacks)
    (hsub : SubcodeAt code [.moveL i, .writeBit i b] pc) :
    (codeTM k hk code).run 2 (cfgOf k hk code pc σ) =
      cfgOf k hk code (pc + 2) (σ.set i (b :: σ i)) := by
  have h1 := subcodeAt_singleton (subcodeAt_append_left (s1 := [.moveL i]) (s2 := [.writeBit i b]) hsub)
  have h2 := subcodeAt_singleton (subcodeAt_append_right (s1 := [.moveL i]) (s2 := [.writeBit i b]) hsub)
  simp only [List.length_singleton] at h2
  have hpc : pc ≤ code.length := by omega
  have hpc1 : pc + 1 ≤ code.length := h1.1
  let midCfg : Cfg (codeTM k hk code).k (codeTM k hk code).Q (codeTM k hk code).G :=
    ⟨clampPC code.length (pc + 1),
     fun j => if j.val = i then ⟨[], (codeTM k hk code).blank, (σ i).map (codeTM k hk code).bitSym⟩
              else (codeTM k hk code).inputTape (σ j.val)⟩
  have hstep1 : (codeTM k hk code).step (cfgOf k hk code pc σ) = some midCfg := by
    unfold TM.step
    rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
          (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
        some (clampPC code.length (pc + 1),
              fun j => ((cfgOf k hk code pc σ).tapes j).head,
              fun j => if j.val = i then .L else .S) by
      simp [codeTM, cfgOf, clampPC_val_of_le hpc, h1.2]]
    dsimp only
    congr 1
    apply Cfg.ext
    · rfl
    · intro j
      dsimp only [midCfg, cfgOf]
      by_cases hj : j.val = i
      · rw [if_pos hj, if_pos hj, ← hj]
        exact (codeTM k hk code).write_head_move_L_inputTape (σ j.val)
      · rw [if_neg hj, if_neg hj]
        exact (codeTM k hk code).write_head_move_S _
  have hstep2 : (codeTM k hk code).step midCfg =
      some (cfgOf k hk code (pc + 2) (σ.set i (b :: σ i))) := by
    unfold TM.step
    have hδ2 : (codeTM k hk code).δ midCfg.state (fun j => (midCfg.tapes j).head) =
        some (clampPC code.length (pc + 1 + 1),
              fun j => if j.val = i then (codeTM k hk code).bitSym b else (midCfg.tapes j).head,
              fun _ => .S) := by
      dsimp only [codeTM, midCfg]
      rw [clampPC_val_of_le hpc1, h2.2]
      rfl
    rw [hδ2]
    dsimp only
    congr 1
    apply Cfg.ext
    · rfl
    · intro j
      dsimp only [midCfg, cfgOf]
      by_cases hj : j.val = i
      · rw [if_pos hj, if_pos hj, hj, Stacks.set_same]
        exact (codeTM k hk code).write_bitSym_move_S_after_L b (σ i)
      · rw [if_neg hj, if_neg hj, Stacks.set_other σ _ hj]
        exact (codeTM k hk code).write_head_move_S _
  change (codeTM k hk code).run (1 + 1) (cfgOf k hk code pc σ) = _
  rw [(codeTM k hk code).run_add 1 1,
      (codeTM k hk code).run_one_of_step_some hstep1,
      (codeTM k hk code).run_one_of_step_some hstep2]

theorem step_popR_single {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {i : Nat} {pc : Nat} (σ : Stacks)
    (hsub : SubcodeAt code [.popR i] pc) :
    (codeTM k hk code).run 1 (cfgOf k hk code pc σ) =
      cfgOf k hk code (pc + 1) (σ.set i (σ i).tail) := by
  rcases subcodeAt_singleton hsub with ⟨hpc1, hget⟩
  have hpc : pc ≤ code.length := by omega
  have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
      some (cfgOf k hk code (pc + 1) (σ.set i (σ i).tail)) := by
    unfold TM.step
    have hδ : (codeTM k hk code).δ (cfgOf k hk code pc σ).state
          (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
        some (clampPC code.length (pc + 1),
              fun j => if j.val = i then (codeTM k hk code).blank else ((cfgOf k hk code pc σ).tapes j).head,
              fun j => if j.val = i then .R else .S) := by
      dsimp only [codeTM, cfgOf]
      rw [clampPC_val_of_le hpc, hget]
      rfl
    rw [hδ]
    dsimp only
    congr 1
    apply Cfg.ext
    · rfl
    · intro j
      dsimp only [cfgOf]
      by_cases hj : j.val = i
      · rw [if_pos hj, if_pos hj, hj, Stacks.set_same]
        exact (codeTM k hk code).write_blank_move_R_inputTape (σ i)
      · rw [if_neg hj, if_neg hj, Stacks.set_other σ _ hj]
        exact (codeTM k hk code).write_head_move_S _
  exact (codeTM k hk code).run_one_of_step_some hstep

theorem step_jump_single {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {target pc : Nat} (σ : Stacks)
    (hsub : SubcodeAt code [.jump target] pc) :
    (codeTM k hk code).run 1 (cfgOf k hk code pc σ) =
      cfgOf k hk code target σ := by
  rcases subcodeAt_singleton hsub with ⟨hpc1, hget⟩
  have hpc : pc ≤ code.length := by omega
  have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
      some (cfgOf k hk code target σ) := by
    unfold TM.step
    rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
          (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
        some (clampPC code.length target,
              fun j => ((cfgOf k hk code pc σ).tapes j).head,
              fun _ => .S) by
      simp [codeTM, cfgOf, TMInstr.jump, clampPC_val_of_le hpc, hget]]
    rfl
  exact (codeTM k hk code).run_one_of_step_some hstep

theorem step_branch_single {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {i pcE pc0 pc1 pc : Nat} (hi : i < k)
    (σ : Stacks) (hsub : SubcodeAt code [.branch i pcE pc0 pc1] pc) :
    (match σ i with
     | [] => (codeTM k hk code).run 1 (cfgOf k hk code pc σ) = cfgOf k hk code pcE σ
     | false :: _ => (codeTM k hk code).run 1 (cfgOf k hk code pc σ) = cfgOf k hk code pc0 σ
     | true :: _ => (codeTM k hk code).run 1 (cfgOf k hk code pc σ) = cfgOf k hk code pc1 σ) := by
  rcases subcodeAt_singleton hsub with ⟨hpc1, hget⟩
  have hpc : pc ≤ code.length := by omega
  cases hσi : σ i with
  | nil =>
    have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
        some (cfgOf k hk code pcE σ) := by
      unfold TM.step
      rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
            (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
          some (clampPC code.length pcE,
                fun j => ((cfgOf k hk code pc σ).tapes j).head,
                fun _ => .S) by
        simp [codeTM, cfgOf, clampPC_val_of_le hpc, hget, hi, hσi, TM.inputTape]]
      rfl
    exact (codeTM k hk code).run_one_of_step_some hstep
  | cons b w =>
    cases b
    · have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
          some (cfgOf k hk code pc0 σ) := by
        unfold TM.step
        rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
              (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
            some (clampPC code.length pc0,
                  fun j => ((cfgOf k hk code pc σ).tapes j).head,
                  fun _ => .S) by
          simp [codeTM, cfgOf, clampPC_val_of_le hpc, hget, hi, hσi, TM.inputTape]]
        rfl
      exact (codeTM k hk code).run_one_of_step_some hstep
    · have hstep : (codeTM k hk code).step (cfgOf k hk code pc σ) =
          some (cfgOf k hk code pc1 σ) := by
        unfold TM.step
        rw [show (codeTM k hk code).δ (cfgOf k hk code pc σ).state
              (fun j => ((cfgOf k hk code pc σ).tapes j).head) =
            some (clampPC code.length pc1,
                  fun j => ((cfgOf k hk code pc σ).tapes j).head,
                  fun _ => .S) by
          simp [codeTM, cfgOf, clampPC_val_of_le hpc, hget, hi, hσi, TM.inputTape]]
        rfl
      exact (codeTM k hk code).run_one_of_step_some hstep

/-! ## 4. Main `Stmt` → `TM` Simulation Theorem -/

/-- Every big-step execution `Exec s σ c σ'` of a stack program `s` (whose stack indices
    are `< k`) is simulated by `(codeTM k hk code)` in at most `2 * c` transitions. -/
theorem exec_sim_tm {k : Nat} (hk : 0 < k) (code : List TMInstr)
    {s : Stmt} {σ σ' : Stacks} {c : Nat} (hexec : Exec s σ c σ')
    (hmax : s.maxStack < k) (pc : Nat)
    (hsub : SubcodeAt code (compileStmt s pc) pc) :
    ∃ steps : Nat,
      steps ≤ 2 * c ∧
      (codeTM k hk code).run steps (cfgOf k hk code pc σ) =
        cfgOf k hk code (pc + (compileStmt s pc).length) σ' := by
  induction hexec generalizing pc with
  | skip σ =>
    exact ⟨0, Nat.le_refl 0, cfgOf_eq (by simp [compileStmt]) (fun _ => rfl)⟩
  | push i b σ =>
    exact ⟨2, Nat.le_refl 2, step_push_pair hk code b σ hsub⟩
  | pop i σ =>
    exact ⟨1, by omega, step_popR_single hk code σ hsub⟩
  | @seq s t σ₁ σ₂ σ₃ c₁ c₂ _ _ ihs iht =>
    simp only [Stmt.maxStack] at hmax
    have hmax_s : s.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_t : t.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hsub_s : SubcodeAt code (compileStmt s pc) pc :=
      subcodeAt_append_left hsub
    have hsub_t : SubcodeAt code (compileStmt t (pc + (compileStmt s pc).length))
        (pc + (compileStmt s pc).length) :=
      subcodeAt_append_right hsub
    rcases ihs hmax_s pc hsub_s with ⟨steps₁, hle₁, hrun₁⟩
    rcases iht hmax_t (pc + (compileStmt s pc).length) hsub_t with ⟨steps₂, hle₂, hrun₂⟩
    refine ⟨steps₁ + steps₂, by omega, ?_⟩
    rw [(codeTM k hk code).run_add steps₁ steps₂, hrun₁, hrun₂]
    exact cfgOf_eq (by simp [compileStmt, List.length_append, Nat.add_assoc]) (fun _ => rfl)
  | @ifE i sE s0 s1 σ σ' c htop _ ihE =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hmax_E : sE.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax_rest
    let pE := pc + 1
    let cE := compileStmt sE pE
    let p0 := pE + cE.length + 1
    let c0 := compileStmt s0 p0
    let p1 := p0 + c0.length + 1
    let c1 := compileStmt s1 p1
    let pEnd := p1 + c1.length
    have hsub_all : SubcodeAt code ([.branch i pE p0 p1] ++ (cE ++ ([.jump pEnd] ++ (c0 ++ ([.jump pEnd] ++ c1))))) pc := by
      simpa [compileStmt, pE, cE, p0, c0, p1, c1, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_cE : SubcodeAt code cE pE := subcodeAt_append_left hsub_r1
    have hsub_r2 := subcodeAt_append_right hsub_r1
    have hsub_jE : SubcodeAt code [.jump pEnd] (pE + cE.length) := subcodeAt_append_left hsub_r2
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    rcases ihE hmax_E pE hsub_cE with ⟨stepsE, hleE, hrunE⟩
    have hjump := step_jump_single hk code σ' hsub_jE
    refine ⟨1 + stepsE + 1, by omega, ?_⟩
    rw [(codeTM k hk code).run_add (1 + stepsE) 1,
        (codeTM k hk code).run_add 1 stepsE,
        hbr, hrunE, hjump]
    exact cfgOf_eq (by simp [compileStmt, pE, cE, p0, c0, p1, c1, pEnd]; omega) (fun _ => rfl)
  | @if0 i sE s0 s1 σ σ' c w htop _ ih0 =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hmax_rest2 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax_rest
    have hmax_0 : s0.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax_rest2
    let pE := pc + 1
    let cE := compileStmt sE pE
    let p0 := pE + cE.length + 1
    let c0 := compileStmt s0 p0
    let p1 := p0 + c0.length + 1
    let c1 := compileStmt s1 p1
    let pEnd := p1 + c1.length
    have hsub_all : SubcodeAt code ([.branch i pE p0 p1] ++ (cE ++ ([.jump pEnd] ++ (c0 ++ ([.jump pEnd] ++ c1))))) pc := by
      simpa [compileStmt, pE, cE, p0, c0, p1, c1, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_r2 := subcodeAt_append_right hsub_r1
    have hsub_r3 := subcodeAt_append_right hsub_r2
    have hsub_c0 : SubcodeAt code c0 p0 := by
      simpa [pE, p0, Nat.add_assoc] using subcodeAt_append_left hsub_r3
    have hsub_r4 := subcodeAt_append_right hsub_r3
    have hsub_j0 : SubcodeAt code [.jump pEnd] (p0 + c0.length) := by
      simpa [pE, p0, Nat.add_assoc] using subcodeAt_append_left hsub_r4
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    rcases ih0 hmax_0 p0 hsub_c0 with ⟨steps0, hle0, hrun0⟩
    have hjump := step_jump_single hk code σ' hsub_j0
    refine ⟨1 + steps0 + 1, by omega, ?_⟩
    rw [(codeTM k hk code).run_add (1 + steps0) 1,
        (codeTM k hk code).run_add 1 steps0,
        hbr, hrun0, hjump]
    exact cfgOf_eq (by simp [compileStmt, pE, cE, p0, c0, p1, c1, pEnd]; omega) (fun _ => rfl)
  | @if1 i sE s0 s1 σ σ' c w htop _ ih1 =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_rest := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    have hmax_rest2 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax_rest
    have hmax_1 : s1.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax_rest2
    let pE := pc + 1
    let cE := compileStmt sE pE
    let p0 := pE + cE.length + 1
    let c0 := compileStmt s0 p0
    let p1 := p0 + c0.length + 1
    let c1 := compileStmt s1 p1
    let pEnd := p1 + c1.length
    have hsub_all : SubcodeAt code ([.branch i pE p0 p1] ++ (cE ++ ([.jump pEnd] ++ (c0 ++ ([.jump pEnd] ++ c1))))) pc := by
      simpa [compileStmt, pE, cE, p0, c0, p1, c1, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_r2 := subcodeAt_append_right hsub_r1
    have hsub_r3 := subcodeAt_append_right hsub_r2
    have hsub_r4 := subcodeAt_append_right hsub_r3
    have hsub_c1 : SubcodeAt code c1 p1 := by
      simpa [pE, p0, p1, Nat.add_assoc] using subcodeAt_append_right hsub_r4
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    rcases ih1 hmax_1 p1 hsub_c1 with ⟨steps1, hle1, hrun1⟩
    refine ⟨1 + steps1, by omega, ?_⟩
    rw [(codeTM k hk code).run_add 1 steps1, hbr, hrun1]
    exact cfgOf_eq (by simp [compileStmt, pE, cE, p0, c0, p1]; omega) (fun _ => rfl)
  | @whileDone i body σ htop =>
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    let pBody := pc + 1
    let cBody := compileStmt body pBody
    let pEnd := pBody + cBody.length + 1
    have hsub_all : SubcodeAt code ([.branch i pEnd pBody pBody] ++ (cBody ++ [.jump pc])) pc := by
      simpa [compileStmt, pBody, cBody, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hbr := step_branch_single hk code hi σ hsub_br
    rw [htop] at hbr
    refine ⟨1, by omega, ?_⟩
    rw [hbr]
    exact cfgOf_eq (by simp [compileStmt, pBody, cBody, pEnd]; omega) (fun _ => rfl)
  | @whileStep i body σ σ' σ'' c c' hne _ _ ihbody ihwhile =>
    have hmax_orig : (Stmt.whileNE i body).maxStack < k := hmax
    simp only [Stmt.maxStack] at hmax
    have hi : i < k := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hmax
    have hmax_body : body.maxStack < k := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hmax
    let pBody := pc + 1
    let cBody := compileStmt body pBody
    let pEnd := pBody + cBody.length + 1
    have hsub_all : SubcodeAt code ([.branch i pEnd pBody pBody] ++ (cBody ++ [.jump pc])) pc := by
      simpa [compileStmt, pBody, cBody, pEnd, List.append_assoc] using hsub
    have hsub_br := subcodeAt_append_left hsub_all
    have hsub_r1 := subcodeAt_append_right hsub_all
    have hsub_cBody : SubcodeAt code cBody pBody := subcodeAt_append_left hsub_r1
    have hsub_jpc : SubcodeAt code [.jump pc] (pBody + cBody.length) := subcodeAt_append_right hsub_r1
    have hbr := step_branch_single hk code hi σ hsub_br
    have hbr_step : (codeTM k hk code).run 1 (cfgOf k hk code pc σ) =
        cfgOf k hk code pBody σ := by
      cases hσi : σ i with
      | nil => exact absurd hσi hne
      | cons b w =>
        rw [hσi] at hbr
        cases b <;> exact hbr
    rcases ihbody hmax_body pBody hsub_cBody with ⟨stepsB, hleB, hrunB⟩
    have hjump := step_jump_single hk code σ' hsub_jpc
    rcases ihwhile hmax_orig pc hsub with ⟨stepsW, hleW, hrunW⟩
    refine ⟨1 + stepsB + 1 + stepsW, by omega, ?_⟩
    rw [(codeTM k hk code).run_add (1 + stepsB + 1) stepsW,
        (codeTM k hk code).run_add (1 + stepsB) 1,
        (codeTM k hk code).run_add 1 stepsB,
        hbr_step, hrunB, hjump, hrunW]



/-- If `s` executes on `initStacks x` with cost `c` and post-state `σ'`, then `stmtToTM s`
    halts on `x` within `2 * c` steps with output `σ' 0`. -/
theorem stmtToTM_haltsWithin (s : Stmt) (x : Word) {c : Nat} {σ' : Stacks}
    (hexec : Exec s (initStacks x) c σ') :
    (stmtToTM s).HaltsWithin x (2 * c) (σ' 0) := by
  let k := s.maxStack + 1
  have hk : 0 < k := Nat.zero_lt_succ _
  let code := compileStmt s 0
  have hmax : s.maxStack < k := Nat.lt_succ_self _
  rcases exec_sim_tm hk code hexec hmax 0 (subcodeAt_self code) with ⟨steps, hle, hrun⟩
  refine ⟨steps, hle, ?_, ?_⟩
  · change (codeTM k hk code).step ((codeTM k hk code).run steps ((codeTM k hk code).init x)) = none
    rw [init_eq_cfgOf k hk code x, hrun]
    have hcfg : cfgOf k hk code (0 + code.length) σ' = cfgOf k hk code code.length σ' :=
      cfgOf_eq (Nat.zero_add _) (fun _ => rfl)
    rw [hcfg]
    exact step_cfgOf_end k hk code σ'
  · change (codeTM k hk code).output ((codeTM k hk code).run steps ((codeTM k hk code).init x)) = σ' 0
    rw [init_eq_cfgOf k hk code x, hrun]
    exact (codeTM k hk code).output_of_inputTape _ (σ' 0) rfl

end BC1992

open BC1992

/-- **Multi-Stack to Multi-Tape Turing Machine Simulation (`stmtToTM_haltsWithin`)**:
    For every structured stack program `s : Stmt`, input word `x : Word`, step count `c : Nat`,
    and final stack assignment `σ' : Stacks`, if `Exec s (initStacks x) c σ'` holds, then the
    compiled deterministic multi-tape Turing machine `stmtToTM s` halts on input `x` within
    `2 * c` transitions with output word `σ' 0`. -/
theorem solution :
    ∀ (s : Stmt) (x : Word) {c : Nat} {σ' : Stacks},
      Exec s (initStacks x) c σ' →
      (stmtToTM s).HaltsWithin x (2 * c) (σ' 0) := by
  exact stmtToTM_haltsWithin
