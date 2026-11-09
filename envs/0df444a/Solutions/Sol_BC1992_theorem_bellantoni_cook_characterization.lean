-- Prove2me | solution 1 for BC1992.theorem_bellantoni_cook_characterization
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:28:15.141597+00:00
-- url     : https://prove2.me/submissions/466604c4-1602-41ae-9165-f55ec195e0f3

import Definitions.Def_BC1992_Syntax
import Definitions.Def_BC1992_Machines
import Definitions.Def_BC1992_Simulation

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

/-
  FeasibleUnivalence/BC/Soundness.lean

  Polynomial-time soundness of the Bellantoni–Cook function algebra (`BCDefinable f → FP f`):
  1. Compiles every BC program `f : Fn n m` into a structured stack program `compileBC base f : Stmt`
     and synthesizes an explicit polynomial time bound `f.timePoly : Poly` purely from the
     syntax of `f`.
  2. Proves that `compileBC base f` evaluates `f.eval xs ys` into stack `base` within
     `f.timePoly.eval K` steps whenever all input words in `xs` and `ys` have length `≤ K`.
  3. Combines with `stmtToTM_haltsWithin` from `CompileStmt.lean` to obtain a multi-tape
     Turing machine `M : TM` and polynomial `p : Poly` witnessing `FP f`.
-/


namespace BC1992

/-! ## 1. Extensionality & Frame Helpers on `Stacks` -/

theorem Stacks.set_set_same (σ : Stacks) (i : Nat) (w₁ w₂ : Word) :
    (σ.set i w₁).set i w₂ = σ.set i w₂ := by
  funext j
  simp only [Stacks.set]
  by_cases h : j = i <;> simp [h]

theorem Stacks.set_set_comm (σ : Stacks) {i j : Nat} (w₁ w₂ : Word) (hne : i ≠ j) :
    (σ.set i w₁).set j w₂ = (σ.set j w₂).set i w₁ := by
  funext k
  simp only [Stacks.set]
  by_cases hki : k = i
  · subst hki
    have hkj : k ≠ j := hne
    simp [hkj]
  · by_cases hkj : k = j
    · subst hkj; simp [hki]
    · simp [hki, hkj]

theorem Stacks.set_eq_self {σ : Stacks} {i : Nat} {w : Word} (h : σ i = w) :
    σ.set i w = σ := by
  funext j
  simp only [Stacks.set]
  by_cases hj : j = i
  · subst hj; simp [h]
  · simp [hj]



@[simp] theorem setFrame_nil (σ : Stacks) (start : Nat) :
    setFrame σ start [] = σ := rfl

@[simp] theorem setFrame_cons (σ : Stacks) (start : Nat) (w : Word) (ws : List Word) :
    setFrame σ start (w :: ws) = (setFrame σ (start + 1) ws).set start w := rfl

theorem setFrame_outside (σ : Stacks) (start : Nat) (ws : List Word) (r : Nat)
    (hr : r < start ∨ start + ws.length ≤ r) :
    setFrame σ start ws r = σ r := by
  induction ws generalizing start with
  | nil => rfl
  | cons w ws ih =>
    simp only [setFrame_cons, List.length_cons] at hr ⊢
    have hne : r ≠ start := by omega
    rw [Stacks.set_other _ _ hne]
    exact ih (start + 1) (by omega)

theorem setFrame_get (σ : Stacks) (start : Nat) (ws : List Word) (i : Nat) (hi : i < ws.length) :
    setFrame σ start ws (start + i) = ws.getD i [] := by
  induction ws generalizing start i with
  | nil => contradiction
  | cons w ws ih =>
    simp only [setFrame_cons, List.length_cons] at hi ⊢
    cases i with
    | zero =>
      simp [List.getD]
    | succ i' =>
      have hne : start + (i' + 1) ≠ start := by omega
      rw [Stacks.set_other _ _ hne]
      have heq : start + (i' + 1) = (start + 1) + i' := by omega
      rw [heq, ih (start + 1) i' (by omega)]
      rfl

theorem setFrame_append (σ : Stacks) (start : Nat) (ws₁ ws₂ : List Word) :
    setFrame (setFrame σ (start + ws₁.length) ws₂) start ws₁ =
      setFrame σ start (ws₁ ++ ws₂) := by
  induction ws₁ generalizing start with
  | nil => simp
  | cons w ws₁ ih =>
    simp only [List.length_cons, List.cons_append, setFrame_cons]
    have hadd : start + (ws₁.length + 1) = (start + 1) + ws₁.length := by omega
    rw [hadd, ih (start + 1)]

theorem setFrame_set_below (σ : Stacks) (start : Nat) (ws : List Word)
    {i : Nat} (w : Word) (hi : i < start) :
    setFrame (σ.set i w) start ws = (setFrame σ start ws).set i w := by
  induction ws generalizing start with
  | nil => rfl
  | cons u ws ih =>
    simp only [setFrame_cons]
    rw [ih (start + 1) (by omega), Stacks.set_set_comm _ _ _ (by omega)]

/-! ## 2. Basic Stack Manipulation Macros in `Stmt` -/



theorem exec_clearStack_aux (dst : Nat) :
    ∀ (w : Word) (σ : Stacks), σ dst = w →
      Exec (clearStack dst) σ (2 * w.length + 1) (σ.set dst [])
  | [], σ, hw => by
    have hdone := Exec.whileDone (body := .pop dst) hw
    rw [Stacks.set_eq_self hw]
    exact hdone
  | b :: w, σ, hw => by
    have hne : σ dst ≠ [] := by rw [hw]; exact List.cons_ne_nil b w
    have hpop : Exec (.pop dst) σ 1 (σ.set dst w) := by
      have hp := Exec.pop dst σ
      rw [hw] at hp
      exact hp
    have ih := exec_clearStack_aux dst w (σ.set dst w) (Stacks.set_same σ dst w)
    rw [Stacks.set_set_same] at ih
    have hstep := Exec.whileStep hne hpop ih
    have hcost : 1 + (2 * w.length + 1) + 1 = 2 * (b :: w).length + 1 := by
      simp [List.length_cons]; omega
    rw [hcost] at hstep
    exact hstep

theorem exec_clearStack (dst : Nat) (σ : Stacks) :
    Exec (clearStack dst) σ (2 * (σ dst).length + 1) (σ.set dst []) :=
  exec_clearStack_aux dst (σ dst) σ rfl



theorem exec_moveRev_aux {src dst : Nat} (hne : src ≠ dst) :
    ∀ (w : Word) (σ : Stacks), σ src = w →
      Exec (moveRev src dst) σ (4 * w.length + 1)
        ((σ.set src []).set dst (w.reverse ++ σ dst))
  | [], σ, hw => by
    have hdone := Exec.whileDone (i := src)
      (body := .ifTop src .skip (.seq (.pop src) (.push dst false)) (.seq (.pop src) (.push dst true))) hw
    have hst : ((σ.set src []).set dst ([].reverse ++ σ dst)) = σ := by
      simp only [List.reverse_nil, List.nil_append]
      rw [Stacks.set_eq_self hw, Stacks.set_eq_self rfl]
    rw [hst]
    exact hdone
  | b :: w, σ, hw => by
    have hne_nil : σ src ≠ [] := by rw [hw]; exact List.cons_ne_nil b w
    let body := Stmt.ifTop src .skip
      (.seq (.pop src) (.push dst false))
      (.seq (.pop src) (.push dst true))
    have hbody : Exec body σ 3 ((σ.set src w).set dst (b :: σ dst)) := by
      have hpop : Exec (.pop src) σ 1 (σ.set src w) := by
        have hp := Exec.pop src σ
        rw [hw] at hp
        exact hp
      have hpush : Exec (.push dst b) (σ.set src w) 1 ((σ.set src w).set dst (b :: σ dst)) := by
        have hpu := Exec.push dst b (σ.set src w)
        rw [Stacks.set_other σ w hne.symm] at hpu
        exact hpu
      have hseq := Exec.seq hpop hpush
      cases b
      · exact Exec.if0 hw hseq
      · exact Exec.if1 hw hseq
    let σ' := (σ.set src w).set dst (b :: σ dst)
    have hσ'_src : σ' src = w := by
      simp [σ', Stacks.set_other _ _ hne]
    have ih := exec_moveRev_aux hne w σ' hσ'_src
    have hst : (σ'.set src []).set dst (w.reverse ++ σ' dst) =
        (σ.set src []).set dst ((b :: w).reverse ++ σ dst) := by
      simp only [σ', Stacks.set_same]
      rw [Stacks.set_set_comm (σ.set src w) (b :: σ dst) [] hne.symm,
          Stacks.set_set_same,
          Stacks.set_set_same,
          List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [hst] at ih
    have hstep := Exec.whileStep hne_nil hbody ih
    have hcost : 3 + (4 * w.length + 1) + 1 = 4 * (b :: w).length + 1 := by
      simp [List.length_cons]; omega
    rw [hcost] at hstep
    exact hstep

theorem exec_moveRev {src dst : Nat} (hne : src ≠ dst) (σ : Stacks) :
    Exec (moveRev src dst) σ (4 * (σ src).length + 1)
      ((σ.set src []).set dst ((σ src).reverse ++ σ dst)) :=
  exec_moveRev_aux hne (σ src) σ rfl



theorem exec_dupRev_aux {tmp src dst : Nat}
    (hts : tmp ≠ src) (htd : tmp ≠ dst) (hsd : src ≠ dst) :
    ∀ (u : Word) (σ : Stacks), σ tmp = u →
      Exec (dupRev tmp src dst) σ (5 * u.length + 1)
        (((σ.set tmp []).set src (u.reverse ++ σ src)).set dst (u.reverse ++ σ dst))
  | [], σ, hu => by
    have hdone := Exec.whileDone (i := tmp)
      (body := .ifTop tmp .skip
        (.seq (.pop tmp) (.seq (.push src false) (.push dst false)))
        (.seq (.pop tmp) (.seq (.push src true) (.push dst true)))) hu
    have hst : (((σ.set tmp []).set src ([].reverse ++ σ src)).set dst ([].reverse ++ σ dst)) = σ := by
      simp only [List.reverse_nil, List.nil_append]
      rw [Stacks.set_eq_self hu, Stacks.set_eq_self rfl, Stacks.set_eq_self rfl]
    rw [hst]
    exact hdone
  | b :: u, σ, hu => by
    have hne_nil : σ tmp ≠ [] := by rw [hu]; exact List.cons_ne_nil b u
    let body := Stmt.ifTop tmp .skip
      (.seq (.pop tmp) (.seq (.push src false) (.push dst false)))
      (.seq (.pop tmp) (.seq (.push src true) (.push dst true)))
    let σ' := ((σ.set tmp u).set src (b :: σ src)).set dst (b :: σ dst)
    have hbody : Exec body σ 4 σ' := by
      have hpop : Exec (.pop tmp) σ 1 (σ.set tmp u) := by
        have hp := Exec.pop tmp σ
        rw [hu] at hp
        exact hp
      have hpush1 : Exec (.push src b) (σ.set tmp u) 1 ((σ.set tmp u).set src (b :: σ src)) := by
        have hp1 := Exec.push src b (σ.set tmp u)
        rw [Stacks.set_other σ u hts.symm] at hp1
        exact hp1
      have hpush2 : Exec (.push dst b) ((σ.set tmp u).set src (b :: σ src)) 1 σ' := by
        have hp2 := Exec.push dst b ((σ.set tmp u).set src (b :: σ src))
        rw [Stacks.set_other _ _ hsd.symm, Stacks.set_other σ u htd.symm] at hp2
        exact hp2
      have hseq := Exec.seq hpop (Exec.seq hpush1 hpush2)
      cases b
      · exact Exec.if0 hu hseq
      · exact Exec.if1 hu hseq
    have hσ'_tmp : σ' tmp = u := by
      simp [σ', Stacks.set_other _ _ htd, Stacks.set_other _ _ hts]
    have ih := exec_dupRev_aux hts htd hsd u σ' hσ'_tmp
    have hst : ((σ'.set tmp []).set src (u.reverse ++ σ' src)).set dst (u.reverse ++ σ' dst) =
        (((σ.set tmp []).set src ((b :: u).reverse ++ σ src)).set dst ((b :: u).reverse ++ σ dst)) := by
      funext k
      simp only [σ', Stacks.set]
      by_cases hkd : k = dst
      · simp [hkd, List.reverse_cons, List.append_assoc]
      · by_cases hks : k = src
        · subst hks
          simp [hkd, List.reverse_cons, List.append_assoc]
        · by_cases hkt : k = tmp
          · subst hkt; simp [hkd, hks]
          · simp [hkd, hks, hkt]
    rw [hst] at ih
    have hstep := Exec.whileStep hne_nil hbody ih
    have hcost : 4 + (5 * u.length + 1) + 1 = 5 * (b :: u).length + 1 := by
      simp [List.length_cons]; omega
    rw [hcost] at hstep
    exact hstep

theorem exec_dupRev {tmp src dst : Nat}
    (hts : tmp ≠ src) (htd : tmp ≠ dst) (hsd : src ≠ dst) (σ : Stacks) :
    Exec (dupRev tmp src dst) σ (5 * (σ tmp).length + 1)
      (((σ.set tmp []).set src ((σ tmp).reverse ++ σ src)).set dst ((σ tmp).reverse ++ σ dst)) :=
  exec_dupRev_aux hts htd hsd (σ tmp) σ rfl



theorem exec_copyToEmpty {src dst tmp : Nat}
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (σ : Stacks) (hdst : σ dst = []) (htmp : σ tmp = []) :
    Exec (copyToEmpty src dst tmp) σ (9 * (σ src).length + 2) (σ.set dst (σ src)) := by
  have h1 := exec_moveRev hst σ
  rw [htmp, List.append_nil] at h1
  let σ₁ := (σ.set src []).set tmp (σ src).reverse
  have h2 := exec_dupRev hst.symm hdt.symm hsd σ₁
  have hσ₁_tmp : σ₁ tmp = (σ src).reverse := Stacks.set_same _ _ _
  have hσ₁_src : σ₁ src = [] := by simp [σ₁, Stacks.set_other _ _ hst]
  have hσ₁_dst : σ₁ dst = [] := by simp [σ₁, Stacks.set_other _ _ hdt, Stacks.set_other _ _ hsd.symm, hdst]
  rw [hσ₁_tmp, hσ₁_src, hσ₁_dst, List.length_reverse, List.reverse_reverse,
      List.append_nil] at h2
  have hst_final : (((σ₁.set tmp []).set src (σ src)).set dst (σ src)) = σ.set dst (σ src) := by
    funext k
    simp only [σ₁, Stacks.set]
    by_cases hkd : k = dst
    · simp [hkd]
    · by_cases hks : k = src
      · subst hks; simp [hkd]
      · by_cases hkt : k = tmp
        · subst hkt; simp [hkd, hks, htmp.symm]
        · simp [hkd, hks, hkt]
  rw [hst_final] at h2
  have hseq := Exec.seq h1 h2
  have hcost : (4 * (σ src).length + 1) + (5 * (σ src).length + 1) = 9 * (σ src).length + 2 := by omega
  rw [hcost] at hseq
  exact hseq



theorem exec_moveStack {src dst tmp : Nat}
    (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (σ : Stacks) (hdst : σ dst = []) (htmp : σ tmp = []) :
    Exec (moveStack src dst tmp) σ (8 * (σ src).length + 2) ((σ.set src []).set dst (σ src)) := by
  have h1 := exec_moveRev hst σ
  rw [htmp, List.append_nil] at h1
  let σ₁ := (σ.set src []).set tmp (σ src).reverse
  have h2 := exec_moveRev hdt.symm σ₁
  have hσ₁_tmp : σ₁ tmp = (σ src).reverse := Stacks.set_same _ _ _
  have hσ₁_dst : σ₁ dst = [] := by simp [σ₁, Stacks.set_other _ _ hdt, Stacks.set_other _ _ hsd.symm, hdst]
  rw [hσ₁_tmp, hσ₁_dst, List.length_reverse, List.reverse_reverse, List.append_nil] at h2
  have hst_final : ((σ₁.set tmp []).set dst (σ src)) = (σ.set src []).set dst (σ src) := by
    funext k
    simp only [σ₁, Stacks.set]
    by_cases hkd : k = dst
    · simp [hkd]
    · by_cases hkt : k = tmp
      · subst hkt; simp [hkd, hst.symm, htmp.symm]
      · simp [hkd, hkt]
  rw [hst_final] at h2
  have hseq := Exec.seq h1 h2
  have hcost : (4 * (σ src).length + 1) + (4 * (σ src).length + 1) = 8 * (σ src).length + 2 := by omega
  rw [hcost] at hseq
  exact hseq

/-! ## 3. Range Copy & Range Clear Macros -/



theorem exec_copyRange (src dst : Nat) (ws : List Word) (tmp : Nat) (σ : Stacks) {K : Nat}
    (hdisj : src + ws.length ≤ dst)
    (htmp_ge : dst + ws.length ≤ tmp)
    (hsrc : ∀ i : Nat, i < ws.length → σ (src + i) = ws.getD i [])
    (hdst : ∀ r : Nat, dst ≤ r → r < dst + ws.length → σ r = [])
    (htmp : σ tmp = [])
    (hlen : ∀ w ∈ ws, w.length ≤ K) :
    ∃ c : Nat,
      c ≤ ws.length * (9 * K + 2) ∧
      Exec (copyRange src dst ws.length tmp) σ c (setFrame σ dst ws) := by
  induction ws generalizing src dst σ with
  | nil =>
    exact ⟨0, Nat.zero_le _, Exec.skip σ⟩
  | cons w ws ih =>
    simp only [List.length_cons, copyRange, setFrame_cons] at hdisj htmp_ge hsrc hdst ⊢
    have hsrc' : ∀ i : Nat, i < ws.length → σ ((src + 1) + i) = ws.getD i [] := by
      intro i hi
      have h1 := hsrc (i + 1) (by omega)
      have heq : src + (i + 1) = (src + 1) + i := by omega
      rw [← heq, h1]
      rfl
    have hdst' : ∀ r : Nat, dst + 1 ≤ r → r < (dst + 1) + ws.length → σ r = [] :=
      fun r hr1 hr2 => hdst r (by omega) (by omega)
    have hlen' : ∀ u ∈ ws, u.length ≤ K :=
      fun u hu => hlen u (.tail w hu)
    rcases ih (src + 1) (dst + 1) σ (by omega) (by omega) hsrc' hdst' htmp hlen' with
      ⟨c₁, hc₁, hexec₁⟩
    let σ₁ := setFrame σ (dst + 1) ws
    have hσ₁_src : σ₁ src = w := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) ws src (by omega)]
      have h0 := hsrc 0 (by omega)
      simpa using h0
    have hσ₁_dst : σ₁ dst = [] := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) ws dst (by omega)]
      exact hdst dst (Nat.le_refl dst) (by omega)
    have hσ₁_tmp : σ₁ tmp = [] := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) ws tmp (by omega)]
      exact htmp
    have hcopy := exec_copyToEmpty (src := src) (dst := dst) (tmp := tmp)
      (by omega) (by omega) (by omega) σ₁ hσ₁_dst hσ₁_tmp
    rw [hσ₁_src] at hcopy
    have hw_le : w.length ≤ K := hlen w (.head ws)
    have hmul : (ws.length + 1) * (9 * K + 2) = ws.length * (9 * K + 2) + (9 * K + 2) :=
      Nat.succ_mul ws.length (9 * K + 2)
    exact ⟨c₁ + (9 * w.length + 2), by omega, Exec.seq hexec₁ hcopy⟩



theorem exec_clearRange (dst : Nat) (ws : List Word) (σ : Stacks) {K : Nat}
    (hempty : ∀ r : Nat, dst ≤ r → σ r = [])
    (hlen : ∀ w ∈ ws, w.length ≤ K) :
    ∃ c : Nat,
      c ≤ ws.length * (2 * K + 1) ∧
      Exec (clearRange dst ws.length) (setFrame σ dst ws) c σ := by
  induction ws generalizing dst with
  | nil =>
    exact ⟨0, Nat.zero_le _, Exec.skip σ⟩
  | cons w ws ih =>
    simp only [List.length_cons, clearRange, setFrame_cons]
    have h1 := exec_clearStack dst ((setFrame σ (dst + 1) ws).set dst w)
    rw [Stacks.set_same, Stacks.set_set_same] at h1
    have hset_nil : (setFrame σ (dst + 1) ws).set dst [] = setFrame σ (dst + 1) ws := by
      apply Stacks.set_eq_self
      rw [setFrame_outside σ (dst + 1) ws dst (by omega)]
      exact hempty dst (Nat.le_refl dst)
    rw [hset_nil] at h1
    rcases ih (dst + 1) (fun r hr => hempty r (by omega)) (fun u hu => hlen u (.tail w hu)) with
      ⟨c₂, hc₂, hexec₂⟩
    have hw_le : w.length ≤ K := hlen w (.head ws)
    have hmul : (ws.length + 1) * (2 * K + 1) = ws.length * (2 * K + 1) + (2 * K + 1) :=
      Nat.succ_mul ws.length (2 * K + 1)
    exact ⟨(2 * w.length + 1) + c₂, by omega, Exec.seq h1 hexec₂⟩

/-! ## 4. List & Subprogram Evaluation Combinators -/

theorem getD_append_left (xs ys : List Word) (i : Nat) (hi : i < xs.length) :
    (xs ++ ys).getD i [] = xs.getD i [] := by
  induction xs generalizing i with
  | nil => contradiction
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [List.length_cons] at hi
      exact ih i' (by omega)

theorem getD_append_right (xs ys : List Word) (j : Nat) :
    (xs ++ ys).getD (xs.length + j) [] = ys.getD j [] := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons, List.cons_append]
    have hadd : (xs.length + 1) + j = (xs.length + j) + 1 := by omega
    rw [hadd]
    exact ih

theorem getD_length_le (ws : List Word) (i : Nat) {K : Nat} (h : ∀ w ∈ ws, w.length ≤ K) :
    (ws.getD i []).length ≤ K :=
  Nat.le_trans (Fn.length_getD_le_maxLen ws i) (Fn.maxLen_le_of_forall h)



theorem exec_evalSubTo (src : Nat) (args : List Word) (dst workBase : Nat)
    (sub : Stmt) (σ : Stacks) (val : Word) {K K_out c_sub : Nat}
    (hsrc_wb : src + args.length ≤ workBase + 1)
    (hdst_wb : dst < workBase)
    (hsrc : ∀ i : Nat, i < args.length → σ (src + i) = args.getD i [])
    (hdst : σ dst = [])
    (hwb : ∀ r : Nat, workBase ≤ r → σ r = [])
    (hlen : ∀ w ∈ args, w.length ≤ K)
    (hval : val.length ≤ K_out)
    (hsub : Exec sub (setFrame σ (workBase + 1) args) c_sub
              ((setFrame σ (workBase + 1) args).set workBase val)) :
    ∃ c : Nat,
      c ≤ c_sub + args.length * (11 * K + 3) + (8 * K_out + 2) ∧
      Exec (evalSubTo src args.length dst workBase sub) σ c (σ.set dst val) := by
  rcases exec_copyRange src (workBase + 1) args (workBase + 1 + args.length) σ
      hsrc_wb (Nat.le_refl _) hsrc
      (fun r hr _ => hwb r (by omega))
      (hwb _ (by omega))
      hlen with
    ⟨c₁, hc₁, hexec₁⟩
  have hframe_eq : (setFrame σ (workBase + 1) args).set workBase val =
      setFrame (σ.set workBase val) (workBase + 1) args :=
    (setFrame_set_below σ (workBase + 1) args val (by omega)).symm
  rw [hframe_eq] at hsub
  rcases exec_clearRange (workBase + 1) args (σ.set workBase val)
      (fun r hr => by rw [Stacks.set_other _ _ (by omega)]; exact hwb r (by omega)) hlen with
    ⟨c₂, hc₂, hexec₂⟩
  have hmove := exec_moveStack (src := workBase) (dst := dst) (tmp := workBase + 1)
    (by omega) (by omega) (by omega) (σ.set workBase val)
    (by rw [Stacks.set_other _ _ (by omega)]; exact hdst)
    (by rw [Stacks.set_other _ _ (by omega)]; exact hwb (workBase + 1) (by omega))
  rw [Stacks.set_same, Stacks.set_set_same, Stacks.set_eq_self (hwb workBase (Nat.le_refl _))] at hmove
  have hmul : args.length * (11 * K + 3) = args.length * (9 * K + 2) + args.length * (2 * K + 1) := by
    rw [← Nat.mul_add]
    have h1 : 9 * K + 2 + (2 * K + 1) = 11 * K + 3 := by omega
    rw [h1]
  exact ⟨c₁ + (c_sub + (c₂ + (8 * val.length + 2))),
    by omega,
    Exec.seq hexec₁ (Exec.seq hsub (Exec.seq hexec₂ hmove))⟩



theorem exec_evalTuple (src : Nat) (args : List Word) (dst workBase : Nat) :
    ∀ {k : Nat} (subs : Fin k → Stmt) (vals : Fin k → Word) (ps : Fin k → Poly)
      (σ : Stacks) {K K_out : Nat},
      src + args.length ≤ dst →
      dst + k ≤ workBase →
      (∀ i : Nat, i < args.length → σ (src + i) = args.getD i []) →
      (∀ r : Nat, dst ≤ r → r < dst + k → σ r = []) →
      (∀ r : Nat, workBase ≤ r → σ r = []) →
      (∀ w ∈ args, w.length ≤ K) →
      (∀ i : Fin k, (vals i).length ≤ K_out) →
      (∀ (i : Fin k) (σ' : Stacks), (∀ r : Nat, workBase ≤ r → σ' r = []) →
        ∃ c : Nat, c ≤ (ps i).eval K ∧
          Exec (subs i) (setFrame σ' (workBase + 1) args) c
            ((setFrame σ' (workBase + 1) args).set workBase (vals i))) →
      ∃ c : Nat,
        c ≤ (Poly.sumFin ps).eval K + k * (args.length * (11 * K + 3) + (8 * K_out + 2)) ∧
        Exec (evalTuple src args.length dst workBase subs) σ c
          (setFrame σ dst (List.ofFn vals))
  | 0, subs, vals, ps, σ, K, K_out, _, _, _, _, _, _, _, _ => by
    simp only [evalTuple, Poly.sumFin, Poly.eval_const, Nat.zero_mul, Nat.add_zero,
      List.ofFn_zero, setFrame_nil]
    exact ⟨0, Nat.le_refl 0, Exec.skip σ⟩
  | k + 1, subs, vals, ps, σ, K, K_out, hsrc_dst, hdst_wb, hsrc, hdst, hwb, hlen, hvals, hsubs => by
    simp only [evalTuple, Poly.sumFin, Poly.eval_add, List.ofFn_succ, setFrame_cons]
    rcases exec_evalTuple src args (dst + 1) workBase
        (fun i => subs i.succ) (fun i => vals i.succ) (fun i => ps i.succ) σ
        (by omega) (by omega) hsrc
        (fun r hr1 hr2 => hdst r (by omega) (by omega))
        hwb hlen
        (fun i => hvals i.succ)
        (fun i σ' hσ' => hsubs i.succ σ' hσ') with
      ⟨c₁, hc₁, hexec₁⟩
    let σ₁ := setFrame σ (dst + 1) (List.ofFn (fun i : Fin k => vals i.succ))
    have hσ₁_wb : ∀ r : Nat, workBase ≤ r → σ₁ r = [] := by
      intro r hr
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) _ r (by simp [List.length_ofFn]; omega)]
      exact hwb r hr
    have hσ₁_src : ∀ i : Nat, i < args.length → σ₁ (src + i) = args.getD i [] := by
      intro i hi
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) _ (src + i) (by omega)]
      exact hsrc i hi
    have hσ₁_dst : σ₁ dst = [] := by
      dsimp only [σ₁]
      rw [setFrame_outside σ (dst + 1) _ dst (by omega)]
      exact hdst dst (Nat.le_refl dst) (by omega)
    rcases hsubs ⟨0, Nat.zero_lt_succ k⟩ σ₁ hσ₁_wb with ⟨c_sub, hc_sub, hexec_sub⟩
    rcases exec_evalSubTo src args dst workBase (subs ⟨0, Nat.zero_lt_succ k⟩) σ₁ (vals ⟨0, Nat.zero_lt_succ k⟩)
        (by omega) (by omega) hσ₁_src hσ₁_dst hσ₁_wb hlen (hvals ⟨0, Nat.zero_lt_succ k⟩) hexec_sub with
      ⟨c₂, hc₂, hexec₂⟩
    have hmul : (k + 1) * (args.length * (11 * K + 3) + (8 * K_out + 2)) =
        k * (args.length * (11 * K + 3) + (8 * K_out + 2)) +
          (args.length * (11 * K + 3) + (8 * K_out + 2)) :=
      Nat.succ_mul k _
    exact ⟨c₁ + c₂, by omega, Exec.seq hexec₁ hexec₂⟩

/-! ## 5. Safe Recursion (`srec`) Loop Combinators -/





theorem exec_evalRecStep (base n m : Nat) (b : Bool) (sub : Stmt)
    (σ_loop : Stacks) (u v' : Word) (xs_tail ys : List Word) (acc newAcc : Word)
    {K_rec c_sub : Nat}
    (hxs_len : xs_tail.length = n) (hys_len : ys.length = m)
    (hacc : σ_loop base = acc)
    (hu : σ_loop (base + 1) = u)
    (hxs : ∀ i : Nat, i < n → σ_loop (base + 2 + i) = xs_tail.getD i [])
    (hys : ∀ j : Nat, j < m → σ_loop (base + 2 + n + j) = ys.getD j [])
    (hrev : σ_loop (base + 2 + n + m) = b :: v')
    (hwb : ∀ r : Nat, base + 3 + n + m ≤ r → σ_loop r = [])
    (hu_le : u.length ≤ K_rec)
    (hxs_le : ∀ x ∈ xs_tail, x.length ≤ K_rec)
    (hys_le : ∀ y ∈ ys, y.length ≤ K_rec)
    (hacc_le : acc.length ≤ K_rec)
    (hnew_le : newAcc.length ≤ K_rec)
    (hsub : Exec sub
      (setFrame σ_loop ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys)))
      c_sub
      ((setFrame σ_loop ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
        (base + 3 + n + m) newAcc)) :
    ∃ c : Nat,
      c ≤ c_sub + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 5) ∧
      Exec (evalRecStep base n m b sub) σ_loop c
        (((σ_loop.set base newAcc).set (base + 2 + n + m) v').set (base + 1) (b :: u)) := by
  let revW := base + 2 + n + m
  let workBase := base + 3 + n + m
  let tmp := workBase + 1 + (n + 1) + (m + 1)
  have hys_copy : ∃ c₁, c₁ ≤ m * (9 * K_rec + 2) ∧
      Exec (copyRange (base + 2 + n) (workBase + 1 + (n + 1) + 1) m tmp) σ_loop c₁
        (setFrame σ_loop (workBase + 1 + (n + 1) + 1) ys) := by
    rw [← hys_len]
    exact exec_copyRange (base + 2 + n) (workBase + 1 + (n + 1) + 1) ys tmp σ_loop
      (by omega) (by omega)
      (fun j hj => hys j (by omega))
      (fun r hr _ => hwb r (by omega))
      (hwb _ (by omega))
      hys_le
  rcases hys_copy with ⟨c₁, hc₁, hexec₁⟩
  let σ₁ := setFrame σ_loop (workBase + 1 + (n + 1) + 1) ys
  have hacc_copy : Exec (copyToEmpty base (workBase + 1 + (n + 1)) tmp) σ₁ (9 * acc.length + 2)
      (setFrame σ_loop (workBase + 1 + (n + 1)) (acc :: ys)) := by
    have hcp := exec_copyToEmpty (src := base) (dst := workBase + 1 + (n + 1)) (tmp := tmp)
      (by omega) (by omega) (by omega) σ₁
      (by dsimp only [σ₁]; rw [setFrame_outside _ _ _ _ (by omega)]; exact hwb _ (by omega))
      (by dsimp only [σ₁]; rw [setFrame_outside _ _ _ _ (by omega)]; exact hwb _ (by omega))
    have hσ₁_base : σ₁ base = acc := by
      dsimp only [σ₁]
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hacc
    rw [hσ₁_base] at hcp
    exact hcp
  let σ₂ := setFrame σ_loop (workBase + 1 + (n + 1)) (acc :: ys)
  have huxs_len : (u :: xs_tail).length = n + 1 := by simp [hxs_len]
  have huxs_le : ∀ x ∈ (u :: xs_tail), x.length ≤ K_rec := by
    intro x hx
    cases hx with
    | head => exact hu_le
    | tail _ hm => exact hxs_le x hm
  have huxs_src : ∀ i : Nat, i < (u :: xs_tail).length → σ₂ (base + 1 + i) = (u :: xs_tail).getD i [] := by
    intro i hi
    dsimp only [σ₂]
    rw [setFrame_outside _ _ _ _ (by omega)]
    cases i with
    | zero => simpa using hu
    | succ i' =>
      have heq : base + 1 + (i' + 1) = base + 2 + i' := by omega
      rw [heq]
      exact hxs i' (by omega)
  have huxs_copy : ∃ c₃, c₃ ≤ (n + 1) * (9 * K_rec + 2) ∧
      Exec (copyRange (base + 1) (workBase + 1) (n + 1) tmp) σ₂ c₃
        (setFrame σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys))) := by
    rcases exec_copyRange (base + 1) (workBase + 1) (u :: xs_tail) tmp σ₂
        (by simp [hxs_len]; omega) (by simp [hxs_len]; omega) huxs_src
        (fun r hr1 hr2 => by
          dsimp only [σ₂]
          rw [setFrame_outside _ _ _ _ (by simp [hxs_len] at hr2; omega)]
          exact hwb r (by omega))
        (by
          dsimp only [σ₂, tmp]
          rw [setFrame_outside _ _ _ _ (by simp [hys_len])]
          exact hwb _ (by omega))
        huxs_le with
      ⟨c₃, hc₃, hexec₃⟩
    have happ : setFrame σ₂ (workBase + 1) (u :: xs_tail) =
        setFrame σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) := by
      dsimp only [σ₂]
      rw [← huxs_len]
      exact setFrame_append σ_loop (workBase + 1) (u :: xs_tail) (acc :: ys)
    rw [happ] at hexec₃
    rw [huxs_len] at hc₃ hexec₃
    exact ⟨c₃, hc₃, hexec₃⟩
  rcases huxs_copy with ⟨c₃, hc₃, hexec₃⟩
  have hframe_eq : (setFrame σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys))).set workBase newAcc =
      setFrame (σ_loop.set workBase newAcc) (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) :=
    (setFrame_set_below σ_loop (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) newAcc (by omega)).symm
  rw [hframe_eq] at hsub
  have hall_len : ((u :: xs_tail) ++ (acc :: ys)).length = (n + 1) + (m + 1) := by
    simp [hxs_len, hys_len]; omega
  have hall_le : ∀ w ∈ ((u :: xs_tail) ++ (acc :: ys)), w.length ≤ K_rec := by
    intro w hw
    rcases List.mem_append.mp hw with h1 | h2
    · exact huxs_le w h1
    · cases h2 with
      | head => exact hacc_le
      | tail _ hm => exact hys_le w hm
  have hclear_args : ∃ c₅, c₅ ≤ ((n + 1) + (m + 1)) * (2 * K_rec + 1) ∧
      Exec (clearRange (workBase + 1) ((n + 1) + (m + 1)))
        (setFrame (σ_loop.set workBase newAcc) (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)))
        c₅ (σ_loop.set workBase newAcc) := by
    rw [← hall_len]
    exact exec_clearRange (workBase + 1) ((u :: xs_tail) ++ (acc :: ys)) (σ_loop.set workBase newAcc)
      (fun r hr => by rw [Stacks.set_other _ _ (by omega)]; exact hwb r (by omega))
      hall_le
  rcases hclear_args with ⟨c₅, hc₅, hexec₅⟩
  have hclear_base : Exec (clearStack base) (σ_loop.set workBase newAcc) (2 * acc.length + 1)
      ((σ_loop.set workBase newAcc).set base []) := by
    have hcl := exec_clearStack base (σ_loop.set workBase newAcc)
    rw [Stacks.set_other _ _ (by omega), hacc] at hcl
    exact hcl
  have hmove_base : Exec (moveStack workBase base (workBase + 1))
      ((σ_loop.set workBase newAcc).set base []) (8 * newAcc.length + 2)
      (σ_loop.set base newAcc) := by
    have hmv := exec_moveStack (src := workBase) (dst := base) (tmp := workBase + 1)
      (by omega) (by omega) (by omega) ((σ_loop.set workBase newAcc).set base [])
      (Stacks.set_same _ _ _)
      (by
        rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
        exact hwb (workBase + 1) (by omega))
    have hwb_val : ((σ_loop.set workBase newAcc).set base []) workBase = newAcc := by
      rw [Stacks.set_other _ _ (by omega), Stacks.set_same]
    rw [hwb_val] at hmv
    have hst : ((((σ_loop.set workBase newAcc).set base []).set workBase []).set base newAcc) =
        σ_loop.set base newAcc := by
      rw [Stacks.set_set_comm (σ_loop.set workBase newAcc) [] [] (by omega),
          Stacks.set_set_same,
          Stacks.set_set_same,
          Stacks.set_eq_self (hwb workBase (Nat.le_refl _))]
    rw [hst] at hmv
    exact hmv
  have hpop_rev : Exec (.pop revW) (σ_loop.set base newAcc) 1
      ((σ_loop.set base newAcc).set revW v') := by
    have hp := Exec.pop revW (σ_loop.set base newAcc)
    have hrev_val : (σ_loop.set base newAcc) revW = b :: v' := by
      rw [Stacks.set_other _ _ (by omega)]
      exact hrev
    rw [hrev_val] at hp
    exact hp
  have hpush_u : Exec (.push (base + 1) b) ((σ_loop.set base newAcc).set revW v') 1
      (((σ_loop.set base newAcc).set revW v').set (base + 1) (b :: u)) := by
    have hpu := Exec.push (base + 1) b ((σ_loop.set base newAcc).set revW v')
    have hu_val : ((σ_loop.set base newAcc).set revW v') (base + 1) = u := by
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hu
    rw [hu_val] at hpu
    exact hpu
  have hcost_arith :
      c₁ + ((9 * acc.length + 2) + (c₃ + (c_sub + (c₅ + ((2 * acc.length + 1) + ((8 * newAcc.length + 2) + (1 + 1))))))) ≤
      c_sub + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 5) := by
    have h1 : ((n + 1) + (m + 1)) * (11 * K_rec + 3) =
        m * (9 * K_rec + 2) + (9 * K_rec + 2) + (n + 1) * (9 * K_rec + 2) +
          ((n + 1) + (m + 1)) * (2 * K_rec + 1) := by
      have ha : (n + 1) + (m + 1) = m + 1 + (n + 1) := by omega
      have hb : 11 * K_rec + 3 = (9 * K_rec + 2) + (2 * K_rec + 1) := by omega
      rw [hb, Nat.mul_add, ha, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    omega
  exact ⟨_, hcost_arith,
    Exec.seq hexec₁ (Exec.seq hacc_copy (Exec.seq hexec₃ (Exec.seq hsub
      (Exec.seq hexec₅ (Exec.seq hclear_base (Exec.seq hmove_base (Exec.seq hpop_rev hpush_u)))))))⟩

/-- Loop invariant state for `recLoop`:
    - `base` holds `recIter gVal stepFn u`
    - `base + 2 + n + m` (`revW`) holds `v`
    - `base + 1` holds `u` -/
def recLoopState (σ₀ : Stacks) (base n m : Nat) (gVal : Word)
    (stepFn : Bool → Word → Word → Word) (u v : Word) : Stacks :=
  (((σ₀.set base (recIter gVal stepFn u)).set (base + 2 + n + m) v).set (base + 1) u)

theorem recLoopState_update (σ₀ : Stacks) (base n m : Nat) (gVal : Word)
    (stepFn : Bool → Word → Word → Word) (u v v' : Word) (b : Bool) :
    ((((recLoopState σ₀ base n m gVal stepFn u v).set base (recIter gVal stepFn (b :: u))).set
        (base + 2 + n + m) v').set (base + 1) (b :: u)) =
      recLoopState σ₀ base n m gVal stepFn (b :: u) v' := by
  simp only [recLoopState]
  rw [Stacks.set_set_comm _ u (recIter gVal stepFn (b :: u)) (by omega),
      Stacks.set_set_comm _ u v' (by omega),
      Stacks.set_set_same,
      Stacks.set_set_comm (σ₀.set base (recIter gVal stepFn u)) v (recIter gVal stepFn (b :: u)) (by omega),
      Stacks.set_set_same,
      Stacks.set_set_same]

theorem exec_recLoop (base n m : Nat) (sub0 sub1 : Stmt)
    (σ₀ : Stacks) (xs_tail ys : List Word) (gVal : Word)
    (stepFn : Bool → Word → Word → Word) {K K_rec C_step : Nat}
    (hK_le : K ≤ K_rec)
    (hxs_len : xs_tail.length = n) (hys_len : ys.length = m)
    (hxs : ∀ i : Nat, i < n → σ₀ (base + 2 + i) = xs_tail.getD i [])
    (hys : ∀ j : Nat, j < m → σ₀ (base + 2 + n + j) = ys.getD j [])
    (hwb : ∀ r : Nat, base + 3 + n + m ≤ r → σ₀ r = [])
    (hxs_le : ∀ x ∈ xs_tail, x.length ≤ K_rec)
    (hys_le : ∀ y ∈ ys, y.length ≤ K_rec)
    (hrec_le : ∀ u : Word, u.length ≤ K → (recIter gVal stepFn u).length ≤ K_rec)
    (hstep0 : ∀ (u acc : Word) (σ' : Stacks),
      u.length ≤ K_rec → acc.length ≤ K_rec →
      (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
      ∃ c : Nat, c ≤ C_step ∧
        Exec sub0 (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
          ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
            (base + 3 + n + m) (stepFn false u acc)))
    (hstep1 : ∀ (u acc : Word) (σ' : Stacks),
      u.length ≤ K_rec → acc.length ≤ K_rec →
      (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
      ∃ c : Nat, c ≤ C_step ∧
        Exec sub1 (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
          ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
            (base + 3 + n + m) (stepFn true u acc))) :
    ∀ (v u : Word), v.length + u.length ≤ K →
      ∃ c : Nat,
        c ≤ v.length * (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) + 1 ∧
        Exec (recLoop base n m sub0 sub1)
          (recLoopState σ₀ base n m gVal stepFn u v)
          c
          (recLoopState σ₀ base n m gVal stepFn (v.reverse ++ u) [])
  | [], u, _ => by
    have hrev : recLoopState σ₀ base n m gVal stepFn u [] (base + 2 + n + m) = [] := by
      simp only [recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_same]
    have hdone := Exec.whileDone (i := base + 2 + n + m)
      (body := .ifTop (base + 2 + n + m) .skip (evalRecStep base n m false sub0) (evalRecStep base n m true sub1))
      hrev
    simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_mul, Nat.zero_add]
    exact ⟨1, Nat.le_refl 1, hdone⟩
  | b :: v', u, hvu => by
    simp only [List.length_cons] at hvu
    let σ_loop := recLoopState σ₀ base n m gVal stepFn u (b :: v')
    have hrev : σ_loop (base + 2 + n + m) = b :: v' := by
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_same]
    have hne : σ_loop (base + 2 + n + m) ≠ [] := by
      rw [hrev]; exact List.cons_ne_nil b v'
    have hloop_base : σ_loop base = recIter gVal stepFn u := by
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_same]
    have hloop_u : σ_loop (base + 1) = u := by
      dsimp only [σ_loop, recLoopState]
      exact Stacks.set_same _ _ _
    have hloop_xs : ∀ i : Nat, i < n → σ_loop (base + 2 + i) = xs_tail.getD i [] := by
      intro i hi
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hxs i hi
    have hloop_ys : ∀ j : Nat, j < m → σ_loop (base + 2 + n + j) = ys.getD j [] := by
      intro j hj
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hys j hj
    have hloop_wb : ∀ r : Nat, base + 3 + n + m ≤ r → σ_loop r = [] := by
      intro r hr
      dsimp only [σ_loop, recLoopState]
      rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
      exact hwb r hr
    have hu_le_K : u.length ≤ K := by omega
    have hbu_le_K : (b :: u).length ≤ K := by simp [List.length_cons]; omega
    have hu_le : u.length ≤ K_rec := by omega
    have hacc_le : (recIter gVal stepFn u).length ≤ K_rec := hrec_le u hu_le_K
    have hnew_le : (recIter gVal stepFn (b :: u)).length ≤ K_rec := hrec_le (b :: u) hbu_le_K
    have hbody : ∃ c_b : Nat,
        c_b ≤ C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 6) ∧
        Exec (.ifTop (base + 2 + n + m) .skip (evalRecStep base n m false sub0) (evalRecStep base n m true sub1))
          σ_loop c_b (recLoopState σ₀ base n m gVal stepFn (b :: u) v') := by
      cases b with
      | false =>
        rcases hstep0 u (recIter gVal stepFn u) σ_loop hu_le hacc_le hloop_wb with
          ⟨c_sub, hc_sub, hexec_sub⟩
        rcases exec_evalRecStep base n m false sub0 σ_loop u v' xs_tail ys
            (recIter gVal stepFn u) (recIter gVal stepFn (false :: u))
            hxs_len hys_len hloop_base hloop_u hloop_xs hloop_ys hrev hloop_wb
            hu_le hxs_le hys_le hacc_le hnew_le hexec_sub with
          ⟨c_step, hc_step, hexec_step⟩
        rw [recLoopState_update] at hexec_step
        exact ⟨c_step + 1, by omega, Exec.if0 hrev hexec_step⟩
      | true =>
        rcases hstep1 u (recIter gVal stepFn u) σ_loop hu_le hacc_le hloop_wb with
          ⟨c_sub, hc_sub, hexec_sub⟩
        rcases exec_evalRecStep base n m true sub1 σ_loop u v' xs_tail ys
            (recIter gVal stepFn u) (recIter gVal stepFn (true :: u))
            hxs_len hys_len hloop_base hloop_u hloop_xs hloop_ys hrev hloop_wb
            hu_le hxs_le hys_le hacc_le hnew_le hexec_sub with
          ⟨c_step, hc_step, hexec_step⟩
        rw [recLoopState_update] at hexec_step
        exact ⟨c_step + 1, by omega, Exec.if1 hrev hexec_step⟩
    rcases hbody with ⟨c_b, hc_b, hexec_b⟩
    rcases exec_recLoop base n m sub0 sub1 σ₀ xs_tail ys gVal stepFn
        hK_le hxs_len hys_len hxs hys hwb hxs_le hys_le hrec_le hstep0 hstep1
        v' (b :: u) (by simp [List.length_cons]; omega) with
      ⟨c_rest, hc_rest, hexec_rest⟩
    have hrev_app : v'.reverse ++ (b :: u) = (b :: v').reverse ++ u := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev_app] at hexec_rest
    have hmul : (v'.length + 1) * (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) =
        v'.length * (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) +
          (C_step + ((n + 1) + (m + 1)) * (11 * K_rec + 3) + (10 * K_rec + 7)) :=
      Nat.succ_mul v'.length _
    simp only [List.length_cons]
    exact ⟨c_b + c_rest + 1, by omega, Exec.whileStep hne hexec_b hexec_rest⟩

/-! ## 6. Compiler from `BC.Fn` to `StackProg.Stmt` and Polynomial-Time Soundness -/



@[simp] theorem Poly.eval_linear (a b n : Nat) :
    (Poly.linear a b).eval n = a * n + b := rfl





/-- **Big-step correctness and polynomial time bound for `compileBC`**:
    For every BC program `f : Fn n m`, frame base `base`, normal inputs `xs` (`xs.length = n`),
    and safe inputs `ys` (`ys.length = m`) with all input lengths `≤ K`,
    `compileBC base f` evaluates `f.eval xs ys` into stack `base` within `f.timePoly.eval K` steps,
    preserving all argument stacks and restoring all scratch stacks above the frame to `[]`. -/
theorem exec_compileBC {n m : Nat} (f : Fn n m) (base : Nat) (σ : Stacks)
    (xs ys : List Word) (K : Nat)
    (hxs : xs.length = n) (hys : ys.length = m)
    (hempty : ∀ r : Nat, base ≤ r → σ r = [])
    (hlenX : ∀ x ∈ xs, x.length ≤ K)
    (hlenY : ∀ y ∈ ys, y.length ≤ K) :
    ∃ c : Nat,
      c ≤ f.timePoly.eval K ∧
      Exec (compileBC base f)
        (setFrame σ (base + 1) (xs ++ ys))
        c
        ((setFrame σ (base + 1) (xs ++ ys)).set base (f.eval xs ys)) := by
  induction f generalizing base σ xs ys K with
  | zero =>
    simp only [compileBC, Fn.timePoly, Poly.eval_const, Fn.eval_zero]
    have hbase : setFrame σ (base + 1) (xs ++ ys) base = [] := by
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hempty base (Nat.le_refl base)
    rw [Stacks.set_eq_self hbase]
    exact ⟨0, by omega, Exec.skip _⟩
  | @projN n m i =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_projN]
    have hi : i.val < n := i.isLt
    have hbase : setFrame σ (base + 1) (xs ++ ys) base = [] := by
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hempty base (Nat.le_refl base)
    have htmp : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + m) = [] := by
      rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
      exact hempty _ (by omega)
    have hsrc : setFrame σ (base + 1) (xs ++ ys) (base + 1 + i.val) = xs.getD i.val [] := by
      rw [setFrame_get _ _ _ i.val (by simp [hxs, hys]; omega)]
      exact getD_append_left xs ys i.val (by omega)
    have hcp := exec_copyToEmpty (src := base + 1 + i.val) (dst := base) (tmp := base + 1 + n + m)
      (by omega) (by omega) (by omega) (setFrame σ (base + 1) (xs ++ ys)) hbase htmp
    rw [hsrc] at hcp
    have hlen_i : (xs.getD i.val []).length ≤ K := getD_length_le xs i.val hlenX
    exact ⟨9 * (xs.getD i.val []).length + 2, by omega, hcp⟩
  | @projS n m j =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_projS]
    have hj : j.val < m := j.isLt
    have hbase : setFrame σ (base + 1) (xs ++ ys) base = [] := by
      rw [setFrame_outside _ _ _ _ (by omega)]
      exact hempty base (Nat.le_refl base)
    have htmp : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + m) = [] := by
      rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
      exact hempty _ (by omega)
    have hsrc : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + j.val) = ys.getD j.val [] := by
      have heq : base + 1 + n + j.val = (base + 1) + (xs.length + j.val) := by omega
      rw [heq, setFrame_get _ _ _ (xs.length + j.val) (by simp [hxs, hys])]
      exact getD_append_right xs ys j.val
    have hcp := exec_copyToEmpty (src := base + 1 + n + j.val) (dst := base) (tmp := base + 1 + n + m)
      (by omega) (by omega) (by omega) (setFrame σ (base + 1) (xs ++ ys)) hbase htmp
    rw [hsrc] at hcp
    have hlen_j : (ys.getD j.val []).length ≤ K := getD_length_le ys j.val hlenY
    exact ⟨9 * (ys.getD j.val []).length + 2, by omega, hcp⟩
  | s0 =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_s0]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 2) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hsrc : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hcp := exec_copyToEmpty (src := base + 1) (dst := base) (tmp := base + 2)
        (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
      rw [hsrc] at hcp
      have hpush := Exec.push base false ((setFrame σ (base + 1) ys).set base (ys.getD 0 []))
      rw [Stacks.set_same, Stacks.set_set_same] at hpush
      have hlen0 : (ys.getD 0 []).length ≤ K := getD_length_le ys 0 hlenY
      exact ⟨(9 * (ys.getD 0 []).length + 2) + 1, by omega, Exec.seq hcp hpush⟩
  | s1 =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_s1]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 2) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hsrc : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hcp := exec_copyToEmpty (src := base + 1) (dst := base) (tmp := base + 2)
        (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
      rw [hsrc] at hcp
      have hpush := Exec.push base true ((setFrame σ (base + 1) ys).set base (ys.getD 0 []))
      rw [Stacks.set_same, Stacks.set_set_same] at hpush
      have hlen0 : (ys.getD 0 []).length ≤ K := getD_length_le ys 0 hlenY
      exact ⟨(9 * (ys.getD 0 []).length + 2) + 1, by omega, Exec.seq hcp hpush⟩
  | pred =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_pred]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 2) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hsrc : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hcp := exec_copyToEmpty (src := base + 1) (dst := base) (tmp := base + 2)
        (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
      rw [hsrc] at hcp
      have hpop := Exec.pop base ((setFrame σ (base + 1) ys).set base (ys.getD 0 []))
      rw [Stacks.set_same, Stacks.set_set_same] at hpop
      have hlen0 : (ys.getD 0 []).length ≤ K := getD_length_le ys 0 hlenY
      exact ⟨(9 * (ys.getD 0 []).length + 2) + 1, by omega, Exec.seq hcp hpop⟩
  | cond =>
    simp only [compileBC, Fn.timePoly, Poly.eval_linear, Fn.eval_cond]
    cases xs with
    | cons _ _ => contradiction
    | nil =>
      simp only [List.nil_append]
      have hbase : setFrame σ (base + 1) ys base = [] := by
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have htmp : setFrame σ (base + 1) ys (base + 5) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hys])]
        exact hempty _ (by omega)
      have hy0 : setFrame σ (base + 1) ys (base + 1) = ys.getD 0 [] := by
        have hget := setFrame_get σ (base + 1) ys 0 (by omega)
        simpa using hget
      have hy1 : setFrame σ (base + 1) ys (base + 2) = ys.getD 1 [] := by
        have hget := setFrame_get σ (base + 1) ys 1 (by omega)
        have heq : (base + 1) + 1 = base + 2 := by omega
        rw [heq] at hget; exact hget
      have hy2 : setFrame σ (base + 1) ys (base + 3) = ys.getD 2 [] := by
        have hget := setFrame_get σ (base + 1) ys 2 (by omega)
        have heq : (base + 1) + 2 = base + 3 := by omega
        rw [heq] at hget; exact hget
      have hy3 : setFrame σ (base + 1) ys (base + 4) = ys.getD 3 [] := by
        have hget := setFrame_get σ (base + 1) ys 3 (by omega)
        have heq : (base + 1) + 3 = base + 4 := by omega
        rw [heq] at hget; exact hget
      cases h0 : ys.getD 0 [] with
      | nil =>
        simp only [condW]
        rw [h0] at hy0
        have hcp := exec_copyToEmpty (src := base + 2) (dst := base) (tmp := base + 5)
          (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
        rw [hy1] at hcp
        have hlen1 : (ys.getD 1 []).length ≤ K := getD_length_le ys 1 hlenY
        exact ⟨(9 * (ys.getD 1 []).length + 2) + 1, by omega, Exec.ifE hy0 hcp⟩
      | cons b w =>
        rw [h0] at hy0
        cases b with
        | false =>
          simp only [condW]
          have hcp := exec_copyToEmpty (src := base + 3) (dst := base) (tmp := base + 5)
            (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
          rw [hy2] at hcp
          have hlen2 : (ys.getD 2 []).length ≤ K := getD_length_le ys 2 hlenY
          exact ⟨(9 * (ys.getD 2 []).length + 2) + 1, by omega, Exec.if0 hy0 hcp⟩
        | true =>
          simp only [condW]
          have hcp := exec_copyToEmpty (src := base + 4) (dst := base) (tmp := base + 5)
            (by omega) (by omega) (by omega) (setFrame σ (base + 1) ys) hbase htmp
          rw [hy3] at hcp
          have hlen3 : (ys.getD 3 []).length ≤ K := getD_length_le ys 3 hlenY
          exact ⟨(9 * (ys.getD 3 []).length + 2) + 1, by omega, Exec.if1 hy0 hcp⟩
  | @comp n m k l h rs ts ihh ihrs ihts =>
    simp only [compileBC, Fn.timePoly, Poly.eval, Poly.eval_linear, Fn.eval_comp]
    have hxy_len : (xs ++ ys).length = n + m := by simp [hxs, hys]
    have hxy_le : ∀ w ∈ (xs ++ ys), w.length ≤ K := by
      intro w hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hlenX w h1
      · exact hlenY w h2
    have h_arg_rs : ∀ i : Fin k, ((rs i).eval xs []).length ≤
        (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
        (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro i
      have h1 := (rs i).eval_length_le_fullSizePoly xs [] hlenX (by intro _ h; cases h)
      have h2 := Poly.le_eval_sumFin (fun i' => (rs i').fullSizePoly) i K
      omega
    have h_arg_ts : ∀ j : Fin l, ((ts j).eval xs ys).length ≤
        (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
        (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro j
      have h1 := (ts j).eval_length_le_fullSizePoly xs ys hlenX hlenY
      have h2 := Poly.le_eval_sumFin (fun j' => (ts j').fullSizePoly) j K
      omega
    have hts_tuple : ∃ c₁ : Nat,
        c₁ ≤ (Poly.sumFin fun j => (ts j).timePoly).eval K +
          l * ((n + m) * (11 * K + 3) +
            (8 * ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                  (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) + 2)) ∧
        Exec (evalTuple (base + 1) (n + m) (base + 1 + n + m + 1 + k) (base + 1 + n + m + 1 + k + l)
                (fun j => compileBC (base + 1 + n + m + 1 + k + l) (ts j)))
          (setFrame σ (base + 1) (xs ++ ys)) c₁
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys)) := by
      rw [← hxy_len]
      exact exec_evalTuple (base + 1) (xs ++ ys) (base + 1 + n + m + 1 + k) (base + 1 + n + m + 1 + k + l)
        (fun j => compileBC (base + 1 + n + m + 1 + k + l) (ts j))
        (fun j => (ts j).eval xs ys)
        (fun j => (ts j).timePoly)
        (setFrame σ (base + 1) (xs ++ ys))
        (by simp [hxs, hys]; omega)
        (by omega)
        (fun a ha => setFrame_get σ (base + 1) (xs ++ ys) a ha)
        (fun r hr _ => by
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        (fun r hr => by
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        hxy_le
        h_arg_ts
        (fun j σ' hσ' => ihts j (base + 1 + n + m + 1 + k + l) σ' xs ys K hxs hys hσ' hlenX hlenY)
    rcases hts_tuple with ⟨c₁, hc₁, hexec₁⟩
    have hrs_tuple : ∃ c₂ : Nat,
        c₂ ≤ (Poly.sumFin fun i => (rs i).timePoly).eval K +
          k * (n * (11 * K + 3) +
            (8 * ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                  (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) + 2)) ∧
        Exec (evalTuple (base + 1) n (base + 1 + n + m + 1) (base + 1 + n + m + 1 + k + l)
                (fun i => compileBC (base + 1 + n + m + 1 + k + l) (rs i)))
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys)) c₂
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
            ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys))) := by
      have hlen_rs : (List.ofFn fun i => (rs i).eval xs []).length = k := List.length_ofFn
      rcases exec_evalTuple (base + 1) xs (base + 1 + n + m + 1) (base + 1 + n + m + 1 + k + l)
          (fun i => compileBC (base + 1 + n + m + 1 + k + l) (rs i))
          (fun i => (rs i).eval xs [])
          (fun i => (rs i).timePoly)
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys))
          (by simp [hxs]; omega)
          (by omega)
          (fun a ha => by
            rw [setFrame_outside _ _ _ _ (by simp [hxs] at ha; omega)]
            rw [setFrame_get _ _ _ a (by simp [hxs, hys]; omega)]
            exact getD_append_left xs ys a ha)
          (fun r hr1 hr2 => by
            rw [setFrame_outside _ _ _ _ (by omega)]
            rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
            exact hempty r (by omega))
          (fun r hr => by
            rw [setFrame_outside _ _ _ _ (by simp [List.length_ofFn]; omega)]
            rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
            exact hempty r (by omega))
          hlenX
          h_arg_rs
          (fun i σ' hσ' => by
            have h := ihrs i (base + 1 + n + m + 1 + k + l) σ' xs [] K hxs rfl hσ' hlenX (by intro _ h; cases h)
            simpa using h) with
        ⟨c₂, hc₂, hexec₂⟩
      have happ : setFrame
          (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1 + k)
            (List.ofFn fun j => (ts j).eval xs ys))
          (base + 1 + n + m + 1)
          (List.ofFn fun i => (rs i).eval xs []) =
        setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
          ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)) := by
        have h := setFrame_append (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
          (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)
        rw [List.length_ofFn] at h
        exact h
      rw [happ] at hexec₂
      rw [hxs] at hc₂ hexec₂
      exact ⟨c₂, hc₂, hexec₂⟩
    rcases hrs_tuple with ⟨c₂, hc₂, hexec₂⟩
    have hrs_mem : ∀ x' ∈ (List.ofFn fun i => (rs i).eval xs []),
        x'.length ≤ (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                    (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro x' hx'
      rcases List.mem_ofFn.mp hx' with ⟨i, rfl⟩
      exact h_arg_rs i
    have hts_mem : ∀ y' ∈ (List.ofFn fun j => (ts j).eval xs ys),
        y'.length ≤ (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                    (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro y' hy'
      rcases List.mem_ofFn.mp hy' with ⟨j, rfl⟩
      exact h_arg_ts j
    rcases ihh (base + 1 + n + m) (setFrame σ (base + 1) (xs ++ ys))
        (List.ofFn fun i => (rs i).eval xs [])
        (List.ofFn fun j => (ts j).eval xs ys)
        ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
         (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K)
        List.length_ofFn List.length_ofFn
        (fun r hr => by
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        hrs_mem hts_mem with
      ⟨c₃, hc₃, hexec₃⟩
    have hframe_eq :
        (setFrame (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1)
          ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys))).set
          (base + 1 + n + m)
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)) =
        setFrame
          ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
            (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
          (base + 1 + n + m + 1)
          ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)) :=
      (setFrame_set_below (setFrame σ (base + 1) (xs ++ ys)) (base + 1 + n + m + 1) _ _ (by omega)).symm
    rw [hframe_eq] at hexec₃
    have hkl_len : ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)).length = k + l := by
      simp [List.length_ofFn]
    have hkl_mem : ∀ w ∈ ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)),
        w.length ≤ (Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                   (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K := by
      intro w hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact hrs_mem w h1
      · exact hts_mem w h2
    have hclear : ∃ c₄ : Nat,
        c₄ ≤ (k + l) * (2 * ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
                             (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) + 1) ∧
        Exec (clearRange (base + 1 + n + m + 1) (k + l))
          (setFrame
            ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
              (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
            (base + 1 + n + m + 1)
            ((List.ofFn fun i => (rs i).eval xs []) ++ (List.ofFn fun j => (ts j).eval xs ys)))
          c₄
          ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
            (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys))) := by
      rw [← hkl_len]
      exact exec_clearRange (base + 1 + n + m + 1) _ _
        (fun r hr => by
          rw [Stacks.set_other _ _ (by omega)]
          rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty r (by omega))
        hkl_mem
    rcases hclear with ⟨c₄, hc₄, hexec₄⟩
    have hmove : Exec (moveStack (base + 1 + n + m) base (base + 1 + n + m + 1))
        ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
        (8 * (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)).length + 2)
        ((setFrame σ (base + 1) (xs ++ ys)).set base
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys))) := by
      have hmv := exec_moveStack (src := base + 1 + n + m) (dst := base) (tmp := base + 1 + n + m + 1)
        (by omega) (by omega) (by omega)
        ((setFrame σ (base + 1) (xs ++ ys)).set (base + 1 + n + m)
          (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)))
        (by
          rw [Stacks.set_other _ _ (by omega), setFrame_outside _ _ _ _ (by omega)]
          exact hempty base (Nat.le_refl base))
        (by
          rw [Stacks.set_other _ _ (by omega), setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
          exact hempty _ (by omega))
      have hchild_empty : setFrame σ (base + 1) (xs ++ ys) (base + 1 + n + m) = [] := by
        rw [setFrame_outside _ _ _ _ (by simp [hxs, hys]; omega)]
        exact hempty _ (by omega)
      rw [Stacks.set_same, Stacks.set_set_same, Stacks.set_eq_self hchild_empty] at hmv
      exact hmv
    have hh_len : (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)).length ≤
        h.fullSizePoly.eval
          ((Poly.sumFin fun i' => (rs i').fullSizePoly).eval K +
           (Poly.sumFin fun j' => (ts j').fullSizePoly).eval K) :=
      h.eval_length_le_fullSizePoly _ _ hrs_mem hts_mem
    exact ⟨c₁ + (c₂ + (c₃ + (c₄ + (8 * (h.eval (List.ofFn fun i => (rs i).eval xs []) (List.ofFn fun j => (ts j).eval xs ys)).length + 2)))),
      by omega,
      Exec.seq hexec₁ (Exec.seq hexec₂ (Exec.seq hexec₃ (Exec.seq hexec₄ hmove)))⟩
  | @srec n m g h0 h1 ihg ih0 ih1 =>
    simp only [compileBC, Fn.timePoly, Poly.eval, Poly.eval_linear]
    cases xs with
    | nil => contradiction
    | cons w xs_tail =>
      simp only [List.length_cons] at hxs
      have hxs_tail : xs_tail.length = n := by omega
      have hw_le : w.length ≤ K := hlenX w (.head xs_tail)
      have hlen_tail : ∀ x ∈ xs_tail, x.length ≤ K := fun x hx => hlenX x (.tail w hx)
      let σ_core := setFrame σ (base + 2) (xs_tail ++ ys)
      have hframe_cons : setFrame σ (base + 1) ((w :: xs_tail) ++ ys) = σ_core.set (base + 1) w := rfl
      have hcore_base : σ_core base = [] := by
        dsimp only [σ_core]
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty base (Nat.le_refl base)
      have hcore_b1 : σ_core (base + 1) = [] := by
        dsimp only [σ_core]
        rw [setFrame_outside _ _ _ _ (by omega)]
        exact hempty (base + 1) (by omega)
      have hcore_rev : ∀ r : Nat, base + 2 + n + m ≤ r → σ_core r = [] := by
        intro r hr
        dsimp only [σ_core]
        rw [setFrame_outside _ _ _ _ (by simp [hxs_tail, hys]; omega)]
        exact hempty r (by omega)
      have hcore_xs : ∀ i : Nat, i < n → σ_core (base + 2 + i) = xs_tail.getD i [] := by
        intro i hi
        dsimp only [σ_core]
        rw [setFrame_get _ _ _ i (by simp [hxs_tail, hys]; omega)]
        exact getD_append_left xs_tail ys i (by omega)
      have hcore_ys : ∀ j : Nat, j < m → σ_core (base + 2 + n + j) = ys.getD j [] := by
        intro j hj
        dsimp only [σ_core]
        have heq : base + 2 + n + j = (base + 2) + (xs_tail.length + j) := by omega
        rw [heq, setFrame_get _ _ _ (xs_tail.length + j) (by simp [hxs_tail, hys]; omega)]
        exact getD_append_right xs_tail ys j
      have hcore_xy : ∀ a : Nat, a < (xs_tail ++ ys).length → σ_core ((base + 2) + a) = (xs_tail ++ ys).getD a [] :=
        fun a ha => setFrame_get σ (base + 2) (xs_tail ++ ys) a ha
      -- Step 1: moveRev (base + 1) (base + 2 + n + m)
      have hmv_w : Exec (moveRev (base + 1) (base + 2 + n + m)) (σ_core.set (base + 1) w)
          (4 * w.length + 1) (σ_core.set (base + 2 + n + m) w.reverse) := by
        have hm := exec_moveRev (src := base + 1) (dst := base + 2 + n + m) (by omega) (σ_core.set (base + 1) w)
        have hrev0 : (σ_core.set (base + 1) w) (base + 2 + n + m) = [] := by
          rw [Stacks.set_other _ _ (by omega)]
          exact hcore_rev _ (Nat.le_refl _)
        rw [Stacks.set_same, hrev0, List.append_nil, Stacks.set_set_same,
            Stacks.set_eq_self hcore_b1] at hm
        exact hm
      -- Step 2: evalSubTo (base + 2) (n + m) base (base + 3 + n + m) (compileBC (base + 3 + n + m) g)
      have hxy_tail_len : (xs_tail ++ ys).length = n + m := by simp [hxs_tail, hys]
      have hxy_tail_le : ∀ z ∈ (xs_tail ++ ys), z.length ≤ K := by
        intro z hz
        rcases List.mem_append.mp hz with h1 | h2
        · exact hlen_tail z h1
        · exact hlenY z h2
      have hrec_bound_le : ∀ u : Word, u.length ≤ K →
          ((Fn.srec g h0 h1).eval (u :: xs_tail) ys).length ≤
            (Fn.srec g h0 h1).fullSizePoly.eval K := by
        intro u hu
        apply (Fn.srec g h0 h1).eval_length_le_fullSizePoly (u :: xs_tail) ys _ hlenY
        intro z hz
        cases hz with
        | head => exact hu
        | tail _ hm => exact hlen_tail z hm
      have hg_len_le : (g.eval xs_tail ys).length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K := by
        have h0 := hrec_bound_le [] (Nat.zero_le K)
        simpa [Fn.eval_srec_nil] using h0
      have hg_eval : ∃ c₂ : Nat,
          c₂ ≤ g.timePoly.eval K + (n + m) * (11 * K + 3) +
            (8 * (Fn.srec g h0 h1).fullSizePoly.eval K + 2) ∧
          Exec (evalSubTo (base + 2) (n + m) base (base + 3 + n + m) (compileBC (base + 3 + n + m) g))
            (σ_core.set (base + 2 + n + m) w.reverse) c₂
            ((σ_core.set (base + 2 + n + m) w.reverse).set base (g.eval xs_tail ys)) := by
        rcases ihg (base + 3 + n + m) (σ_core.set (base + 2 + n + m) w.reverse) xs_tail ys K
            hxs_tail hys
            (fun r hr => by
              rw [Stacks.set_other _ _ (by omega)]
              exact hcore_rev r (by omega))
            hlen_tail hlenY with
          ⟨c_g, hc_g, hexec_g⟩
        rcases exec_evalSubTo (base + 2) (xs_tail ++ ys) base (base + 3 + n + m)
            (compileBC (base + 3 + n + m) g)
            (σ_core.set (base + 2 + n + m) w.reverse)
            (g.eval xs_tail ys)
            (by simp [hxs_tail, hys]; omega)
            (by omega)
            (fun a ha => by
              rw [Stacks.set_other _ _ (by simp [hxs_tail, hys] at ha; omega)]
              exact hcore_xy a ha)
            (by rw [Stacks.set_other _ _ (by omega)]; exact hcore_base)
            (fun r hr => by
              rw [Stacks.set_other _ _ (by omega)]
              exact hcore_rev r (by omega))
            hxy_tail_le
            hg_len_le
            hexec_g with
          ⟨c₂, hc₂, hexec₂⟩
        rw [hxy_tail_len] at hc₂ hexec₂
        exact ⟨c₂, by omega, hexec₂⟩
      rcases hg_eval with ⟨c₂, hc₂, hexec₂⟩
      -- Step 3: recLoop
      let stepFn : Bool → Word → Word → Word :=
        fun b u r => if b then h1.eval (u :: xs_tail) (r :: ys) else h0.eval (u :: xs_tail) (r :: ys)
      have hstate_init : ((σ_core.set (base + 2 + n + m) w.reverse).set base (g.eval xs_tail ys)) =
          recLoopState σ_core base n m (g.eval xs_tail ys) stepFn [] w.reverse := by
        simp only [recLoopState, recIter_nil]
        have hb1 : ((σ_core.set base (g.eval xs_tail ys)).set (base + 2 + n + m) w.reverse) (base + 1) = [] := by
          rw [Stacks.set_other _ _ (by omega), Stacks.set_other _ _ (by omega)]
          exact hcore_b1
        rw [Stacks.set_eq_self hb1]
        exact Stacks.set_set_comm σ_core w.reverse (g.eval xs_tail ys) (by omega)
      rw [hstate_init] at hexec₂
      have hK_le_Krec : K ≤ (Fn.srec g h0 h1).fullSizePoly.eval K := by
        simp [Fn.fullSizePoly, Poly.eval_add, Poly.eval_var]
      have hxs_le_Krec : ∀ x ∈ xs_tail, x.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K :=
        fun x hx => Nat.le_trans (hlen_tail x hx) hK_le_Krec
      have hys_le_Krec : ∀ y ∈ ys, y.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K :=
        fun y hy => Nat.le_trans (hlenY y hy) hK_le_Krec
      have hstep0 : ∀ (u acc : Word) (σ' : Stacks),
          u.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          acc.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
          ∃ c : Nat,
            c ≤ h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
                h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) ∧
            Exec (compileBC (base + 3 + n + m) h0)
              (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
              ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
                (base + 3 + n + m) (stepFn false u acc)) := by
        intro u acc σ' hu_le hacc_le hσ'
        rcases ih0 (base + 3 + n + m) σ' (u :: xs_tail) (acc :: ys)
            ((Fn.srec g h0 h1).fullSizePoly.eval K)
            (by simp [hxs_tail]) (by simp [hys]) hσ'
            (by intro z hz; cases hz with | head => exact hu_le | tail _ hm => exact hxs_le_Krec z hm)
            (by intro z hz; cases hz with | head => exact hacc_le | tail _ hm => exact hys_le_Krec z hm) with
          ⟨c, hc, hexec⟩
        exact ⟨c, by omega, hexec⟩
      have hstep1 : ∀ (u acc : Word) (σ' : Stacks),
          u.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          acc.length ≤ (Fn.srec g h0 h1).fullSizePoly.eval K →
          (∀ r : Nat, base + 3 + n + m ≤ r → σ' r = []) →
          ∃ c : Nat,
            c ≤ h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
                h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) ∧
            Exec (compileBC (base + 3 + n + m) h1)
              (setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))) c
              ((setFrame σ' ((base + 3 + n + m) + 1) ((u :: xs_tail) ++ (acc :: ys))).set
                (base + 3 + n + m) (stepFn true u acc)) := by
        intro u acc σ' hu_le hacc_le hσ'
        rcases ih1 (base + 3 + n + m) σ' (u :: xs_tail) (acc :: ys)
            ((Fn.srec g h0 h1).fullSizePoly.eval K)
            (by simp [hxs_tail]) (by simp [hys]) hσ'
            (by intro z hz; cases hz with | head => exact hu_le | tail _ hm => exact hxs_le_Krec z hm)
            (by intro z hz; cases hz with | head => exact hacc_le | tail _ hm => exact hys_le_Krec z hm) with
          ⟨c, hc, hexec⟩
        exact ⟨c, by omega, hexec⟩
      rcases exec_recLoop base n m (compileBC (base + 3 + n + m) h0) (compileBC (base + 3 + n + m) h1)
          σ_core xs_tail ys (g.eval xs_tail ys) stepFn
          hK_le_Krec hxs_tail hys hcore_xs hcore_ys
          (fun r hr => hcore_rev r (by omega))
          hxs_le_Krec hys_le_Krec
          (fun u hu => hrec_bound_le u hu)
          hstep0 hstep1
          w.reverse [] (by simp [List.length_reverse]; exact hw_le) with
        ⟨c₃, hc₃, hexec₃⟩
      simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hc₃ hexec₃
      have hstate_final :
          recLoopState σ_core base n m (g.eval xs_tail ys) stepFn w [] =
          (setFrame σ (base + 1) ((w :: xs_tail) ++ ys)).set base ((Fn.srec g h0 h1).eval (w :: xs_tail) ys) := by
        rw [hframe_cons]
        simp only [recLoopState, Fn.eval_srec, List.headD_cons, List.tail_cons]
        have hrev_empty : (σ_core.set base (recIter (g.eval xs_tail ys) stepFn w)) (base + 2 + n + m) = [] := by
          rw [Stacks.set_other _ _ (by omega)]
          exact hcore_rev (base + 2 + n + m) (Nat.le_refl _)
        rw [Stacks.set_eq_self hrev_empty]
        exact Stacks.set_set_comm σ_core (recIter (g.eval xs_tail ys) stepFn w) w (by omega)
      rw [hstate_final] at hexec₃
      have hmul_bound :
          w.length *
            ((h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
              h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K)) +
             ((n + 1) + (m + 1)) * (11 * (Fn.srec g h0 h1).fullSizePoly.eval K + 3) +
             (10 * (Fn.srec g h0 h1).fullSizePoly.eval K + 7)) ≤
          K *
            ((h0.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K) +
              h1.timePoly.eval ((Fn.srec g h0 h1).fullSizePoly.eval K)) +
             ((n + 1) + (m + 1)) * (11 * (Fn.srec g h0 h1).fullSizePoly.eval K + 3) +
             (10 * (Fn.srec g h0 h1).fullSizePoly.eval K + 7)) :=
        Nat.mul_le_mul_right _ hw_le
      exact ⟨(4 * w.length + 1) + (c₂ + c₃),
        by omega,
        Exec.seq hmv_w (Exec.seq hexec₂ hexec₃)⟩





theorem topCompileBC_haltsWithin (prog : Fn 1 0) (x : Word) :
    (stmtToTM (topCompileBC prog)).HaltsWithin x
      ((topTimePoly prog).eval x.length)
      (prog.eval [x] []) := by
  let σ_empty : Stacks := fun _ => []
  have hmv : Exec (moveStack 0 1 2) (initStacks x) (8 * x.length + 2)
      (setFrame σ_empty 1 ([x] ++ [])) := by
    have hm := exec_moveStack (src := 0) (dst := 1) (tmp := 2)
      (by decide) (by decide) (by decide) (initStacks x) rfl rfl
    have h0 : (initStacks x 0).length = x.length := rfl
    have hst : ((initStacks x).set 0 []).set 1 (initStacks x 0) = setFrame σ_empty 1 ([x] ++ []) := by
      funext k
      simp only [initStacks, List.cons_append, List.nil_append, setFrame_cons, setFrame_nil, σ_empty, Stacks.set]
      by_cases hk1 : k = 1
      · subst hk1; rfl
      · by_cases hk0 : k = 0
        · subst hk0; rfl
        · simp [hk1, hk0]
    rw [hst] at hm
    exact hm
  rcases exec_compileBC prog 0 σ_empty [x] [] x.length rfl rfl
      (fun _ _ => rfl)
      (fun z hz => by cases hz with | head => exact Nat.le_refl _ | tail _ h => cases h)
      (fun _ h => by cases h) with
    ⟨c, hc, hexec⟩
  have hfull := Exec.seq hmv hexec
  rcases stmtToTM_haltsWithin (topCompileBC prog) x hfull with ⟨s, hs, hstep, hout⟩
  rw [Stacks.set_same] at hout
  refine ⟨s, ?_, hstep, hout⟩
  simp only [topTimePoly, Poly.eval, Poly.eval_linear]
  omega

/-- **Bellantoni–Cook Polynomial-Time Soundness (`BCDefinable f → FP f`)**:
    Every unary word function definable in the Bellantoni–Cook safe recursion algebra
    is computable in polynomial time by a deterministic multi-tape Turing machine. -/
theorem bc_soundness (f : Word → Word) (h : BCDefinable f) : FP f := by
  rcases h with ⟨prog, hprog⟩
  refine ⟨stmtToTM (topCompileBC prog), topTimePoly prog, fun x => ?_⟩
  rw [← hprog x]
  exact topCompileBC_haltsWithin prog x

end BC1992

/-
  FeasibleUnivalence/BC/Completeness.lean

  Polynomial-time completeness of the Bellantoni–Cook function algebra (`FP f → BCDefinable f`)
  and the headline characterization theorem `defFun_eq_FP`:
  $$(∃ \text{prog} : \text{Fn } 1\ 0,\ \forall x,\ \text{prog.eval } [x]\ [] = f\ x) \iff \text{FP } f.$$

  Architecture:
  1. Basic BC combinators (`prependConst`, `constWord`, `branchPrefix`, `dropConst`, `dropBlock`,
     `polyWord`).
  2. Fixed-width block tables (`concatRev`, `tableOf`, `revBlocks`).
  3. Unary encoding of bounded naturals and TM block data (`BlockData`, `encBlock`, `decBlock`,
     `cfgBlock`, `encCfg`).
  4. Initial TM configuration in BC (`initCfgBC`).
  5. Single-step TM transition (`stepCfgBC`) and polynomial-time iteration (`runCfgBC`).
  6. Output tape decoding (`outputCfgBC`), full TM simulator (`simTM`), `bc_completeness`,
     and `defFun_eq_FP`.
-/


namespace BC1992

/-! ## 1. Basic BC Combinators and `polyWord` -/









@[simp] theorem vec1_zero {α : Type _} (a : α) : vec1 a 0 = a := rfl
@[simp] theorem vec2_zero {α : Type _} (a b : α) : vec2 a b 0 = a := rfl
@[simp] theorem vec2_one {α : Type _} (a b : α) (i : Fin 1) : vec2 a b i.succ = b := by
  cases i; rfl
@[simp] theorem vec3_zero {α : Type _} (a b c : α) : vec3 a b c 0 = a := rfl
@[simp] theorem vec3_succ {α : Type _} (a b c : α) (i : Fin 2) : vec3 a b c i.succ = vec2 b c i := by
  rcases i with ⟨_ | _, _⟩ <;> rfl
@[simp] theorem vec4_zero {α : Type _} (a b c d : α) : vec4 a b c d 0 = a := rfl
@[simp] theorem vec4_succ {α : Type _} (a b c d : α) (i : Fin 3) : vec4 a b c d i.succ = vec3 b c d i := by
  rcases i with ⟨_ | _ | _, _⟩ <;> rfl



@[simp] theorem eval_constZero {n m : Nat} (xs ys : List Word) :
    (constZero (n := n) (m := m)).eval xs ys = [] := by
  simp [constZero, List.ofFn_zero]



@[simp] theorem eval_prependConstAt {n m : Nat} (j : Fin m) (u : Word) (xs ys : List Word) :
    (prependConstAt (n := n) j u).eval xs ys = u ++ ys.getD j.val [] := by
  induction u with
  | nil => simp [prependConstAt]
  | cons b u ih =>
    cases b <;> simp [prependConstAt, List.ofFn_succ, List.ofFn_zero, ih]



@[simp] theorem eval_prependConst (u : Word) (xs ys : List Word) :
    (prependConst u).eval xs ys = u ++ ys.getD 0 [] :=
  eval_prependConstAt ⟨0, Nat.zero_lt_one⟩ u xs ys



@[simp] theorem eval_constWord {n m : Nat} (u : Word) (xs ys : List Word) :
    (constWord (n := n) (m := m) u).eval xs ys = u := by
  simp [constWord, List.ofFn_succ, List.ofFn_zero]



@[simp] theorem padFalse_zero (y : Word) : padFalse 0 y = [] := rfl
@[simp] theorem padFalse_nil (B : Nat) : padFalse B [] = List.replicate B false := by
  induction B with
  | zero => rfl
  | succ B ih => simp [padFalse, List.replicate_succ, ih]

@[simp] theorem length_padFalse (B : Nat) (y : Word) : (padFalse B y).length = B := by
  induction B generalizing y with
  | zero => rfl
  | succ B ih =>
    cases y with
    | nil => simp [padFalse]
    | cons b y => simp [padFalse, ih]

theorem padFalse_append_exact (u v : Word) :
    padFalse u.length (u ++ v) = u := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [padFalse, ih]

theorem padFalse_eq_of_length {B : Nat} {u v : Word} (h : u.length = B) :
    padFalse B (u ++ v) = u := by
  subst h
  exact padFalse_append_exact u v

theorem padFalse_self {B : Nat} {u : Word} (h : u.length = B) :
    padFalse B u = u := by
  have h1 := padFalse_eq_of_length (v := []) h
  simpa using h1

theorem padFalse_add (A B : Nat) (w : Word) :
    padFalse (A + B) w = padFalse A w ++ padFalse B (w.drop A) := by
  induction A generalizing w with
  | zero => simp
  | succ A ih =>
    rw [Nat.succ_add]
    cases w with
    | nil => simp [padFalse, ih []]
    | cons b w => simp [padFalse, ih w]



theorem ofFn_getD_eq_self : ∀ {m : Nat} (ys : List Word), ys.length = m →
    (List.ofFn fun j : Fin m => ys.getD j.val []) = ys
  | 0, [], _ => rfl
  | m + 1, y :: ys, h => by
    simp only [List.length_cons] at h
    rw [List.ofFn_succ]
    congr 1
    exact ofFn_getD_eq_self ys (by omega)

theorem ofFn_getD_succ (y : Word) : ∀ {m : Nat} (ys : List Word), ys.length = m →
    (List.ofFn fun j : Fin m => (y :: ys).getD j.succ.val []) = ys
  | 0, [], _ => rfl
  | m + 1, y' :: ys, h => by
    simp only [List.length_cons] at h
    rw [List.ofFn_succ]
    congr 1
    exact ofFn_getD_succ y' ys (by omega)

theorem eval_shiftSafe {m : Nat} (f : Fn 0 m) (y : Word) (ys : List Word) (hys : ys.length = m) :
    (shiftSafe f).eval [] (y :: ys) = f.eval [] ys := by
  simp only [shiftSafe, Fn.eval_comp, List.ofFn_zero, Fn.eval_projS]
  rw [ofFn_getD_succ y ys hys]



theorem eval_predFirstSafe {m : Nat} (g : Fn 0 (m + 1)) (y : Word) (ys : List Word)
    (hys : ys.length = m) :
    (predFirstSafe g).eval [] (y :: ys) = g.eval [] (y.tail :: ys) := by
  simp only [predFirstSafe, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ, Fin.cases_zero,
    Fin.cases_succ, vec1_zero, Fn.eval_pred, Fn.eval_projS, List.getD_cons_zero]
  rw [ofFn_getD_succ y ys hys]



theorem eval_branchPrefix {m : Nat} (B : Nat) (K : Word → Fn 0 m)
    (y : Word) (ys : List Word) (hys : ys.length = m) :
    (branchPrefix B K).eval [] (y :: ys) = (K (padFalse B y)).eval [] ys := by
  induction B generalizing K y with
  | zero =>
    exact eval_shiftSafe (K []) y ys hys
  | succ B ih =>
    simp only [branchPrefix, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
      vec4_zero, vec4_succ, vec3_zero, vec3_succ, vec2_zero, vec2_one,
      Fn.eval_cond, Fn.eval_projS, List.getD_cons_zero, List.getD_cons_succ]
    cases y with
    | nil =>
      simp only [condW, padFalse]
      rw [eval_predFirstSafe _ [] ys hys, List.tail_nil]
      exact ih (fun w => K (false :: w)) []
    | cons b y' =>
      cases b with
      | false =>
        simp only [condW, padFalse]
        rw [eval_predFirstSafe _ (false :: y') ys hys, List.tail_cons]
        exact ih (fun w => K (false :: w)) y'
      | true =>
        simp only [condW, padFalse]
        rw [eval_predFirstSafe _ (true :: y') ys hys, List.tail_cons]
        exact ih (fun w => K (true :: w)) y'



@[simp] theorem eval_dropConst (D : Nat) (xs : List Word) (y : Word) :
    (dropConst D).eval xs [y] = y.drop D := by
  induction D generalizing y with
  | zero => simp [dropConst]
  | succ D ih =>
    simp only [dropConst, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ, vec1_zero,
      Fn.eval_pred, List.getD_cons_zero, ih]
    rw [← List.drop_drop]
    cases List.drop D y <;> rfl



@[simp] theorem eval_dropBlock (D : Nat) (w y : Word) :
    (dropBlock D).eval [w] [y] = y.drop (w.length * D) := by
  induction w with
  | nil => simp [dropBlock]
  | cons b w ih =>
    have hstep : ((dropBlock D).eval [b :: w] [y]) =
        ((dropBlock D).eval [w] [y]).drop D := by
      cases b <;> simp [dropBlock, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, ih, List.drop_drop, List.length_cons, Nat.succ_mul]



theorem length_eval_appendSafe (w y : Word) :
    (appendSafe.eval [w] [y]).length = w.length + y.length := by
  induction w with
  | nil => simp [appendSafe]
  | cons b w ih =>
    have hstep : appendSafe.eval [b :: w] [y] = false :: appendSafe.eval [w] [y] := by
      cases b <;> simp [appendSafe, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, List.length_cons, ih, List.length_cons, Nat.succ_add]



theorem length_eval_mulWord (w₁ w₂ : Word) :
    (mulWord.eval [w₁, w₂] []).length = w₁.length * w₂.length := by
  induction w₁ with
  | nil => simp [mulWord]
  | cons b w₁ ih =>
    have hstep : mulWord.eval [b :: w₁, w₂] [] =
        appendSafe.eval [w₂] [mulWord.eval [w₁, w₂] []] := by
      cases b <;> simp [mulWord, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, length_eval_appendSafe, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]



@[simp] theorem length_eval_polyWord (q : Poly) (x : Word) :
    ((polyWord q).eval [x] []).length = q.eval x.length := by
  induction q generalizing x with
  | const c => simp [polyWord]
  | var => simp [polyWord]
  | add p q ihp ihq =>
    simp [polyWord, List.ofFn_succ, List.ofFn_zero, length_eval_appendSafe, ihp, ihq]
  | mul p q ihp ihq =>
    simp [polyWord, List.ofFn_succ, List.ofFn_zero, length_eval_mulWord, ihp, ihq]
  | comp p q ihp ihq =>
    simp [polyWord, List.ofFn_succ, List.ofFn_zero, ihp, ihq]

/-! ## 2. Fixed-Width Block Tables (`concatRev`, `tableOf`, `revBlocks`) -/



@[simp] theorem concatRev_zero (f : Nat → Word) : concatRev f 0 = [] := rfl
@[simp] theorem concatRev_succ (f : Nat → Word) (n : Nat) :
    concatRev f (n + 1) = f n ++ concatRev f n := rfl

theorem length_concatRev {D : Nat} (f : Nat → Word) (n : Nat)
    (hf : ∀ i : Nat, i < n → (f i).length = D) :
    (concatRev f n).length = n * D := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [concatRev_succ, List.length_append, Nat.succ_mul]
    rw [ih (fun i hi => hf i (by omega)), hf n (Nat.lt_succ_self n), Nat.add_comm]

theorem drop_append_exact (u v : Word) :
    (u ++ v).drop u.length = v := by
  induction u with
  | nil => rfl
  | cons _ u ih => simp [ih]

theorem drop_append_of_length {D : Nat} {u v : Word} (h : u.length = D) :
    (u ++ v).drop D = v := by
  subst h
  exact drop_append_exact u v

theorem replicate_add {α : Type _} (m n : Nat) (a : α) :
    List.replicate (m + n) a = List.replicate m a ++ List.replicate n a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, List.replicate_succ, List.replicate_succ, List.cons_append, ih]

theorem padFalse_drop_concatRev {D : Nat} (f : Nat → Word) (n : Nat)
    (hf : ∀ i : Nat, i < n → (f i).length = D) :
    ∀ k : Nat, k < n → padFalse D ((concatRev f n).drop (k * D)) = f (n - 1 - k) := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    simp only [concatRev_succ]
    have hfn : (f n).length = D := hf n (Nat.lt_succ_self n)
    cases k with
    | zero =>
      simp only [Nat.zero_mul, List.drop_zero, Nat.add_sub_cancel, Nat.sub_zero]
      exact padFalse_eq_of_length hfn
    | succ k' =>
      rw [Nat.succ_mul, Nat.add_comm (k' * D) D, ← List.drop_drop, ← hfn,
          drop_append_exact (f n) (concatRev f n), hfn]
      rw [ih (fun i hi => hf i (by omega)) k' (by omega)]
      congr 1
      omega



theorem length_tableOf {D : Nat} (f : Nat → Word) (N : Nat)
    (hf : ∀ j : Nat, j < N → (f j).length = D) :
    (tableOf f N).length = N * D := by
  apply length_concatRev
  intro k hk
  exact hf (N - 1 - k) (by omega)

theorem padFalse_drop_tableOf {D : Nat} (f : Nat → Word) (N : Nat)
    (hf : ∀ j : Nat, j < N → (f j).length = D) {j : Nat} (hj : j < N) :
    padFalse D ((tableOf f N).drop (j * D)) = f j := by
  unfold tableOf
  rw [padFalse_drop_concatRev (fun k => f (N - 1 - k)) N
        (fun k hk => hf (N - 1 - k) (by omega)) j hj]
  congr 1
  omega



theorem eval_revBlocks_prefix (D : Nat) (y : Word) (u : Word) :
    (revBlocks D).eval [u] [y] =
      concatRev (fun k => padFalse D (y.drop (k * D))) u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have hstep : (revBlocks D).eval [b :: u] [y] =
        (branchPrefix D prependConst).eval [] [y.drop (u.length * D), (revBlocks D).eval [u] [y]] := by
      cases b <;> simp [revBlocks, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    rw [hstep, eval_branchPrefix D prependConst (y.drop (u.length * D)) [(revBlocks D).eval [u] [y]] rfl]
    simp [ih]

theorem eval_revBlocks {D : Nat} (f : Nat → Word) (W : Word)
    (hf : ∀ i : Nat, i < W.length → (f i).length = D) :
    (revBlocks D).eval [W] [concatRev f W.length] = tableOf f W.length := by
  rw [eval_revBlocks_prefix]
  unfold tableOf
  have hcongr : ∀ n : Nat, n ≤ W.length →
      concatRev (fun k => padFalse D ((concatRev f W.length).drop (k * D))) n =
      concatRev (fun k => f (W.length - 1 - k)) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [concatRev_succ]
      rw [padFalse_drop_concatRev f W.length hf n (by omega), ih (by omega)]
  exact hcongr W.length (Nat.le_refl _)

theorem eval_revBlocks_tableOf {D : Nat} (f : Nat → Word) (W : Word)
    (hf : ∀ j : Nat, j < W.length → (f j).length = D) :
    (revBlocks D).eval [W] [tableOf f W.length] = concatRev f W.length := by
  unfold tableOf
  rw [eval_revBlocks (fun k => f (W.length - 1 - k)) W (fun k hk => hf _ (by omega))]
  unfold tableOf
  have hcongr : ∀ n : Nat, n ≤ W.length →
      concatRev (fun k => f (W.length - 1 - (W.length - 1 - k))) n = concatRev f n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [concatRev_succ]
      have hidx : W.length - 1 - (W.length - 1 - n) = n := by omega
      rw [hidx, ih (by omega)]
  exact hcongr W.length (Nat.le_refl _)

/-! ## 3. Unary Encoding of Bounded Naturals and TM Block Data -/



theorem length_encFin {W : Nat} (v : Fin W) : (encFin v).length = W := by
  simp only [encFin, List.length_append, List.length_replicate]
  have hv : v.val < W := v.isLt
  omega

theorem encFin_zero {W : Nat} (hW : 0 < W) :
    encFin (⟨0, hW⟩ : Fin W) = List.replicate W false := by
  simp [encFin]



theorem countTrue_replicate_true_cons_false (n : Nat) (w : Word) :
    countTrue (List.replicate n true ++ false :: w) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [List.replicate_succ, countTrue, ih]

theorem countTrue_encFin {W : Nat} (v : Fin W) :
    countTrue (encFin v) = v.val := by
  unfold encFin
  have hv : v.val < W := v.isLt
  have hsub : W - v.val = (W - 1 - v.val) + 1 := by omega
  rw [hsub, List.replicate_succ]
  exact countTrue_replicate_true_cons_false v.val _



theorem decFin_encFin {W : Nat} (hW : 0 < W) (v : Fin W) :
    decFin hW (encFin v) = v := by
  unfold decFin
  rw [countTrue_encFin, dif_pos v.isLt]





theorem length_encTuple {α : Type _} {E : Nat} (enc : α → Word)
    (henc : ∀ a : α, (enc a).length = E) :
    ∀ {k : Nat} (f : Fin k → α), (encTuple enc f).length = k * E
  | 0, _ => by simp [encTuple]
  | k + 1, f => by
    simp only [encTuple, List.length_append, henc (f ⟨0, Nat.zero_lt_succ k⟩),
      length_encTuple enc henc (fun i => f i.succ), Nat.succ_mul, Nat.add_comm]

theorem decTuple_encTuple {α : Type _} {E : Nat} (enc : α → Word) (dec : Word → α)
    (henc : ∀ a : α, (enc a).length = E) (hdec : ∀ a : α, dec (enc a) = a) :
    ∀ {k : Nat} (f : Fin k → α), decTuple E dec k (encTuple enc f) = f
  | 0, f => by funext i; exact i.elim0
  | k + 1, f => by
    funext ⟨i, hi⟩
    cases i with
    | zero =>
      simp only [decTuple, encTuple]
      rw [padFalse_eq_of_length (henc _), hdec]
    | succ i' =>
      simp only [decTuple, encTuple]
      rw [drop_append_of_length (henc _)]
      have ih := congrFun (decTuple_encTuple enc dec henc hdec (fun j : Fin k => f j.succ)) ⟨i', Nat.lt_of_succ_lt_succ hi⟩
      exact ih

theorem encTuple_replicate_false {α : Type _} {E : Nat} (enc : α → Word) (a₀ : α)
    (ha₀ : enc a₀ = List.replicate E false) :
    ∀ (k : Nat), encTuple enc (fun _ : Fin k => a₀) = List.replicate (k * E) false
  | 0 => by simp [encTuple]
  | k + 1 => by
    simp only [encTuple, ha₀, encTuple_replicate_false enc a₀ ha₀ k,
      Nat.succ_mul, Nat.add_comm (k * E) E, replicate_add]





theorem blockWidth_pos (M : TM) : 0 < blockWidth M := by
  unfold blockWidth
  omega





theorem length_encBlock (M : TM) (b : BlockData M) :
    (encBlock M b).length = blockWidth M := by
  simp only [encBlock, blockWidth, List.length_append, List.length_singleton,
    length_encFin, length_encTuple encFin (fun a => length_encFin a)]
  omega

theorem encBlock_blankBlock (M : TM) :
    encBlock M (blankBlock M) = List.replicate (blockWidth M) false := by
  have hG0 : 0 < M.G := by have := M.hG; omega
  have hblank : encFin M.blank = List.replicate M.G false := encFin_zero hG0
  have htuple : encTuple encFin (fun _ : Fin M.k => M.blank) = List.replicate (M.k * M.G) false :=
    encTuple_replicate_false encFin M.blank hblank M.k
  simp only [encBlock, blankBlock, encFin_zero M.hQ, htuple, blockWidth, Nat.add_assoc, replicate_add]
  rfl



theorem decBlock_encBlock (M : TM) (b : BlockData M) :
    decBlock M (encBlock M b) = b := by
  have hG0 : 0 < M.G := by have := M.hG; omega
  have hlen_q : (encFin b.state).length = M.Q := length_encFin b.state
  have hlen_h : (encTuple encFin b.headSym).length = M.k * M.G :=
    length_encTuple encFin length_encFin b.headSym
  have hlen_l : (encTuple encFin b.leftSym).length = M.k * M.G :=
    length_encTuple encFin length_encFin b.leftSym
  have hlen_r : (encTuple encFin b.rightSym).length = M.k * M.G :=
    length_encTuple encFin length_encFin b.rightSym
  unfold decBlock encBlock
  dsimp only
  have hd1 : ([b.isZero] ++ (encFin b.state ++ (encTuple encFin b.headSym ++ (encTuple encFin b.leftSym ++ encTuple encFin b.rightSym)))).drop 1 =
      encFin b.state ++ (encTuple encFin b.headSym ++ (encTuple encFin b.leftSym ++ encTuple encFin b.rightSym)) := rfl
  rw [hd1]
  rw [drop_append_of_length hlen_q]
  rw [drop_append_of_length hlen_h]
  rw [drop_append_of_length hlen_l]
  rw [padFalse_eq_of_length hlen_q,
      padFalse_eq_of_length hlen_h,
      padFalse_eq_of_length hlen_l,
      padFalse_self hlen_r,
      decFin_encFin M.hQ b.state,
      decTuple_encTuple encFin (decFin hG0) length_encFin (decFin_encFin hG0) b.headSym,
      decTuple_encTuple encFin (decFin hG0) length_encFin (decFin_encFin hG0) b.leftSym,
      decTuple_encTuple encFin (decFin hG0) length_encFin (decFin_encFin hG0) b.rightSym]
  cases b
  rfl

theorem decBlock_replicate_false (M : TM) :
    decBlock M (List.replicate (blockWidth M) false) = blankBlock M := by
  rw [← encBlock_blankBlock M, decBlock_encBlock M]





theorem length_encCfg (M : TM) (N : Nat) (c : Cfg M.k M.Q M.G) :
    (encCfg M N c).length = N * blockWidth M :=
  length_tableOf _ N (fun j _ => length_encBlock M (cfgBlock M c j))

/-! ## 4. Initial TM Configuration in BC (`initCfgBC`) -/



theorem eval_branchHead {m : Nat} (K : Option Bool → Fn 0 m)
    (y : Word) (ys : List Word) (hys : ys.length = m) :
    (branchHead K).eval [] (y :: ys) = (K y.head?).eval [] ys := by
  simp only [branchHead, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec4_zero, vec4_succ, vec3_zero, vec3_succ, vec2_zero, vec2_one,
    Fn.eval_cond, Fn.eval_projS, List.getD_cons_zero,
    eval_shiftSafe _ y ys hys]
  cases y with
  | nil => rfl
  | cons b y' => cases b <;> rfl



theorem map_bitSym_getD (M : TM) (w : Word) (j : Nat) :
    (w.map M.bitSym).getD j M.blank =
      match (w.drop j).head? with
      | none => M.blank
      | some b => M.bitSym b := by
  induction w generalizing j with
  | nil => simp [List.getD]
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j' => exact ih j'

theorem inputTape_right_getD (M : TM) (x : Word) (j : Nat) :
    (M.inputTape x).right.getD j M.blank =
      match (x.drop j).tail.head? with
      | none => M.blank
      | some b => M.bitSym b := by
  cases x with
  | nil => simp [TM.inputTape, List.getD]
  | cons b w =>
    simp only [TM.inputTape]
    rw [map_bitSym_getD M w j]
    congr 2
    cases j <;> simp

theorem initBlockFromDrop_eq_cfgBlock (M : TM) (x : Word) (j : Nat) :
    initBlockFromDrop M (decide (j = 0)) (x.drop j).head? (x.drop j).tail.head? =
      cfgBlock M (M.init x) j := by
  by_cases hj : j = 0
  · subst hj
    simp only [initBlockFromDrop, cfgBlock, decide_true, ↓reduceIte, List.drop_zero, TM.init]
    congr 1
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        cases x <;> rfl
      · simp [hi, TM.blankTape]
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        cases x <;> rfl
      · simp [hi, TM.blankTape]
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        exact (inputTape_right_getD M x 0).symm
      · simp [hi, TM.blankTape, List.getD]
  · simp only [initBlockFromDrop, cfgBlock, hj, decide_false, Bool.false_eq_true, ↓reduceIte, TM.init]
    congr 1
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        cases x <;> simp [TM.inputTape, List.getD]
      · simp [hi, TM.blankTape, List.getD]
    · funext i
      by_cases hi : i.val = 0
      · simp only [hi, ↓reduceIte]
        exact (inputTape_right_getD M x j).symm
      · simp [hi, TM.blankTape, List.getD]



theorem eval_initBlockBranch (M : TM) (isZero : Bool) (y r : Word) :
    (initBlockBranch M isZero).eval [] [y, y.tail, r] =
      encBlock M (initBlockFromDrop M isZero y.head? y.tail.head?) ++ r := by
  unfold initBlockBranch
  rw [eval_branchHead _ y [y.tail, r] rfl,
      eval_branchHead _ y.tail [r] rfl,
      eval_prependConst]
  rfl



theorem eval_initStepBC (M : TM) (u r x : Word) (hr : r = [] ↔ u.length = 0) :
    (initStepBC M).eval [u] [r, x] =
      encBlock M (cfgBlock M (M.init x) u.length) ++ r := by
  have hy : (dropBlock 1).eval [u] [x] = x.drop u.length := by
    simp [eval_dropBlock]
  simp only [initStepBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec4_zero, vec4_succ, vec3_zero, vec3_succ, vec2_zero, vec2_one, vec1_zero,
    Fn.eval_cond, Fn.eval_projN, Fn.eval_projS, Fn.eval_pred, List.getD_cons_zero, List.getD_cons_succ, hy]
  rw [eval_initBlockBranch M true (x.drop u.length) r,
      eval_initBlockBranch M false (x.drop u.length) r]
  cases r with
  | nil =>
    have hu0 : u.length = 0 := hr.mp rfl
    simp only [condW, hu0, List.drop_zero]
    rw [← initBlockFromDrop_eq_cfgBlock M x 0]
    rfl
  | cons b r' =>
    have hne : u.length ≠ 0 := fun h0 => List.cons_ne_nil b r' (hr.mpr h0)
    have hdec : decide (u.length = 0) = false := decide_eq_false hne
    cases b <;> {
      simp only [condW]
      rw [← initBlockFromDrop_eq_cfgBlock M x u.length, hdec]
    }



theorem eval_initCfgBC_buildRev (M : TM) (x u : Word) :
    (Fn.srec constZero (initStepBC M) (initStepBC M)).eval [u] [x] =
      concatRev (fun j => encBlock M (cfgBlock M (M.init x) j)) u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have hstep : (Fn.srec constZero (initStepBC M) (initStepBC M)).eval [b :: u] [x] =
        (initStepBC M).eval [u]
          [(Fn.srec constZero (initStepBC M) (initStepBC M)).eval [u] [x], x] := by
      cases b <;> simp [Fn.eval_srec_cons]
    have hr : (Fn.srec constZero (initStepBC M) (initStepBC M)).eval [u] [x] = [] ↔ u.length = 0 := by
      rw [ih]
      have hlen := length_concatRev (fun j => encBlock M (cfgBlock M (M.init x) j)) u.length
        (fun j _ => length_encBlock M _)
      have hbw : 0 < blockWidth M := blockWidth_pos M
      constructor
      · intro hnil
        rw [hnil, List.length_nil] at hlen
        cases u with
        | nil => rfl
        | cons _ u' =>
          simp only [List.length_cons, Nat.succ_mul] at hlen
          omega
      · intro h0
        have hu : u = [] := List.eq_nil_of_length_eq_zero h0
        subst hu
        rfl
    rw [hstep, eval_initStepBC M u _ x hr, ih]
    rfl

theorem eval_initCfgBC (M : TM) (W x : Word) :
    (initCfgBC M).eval [W] [x] = encCfg M W.length (M.init x) := by
  simp only [initCfgBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec1_zero, Fn.eval_projN, List.getD_cons_zero]
  rw [eval_initCfgBC_buildRev M x W]
  exact eval_revBlocks (fun j => encBlock M (cfgBlock M (M.init x) j)) W
    (fun j _ => length_encBlock M _)

/-! ## 5. Single-Step TM Transition (`stepCfgBC`) and Multi-Step Iteration (`runCfgBC`) -/



theorem TM.run_succ_eq_stepOrSelf (M : TM) (t : Nat) (c : Cfg M.k M.Q M.G) :
    M.run (t + 1) c = M.stepOrSelf (M.run t c) := by
  induction t generalizing c with
  | zero =>
    simp only [TM.run, TM.stepOrSelf]
    cases M.step c <;> rfl
  | succ t ih =>
    simp only [TM.run]
    cases h : M.step c with
    | none =>
      simp [TM.stepOrSelf, h]
    | some c' =>
      exact ih c'

theorem Tape.consB_getD {Γ : Type} [DecidableEq Γ] (blank a : Γ) (l : List Γ) (k : Nat) :
    (Tape.consB blank a l).getD k blank = (a :: l).getD k blank := by
  cases l with
  | nil =>
    simp only [Tape.consB]
    by_cases h : a = blank
    · subst h
      simp only [↓reduceIte]
      cases k <;> rfl
    · simp [h]
  | cons b l' => rfl

theorem Tape.consB_length_le {Γ : Type} [DecidableEq Γ] (blank a : Γ) (l : List Γ) :
    (Tape.consB blank a l).length ≤ l.length + 1 := by
  cases l with
  | nil =>
    simp only [Tape.consB]
    by_cases h : a = blank <;> simp [h]
  | cons b l' =>
    simp [Tape.consB]

theorem Tape.move_left_length_le {Γ : Type} [DecidableEq Γ] (blank : Γ) (d : Dir) (t : Tape Γ) :
    (t.move blank d).left.length ≤ t.left.length + 1 := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> simp [Tape.move] <;> omega
  | R =>
    cases r <;> simp only [Tape.move] <;> exact Tape.consB_length_le blank h l
  | S =>
    simp [Tape.move]

theorem Tape.move_right_length_le {Γ : Type} [DecidableEq Γ] (blank : Γ) (d : Dir) (t : Tape Γ) :
    (t.move blank d).right.length ≤ t.right.length + 1 := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> simp only [Tape.move] <;> exact Tape.consB_length_le blank h r
  | R =>
    cases r <;> simp [Tape.move] <;> omega
  | S =>
    simp [Tape.move]



theorem TM.tapeBounded_init (M : TM) (x : Word) :
    M.TapeBounded x.length (M.init x) := by
  intro i
  simp only [TM.init]
  by_cases hi : i.val = 0
  · simp only [hi, ↓reduceIte]
    cases x <;> simp [TM.inputTape]
  · simp [hi, TM.blankTape]

theorem TM.tapeBounded_stepOrSelf (M : TM) {L : Nat} {c : Cfg M.k M.Q M.G}
    (h : M.TapeBounded L c) :
    M.TapeBounded (L + 1) (M.stepOrSelf c) := by
  intro i
  unfold TM.stepOrSelf TM.step
  rcases h i with ⟨hl, hr⟩
  cases hδ : M.δ c.state (fun i => (c.tapes i).head) with
  | none =>
    simp only
    exact ⟨by omega, by omega⟩
  | some qwd =>
    rcases qwd with ⟨q', w, d⟩
    simp only
    have h1 := Tape.move_left_length_le M.blank (d i) ((c.tapes i).write (w i))
    have h2 := Tape.move_right_length_le M.blank (d i) ((c.tapes i).write (w i))
    have hw_l : ((c.tapes i).write (w i)).left.length = (c.tapes i).left.length := rfl
    have hw_r : ((c.tapes i).write (w i)).right.length = (c.tapes i).right.length := rfl
    rw [hw_l] at h1
    rw [hw_r] at h2
    exact ⟨by omega, by omega⟩

theorem TM.tapeBounded_run (M : TM) (x : Word) (t : Nat) :
    M.TapeBounded (x.length + t) (M.run t (M.init x)) := by
  induction t with
  | zero =>
    simp only [TM.run, Nat.add_zero]
    exact M.tapeBounded_init x
  | succ t ih =>
    rw [M.run_succ_eq_stepOrSelf]
    exact M.tapeBounded_stepOrSelf ih

theorem getD_eq_default_of_le_length {α : Type _} (l : List α) (d : α) (j : Nat)
    (hj : l.length ≤ j) :
    l.getD j d = d := by
  induction l generalizing j with
  | nil => simp [List.getD]
  | cons a l ih =>
    cases j with
    | zero => simp at hj
    | succ j' =>
      simp only [List.length_cons] at hj
      exact ih j' (by omega)

theorem cfgBlock_eq_blankBlock_of_tapeBounded (M : TM) {L : Nat} {c : Cfg M.k M.Q M.G}
    (h : M.TapeBounded L c) (j : Nat) (hj0 : 0 < j) (hjL : L ≤ j) :
    cfgBlock M c j = blankBlock M := by
  have hj_ne : j ≠ 0 := by omega
  simp only [cfgBlock, hj_ne, ↓reduceIte, blankBlock]
  congr 1
  · funext i
    exact getD_eq_default_of_le_length (c.tapes i).left M.blank j (Nat.le_trans (h i).1 hjL)
  · funext i
    exact getD_eq_default_of_le_length (c.tapes i).right M.blank j (Nat.le_trans (h i).2 hjL)



theorem move_head_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) :
    ((t.write w).move M.blank d).head =
      match d with
      | .L => t.left.getD 0 M.blank
      | .R => t.right.getD 0 M.blank
      | .S => w := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L => cases l <;> rfl
  | R => cases r <;> rfl
  | S => rfl

theorem move_left_zero_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) :
    ((t.write w).move M.blank d).left.getD 0 M.blank =
      match d with
      | .L => t.left.getD 1 M.blank
      | .R => w
      | .S => t.left.getD 0 M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l with
    | nil => rfl
    | cons a l' => rfl
  | R =>
    cases r <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w l 0]
      rfl
    }
  | S => rfl

theorem move_right_zero_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) :
    ((t.write w).move M.blank d).right.getD 0 M.blank =
      match d with
      | .L => w
      | .R => t.right.getD 1 M.blank
      | .S => t.right.getD 0 M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w r 0]
      rfl
    }
  | R =>
    cases r with
    | nil => rfl
    | cons a r' => rfl
  | S => rfl

theorem move_left_succ_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) (j : Nat) :
    ((t.write w).move M.blank d).left.getD (j + 1) M.blank =
      match d with
      | .L => t.left.getD (j + 2) M.blank
      | .R => t.left.getD j M.blank
      | .S => t.left.getD (j + 1) M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l with
    | nil => rfl
    | cons a l' => rfl
  | R =>
    cases r <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w l (j + 1)]
      rfl
    }
  | S => rfl

theorem move_right_succ_eq (M : TM) (t : Tape (Fin M.G)) (w : Fin M.G) (d : Dir) (j : Nat) :
    ((t.write w).move M.blank d).right.getD (j + 1) M.blank =
      match d with
      | .L => t.right.getD j M.blank
      | .R => t.right.getD (j + 2) M.blank
      | .S => t.right.getD (j + 1) M.blank := by
  rcases t with ⟨l, h, r⟩
  cases d with
  | L =>
    cases l <;> {
      simp only [Tape.write, Tape.move]
      rw [Tape.consB_getD M.blank w r (j + 1)]
      rfl
    }
  | R =>
    cases r with
    | nil => rfl
    | cons a r' => rfl
  | S => rfl

theorem nextBlockData_correct (M : TM) (c : Cfg M.k M.Q M.G) (j : Nat) :
    nextBlockData M
      (cfgBlock M c 0)
      (if j = 0 then blankBlock M else cfgBlock M c (j - 1))
      (cfgBlock M c j)
      (cfgBlock M c (j + 1)) =
    cfgBlock M (M.stepOrSelf c) j := by
  have hb0_state : (cfgBlock M c 0).state = c.state := rfl
  have hb0_head : (cfgBlock M c 0).headSym = fun i => (c.tapes i).head := rfl
  unfold nextBlockData TM.stepOrSelf TM.step
  rw [hb0_state, hb0_head]
  cases hδ : M.δ c.state (fun i => (c.tapes i).head) with
  | none => rfl
  | some qwd =>
    rcases qwd with ⟨q', w, d⟩
    cases j with
    | zero =>
      simp only [cfgBlock, ↓reduceIte, Nat.zero_add, Nat.add_one_ne_zero]
      congr 1
      · funext i; exact (move_head_eq M (c.tapes i) (w i) (d i)).symm
      · funext i; exact (move_left_zero_eq M (c.tapes i) (w i) (d i)).symm
      · funext i; exact (move_right_zero_eq M (c.tapes i) (w i) (d i)).symm
    | succ j' =>
      have hj_ne1 : j' + 1 ≠ 0 := by omega
      have hj_ne2 : j' + 1 + 1 ≠ 0 := by omega
      simp only [cfgBlock, hj_ne1, hj_ne2, Nat.add_sub_cancel, Bool.false_eq_true, ↓reduceIte]
      congr 1
      · funext i
        rw [move_left_succ_eq M (c.tapes i) (w i) (d i) j']
        cases d i <;> cases j' <;> rfl
      · funext i
        rw [move_right_succ_eq M (c.tapes i) (w i) (d i) j']
        cases d i <;> cases j' <;> rfl



theorem padFalse_drop_tableOf_ge {D : Nat} (f : Nat → Word) (N : Nat)
    (hf : ∀ j : Nat, j < N → (f j).length = D) {j : Nat} (hj : N ≤ j) :
    padFalse D ((tableOf f N).drop (j * D)) = List.replicate D false := by
  have hlen : (tableOf f N).length ≤ j * D := by
    rw [length_tableOf f N hf]
    exact Nat.mul_le_mul_right D hj
  rw [List.drop_eq_nil_of_le hlen, padFalse_nil]

theorem stepBlockWord_on_encCfg (M : TM) {N : Nat} {c : Cfg M.k M.Q M.G}
    (hbnd : M.TapeBounded N c) {j : Nat} (hj : j < N) :
    stepBlockWord M
      (padFalse (blockWidth M) (encCfg M N c))
      (padFalse (blockWidth M + (blockWidth M + blockWidth M))
        ((List.replicate (blockWidth M) false ++ encCfg M N c).drop (j * blockWidth M))) =
    encBlock M (cfgBlock M (M.stepOrSelf c) j) := by
  let D := blockWidth M
  let f := fun k => encBlock M (cfgBlock M c k)
  have hf : ∀ k : Nat, k < N → (f k).length = D := fun k _ => length_encBlock M _
  have h0N : 0 < N := by omega
  have hw0 : padFalse D (padFalse D (encCfg M N c)) = encBlock M (cfgBlock M c 0) := by
    rw [padFalse_self (length_padFalse D _)]
    have h0 := padFalse_drop_tableOf f N hf h0N
    simpa [encCfg, f, D] using h0
  let wShift := (List.replicate D false ++ encCfg M N c).drop (j * D)
  have hwin_split :
      padFalse (D + (D + D)) wShift =
        padFalse D wShift ++ (padFalse D (wShift.drop D) ++ padFalse D ((wShift.drop D).drop D)) := by
    rw [padFalse_add D (D + D) wShift, padFalse_add D D (wShift.drop D)]
  have hprev : decBlock M (padFalse D (padFalse (D + (D + D)) wShift)) =
      (if j = 0 then blankBlock M else cfgBlock M c (j - 1)) := by
    rw [hwin_split, padFalse_eq_of_length (length_padFalse D wShift)]
    cases j with
    | zero =>
      dsimp only [wShift]
      simp only [Nat.zero_mul, List.drop_zero, ↓reduceIte]
      rw [padFalse_eq_of_length (@List.length_replicate _ D false), decBlock_replicate_false M]
    | succ j' =>
      have hj1 : j' + 1 ≠ 0 := by omega
      simp only [hj1, ↓reduceIte, Nat.add_sub_cancel]
      dsimp only [wShift, encCfg]
      rw [Nat.succ_mul, Nat.add_comm (j' * D) D, ← List.drop_drop,
          drop_append_of_length (@List.length_replicate _ D false)]
      rw [padFalse_drop_tableOf f N hf (by omega), decBlock_encBlock M]
  have hcur : decBlock M (padFalse D ((padFalse (D + (D + D)) wShift).drop D)) =
      cfgBlock M c j := by
    rw [hwin_split, drop_append_of_length (length_padFalse D wShift),
        padFalse_eq_of_length (length_padFalse D (wShift.drop D))]
    dsimp only [wShift, encCfg]
    rw [List.drop_drop, Nat.add_comm (j * D) D, ← List.drop_drop,
        drop_append_of_length (@List.length_replicate _ D false)]
    rw [padFalse_drop_tableOf f N hf hj, decBlock_encBlock M]
  have hnext : decBlock M (padFalse D (((padFalse (D + (D + D)) wShift).drop D).drop D)) =
      cfgBlock M c (j + 1) := by
    rw [hwin_split, drop_append_of_length (length_padFalse D wShift),
        drop_append_of_length (length_padFalse D (wShift.drop D)),
        padFalse_self (length_padFalse D ((wShift.drop D).drop D))]
    dsimp only [wShift, encCfg]
    rw [List.drop_drop, List.drop_drop,
        show j * D + (D + D) = D + (j + 1) * D by rw [Nat.succ_mul]; omega,
        ← List.drop_drop,
        drop_append_of_length (@List.length_replicate _ D false)]
    by_cases hj1 : j + 1 < N
    · rw [padFalse_drop_tableOf f N hf hj1, decBlock_encBlock M]
    · have hj_eq : j + 1 = N := by omega
      rw [padFalse_drop_tableOf_ge f N hf (j := j + 1) (by omega), decBlock_replicate_false M, hj_eq]
      exact (cfgBlock_eq_blankBlock_of_tapeBounded M hbnd N h0N (Nat.le_refl N)).symm
  unfold stepBlockWord
  dsimp only
  change encBlock M (nextBlockData M
    (decBlock M (padFalse D (padFalse D (encCfg M N c))))
    (decBlock M (padFalse D (padFalse (D + (D + D)) wShift)))
    (decBlock M (padFalse D ((padFalse (D + (D + D)) wShift).drop D)))
    (decBlock M (padFalse D (((padFalse (D + (D + D)) wShift).drop D).drop D)))) = _
  rw [hw0, decBlock_encBlock M, hprev, hcur, hnext, nextBlockData_correct M c j]



theorem eval_stepBlockBranch (M : TM) (y wShift r : Word) :
    (stepBlockBranch M).eval [] [y, wShift, r] =
      stepBlockWord M (padFalse (blockWidth M) y)
        (padFalse (blockWidth M + (blockWidth M + blockWidth M)) wShift) ++ r := by
  unfold stepBlockBranch
  rw [eval_branchPrefix (blockWidth M) _ y [wShift, r] rfl,
      eval_branchPrefix (blockWidth M + (blockWidth M + blockWidth M)) _ wShift [r] rfl,
      eval_prependConst]
  rfl



theorem eval_stepCfgStepBC (M : TM) (u r y : Word) :
    (stepCfgStepBC M).eval [u] [r, y] =
      stepBlockWord M (padFalse (blockWidth M) y)
        (padFalse (blockWidth M + (blockWidth M + blockWidth M))
          ((List.replicate (blockWidth M) false ++ y).drop (u.length * blockWidth M))) ++ r := by
  simp only [stepCfgStepBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec3_zero, vec3_succ, vec2_zero, vec2_one, vec1_zero,
    Fn.eval_projN, Fn.eval_projS, eval_prependConst, eval_dropBlock,
    List.getD_cons_zero, List.getD_cons_succ]
  exact eval_stepBlockBranch M y _ r



theorem eval_stepCfgBC_buildRev (M : TM) {N : Nat} {c : Cfg M.k M.Q M.G}
    (hbnd : M.TapeBounded N c) (u : Word) (hu : u.length ≤ N) :
    (Fn.srec constZero (stepCfgStepBC M) (stepCfgStepBC M)).eval [u] [encCfg M N c] =
      concatRev (fun j => encBlock M (cfgBlock M (M.stepOrSelf c) j)) u.length := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [List.length_cons] at hu
    have hstep : (Fn.srec constZero (stepCfgStepBC M) (stepCfgStepBC M)).eval [b :: u] [encCfg M N c] =
        (stepCfgStepBC M).eval [u]
          [(Fn.srec constZero (stepCfgStepBC M) (stepCfgStepBC M)).eval [u] [encCfg M N c], encCfg M N c] := by
      cases b <;> simp [Fn.eval_srec_cons]
    rw [hstep, eval_stepCfgStepBC, stepBlockWord_on_encCfg M hbnd (by omega), ih (by omega)]
    rfl

theorem eval_stepCfgBC (M : TM) (W : Word) {c : Cfg M.k M.Q M.G}
    (hbnd : M.TapeBounded W.length c) :
    (stepCfgBC M).eval [W] [encCfg M W.length c] =
      encCfg M W.length (M.stepOrSelf c) := by
  simp only [stepCfgBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec1_zero, Fn.eval_projN, List.getD_cons_zero]
  rw [eval_stepCfgBC_buildRev M hbnd W (Nat.le_refl W.length)]
  exact eval_revBlocks (fun j => encBlock M (cfgBlock M (M.stepOrSelf c) j)) W
    (fun j _ => length_encBlock M _)



theorem eval_runCfgBC (M : TM) (T W x : Word) (hW : x.length + T.length ≤ W.length) :
    (runCfgBC M).eval [T, W] [encCfg M W.length (M.init x)] =
      encCfg M W.length (M.run T.length (M.init x)) := by
  induction T with
  | nil => rfl
  | cons b T ih =>
    simp only [List.length_cons] at hW ⊢
    have hstep : (runCfgBC M).eval [b :: T, W] [encCfg M W.length (M.init x)] =
        (stepCfgBC M).eval [W] [(runCfgBC M).eval [T, W] [encCfg M W.length (M.init x)]] := by
      cases b <;> simp [runCfgBC, Fn.eval_srec_cons, List.ofFn_zero, List.ofFn_succ]
    have hbnd_T : M.TapeBounded W.length (M.run T.length (M.init x)) := by
      intro i
      rcases M.tapeBounded_run x T.length i with ⟨hl, hr⟩
      exact ⟨by omega, by omega⟩
    rw [hstep, ih (by omega), eval_stepCfgBC M W hbnd_T, ← M.run_succ_eq_stepOrSelf]

/-! ## 6. Output Decoding (`outputCfgBC`) and Main Completeness Theorem (`defFun_eq_FP`) -/





theorem eval_outBlockFn (M : TM) (w r : Word) :
    (outBlockFn M w).eval [] [r] = outStepWord M (decBlock M w) r := by
  unfold outBlockFn outStepWord
  dsimp only
  cases (decBlock M w).isZero with
  | false =>
    cases M.decodeBit ((decBlock M w).rightSym ⟨0, M.hk⟩) <;> simp
  | true =>
    cases M.decodeBit ((decBlock M w).headSym ⟨0, M.hk⟩) with
    | none =>
      cases M.decodeBit ((decBlock M w).rightSym ⟨0, M.hk⟩) <;> simp
    | some bit0 =>
      cases M.decodeBit ((decBlock M w).rightSym ⟨0, M.hk⟩) <;> simp



theorem eval_outCfgStepBC (M : TM) (u r yRev : Word) :
    (outCfgStepBC M).eval [u] [r, yRev] =
      outStepWord M (decBlock M (padFalse (blockWidth M) (yRev.drop (u.length * blockWidth M)))) r := by
  simp only [outCfgStepBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec2_zero, vec2_one, vec1_zero, Fn.eval_projN, Fn.eval_projS, eval_dropBlock,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [eval_branchPrefix (blockWidth M) (outBlockFn M) _ [r] rfl, eval_outBlockFn]

theorem decodeBit_blank (M : TM) : M.decodeBit M.blank = none := by
  rfl

theorem readBits_drop_step (M : TM) (right : List (Fin M.G)) (j : Nat) :
    (match M.decodeBit (right.getD j M.blank) with
     | some bit => bit :: M.readBits (right.drop (j + 1))
     | none => []) = M.readBits (right.drop j) := by
  induction right generalizing j with
  | nil =>
    simp [List.getD, TM.readBits]
  | cons a l ih =>
    cases j with
    | zero =>
      rfl
    | succ j' =>
      simpa [List.getD] using ih j'

theorem eval_outExtract_lt (M : TM) {N : Nat} {c : Cfg M.k M.Q M.G}
    (hbnd : (c.tapes ⟨0, M.hk⟩).right.length < N) :
    ∀ (u : Word), u.length < N →
      (Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [u]
        [concatRev (fun j => encBlock M (cfgBlock M c j)) N] =
      M.readBits (((c.tapes ⟨0, M.hk⟩).right).drop (N - u.length))
  | [], _ => by
    simp only [List.length_nil, Nat.sub_zero, Fn.eval_srec_nil, eval_constZero]
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | b :: u, hu => by
    simp only [List.length_cons] at hu ⊢
    have hstep : (Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [b :: u]
        [concatRev (fun j => encBlock M (cfgBlock M c j)) N] =
      (outCfgStepBC M).eval [u]
        [(Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [u]
          [concatRev (fun j => encBlock M (cfgBlock M c j)) N],
         concatRev (fun j => encBlock M (cfgBlock M c j)) N] := by
      cases b <;> simp [Fn.eval_srec_cons]
    rw [hstep, eval_outCfgStepBC,
        padFalse_drop_concatRev (fun j => encBlock M (cfgBlock M c j)) N
          (fun j _ => length_encBlock M _) u.length (by omega),
        decBlock_encBlock M,
        eval_outExtract_lt M hbnd u (by omega)]
    have hj_pos : N - 1 - u.length ≠ 0 := by omega
    have hj_add : (N - 1 - u.length) + 1 = N - u.length := by omega
    have hj_sub : N - (u.length + 1) = N - 1 - u.length := by omega
    simp only [outStepWord, cfgBlock, hj_pos, Bool.false_eq_true, ↓reduceIte,
      ← hj_add, hj_sub]
    exact readBits_drop_step M (c.tapes ⟨0, M.hk⟩).right (N - 1 - u.length)



theorem eval_outputCfgBC (M : TM) (W : Word) {c : Cfg M.k M.Q M.G}
    (hbnd : (c.tapes ⟨0, M.hk⟩).right.length < W.length) :
    (outputCfgBC M).eval [W] [encCfg M W.length c] = M.output c := by
  simp only [outputCfgBC, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec1_zero, Fn.eval_projN, Fn.eval_projS, List.getD_cons_zero]
  have hrev : (revBlocks (blockWidth M)).eval [W] [encCfg M W.length c] =
      concatRev (fun j => encBlock M (cfgBlock M c j)) W.length :=
    eval_revBlocks_tableOf (fun j => encBlock M (cfgBlock M c j)) W (fun j _ => length_encBlock M _)
  rw [hrev]
  cases W with
  | nil =>
    simp at hbnd
  | cons b u =>
    have hstep : (Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [b :: u]
        [concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length] =
      (outCfgStepBC M).eval [u]
        [(Fn.srec constZero (outCfgStepBC M) (outCfgStepBC M)).eval [u]
          [concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length],
         concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length] := by
      cases b <;> simp [Fn.eval_srec_cons]
    have hu_lt : u.length < (b :: u).length := by simp
    rw [hstep, eval_outCfgStepBC,
        padFalse_drop_concatRev (fun j => encBlock M (cfgBlock M c j)) (b :: u).length
          (fun j _ => length_encBlock M _) u.length hu_lt,
        decBlock_encBlock M,
        eval_outExtract_lt M hbnd u hu_lt]
    have h0 : (b :: u).length - 1 - u.length = 0 := by simp
    have h1 : (b :: u).length - u.length = 1 := by simp
    rw [h0, h1]
    simp only [outStepWord, cfgBlock, ↓reduceIte]
    have hr0 := readBits_drop_step M (c.tapes ⟨0, M.hk⟩).right 0
    simp only [Nat.zero_add, List.drop_zero] at hr0
    cases hh : M.decodeBit (c.tapes ⟨0, M.hk⟩).head <;> simp only [hh, TM.output, TM.readBits]
    congr 1

/-- If `M.HaltsWithin x T y`, then running `M` for `T` steps yields a configuration whose
    output is `y`. -/
theorem TM.output_run_of_haltsWithin (M : TM) {x : Word} {T : Nat} {y : Word}
    (h : M.HaltsWithin x T y) :
    M.output (M.run T (M.init x)) = y := by
  rcases h with ⟨s, hs, hstep, hout⟩
  have hadd : T = s + (T - s) := by omega
  rw [hadd, M.run_add s (T - s) (M.init x),
      M.run_of_step_none hstep (T - s), hout]



theorem eval_simTM (M : TM) (p : Poly) (x : Word) :
    (simTM M p).eval [x] [] = M.output (M.run (p.eval x.length) (M.init x)) := by
  let W := (polyWord (.add (.add .var p) (.const 1))).eval [x] []
  let T := (polyWord p).eval [x] []
  have hW_len : W.length = x.length + p.eval x.length + 1 := by
    simp [W]
  have hT_len : T.length = p.eval x.length := by
    simp [T]
  simp only [simTM, Fn.eval_comp, List.ofFn_zero, List.ofFn_succ,
    vec2_zero, vec2_one, vec1_zero, Fn.eval_projN, List.getD_cons_zero]
  change (outputCfgBC M).eval [W] [(runCfgBC M).eval [T, W] [(initCfgBC M).eval [W] [x]]] = _
  rw [eval_initCfgBC M W x,
      eval_runCfgBC M T W x (by omega),
      hT_len]
  apply eval_outputCfgBC M W
  have hbnd := (M.tapeBounded_run x (p.eval x.length) ⟨0, M.hk⟩).2
  omega

/-- **Bellantoni–Cook Polynomial-Time Completeness (`FP f → BCDefinable f`)**:
    Every word function computable in polynomial time by a multi-tape Turing machine
    is definable in the Bellantoni–Cook safe recursion algebra. -/
theorem bc_completeness (f : Word → Word) (h : FP f) : BCDefinable f := by
  rcases h with ⟨M, p, hM⟩
  refine ⟨simTM M p, fun x => ?_⟩
  rw [eval_simTM M p x]
  exact M.output_run_of_haltsWithin (hM x)

/-- **Bellantoni–Cook Theorem (1992) (`defFun_eq_FP`)**:
    A unary word function `f : Word → Word` is definable by a closed Bellantoni–Cook
    program `prog : Fn 1 0` if and only if `f ∈ FP`. -/
theorem defFun_eq_FP (f : Word → Word) :
    (∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f :=
  ⟨bc_soundness f, bc_completeness f⟩

/-- Equivalent formulation of `defFun_eq_FP` using `BCDefinable`. -/
theorem bcDefinable_iff_FP (f : Word → Word) :
    BCDefinable f ↔ FP f :=
  defFun_eq_FP f

end BC1992

open BC1992

/-- **Main Theorem (Bellantoni & Cook 1992 — Recursion-Theoretic Characterization of `FP`)**:
    1. (`bc_soundness`) Every BC-definable unary word function belongs to `FP`.
    2. (`bc_completeness`) Every word function in `FP` is BC-definable.
    3. (`defFun_eq_FP`) For every unary word function `f : Word → Word`,
       `(∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f`.
    4. (`bcDefinable_iff_FP`) `BCDefinable f ↔ FP f`. -/
theorem solution :
    (∀ f : Word → Word, BCDefinable f → FP f) ∧
    (∀ f : Word → Word, FP f → BCDefinable f) ∧
    (∀ f : Word → Word,
      (∃ prog : Fn 1 0, ∀ x : Word, prog.eval [x] [] = f x) ↔ FP f) ∧
    (∀ f : Word → Word, BCDefinable f ↔ FP f) := by
  exact ⟨bc_soundness, bc_completeness, defFun_eq_FP, bcDefinable_iff_FP⟩
