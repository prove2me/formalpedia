-- Prove2me | solution 1 for BC1992.lemma_2_1_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T03:16:22.580909+00:00
-- url     : https://prove2.me/submissions/d6669a80-def1-4739-9cff-a7580d158b3b

import Definitions.Def_BC1992_Syntax

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

open BC1992

/-- **Lemma 2.1 (Bellantoni & Cook 1992 — Syntactic Polynomial Output-Length Bound)**:
    1. Every syntactic polynomial `p : Poly` is monotone on `Nat`.
    2. For every `f : Fn n m`, normal inputs `xs` with `∀ x ∈ xs, x.length ≤ N`, and safe inputs `ys`,
       `(f.eval xs ys).length ≤ f.sizePoly.eval N + Fn.maxLen ys`.
    3. When `f : Fn n 0` has no safe inputs (`ys = []`), `(f.eval xs []).length ≤ f.sizePoly.eval N`.
    4. For a unary program `f : Fn 1 0` and input word `x : Word`,
       `(f.eval [x] []).length ≤ f.sizePoly.eval x.length`.
    5. When all normal inputs `xs` and safe inputs `ys` have length at most `K`,
       `(f.eval xs ys).length ≤ f.fullSizePoly.eval K`. -/
theorem solution :
    (∀ (p : Poly) {n m : Nat}, n ≤ m → p.eval n ≤ p.eval m) ∧
    (∀ {n m : Nat} (f : Fn n m) (xs ys : List Word) {N : Nat},
      (∀ x ∈ xs, x.length ≤ N) →
      (f.eval xs ys).length ≤ f.sizePoly.eval N + Fn.maxLen ys) ∧
    (∀ {n : Nat} (f : Fn n 0) (xs : List Word) {N : Nat},
      (∀ x ∈ xs, x.length ≤ N) →
      (f.eval xs []).length ≤ f.sizePoly.eval N) ∧
    (∀ (f : Fn 1 0) (x : Word),
      (f.eval [x] []).length ≤ f.sizePoly.eval x.length) ∧
    (∀ {n m : Nat} (f : Fn n m) (xs ys : List Word) {K : Nat},
      (∀ x ∈ xs, x.length ≤ K) →
      (∀ y ∈ ys, y.length ≤ K) →
      (f.eval xs ys).length ≤ f.fullSizePoly.eval K) := by
  exact ⟨Poly.eval_mono, Fn.eval_length_le_sizePoly, Fn.eval_normal_length_le, Fn.eval_one_length_le, Fn.eval_length_le_fullSizePoly⟩
