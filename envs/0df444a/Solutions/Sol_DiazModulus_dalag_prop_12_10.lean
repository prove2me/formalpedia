-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_10
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-15T05:51:32.385552+00:00
-- url     : https://prove2.me/submissions/d0767086-293f-4faa-8baa-9234dc2a2cbe

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # DALAG Prop. 12.10 (D. Roy): every polynomial is a determinant of a linear matrix

Write `x₀ = 1` and `x_{i+1} = X_i`, so every `x_t` has degree at most `1`. First, every polynomial of total
degree at most `m + 1` is `Σ_t x_t g_t` with each `g_t` of degree at most `m`: a constant monomial goes to `g₀`,
and any other monomial is `X_i` times a monomial of one degree less. Second, let `M` be a square matrix with
entries of degree at most `m + 1`, `m ≥ 1`. Decomposing every entry, `M = AB` with `A_{i,(t,j)} = δ_{ij} x_t`
(degree at most `1`) and `B_{(t,j),l}` the `g_t` of `M_{jl}` (degree at most `m`); the block matrix `(1 B; −A 0)`
has entries of degree at most `m` and determinant `det(AB) = det M`, by the Schur complement. Starting from the
`1 × 1` matrix `(P)` and repeating this `deg P` times gives a square matrix with entries of degree at most `1` and
determinant `P`. Finally, decomposing each entry of that matrix with `m = 0` gives constant `g_t`, so it is
`A₀ + Σ_i X_i A_i` with all `A_i` over `k`. -/

namespace RC8_P1210
open DiazModulus

/-- `x₀ = 1`, `x_{i+1} = X_i`. -/
noncomputable abbrev xs (k : Type*) [CommRing k] (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin n) k :=
  Fin.cons 1 MvPolynomial.X

theorem xs_deg {k : Type*} [CommRing k] {n : ℕ} (t : Fin (n + 1)) : (xs k n t).totalDegree ≤ 1 := by
  refine Fin.cases ?_ (fun i => ?_) t
  · simp [xs, MvPolynomial.totalDegree_one]
  · simp only [xs, Fin.cons_succ]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    simp

/-- The degree decomposition of one monomial. -/
theorem mono_decomp {k : Type*} [CommRing k] {n : ℕ} (m : ℕ) (a : Fin n →₀ ℕ) (c : k)
    (ha : (a.sum fun _ e => e) ≤ m + 1) :
    ∃ g : Fin (n + 1) → MvPolynomial (Fin n) k, (∀ t, (g t).totalDegree ≤ m) ∧
      MvPolynomial.monomial a c = ∑ t, xs k n t * g t := by
  classical
  by_cases h0 : a = 0
  · refine ⟨Fin.cons (MvPolynomial.C c) 0, ?_, ?_⟩
    · intro t; refine Fin.cases ?_ (fun i => ?_) t <;> simp [MvPolynomial.totalDegree_C]
    · simp [Fin.sum_univ_succ, h0, xs]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra h; push Not at h; exact h0 (Finsupp.ext h)
    set b := a - Finsupp.single i 1 with hb
    have hab : a = b + Finsupp.single i 1 := by
      rw [hb, tsub_add_cancel_of_le]
      exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    have hbdeg : (b.sum fun _ e => e) ≤ m := by
      have : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by
        rw [hab, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      omega
    refine ⟨Pi.single i.succ (MvPolynomial.monomial b c), ?_, ?_⟩
    · intro t
      by_cases ht : t = i.succ
      · subst ht; simp only [Pi.single_eq_same]
        exact (MvPolynomial.totalDegree_monomial_le _ _).trans hbdeg
      · simp [ht, MvPolynomial.totalDegree_zero]
    · rw [Finset.sum_eq_single i.succ (fun t _ ht => by simp [ht]) (by simp)]
      rw [hab, MvPolynomial.monomial_add_single, pow_one]
      simp [xs, mul_comm]

/-- The degree decomposition `f = Σ_t x_t g_t`. -/
theorem decomp {k : Type*} [CommRing k] {n : ℕ} (m : ℕ) (f : MvPolynomial (Fin n) k)
    (hf : f.totalDegree ≤ m + 1) :
    ∃ g : Fin (n + 1) → MvPolynomial (Fin n) k, (∀ t, (g t).totalDegree ≤ m) ∧
      f = ∑ t, xs k n t * g t := by
  classical
  have key : ∀ a ∈ f.support, ∃ g : Fin (n + 1) → MvPolynomial (Fin n) k, (∀ t, (g t).totalDegree ≤ m) ∧
      MvPolynomial.monomial a (MvPolynomial.coeff a f) = ∑ t, xs k n t * g t :=
    fun a ha => mono_decomp m a _ ((MvPolynomial.le_totalDegree ha).trans hf)
  choose G hGdeg hGeq using key
  refine ⟨fun t => ∑ a ∈ f.support.attach, G a.1 a.2 t, ?_, ?_⟩
  · intro t
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    exact Finset.sup_le fun a _ => hGdeg _ _ t
  · conv_lhs => rw [MvPolynomial.as_sum f, ← Finset.sum_attach]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => hGeq a.1 a.2

/-- One reduction of the degree bound, through the block matrix `(1 B; −A 0)`. -/
theorem reduce {k : Type*} [CommRing k] {n : ℕ} (m : ℕ) (hm : 1 ≤ m)
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial (Fin n) k))
    (hM : ∀ a b, (M a b).totalDegree ≤ m + 1) :
    ∃ F : Matrix ((Fin (n + 1) × ι) ⊕ ι) ((Fin (n + 1) × ι) ⊕ ι) (MvPolynomial (Fin n) k),
      (∀ a b, (F a b).totalDegree ≤ m) ∧ F.det = M.det := by
  classical
  choose G hGdeg hGeq using fun a b => decomp m (M a b) (hM a b)
  let A : Matrix ι (Fin (n + 1) × ι) (MvPolynomial (Fin n) k) :=
    fun i tj => if tj.2 = i then xs k n tj.1 else 0
  let B : Matrix (Fin (n + 1) × ι) ι (MvPolynomial (Fin n) k) := fun tj l => G tj.2 l tj.1
  have hAB : A * B = M := by
    refine Matrix.ext fun i l => ?_
    rw [Matrix.mul_apply, Fintype.sum_prod_type (f := fun tj => A i tj * B tj l), hGeq i l]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [A, B, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨Matrix.fromBlocks 1 B (-A) 0, ?_, ?_⟩
  · rintro (⟨t, j⟩ | i) (⟨t', j'⟩ | l)
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      split_ifs <;> simp [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_zero]
    · rw [Matrix.fromBlocks_apply₁₂]; exact hGdeg j l t
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, MvPolynomial.totalDegree_neg]
      simp only [A]
      split_ifs
      · exact (xs_deg t').trans hm
      · simp [MvPolynomial.totalDegree_zero]
    · simp [MvPolynomial.totalDegree_zero]
  · rw [Matrix.det_fromBlocks_one₁₁, zero_sub, Matrix.neg_mul, neg_neg, hAB]

/-- Iteration down to degree at most `1`. -/
theorem iter {k : Type*} [CommRing k] {n : ℕ} (m : ℕ) :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial (Fin n) k)),
      (∀ a b, (M a b).totalDegree ≤ m + 1) →
      ∃ (s : ℕ) (M' : Matrix (Fin s) (Fin s) (MvPolynomial (Fin n) k)),
        (∀ a b, (M' a b).totalDegree ≤ 1) ∧ M'.det = M.det := by
  induction m with
  | zero =>
    intro ι _ _ M hM
    let e := Fintype.equivFin ι
    exact ⟨Fintype.card ι, Matrix.reindex e e M, fun a b => hM _ _, Matrix.det_reindex_self e M⟩
  | succ m IH =>
    intro ι _ _ M hM
    obtain ⟨F, hF, hdet⟩ := reduce (m + 1) (by omega) M hM
    obtain ⟨s, M', hM', hdet'⟩ := IH F hF
    exact ⟨s, M', hM', hdet'.trans hdet⟩

/-- A matrix with entries of degree at most `1` is `A₀ + Σ_i X_i A_i`. -/
theorem coeff_form {k : Type*} [CommRing k] {n s : ℕ}
    (M : Matrix (Fin s) (Fin s) (MvPolynomial (Fin n) k)) (hM : ∀ a b, (M a b).totalDegree ≤ 1) :
    ∃ (A₀ : Matrix (Fin s) (Fin s) k) (A : Fin n → Matrix (Fin s) (Fin s) k),
      A₀.map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) +
        ∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) k) •
          (A i).map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) = M := by
  choose G hGdeg hGeq using fun a b => decomp 0 (M a b) (hM a b)
  have hC : ∀ a b t, G a b t = MvPolynomial.C ((G a b t).coeff 0) :=
    fun a b t => MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp (hGdeg a b t))
  refine ⟨Matrix.of fun a b => (G a b 0).coeff 0,
    fun i => Matrix.of fun a b => (G a b i.succ).coeff 0, ?_⟩
  refine Matrix.ext fun a b => ?_
  rw [hGeq a b, Fin.sum_univ_succ]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, xs, Fin.cons_zero, Fin.cons_succ, one_mul]
  rw [← hC a b 0]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [← hC a b i.succ]

end RC8_P1210

open DiazModulus RC8_P1210 in
theorem solution {k : Type*} [CommRing k] {n : ℕ} (P : MvPolynomial (Fin n) k) :
    ∃ (s : ℕ) (A₀ : Matrix (Fin s) (Fin s) k) (A : Fin n → Matrix (Fin s) (Fin s) k),
      (A₀.map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k) +
        ∑ i, (MvPolynomial.X i : MvPolynomial (Fin n) k) •
          (A i).map (MvPolynomial.C : k →+* MvPolynomial (Fin n) k)).det = P := by
  obtain ⟨s, M', hM', hdet⟩ := iter (k := k) (n := n) P.totalDegree
    (Matrix.of fun _ _ : Fin 1 => P) (fun _ _ => by simp)
  obtain ⟨A₀, A, hA⟩ := coeff_form M' hM'
  exact ⟨s, A₀, A, by rw [hA, hdet, Matrix.det_unique]; rfl⟩
