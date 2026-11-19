-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_13_ii_iv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:22:32.670044+00:00
-- url     : https://prove2.me/submissions/36c3638a-fe3a-441c-8f28-385bf6aec349

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_lemma_12_9
import Theorems.Thm_DiazModulus_matrix_rank_map_field

open Complex ComplexConjugate

/-! # DALAG Prop. 12.13, (ii) ⇒ (iv)

Extend `{1}` to a `k`-basis `b` of `k·1 + span(e)` inside `{1} ∪ {e₁, …, e_m}`, and list `b ∖ {1}` as
`y₁, …, y_q`. Then `1, y₁, …, y_q` is a basis of a subspace `W ⊇ span(e)`, and each `yᵢ` lies in `E`, so by (ii)
the `yᵢ` are algebraically independent over `k`. Extend the coordinate map of `W` in this basis to a `k`-linear
map `φ : K → k^{q+1}`; it is injective on `span(e)`, and every `w ∈ W` equals
`φ(w)₀ + Σᵢ φ(w)ᵢ₊₁ yᵢ`. Lemma 12.9 says that the matrix obtained from `M` by replacing each entry `w` with
the linear polynomial `φ(w)₀ + Σᵢ φ(w)ᵢ₊₁ Xᵢ`, viewed over the fraction field of `k[X₁, …, X_q]`, has the same
rank as the generic matrix `Σⱼ Xⱼ Nⱼ`. Since the `yᵢ` are algebraically independent, evaluation at `y` extends
to a field homomorphism from the fraction field of `k[X₁, …, X_q]` to `K`, which maps that polynomial matrix
to `M` entrywise (the entries of `M` lie in `span(e) ⊆ W`). A field homomorphism preserves rank, so the rank
of `M` is the rank of the generic matrix. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (h1 : (1 : K) ∈ E)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x)
    {s t m : ℕ} (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
    (N : Fin m → Matrix (Fin s) (Fin t) k) (he : LinearIndependent k e) (heE : ∀ j, e j ∈ E)
    (hM : M = ∑ j, e j • (N j).map (algebraMap k K)) :
    M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  classical
  -- a basis of `span (1, e)` containing `1`
  obtain ⟨b, hbS, h1b, hSb, hbli⟩ := exists_linearIndepOn_id_extension (K := k)
    (s := ({1} : Set K)) (t := insert (1 : K) (Set.range e))
    (by simp)
    (by simp)
  have h1b' : (1 : K) ∈ b := h1b rfl
  set b' : Set K := b \ {1} with hb'
  have hbfin : b.Finite := (Set.finite_range e).insert 1 |>.subset hbS
  have : Finite b' := (hbfin.subset Set.sdiff_subset).to_subtype
  let eqv := Finite.equivFin b'
  set q := Nat.card b'
  let y : Fin q → K := fun i => (eqv.symm i : K)
  have hrange_y : Set.range y = b' := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; exact (eqv.symm i).2
    · intro hz; exact ⟨eqv ⟨z, hz⟩, by simp [y]⟩
  have hbeq : b = insert 1 b' := by simp [hb', Set.insert_eq_of_mem h1b']
  have hyli : LinearIndependent k y := by
    have : LinearIndepOn k id b' := hbli.mono Set.sdiff_subset
    exact LinearIndependent.comp (ι' := Fin q) this eqv.symm eqv.symm.injective
  have h1y : (1 : K) ∉ Submodule.span k (Set.range y) := by
    rw [hrange_y]
    have := hbli
    rw [hbeq, linearIndepOn_insert (by simp [hb'])] at this
    simpa using this.2
  let c : Fin (q + 1) → K := Fin.cons 1 y
  have hcli : LinearIndependent k c := linearIndependent_finCons.2 ⟨hyli, h1y⟩
  let W := Submodule.span k (Set.range c)
  have hrc : Set.range c = b := by
    simp only [c, Fin.range_cons, hrange_y, hbeq]
  have heW : Submodule.span k (Set.range e) ≤ W := by
    rw [Submodule.span_le]
    intro z hz
    have : z ∈ Submodule.span k b := hSb (Set.mem_insert_of_mem _ hz)
    simpa [W, hrc] using this
  let B := Module.Basis.span hcli
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (B.equivFun.toLinearMap : W →ₗ[k] (Fin (q + 1) → k))
  have hφW : ∀ x (hx : x ∈ W), φ x = B.equivFun ⟨x, hx⟩ := fun x hx => by
    simpa using LinearMap.congr_fun hφ ⟨x, hx⟩
  have hexp : ∀ x (hx : x ∈ W), x = algebraMap k K (φ x 0) +
      ∑ i : Fin q, algebraMap k K (φ x i.succ) * y i := by
    intro x hx
    have h := congrArg Subtype.val (B.sum_equivFun ⟨x, hx⟩)
    rw [← hφW x hx] at h
    simp only [Submodule.coe_sum, Submodule.coe_smul, B, Module.Basis.span_apply] at h
    rw [Fin.sum_univ_succ] at h
    simp only [c, Fin.cons_zero, Fin.cons_succ, Algebra.smul_def, mul_one] at h
    exact h.symm
  have hinj : Set.InjOn φ (Submodule.span k (Set.range e) : Set K) := by
    intro x hx x' hx' h
    rw [hφW x (heW hx), hφW x' (heW hx')] at h
    simpa using B.equivFun.injective h
  have h12 := DiazModulus.dalag_lemma_12_9 (n := q) M e he N hM φ hinj
  have hy : AlgebraicIndependent k y := hii q y (fun i => ?_) hcli
  swap
  · have : y i ∈ b := hbeq ▸ Set.mem_insert_of_mem _ (hrange_y ▸ Set.mem_range_self i)
    rcases hbS this with h | ⟨j, hj⟩
    · rw [h]; exact h1
    · rw [← hj]; exact heE j
  let f : FractionRing (MvPolynomial (Fin q) k) →+* K :=
    IsFractionRing.lift (A := MvPolynomial (Fin q) k)
      (g := (MvPolynomial.aeval (R := k) y).toRingHom) (by exact hy)
  rw [← h12, ← DiazModulus.matrix_rank_map_field f]
  congr 1
  ext a b₀
  have hmem : M a b₀ ∈ Submodule.span k (Set.range e) := by
    rw [hM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  simp only [Matrix.map_apply, f]
  simp [MvPolynomial.aeval_X]
  exact hexp _ (heW hmem)
