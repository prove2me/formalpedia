-- Prove2me | solution 1 for DiazModulus.dalag_cor_12_14
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:34.468444+00:00
-- url     : https://prove2.me/submissions/2973d290-60d3-4c5a-af83-c9a4f3d97aa6

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_13_i_ii_span
import Theorems.Thm_DiazModulus_dalag_prop_12_13_ii_iv
import Theorems.Thm_DiazModulus_dalag_prop_12_13_iii_ii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_iv_iii

open Complex ComplexConjugate

/-! # DALAG Cor. 12.14

Let `E₀` be a `k`-subspace of `K` with `k ∩ E₀ = {0}`, and `E = k + E₀`, which contains `1`. Both directions go
through Prop. 12.13 for `E`.
(⇒) We show (ii) for `E`. Let `x` be a family in `E` with `1, x` linearly independent over `k`; write
`xᵢ = cᵢ + yᵢ` with `cᵢ ∈ k` and `yᵢ ∈ E₀`. The `yᵢ` are `k`-free: a relation `Σ λᵢ yᵢ = 0` gives
`Σ λᵢ xᵢ − (Σ λᵢ cᵢ)·1 = 0`, a relation among `1, x`, so every `λᵢ = 0`. By hypothesis the `yᵢ` are then
algebraically independent, and each `xᵢ` lies in the span of `1` and the `yᵢ`; the affine change of variables
(the span form of (i) ⇒ (ii)) makes `x` algebraically independent. Then (ii) ⇒ (iv) (Lemma 12.9) gives the
equality of rank and structural rank for every matrix over `E`.
(⇐) The rank property is (iv) for `E`; (iv) ⇒ (iii) ⇒ (ii) gives (ii) for `E`. Let `x` be a `k`-free family in
`E₀`. If `1` were in the `k`-span of `x`, it would lie in `E₀`, against `k ∩ E₀ = {0}`; so `1, x` is `k`-free,
and (ii) makes `x` algebraically independent. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E₀ : Submodule k K)
    (hE₀ : ∀ c : k, algebraMap k K c ∈ E₀ → c = 0) :
    (∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E₀) → LinearIndependent k x →
        AlgebraicIndependent k x) ↔
      ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
        (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e →
        (∀ j, e j ∈ Submodule.span k {(1 : K)} ⊔ E₀) →
        M = ∑ j, e j • (N j).map (algebraMap k K) →
        M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k)
          (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) •
            (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank := by
  have h1 : (1 : K) ∈ Submodule.span k {(1 : K)} ⊔ E₀ :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self 1)
  constructor
  · intro hL
    -- (ii) for `E = k + E₀`
    have hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ Submodule.span k {(1 : K)} ⊔ E₀) →
        LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x := by
      intro n x hxE hx
      have hdec : ∀ i, ∃ c : k, ∃ y ∈ E₀, x i = c • (1 : K) + y := by
        intro i
        obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp (hxE i)
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
        exact ⟨c, y, hy, hay.symm⟩
      choose c y hyE hxy using hdec
      have hy : LinearIndependent k y := by
        rw [Fintype.linearIndependent_iff] at hx ⊢
        intro g hg
        have hsum : ∑ j, (Fin.cons (-∑ i, g i * c i) g : Fin (n + 1) → k) j •
            (Fin.cons (1 : K) x : Fin (n + 1) → K) j = 0 := by
          simp [Fin.sum_univ_succ, hxy, smul_add, smul_smul, Finset.sum_add_distrib, hg, ← Finset.sum_smul]
        have h0 := hx _ hsum
        intro i
        simpa using h0 i.succ
      refine DiazModulus.dalag_prop_12_13_i_ii_span y (hL n y hyE hy) x (fun i => ?_) hx
      rw [hxy i]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
        (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
    exact fun _ _ _ M e N he heE hM => DiazModulus.dalag_prop_12_13_ii_iv _ h1 hii M e N he heE hM
  · intro hiv n x hxE hx
    refine DiazModulus.dalag_prop_12_13_iii_ii _ h1
      (fun _ _ y hy hyE P hP hP0 => DiazModulus.dalag_prop_12_13_iv_iii _ hiv y hy hyE P hP hP0) x
      (fun i => Submodule.mem_sup_right (hxE i)) ?_
    rw [linearIndependent_finCons]
    refine ⟨hx, fun h => ?_⟩
    have h1E : (1 : K) ∈ E₀ := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hxE i) h
    exact one_ne_zero (hE₀ 1 (by simpa using h1E))
