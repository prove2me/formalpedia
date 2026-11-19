-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_2_ii
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:22:38.563442+00:00
-- url     : https://prove2.me/submissions/869c5345-ca02-4adb-9baa-606847659460

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_2_split
import Theorems.Thm_DiazModulus_dalag_prop_12_2_step

open Complex ComplexConjugate

/-! # DALAG Prop. 12.2 for every subspace satisfying (ii)

We prove the claim for all matrices `M` over `E` by strong induction on the dimension of the `k`-span `F` of
the entries of `M`. If `F = 0`, then `M = 0` and `r = 0`, `P = Q = 1` work. Otherwise `F` is a non-zero
finite-dimensional subspace of `E`, and the splitting lemma (which uses (ii)) gives `x ∈ F`, `x ≠ 0` and a
subspace `F₁ < F` such that every `f ∈ F` is congruent to `x·c` modulo `F₁` for some `c ∈ k`, and either
`F₁ = 0` or `x` is transcendental over `k(F₁)`. Choosing these `c` entrywise gives a matrix `N` over `k` with
`M − xN` over `F₁`. Every matrix over `F₁` has the required form by the induction hypothesis, since its
entries span a subspace of `F₁ ⊆ E`, of dimension at most `dim F₁ < dim F`. The induction step then gives the
required form for `M`. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (hii : ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
      LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x)
    {s t : ℕ} (M : Matrix (Fin s) (Fin t) K) (hM : ∀ i j, M i j ∈ E) :
    ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  classical
  suffices H : ∀ n : ℕ, ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) →
      Module.finrank k (Submodule.span k (Set.range fun p : Fin s × Fin t => M p.1 p.2)) ≤ n →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det from H _ s t M hM le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t M hM hdim
  set F := Submodule.span k (Set.range fun p : Fin s × Fin t => M p.1 p.2) with hFdef
  have hMF : ∀ i j, M i j ∈ F := fun i j => Submodule.subset_span ⟨(i, j), rfl⟩
  by_cases hF : F = ⊥
  · have hM0 : M = 0 := Matrix.ext fun i j => by simpa [hF] using hMF i j
    exact ⟨0, Nat.zero_le _, Nat.zero_le _, 1, 1, by simp, by simp, fun i j _ _ => by simp [hM0],
      by simp⟩
  have : FiniteDimensional k F := FiniteDimensional.span_of_finite k (Set.finite_range _)
  have hFE : F ≤ E := Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hM p.1 p.2)
  obtain ⟨x, F₁, -, hx0, hlt, hdec, htr⟩ := DiazModulus.dalag_prop_12_2_split E hii F hFE hF
  choose N hN using fun i j => hdec (M i j) (hMF i j)
  refine DiazModulus.dalag_prop_12_2_step F₁ (fun s' t' D hD => ?_) x hx0 htr M N hN
  have : FiniteDimensional k F₁ := Submodule.finiteDimensional_of_le hlt.le
  refine ih (Module.finrank k F₁) (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hlt) hdim)
    s' t' D (fun i j => hlt.le.trans hFE (hD i j)) ?_
  exact Submodule.finrank_mono (Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hD p.1 p.2))
