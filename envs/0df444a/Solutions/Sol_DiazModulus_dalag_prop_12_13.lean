-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_13
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:37.233065+00:00
-- url     : https://prove2.me/submissions/2419c7d9-dceb-44e6-b3bb-ae8a8b9fb034

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_13_i_ii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_ii_iv
import Theorems.Thm_DiazModulus_dalag_prop_12_13_iv_iii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_iii_ii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_ii_i

open Complex ComplexConjugate

/-! # DALAG Prop. 12.13

Let `E` be a `k`-subspace of `K` containing `1`. The four properties are (i) `E` has a basis containing `1` whose
other members are algebraically independent over `k`; (ii) every family `x` in `E` with `1, x` linearly
independent over `k` is algebraically independent over `k`; (iii) no non-zero homogeneous polynomial over `k`
vanishes at a `k`-free family of elements of `E`; (iv) every matrix `M = Σ eⱼ Nⱼ`, with `e` a `k`-free family in
`E` and the `Nⱼ` over `k`, has rank equal to its structural rank (the rank of `Σ Xⱼ Nⱼ` over `k(X)`). The
equivalence is proved along the cycle (i) ⇒ (ii) ⇒ (iv) ⇒ (iii) ⇒ (ii) ⇒ (i). (i) ⇒ (ii) is an affine change of
variables; (ii) ⇒ (iv) is Lemma 12.9; (iv) ⇒ (iii) writes the dehomogenised polynomial as a determinant
`det(N₀ + Σ Xᵢ Nᵢ)` (Prop. 12.10) and compares the rank of `Σ xⱼ Nⱼ` with its structural rank; (iii) ⇒ (ii) is homogenisation with `x₀ = 1`; (ii) ⇒ (i) extends `1` to a basis of `E`
and checks algebraic independence on finite subfamilies. -/

universe u v

open DiazModulus in
theorem solution {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    (E : Submodule k K) (h1 : (1 : K) ∈ E) :
    List.TFAE
      [∃ (ι : Type v) (b : Module.Basis ι k ↥E) (i₀ : ι),
          (b i₀ : K) = 1 ∧ AlgebraicIndependent k (fun i : {i : ι // i ≠ i₀} => (b i : K)),
        ∀ (n : ℕ) (x : Fin n → K), (∀ i, x i ∈ E) →
          LinearIndependent k (Fin.cons (1 : K) x : Fin (n + 1) → K) → AlgebraicIndependent k x,
        ∀ (n D : ℕ) (x : Fin (n + 1) → K), LinearIndependent k x → (∀ i, x i ∈ E) →
          ∀ P : MvPolynomial (Fin (n + 1)) k, P.IsHomogeneous D → P ≠ 0 →
            MvPolynomial.aeval x P ≠ 0,
        ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
          (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e → (∀ j, e j ∈ E) →
          M = ∑ j, e j • (N j).map (algebraMap k K) →
          M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k)
            (FractionRing (MvPolynomial (Fin m) k)) (MvPolynomial.X j)) •
              (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank] := by
  tfae_have 1 → 2 := fun ⟨_, b, i₀, hb₀, hb⟩ _ x hxE hx =>
    DiazModulus.dalag_prop_12_13_i_ii E b i₀ hb₀ hb x hxE hx
  tfae_have 2 → 4 := fun hii _ _ _ M e N he heE hM =>
    DiazModulus.dalag_prop_12_13_ii_iv E h1 hii M e N he heE hM
  tfae_have 4 → 3 := fun hiv _ _ x hx hxE P hP hP0 =>
    DiazModulus.dalag_prop_12_13_iv_iii E hiv x hx hxE P hP hP0
  tfae_have 3 → 2 := fun hiii _ x hxE hx => DiazModulus.dalag_prop_12_13_iii_ii E h1 hiii x hxE hx
  tfae_have 2 → 1 := fun hii => DiazModulus.dalag_prop_12_13_ii_i E h1 hii
  tfae_finish
