-- Prove2me | solution 1 for DiazModulus.dalag_conclusion_12_1_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:31.732565+00:00
-- url     : https://prove2.me/submissions/706fb425-6a5c-4186-8016-1893425626d4

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_2_ii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_iii_ii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_iv_iii

open Complex ComplexConjugate

/-! # DALAG §12.1.6: rank equal to structural rank gives Property (A B; C 0)

Let `E` be a `k`-subspace of `K` containing `1`, and suppose every matrix with entries in `E` has rank equal to
its structural rank over `k` (property (iv) of Prop. 12.13, in presentation form). By the implication
(iv) ⇒ (iii) of Prop. 12.13, no non-zero homogeneous polynomial over `k` vanishes at a `k`-free family of
elements of `E`; by (iii) ⇒ (ii) (homogenisation with `x₀ = 1`, which uses `1 ∈ E`), every family `x` in `E`
with `1, x` linearly independent over `k` is algebraically independent over `k`. The first proof of Prop. 12.2,
which works for any subspace with this property, then puts every matrix `M` over `E` in the block form
`P M Q = (A B; C 0)` with `P`, `Q` invertible over `k` and `A` a regular square matrix. The hypothesis `M ≠ 0`
is not needed. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] (E : Submodule k K)
    (h1 : (1 : K) ∈ E)
    (hiv : ∀ (s t m : ℕ) (M : Matrix (Fin s) (Fin t) K) (e : Fin m → K)
      (N : Fin m → Matrix (Fin s) (Fin t) k), LinearIndependent k e → (∀ j, e j ∈ E) →
      M = ∑ j, e j • (N j).map (algebraMap k K) →
      M.rank = (∑ j, (algebraMap (MvPolynomial (Fin m) k) (FractionRing (MvPolynomial (Fin m) k))
        (MvPolynomial.X j)) • (N j).map (algebraMap k (FractionRing (MvPolynomial (Fin m) k)))).rank) :
    ∀ (s t : ℕ) (M : Matrix (Fin s) (Fin t) K), (∀ i j, M i j ∈ E) → M ≠ 0 →
      ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det := by
  intro _ _ M hM _
  exact DiazModulus.dalag_prop_12_2_ii E (fun _ x hxE hx => DiazModulus.dalag_prop_12_13_iii_ii E h1
    (fun _ _ y hy hyE P hP hP0 => DiazModulus.dalag_prop_12_13_iv_iii E hiv y hy hyE P hP hP0)
    x hxE hx) M hM
