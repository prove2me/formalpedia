-- Prove2me | solution 1 for DiazModulus.dalag_prop_12_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:18:39.951183+00:00
-- url     : https://prove2.me/submissions/38acbeb6-0cab-47d2-a64f-e66cf9c77064

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_dalag_prop_12_2_ii
import Theorems.Thm_DiazModulus_dalag_prop_12_13_i_ii_span

open Complex ComplexConjugate

/-! # DALAG Prop. 12.2

Let `E` be the `k`-span of the algebraically independent family `b`. Every matrix over a subspace `E` with
property (ii) — whenever `x₁, …, xₙ ∈ E` and `1, x₁, …, xₙ` are `k`-free, the `xᵢ` are algebraically
independent over `k` — can be brought by invertible matrices `P`, `Q` over `k` to the form whose entries with
both indices at least `r` vanish and whose leading `r × r` block has unit determinant. So it suffices to check
(ii) for `E`. If `x₁, …, xₙ ∈ span(b)` and `1, x₁, …, xₙ` are `k`-free, then the `xᵢ` lie in the larger span of
`1` and `b`, and the affine change of variables (Prop. 12.13, (i) ⇒ (ii) in span form) shows that they are
algebraically independent over `k`. No hypothesis on `k` is needed. -/

open DiazModulus in
theorem solution {k K : Type*} [Field k] [Field K] [Algebra k K] {ι : Type*} (b : ι → K)
    (hb : AlgebraicIndependent k b) {s t : ℕ} (M : Matrix (Fin s) (Fin t) K)
    (hM : ∀ i j, M i j ∈ Submodule.span k (Set.range b)) :
    ∃ (r : ℕ) (hrs : r ≤ s) (hrt : r ≤ t) (P : Matrix (Fin s) (Fin s) k)
        (Q : Matrix (Fin t) (Fin t) k), IsUnit P.det ∧ IsUnit Q.det ∧
        (∀ (i : Fin s) (j : Fin t), r ≤ i.val → r ≤ j.val →
          (P.map (algebraMap k K) * M * Q.map (algebraMap k K)) i j = 0) ∧
        IsUnit ((P.map (algebraMap k K) * M * Q.map (algebraMap k K)).submatrix
          (Fin.castLE hrs) (Fin.castLE hrt)).det :=
  DiazModulus.dalag_prop_12_2_ii _ (fun _ x hxE hx => DiazModulus.dalag_prop_12_13_i_ii_span b hb x
    (fun i => Submodule.span_mono (Set.subset_insert _ _) (hxE i)) hx) M hM
