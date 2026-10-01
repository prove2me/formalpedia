-- Prove2me | solution 2 for BurauFaithful.burau_three_spec_kernel
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T12:51:17.055996+00:00
-- url     : https://prove2.me/submissions/0917f8a8-7bc5-4d9e-be94-37cf0584f1df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Decomposition of the mission node `BurauFaithful.burau_three_spec_kernel`:

```lean
spec(ρ₃ β) = 1 ↔ ∃ k : ℤ, β = (σ₀σ₁)^(6k)
```

* `(⟹)` is exactly the Open child `BurauFaithful.burau_three_spec_kernel_hard` (a braid killed by
  the specialization is a power of the full twist) — imported here, hence a decomposition child;
* `(⟸)` is the **Proved** node `BurauFaithful.burau_three_spec_twist_zpow`, which says that every
  power `(σ₀σ₁)^(6k)` is killed by the specialization.

Both are already mission nodes, so this reduces the iff to its honest remaining gap (the child
`BurauFaithful.spec_reduced_kernel_normalClosure`, i.e. the Coxeter–Moser injectivity, which the
finer decomposition of the hard node attaches below it).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_burau_three_spec_kernel_hard
import Theorems.Thm_BurauFaithful_burau_three_spec_twist_zpow

set_option autoImplicit false

theorem solution (β : BraidsLinksMCG.ArtinBraidGroup 3) :
    Matrix.GeneralLinearGroup.map (LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ))
        (BurauFaithful.burauRep 3 β) = 1 ↔
      ∃ k : ℤ, β = (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩) ^ (6 * k) := by
  constructor
  · exact BurauFaithful.burau_three_spec_kernel_hard β
  · rintro ⟨k, rfl⟩
    exact BurauFaithful.burau_three_spec_twist_zpow k
