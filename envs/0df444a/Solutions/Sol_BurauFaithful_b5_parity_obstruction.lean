-- Prove2me | solution 1 for BurauFaithful.b5_parity_obstruction
-- status  : ACCEPTED   (disprove)
-- author  : @lt9
-- created : 2026-09-30T12:28:33.226505+00:00
-- url     : https://prove2.me/submissions/dfdc9e79-8f3e-429f-ae4b-723df8973c9e

/-
Counterexample refuting the platform statement as formalized:

```lean
theorem b5_parity_obstruction (K4 : Subgroup (ArtinBraidGroup 4))
    (gamma1 : ArtinBraidGroup 4) (hgamma1 : gamma1 ∈ K4)
    (Phi Phi' : ArtinBraidGroup 4)
    (hPhi' : Phi' ∈ K4) (hPhi : Phi ∈ K4) (hprod : Phi = Phi' * gamma1) :
    burauRep 4 Phi ≠ 1
```

`K4` is an *arbitrary* subgroup and `gamma1` an *arbitrary* element of it, so the theorem asserts in
particular that `burauRep 4 1 ≠ 1`: take `K4 = ⊤`, `gamma1 = 1`, `Phi = Phi' = 1` (all hypotheses hold,
`hprod` being `1 = 1 * 1`), but `burauRep 4 1 = 1` because `burauRep 4` is a monoid homomorphism.

In the source (BBB, Proposition 6.4/Corollary 6.5) `K4` is the *point-pushing* subgroup and `gamma1`
the specific push-map of Figure 6.3; the formal statement omits those hypotheses. Hence the statement
as published is not provable, and this file proves its negation.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem solution :
    ¬ (∀ (K4 : Subgroup (BraidsLinksMCG.ArtinBraidGroup 4))
        (gamma1 : BraidsLinksMCG.ArtinBraidGroup 4), gamma1 ∈ K4 →
        ∀ (Phi Phi' : BraidsLinksMCG.ArtinBraidGroup 4), Phi' ∈ K4 → Phi ∈ K4 →
          Phi = Phi' * gamma1 → BurauFaithful.burauRep 4 Phi ≠ 1) := by
  intro h
  exact (h ⊤ 1 (Subgroup.mem_top 1) 1 1 (Subgroup.mem_top 1) (Subgroup.mem_top 1) (by simp))
    (map_one _)
