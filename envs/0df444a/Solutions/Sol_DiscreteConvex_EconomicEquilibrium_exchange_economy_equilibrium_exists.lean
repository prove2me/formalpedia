-- Prove2me | solution 1 for DiscreteConvex.EconomicEquilibrium.exchange_economy_equilibrium_exists
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:34:54.750722+00:00
-- url     : https://prove2.me/submissions/d91b39a8-4288-481e-a3d9-ab98d556f4ff

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_MNaturalConcave
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_Nondecreasing
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_UDom
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_BoundedSet
import Definitions.Def_DiscreteConvex_EconomicEquilibrium_IsEquilibrium

open DiscreteConvex.EconomicEquilibrium

/-- With no agents (`H = PEmpty`) every hypothesis is vacuous, but the supply-demand balance
`∑_h x_h = x°` forces `x° = 0`; the endowment `x° = 1` therefore admits no equilibrium. -/
theorem solution : ¬ (∀ {H K : Type} [Fintype H] [Fintype K] [DecidableEq K]
    (U : H → (K → ℤ) → WithBot ℝ) (hU : ∀ h, MNaturalConcave (U h))
    (hUnd : ∀ h, Nondecreasing (U h)) (hUb : ∀ h, BoundedSet (UDom (U h)))
    (x0 : K → ℤ) (hx0 : ∀ h, x0 ∈ UDom (U h)),
    ∃ (x : H → (K → ℤ)) (p : K → ℝ),
      IsEquilibrium U (fun l : PEmpty.{1} => l.elim) x0 x (fun l : PEmpty.{1} => l.elim) p) := by
  intro h
  obtain ⟨x, p, hE⟩ := @h PEmpty Unit _ _ _ (fun e => e.elim) (fun e => e.elim)
    (fun e => e.elim) (fun e => e.elim) (fun _ => 1) (fun e => e.elim)
  have hb := congrFun hE.2.2.1 ()
  simp at hb

#print axioms solution

-- sanity check: the negated statement at universe levels 0,0,0 is exactly `solution`'s type
example : ¬ (∀ {H K : Type} [Fintype H] [Fintype K] [DecidableEq K]
    (U : H → (K → ℤ) → WithBot ℝ), (∀ h, MNaturalConcave (U h)) →
    (∀ h, Nondecreasing (U h)) → (∀ h, BoundedSet (UDom (U h))) →
    ∀ (x0 : K → ℤ), (∀ h, x0 ∈ UDom (U h)) →
    ∃ (x : H → (K → ℤ)) (p : K → ℝ),
      IsEquilibrium U (fun l : PEmpty.{1} => l.elim) x0 x (fun l : PEmpty.{1} => l.elim) p) :=
  solution
