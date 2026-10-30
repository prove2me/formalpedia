-- Prove2me | solution 1 for CubicTurning.every_monic_cubic_uniform_forward_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:42:50.156057+00:00
-- url     : https://prove2.me/submissions/2d62385e-388c-4438-a140-51dfd1186992

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_every_cubic_uniform_forward_law
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


open CubicTurning in
theorem solution (p : Polynomial ℂ)
    (hp : p.Monic) (hd : p.natDegree=3) :
    ∃ a b c : ℂ, p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) ∧
      ∃ L : AffineUniformForwardLaw a b c (centroid a b c),
        (∀ i j : Fin 3, ((Polynomial.derivative^[3-(j.val+1)]) p).eval (L.paths i j)=0) ∧
        L.meanEnergy ≤ (anisotropy a b c +
          Real.sqrt (anisotropy a b c*(2*centeredVariance a b c-anisotropy a b c)))/3 ∧
        L.meanEnergy ≤ (2/3)*centeredVariance a b c := by
  have hcard : p.roots.card=3 := by
    rw [←(IsAlgClosed.splits p).natDegree_eq_card_roots,hd]
  obtain ⟨a,b,c,hroots⟩ := Multiset.card_eq_three.mp hcard
  have hpoly : p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) := by
    rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp,hroots]
    simp [DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ]
  obtain ⟨L,h₀,h₁⟩ := every_cubic_uniform_forward_law a b c
  refine ⟨a,b,c,hpoly,L,?_,h₀,h₁⟩
  intro i j
  rw [hpoly]
  exact L.actual i j
