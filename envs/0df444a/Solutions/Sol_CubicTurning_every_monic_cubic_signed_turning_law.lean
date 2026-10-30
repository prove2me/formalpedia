-- Prove2me | solution 1 for CubicTurning.every_monic_cubic_signed_turning_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:44:50.15167+00:00
-- url     : https://prove2.me/submissions/77c60984-ba88-42d1-8289-b7043f535d5c

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_energy_eq_halfAngleEnergy
import Theorems.Thm_CubicTurning_every_monic_cubic_uniform_forward_law
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning























































































theorem uniform_terminal_marginal {a b c u : ℂ} (L : AffineUniformForwardLaw a b c u)
    (f : ℂ → ℝ) :
    (∑ i : Fin 3, f (L.paths i 2))/3=(f a+f b+f c)/3 := by
  simp only [L.endpoint]
  simp [Fin.sum_univ_succ]
  ring






















end CubicTurning


set_option autoImplicit false
open scoped BigOperators
namespace CubicTurning

theorem meanEnergy_eq_half_angle {a b c u : ℂ} (L : AffineUniformForwardLaw a b c u) :
    L.meanEnergy=(∑ i,halfAngleEnergy (L.axes i)
      (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1))/3 := by
  unfold AffineUniformForwardLaw.meanEnergy
  congr 1
  exact Finset.sum_congr rfl (fun i _ => energy_eq_halfAngleEnergy _ _ _ (L.forward i))

theorem uniform_law_balanced {a b c : ℂ}
    (L : AffineUniformForwardLaw a b c (centroid a b c)) :
    (∑ i, (1/3:ℂ)*(L.paths i 2-centroid a b c))=0 := by
  simp only [L.endpoint]
  simp [Fin.sum_univ_succ,centroid]
  ring




end CubicTurning

open CubicTurning in
theorem solution (p : Polynomial ℂ)
    (hp : p.Monic) (hd : p.natDegree=3) :
    ∃ a b c : ℂ, p=DerivativeChainPrivate.fromRoots (![a,b,c] : Fin 3 → ℂ) ∧
      ∃ L : AffineUniformForwardLaw a b c (centroid a b c),
        (∀ i j : Fin 3, ((Polynomial.derivative^[3-(j.val+1)]) p).eval (L.paths i j)=0) ∧
        (∀ f : ℂ → ℝ, (∑ i,f (L.paths i 2))/3=(f a+f b+f c)/3) ∧
        (∑ i,(1/3:ℂ)*(L.paths i 2-centroid a b c))=0 ∧
        (∑ i,halfAngleEnergy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1))/3 ≤
          (anisotropy a b c+Real.sqrt (anisotropy a b c*(2*centeredVariance a b c-anisotropy a b c)))/3 ∧
        (∑ i,halfAngleEnergy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1))/3 ≤
          (2/3)*centeredVariance a b c := by
  obtain ⟨a,b,c,hpoly,L,hactual,haniso,hbound⟩ := every_monic_cubic_uniform_forward_law p hp hd
  refine ⟨a,b,c,hpoly,L,hactual,uniform_terminal_marginal L,uniform_law_balanced L,?_,?_⟩
  · rwa [←meanEnergy_eq_half_angle L]
  · rwa [←meanEnergy_eq_half_angle L]
