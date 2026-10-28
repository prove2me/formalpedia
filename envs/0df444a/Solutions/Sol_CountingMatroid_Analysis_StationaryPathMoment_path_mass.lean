-- Prove2me | solution 1 for CountingMatroid.Analysis.StationaryPathMoment.path_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:12:58.152573+00:00
-- url     : https://prove2.me/submissions/890e57a7-ecc6-4822-ac9b-8d0382b1b70e

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Definitions.Def_CountingMatroid_Analysis_StationaryPathMoment
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF

namespace Arlib
end Arlib
section


set_option autoImplicit false

/-!
Finite product-path expectations and moments. The last transition is unused
by the observations, matching the stationary observation experiment.
-/
namespace CountingMatroid.Analysis.StationaryPathMoment

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω]





/-- INTERNAL: Split a finite path sum at its first vertex. -/
theorem sum_paths_cons (N : ℕ) (F : (Fin (N + 2) → Ω) → ℝ) :
    (∑ path, F path) = ∑ x : Ω, ∑ path : Fin (N + 1) → Ω, F (Fin.cons x path) := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 2) => Ω)) F]
  exact Fintype.sum_prod_type _

/-- INTERNAL: Splitting off the first transition factors the product weight. -/
theorem path_weight_cons (P : FinChain Ω) (N : ℕ) (x : Ω)
    (path : Fin (N + 1) → Ω) :
    pathWeight P (N + 1) (Fin.cons x path) = P x (path 0) * pathWeight P N path := by
  classical
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
    ← Fin.succ_castSucc]















end CountingMatroid.Analysis.StationaryPathMoment

end
set_option autoImplicit false

/-!
Finite product-path expectations and moments. The last transition is unused
by the observations, matching the stationary observation experiment.
-/
namespace CountingMatroid.Analysis.StationaryPathMoment
end CountingMatroid.Analysis.StationaryPathMoment
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.StationaryPathMoment

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω]

/-- INTERNAL: Summing the product-path law against its initial weight
preserves the total mass, for arbitrary real initial weights. -/
theorem solution (P : FinChain Ω) (N : ℕ) (w : Ω → ℝ) :
    (∑ path : Fin (N + 1) → Ω, w (path 0) * pathWeight P N path) = ∑ x, w x := by
  classical
  induction N generalizing w with
  | zero =>
    simp only [pathWeight, Fin.prod_univ_zero, mul_one]
    exact Equiv.sum_comp (Equiv.funUnique (Fin 1) Ω) w
  | succ N ih =>
    rw [sum_paths_cons N]
    simp only [Fin.cons_zero, path_weight_cons, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [ih (fun y => ∑ x, w x * P x y)]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, P.sum_coe, mul_one]
