-- Prove2me | solution 1 for Eden.singularValues_evolution_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:20.990268+00:00
-- url     : https://prove2.me/submissions/a7302dc4-2b7f-4e5a-ae4a-4ee4c9819d83

import Definitions.Def_Eden_ExteriorCocycle
import Definitions.Def_Eden_FactorBounds
import Definitions.Def_Eden_IntegerGrowthBounds
import Theorems.Thm_Eden_derivativeFactors_upper_bound
import Theorems.Thm_Eden_derivativeFactors_ge_fifth
import Theorems.Thm_Eden_exists_equiv_of_multiset_eq
import Theorems.Thm_Eden_singularValues_fderiv_evolution


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ attractor) (i : Fin 5) :
    Real.exp (-c * t) ≤ (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i ∧
      (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i ≤ Real.exp (3 * t) := by
  obtain ⟨e, he⟩ := exists_equiv_of_multiset_eq (singularValues_fderiv_evolution c ht p)
  rw [← he i]
  exact ⟨derivativeFactors_ge_fifth hc ht hp (e i),
    derivativeFactors_upper_bound (by linarith) ht p (e i)⟩
end Eden
