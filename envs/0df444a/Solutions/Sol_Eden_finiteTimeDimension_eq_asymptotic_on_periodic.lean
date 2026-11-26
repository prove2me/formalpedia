-- Prove2me | solution 1 for Eden.finiteTimeDimension_eq_asymptotic_on_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:21.290753+00:00
-- url     : https://prove2.me/submissions/684d3da9-d577-49c6-84c7-8917792f34f0

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions
import Theorems.Thm_Eden_normalizedLogSingularValues_eq_lyapunovExponent_of_stationary
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_periodicEquilibriumSet_eq_positiveReturnSet
import Theorems.Thm_Eden_stationary_radii_of_evolution_return


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ periodicEquilibriumSet c) :
    finiteTimeDimension c t p = asymptoticDimension c p := by
  rw [periodicEquilibriumSet_eq_positiveReturnSet hc] at hp
  obtain ⟨u, hu, hret⟩ := hp
  have hs := stationary_radii_of_evolution_return c hu hret
  rw [finiteTimeDimension_eq_kaplanYorke c ht p,
    normalizedLogSingularValues_eq_lyapunovExponent_of_stationary c ht p hs.1 hs.2]
  rfl
end Eden
