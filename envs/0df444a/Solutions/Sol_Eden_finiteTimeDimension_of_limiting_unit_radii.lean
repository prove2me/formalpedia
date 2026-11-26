-- Prove2me | solution 1 for Eden.finiteTimeDimension_of_limiting_unit_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:09:46.542708+00:00
-- url     : https://prove2.me/submissions/9760e90f-de38-4dec-b95f-80c173fc47da

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff
import Theorems.Thm_Eden_limitingSquaredRadius_eq_one_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 1)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 1) :
    finiteTimeDimension c t p = targetDimension c := by
  apply (finiteTimeDimension_eq_target_iff hc ht hp).mpr
  exact ⟨(limitingSquaredRadius_eq_one_iff _).mp h₁,
    (limitingSquaredRadius_eq_one_iff _).mp h₂, hp.2.2⟩
end Eden
