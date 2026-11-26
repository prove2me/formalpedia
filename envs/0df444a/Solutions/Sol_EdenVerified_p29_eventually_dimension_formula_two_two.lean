-- Prove2me | solution 1 for EdenVerified.p29_eventually_dimension_formula_two_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:21:29.731799+00:00
-- url     : https://prove2.me/submissions/3dcdf5dc-f62c-47e4-b708-a2e51a090a7d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_eventually_dimension_formula_two_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ attractor)
    (h₁ : limitingSquaredRadius (radiusSq₁ p) = 2)
    (h₂ : limitingSquaredRadius (radiusSq₂ p) = 2),
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < 2 → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 3 < 0 ∧
      normalizedLogSingularValues c t p 2 < 0 ∧
      finiteTimeDimension c t p = 2 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 2 /
          -normalizedLogSingularValues c t p 2 :=
  @Eden.eventually_dimension_formula_two_two
end EdenVerified
