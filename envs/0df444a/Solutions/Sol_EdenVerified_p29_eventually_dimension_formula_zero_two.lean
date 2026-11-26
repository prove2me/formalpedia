-- Prove2me | solution 1 for EdenVerified.p29_eventually_dimension_formula_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:21:13.555255+00:00
-- url     : https://prove2.me/submissions/597f88b4-9570-49ac-9591-c7827a64e9dd

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_eventually_dimension_formula_zero_two


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
    (hpair : (limitingSquaredRadius (radiusSq₁ p) = 0 ∧
        limitingSquaredRadius (radiusSq₂ p) = 2) ∨
      (limitingSquaredRadius (radiusSq₁ p) = 2 ∧
        limitingSquaredRadius (radiusSq₂ p) = 0)),
    ∀ᶠ t in atTop, 0 ≤ normalizedLogSingularValues c t p 0 ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) 2 < 0 ∧
      normalizedLogSingularValues c t p 1 < 0 ∧
      finiteTimeDimension c t p = 1 +
        spectrumPartialSum (normalizedLogSingularValues c t p) 1 /
          -normalizedLogSingularValues c t p 1 :=
  @Eden.eventually_dimension_formula_zero_two
end EdenVerified
