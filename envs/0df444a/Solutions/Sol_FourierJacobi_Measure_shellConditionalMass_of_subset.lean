-- Prove2me | solution 1 for FourierJacobi.Measure.shellConditionalMass_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:55:07.645328+00:00
-- url     : https://prove2.me/submissions/0e5c0ae6-3574-4a82-a8fc-b9d967f961d0

import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_real_integerShell


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.shellCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Measure
theorem _root_.solution (n : ℤ) (s : Set K)
    (hs : s ⊆ integerShell K n) :
    shellConditionalMass K n s =
      (additiveHaar K).real s /
        ((1 - (residueCardinality K : ℝ)⁻¹) * (residueCardinality K : ℝ) ^ (-n)) := by
  rw [shellConditionalMass, Set.inter_eq_self_of_subset_left hs, additiveHaar_real_integerShell]
end FourierJacobi.Measure
