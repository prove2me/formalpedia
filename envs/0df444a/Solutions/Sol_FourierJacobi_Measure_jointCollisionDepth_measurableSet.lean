-- Prove2me | solution 1 for FourierJacobi.Measure.jointCollisionDepth_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:03.646312+00:00
-- url     : https://prove2.me/submissions/23f94637-add9-46eb-8e26-83a9648d4123

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_integerShell_measurableSet


set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.jointCollision_t2Space
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Measure.jointCollision_secondCountable
attribute [local instance] FourierJacobi.Measure.jointCollision_additiveHaar_sigmaFinite
namespace FourierJacobi.Measure
theorem _root_.solution (z : K) (j h s : ℤ) (c : ℕ) :
    MeasurableSet (jointCollisionDepth K z j h s c) := by
  have h1 := (integerShell_measurableSet K h).preimage
    (show Measurable (fun p : K × K => p.1) from measurable_fst)
  have h2 := (integerShell_measurableSet K j).preimage
    (show Measurable (fun p : K × K => p.2) from measurable_snd)
  have h3 := (integerShell_measurableSet K (j + s + (c : ℤ))).preimage
    (show Measurable (fun p : K × K => p.1 ^ 2 - p.2 * z) by fun_prop)
  exact h1.inter (h2.inter h3)
end FourierJacobi.Measure
