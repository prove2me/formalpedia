-- Prove2me | solution 1 for FourierJacobi.Measure.additiveHaar_prod_jointCollisionDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:48:06.928441+00:00
-- url     : https://prove2.me/submissions/0f2375e5-9ec6-4380-94a0-281b6f663e5b

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision
import Theorems.Thm_FourierJacobi_Measure_collision_center_valuation
import Theorems.Thm_FourierJacobi_Measure_jointCollisionDepth_section
import Theorems.Thm_FourierJacobi_Measure_additiveHaar_shellCollisionDepth
import Theorems.Thm_FourierJacobi_Measure_jointCollisionDepth_measurableSet
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
theorem _root_.solution (z : K) (j h s : ℤ) (c : ℕ)
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    ((additiveHaar K).prod (additiveHaar K)) (jointCollisionDepth K z j h s c) =
      ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j)) * additiveHaar K (integerShell K h) := by
  rw [Measure.prod_apply (jointCollisionDepth_measurableSet K z j h s c)]
  have he : (fun y => additiveHaar K (Prod.mk y ⁻¹' jointCollisionDepth K z j h s c)) =
      (integerShell K h).indicator (fun _ => ENNReal.ofReal (shellCollisionProbability K c *
        (additiveHaar K).real (integerShell K j))) := by
    funext y
    rw [jointCollisionDepth_section K y z j h s c hz]
    by_cases hy : localFieldValuation K y = (h : WithTop ℤ)
    · rw [if_pos hy, Set.indicator_of_mem (show y ∈ integerShell K h from hy),
        additiveHaar_shellCollisionDepth K (y ^ 2 / z) j c
          (collision_center_valuation K y z h j s hy hz hlocus)]
    · rw [if_neg hy, Set.indicator_of_notMem (show y ∉ integerShell K h from hy), measure_empty]
  rw [he, lintegral_indicator_const (integerShell_measurableSet K h)]
end FourierJacobi.Measure
