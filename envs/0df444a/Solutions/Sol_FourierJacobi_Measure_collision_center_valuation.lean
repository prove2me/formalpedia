-- Prove2me | solution 1 for FourierJacobi.Measure.collision_center_valuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:32.893551+00:00
-- url     : https://prove2.me/submissions/3e7a8969-31c0-4744-a8e6-6985c371aede

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Measure_JointCollision

set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
open FourierJacobi FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
attribute [local instance] FourierJacobi.Measure.jointCollision_t2Space
namespace FourierJacobi.Measure
theorem _root_.solution (y z : K) (h j s : ℤ)
    (hy : localFieldValuation K y = (h : WithTop ℤ))
    (hz : localFieldValuation K z = (s : WithTop ℤ)) (hlocus : 2 * h = j + s) :
    localFieldValuation K (y ^ 2 / z) = (j : WithTop ℤ) := by
  rw [(localFieldValuation K).map_div, (localFieldValuation K).map_pow, hy, hz, two_nsmul]
  change ((h + h - s : ℤ) : WithTop ℤ) = (j : WithTop ℤ)
  congr 1
  omega
end FourierJacobi.Measure
