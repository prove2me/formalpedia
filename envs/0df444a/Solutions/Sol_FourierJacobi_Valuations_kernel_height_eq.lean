-- Prove2me | solution 1 for FourierJacobi.Valuations.kernel_height_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:15.496833+00:00
-- url     : https://prove2.me/submissions/5abc8ae9-5af1-4e25-960d-b31f357d0a66

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_FourierJacobi_Valuations_KernelIndices

set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Valuations
theorem _root_.solution (p : KernelPoint K) :
    kernelHeight K p = -kernelEntryIndex K p := by
  unfold kernelHeight kernelN kernelB
  ring
end FourierJacobi.Valuations
