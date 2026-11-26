-- Prove2me | solution 1 for FourierJacobi.Valuations.kernel_half_ell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:13.987995+00:00
-- url     : https://prove2.me/submissions/00f4ef2b-6f5c-4816-9fec-adfd58366755

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
theorem _root_.solution (p : KernelPoint K) : kernelEll K p / 2 = kernelN K p := by
  unfold kernelEll
  omega
end FourierJacobi.Valuations
