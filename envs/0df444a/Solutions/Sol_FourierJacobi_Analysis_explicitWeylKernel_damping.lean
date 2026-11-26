-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitWeylKernel_damping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:49.725806+00:00
-- url     : https://prove2.me/submissions/ebdfffd3-e4e9-48a4-a774-f8c060bf78f8

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Theorems.Thm_FourierJacobi_Analysis_weylKernelAtIndices_damping

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (t a b T : ℂ) (p : KernelPoint K) (hT : T ≠ 0) :
    T ^ (kernelHeight K p) * explicitWeylKernel K t a b p =
      (poincare t)⁻¹ * ∑ i : Fin 8,
        weylWeights t a b i * t ^ (6 * kernelN K p + 4 * kernelB K p) *
          (T * weylU a b i) ^ (kernelN K p) *
            (T * weylV a b i) ^ (kernelB K p) :=
  weylKernelAtIndices_damping t a b T (kernelN K p) (kernelB K p) hT
end FourierJacobi.Analysis
