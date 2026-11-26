-- Prove2me | solution 1 for FourierJacobi.Analysis.kernelCartanFiber_empty_of_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:13.714328+00:00
-- url     : https://prove2.me/submissions/b39b3b62-470a-4759-aa01-1ec5981a9b10

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Valuations_kernel_indices_nonnegative


set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_d9a05d5624_103
omit [MeasurableSpace K] [BorelSpace K]
namespace FourierJacobi.Analysis
theorem _root_.solution {n B : ℤ} (h : n < 0 ∨ B < 0) :
    kernelCartanFiber K n B = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hn := kernel_indices_nonnegative K p
  change kernelN K p = n ∧ kernelB K p = B at hp
  omega
end FourierJacobi.Analysis
