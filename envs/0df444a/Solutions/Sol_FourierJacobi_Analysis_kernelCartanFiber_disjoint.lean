-- Prove2me | solution 1 for FourierJacobi.Analysis.kernelCartanFiber_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:48.824295+00:00
-- url     : https://prove2.me/submissions/06288a29-53ae-45da-bb9a-c2b98e84c0c4

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe
attribute [local simp] FourierJacobi.Analysis.coreCentral_zero
attribute [local simp] FourierJacobi.Analysis.coreCentral_one
attribute [local simp] FourierJacobi.Analysis.coreCentral_two

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
theorem _root_.solution {n B m C : ℤ} (h : (n,B) ≠ (m,C)) :
    Disjoint (kernelCartanFiber K n B) (kernelCartanFiber K m C) := by
  rw [Set.disjoint_left]
  intro p hp hq
  exact h (Prod.ext (hp.1.symm.trans hq.1) (hp.2.symm.trans hq.2))
end FourierJacobi.Analysis
