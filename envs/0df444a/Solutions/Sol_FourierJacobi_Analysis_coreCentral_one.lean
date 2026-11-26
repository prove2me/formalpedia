-- Prove2me | solution 1 for FourierJacobi.Analysis.coreCentral_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:49.193396+00:00
-- url     : https://prove2.me/submissions/0add5d28-4798-48a7-9e0b-1826a4c7addb

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero


attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe
attribute [local simp] FourierJacobi.Analysis.coreCentral_zero

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (π : Kˣ) : coreCentral K π 1 = (π : K)⁻¹ := by
  simp [coreCentral]
end FourierJacobi.Analysis
