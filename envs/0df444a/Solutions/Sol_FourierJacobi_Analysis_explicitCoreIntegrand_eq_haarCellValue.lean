-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitCoreIntegrand_eq_haarCellValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:46:36.728056+00:00
-- url     : https://prove2.me/submissions/e48d7560-02c3-4793-b045-725d35fd6de8

import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_HaarCellValue
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_haarLatticeCell_kernelCoordinates
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
attribute [local simp] FourierJacobi.Analysis.coreCentral_one
attribute [local simp] FourierJacobi.Analysis.coreCentral_two
attribute [local simp] FourierJacobi.Analysis.coreCentral_zero
attribute [local simp] FourierJacobi.Analysis.coreScaleExponent_coe
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.masterTerm_zero
attribute [local simp] FourierJacobi.Analysis.shellMonomial_zero
attribute [local simp] FourierJacobi.Valuations.actualEntryInteger_coe
attribute [local simp] FourierJacobi.Valuations.actualMinorInteger_coe
attribute [local simp] FourierJacobi.Valuations.localFieldValuation_zero



set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
set_option maxHeartbeats 2000000
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (a b d : ℂ) (T : ℝ)
    (r : ℤ) (z : K) (hz : CentralRepresentative K r z) (i : LatticeIndex)
    (p : HaarPoint K) (hp : p ∈ haarLatticeCell K r z i) :
    explicitCoreIntegrand K q a b d T z p = haarCellValue q a b d T r i := by
  have hk : coreScaleExponent K p.1 = i.1 := by
    apply WithTop.coe_injective
    exact (coreScaleExponent_coe K p.1).trans hp.1
  obtain ⟨_, _, _, hn, hb, _, hH⟩ :=
    haarLatticeCell_kernelCoordinates K r z hz i p hp
  unfold explicitCoreIntegrand coreLocalAbs explicitWeylKernel haarCellValue
  simp only [Function.comp_apply, hk, hn, hb, hH]
end FourierJacobi.Analysis
