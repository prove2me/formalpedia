-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_kernelCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:00.996783+00:00
-- url     : https://prove2.me/submissions/a473be96-fb12-4da4-875f-0368f0c303d2

import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Valuations_KernelShells
import Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_one
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_two
import Theorems.Thm_FourierJacobi_Analysis_coreCentral_zero
import Theorems.Thm_FourierJacobi_Analysis_coreScaleExponent_coe
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
import Theorems.Thm_FourierJacobi_Analysis_masterTerm_zero
import Theorems.Thm_FourierJacobi_Analysis_shellMonomial_zero
import Theorems.Thm_FourierJacobi_Valuations_actualEntryInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_actualMinorInteger_coe
import Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_nonzero
import Theorems.Thm_FourierJacobi_Valuations_kernelShellCoordinates_zero
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
set_option maxHeartbeats 1000000
open MeasureTheory Filter ValuativeRel
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
namespace FourierJacobi.Analysis
theorem _root_.solution (r : ℤ) (z : K)
    (hz : CentralRepresentative K r z) (i : LatticeIndex)
    (p : HaarPoint K) (hp : p ∈ haarLatticeCell K r z i) :
    KernelShellCoordinates K (coreAtCentral K z p) r i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  rcases i with ⟨k,j,h,c⟩
  obtain ⟨hk,hj,hh,hc⟩ := hp
  rcases hz with ⟨hr,hz⟩ | ⟨hr,hz⟩
  · subst r z
    have ec : c=0 := by simpa only [true_or, if_true] using hc
    subst c
    exact kernelShellCoordinates_zero K p.1 p.2.1 p.2.2 k j h hk hj hh
  · apply kernelShellCoordinates_nonzero K p.1 p.2.1 p.2.2 z r k j h c hr hk hj hh hz
    intro heq
    simpa only [hr, heq, ne_eq, not_true_eq_false, or_self, if_false] using hc
end FourierJacobi.Analysis
