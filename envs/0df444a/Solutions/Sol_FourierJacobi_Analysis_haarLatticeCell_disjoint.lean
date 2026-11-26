-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:05.953795+00:00
-- url     : https://prove2.me/submissions/10ca39b6-c0dd-4422-9b6f-8edbe4408de1

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
theorem _root_.solution (r : ℤ) (z : K) {i i' : LatticeIndex} (hii : i ≠ i') :
    Disjoint (haarLatticeCell K r z i) (haarLatticeCell K r z i') := by
  rcases i with ⟨k,j,h,c⟩
  rcases i' with ⟨k',j',h',c'⟩
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨hk,hj,hh,hc⟩ := hp
  obtain ⟨hk',hj',hh',hc'⟩ := hp'
  have ek : k=k' := WithTop.coe_injective (hk.symm.trans hk')
  have ej : j=j' := WithTop.coe_injective (hj.symm.trans hj')
  have eh : h=h' := WithTop.coe_injective (hh.symm.trans hh')
  subst k' j' h'
  have ec : c=c' := by
    by_cases he : r=0 ∨ 2*h ≠ j-r
    · simp only [he, if_true] at hc hc'
      exact hc.trans hc'.symm
    · simp only [he, if_false] at hc hc'
      exact Int.natCast_inj.mp (WithTop.coe_injective (hc.symm.trans hc'))
  exact hii (by subst c'; rfl)
end FourierJacobi.Analysis
