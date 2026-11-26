-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:17.125227+00:00
-- url     : https://prove2.me/submissions/ac360938-daa2-42a1-9a29-8f53cd52a110

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
import Theorems.Thm_FourierJacobi_Valuations_kernel_localFieldValuation_measurable
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
variable [MeasurableSpace K] [BorelSpace K]
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_9fc63f53e5_126
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_9fc63f53e5_127
namespace FourierJacobi.Analysis
theorem _root_.solution (r : ℤ) (z : K) (i : LatticeIndex) :
    MeasurableSet (haarLatticeCell K r z i) := by
  have hv := kernel_localFieldValuation_measurable K
  have ha : Measurable (fun p : HaarPoint K => (p.1:K)) :=
    (show Measurable (fun a : Kˣ => (a:K)) from MeasurableSpace.le_map_comap).comp
      measurable_fst
  have hx : Measurable (fun p : HaarPoint K => p.2.1) := measurable_snd.fst
  have hy : Measurable (fun p : HaarPoint K => p.2.2) := measurable_snd.snd
  have hk := (measurableSet_singleton (i.1 : WithTop ℤ)).preimage (hv.comp ha)
  have hj := (measurableSet_singleton (i.2.1 : WithTop ℤ)).preimage (hv.comp hx)
  have hh := (measurableSet_singleton (i.2.2.1 : WithTop ℤ)).preimage (hv.comp hy)
  have hc : MeasurableSet {p : HaarPoint K |
      if r=0 ∨ 2*i.2.2.1 ≠ i.2.1-r then i.2.2.2=0
      else localFieldValuation K (p.2.2^2/(p.2.1*z)-1) =
        ((i.2.2.2:ℤ) : WithTop ℤ)} := by
    split_ifs
    · by_cases hc : i.2.2.2=0 <;> simp only [hc, Set.ofPred_true, Set.ofPred_false,
        MeasurableSet.univ, MeasurableSet.empty]
    · exact (measurableSet_singleton ((i.2.2.2:ℤ) : WithTop ℤ)).preimage
        (hv.comp (((hy.pow_const 2).div (hx.mul_const z)).sub_const 1))
  exact hk.inter (hj.inter (hh.inter hc))
end FourierJacobi.Analysis
