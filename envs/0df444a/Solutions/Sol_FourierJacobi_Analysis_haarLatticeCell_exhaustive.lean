-- Prove2me | solution 1 for FourierJacobi.Analysis.haarLatticeCell_exhaustive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:11.784504+00:00
-- url     : https://prove2.me/submissions/612c1d7a-966d-4009-855b-0742d62b3dc2

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
import Theorems.Thm_FourierJacobi_Valuations_actual_cancellation_depth_nonnegative
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_zero
import Theorems.Thm_FourierJacobi_Valuations_nonzero_of_integer_valuation
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
theorem _root_.solution (r : ℤ) (z : K) (hz : CentralRepresentative K r z)
    (p : HaarPoint K) (hp : p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧ p.2.2^2-p.2.1*z ≠ 0) :
    ∃ i : LatticeIndex, p ∈ haarLatticeCell K r z i := by
  let k := coreScaleExponent K p.1
  have hk : localFieldValuation K (p.1:K) = (k : WithTop ℤ) :=
    (coreScaleExponent_coe K p.1).symm
  obtain ⟨j,hj⟩ := WithTop.ne_top_iff_exists.mp
    ((localFieldValuation_ne_top K p.2.1).mpr hp.1)
  obtain ⟨h,hh⟩ := WithTop.ne_top_iff_exists.mp
    ((localFieldValuation_ne_top K p.2.2).mpr hp.2.1)
  have hj' := hj.symm
  have hh' := hh.symm
  by_cases he : r=0 ∨ 2*h ≠ j-r
  · refine ⟨(k,j,h,0), hk, hj', hh', ?_⟩
    simp only [he, if_true]
  · have hr : r ≠ 0 := fun hr => he (Or.inl hr)
    have heq : 2*h=j-r := Classical.not_not.mp (fun hh => he (Or.inr hh))
    have hz' : localFieldValuation K z = ((-r : ℤ) : WithTop ℤ) := by
      rcases hz with ⟨hr',_⟩ | ⟨_,hz'⟩
      · exact (hr hr').elim
      · exact hz'
    have hz0 : z ≠ 0 := nonzero_of_integer_valuation _ _ _ hz'
    have hd0 : p.2.2^2/(p.2.1*z)-1 ≠ 0 := by
      intro hed
      apply hp.2.2
      exact sub_eq_zero.mpr ((div_eq_one_iff_eq (mul_ne_zero hp.1 hz0)).mp
        (sub_eq_zero.mp hed))
    obtain ⟨c,hc⟩ := WithTop.ne_top_iff_exists.mp
      ((localFieldValuation_ne_top K _).mpr hd0)
    have hcn := actual_cancellation_depth_nonnegative (localFieldValuation K)
      p.2.1 p.2.2 z r j h c hj' hh' hz' heq hc.symm
    refine ⟨(k,j,h,c.toNat), hk, hj', hh', ?_⟩
    simpa only [he, if_false, Int.toNat_of_nonneg hcn] using hc.symm
end FourierJacobi.Analysis
