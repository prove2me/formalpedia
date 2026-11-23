-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.uNormBound_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.808038+00:00
-- url     : https://prove2.me/submissions/dbcc0cba-ac89-476c-95d4-3d5a053cd4c0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_finite_cosets
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_out_sub_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution : UNormBound := by
  intro hU hP hC hM _ K _ _ _ R ψ hD m n₀ F Θ hF hA t cr hcr
  classical
  obtain ⟨h1, h2, ⟨L, _, hLc, hL0⟩, h4, h5, _, _⟩ := hA
  have hfin := finite_cosets R.toAddSubgroup hD.isOpen (L : Set K) hLc
  set x₀ : K ⧸ R.toAddSubgroup := ((t : K) : K ⧸ R.toAddSubgroup) with hx₀
  set T := insert x₀ hfin.toFinset with hTdef
  have hsum : ∀ h ∈ F, ∀ h' ∈ F, ∑ᶠ x : K ⧸ R.toAddSubgroup, Θ (Quotient.out x) h h' =
      Θ (t : K) h h' + ∑ x ∈ T.erase x₀, Θ (Quotient.out x) h h' := by
    intro h hh h' hh'
    rw [finsum_eq_sum_of_support_subset (s := T)]
    · rw [← Finset.add_sum_erase T _ (Finset.mem_insert_self x₀ _)]
      congr 1
      have hr := out_sub_mem R.toAddSubgroup (t : K)
      have := h1 (t : K) _ hr
      rw [add_sub_cancel] at this
      rw [this]
    · intro x hx
      by_contra hxT
      apply hx
      apply hL0 _ _ h hh h' hh'
      intro hxL
      apply hxT
      rw [hTdef]
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Set.Finite.mem_toFinset]
      exact Or.inr hxL
  have key := psd_scale (fun h : Point K => cSize R h)
    (psd_add (psd_add h5 (psd_sum (T.erase x₀) (fun x => Θ (Quotient.out x)) fun x _ => h2 _)) (h4 t))
  refine psd_congr ?_ key
  intro h hh h' hh'
  rw [hU hP hC hM K R ψ hD m h h' t t cr ((hF h hh).trans (hF h' hh').symm) hcr, hsum h hh h' hh']
  push_cast
  ring
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
