-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.cutPSD_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:50.414733+00:00
-- url     : https://prove2.me/submissions/99f99024-0c21-45fb-970b-53ad8861aa3e

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_psd_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveSemidefiniteClosure_uGram_eq_sum
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_psd_comap
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
theorem _root_.solution : CutPSD := by
  intro hG hP hM K _ _ _ R ψ hD m cr S F hcr hsz
  classical

  have hfin : (⋃ p ∈ F, ⋃ p' ∈ F, Function.support (fun x =>
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)))).Finite := by
    refine Set.Finite.biUnion F.finite_toSet fun p hp => Set.Finite.biUnion F.finite_toSet
      fun p' hp' => ?_
    have hs : (addBlock p.1 m p.2).1.sum = (addBlock p'.1 m p'.2).1.sum := by
      simp [addBlock, hsz p hp p' hp']
    have := (hP K R ψ hD (addBlock p.1 m p.2) (addBlock p'.1 m p'.2) hs cr hcr).1
    refine this.subset ?_
    intro x hx
    simpa [Ns, pt2] using hx
  set T := hfin.toFinset with hTdef
  have hT : ∀ p ∈ F, ∀ p' ∈ F, ∀ x, x ∉ T →
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x)) = 0 := by
    intro p hp p' hp' x hx
    by_contra hne
    apply hx
    rw [hTdef, Set.Finite.mem_toFinset]
    simp only [Set.mem_iUnion]
    exact ⟨p, hp, p', hp', hne⟩
  have hk : ∀ x, IsPSD F (fun p p' : Point K × Kˣ =>
      Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x))) := fun x =>
    A5x6.psd_comap (Kp R ψ) (fun p : Point K × Kˣ => pt2 p.1 m p.2 (cr x)) F (hG K R ψ hD _)
  have hgen : ∀ T' : Finset (K ⧸ R.toAddSubgroup), IsPSD F (fun p p' : Point K × Kˣ =>
      ((modK R (p.2 : K) ^ (m * (m + 1) / 2) * modK R (p'.2 : K) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
        ∑ x ∈ T', Kp R ψ (pt2 p.1 m p.2 (cr x)) (pt2 p'.1 m p'.2 (cr x))) := fun T' =>
    psd_scale (fun p : Point K × Kˣ => modK R (p.2 : K) ^ (m * (m + 1) / 2))
      (psd_sum T' _ fun x _ => hk x)
  constructor
  · refine psd_congr ?_ (hgen (T.filter fun x => (cr x : K) ∈ S))
    intro p hp p' hp'
    rw [uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'), (hM K R ψ hD p.2 p'.2).2,
      mul_pow]
  · refine psd_congr ?_ (hgen (T.filter fun x => ¬ (cr x : K) ∈ S))
    intro p hp p' hp'
    rw [uGram_eq_sum R ψ m cr S p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'),
      uGram_eq_sum R ψ m cr Set.univ p.1 p'.1 p.2 p'.2 T (hT p hp p' hp'),
      (hM K R ψ hD p.2 p'.2).2, mul_pow, ← mul_sub]
    congr 1
    simp only [Set.mem_univ, Finset.filter_true]
    rw [← Finset.sum_filter_add_sum_filter_not T (fun x => (cr x : K) ∈ S)]
    ring
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
