-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.EtaleCoordinates.derivIdealIterate_le_iSup_logDerivIdealIterate_partialDerivIdealIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:38:36.48678+00:00
-- url     : https://prove2.me/submissions/21702d24-ae2e-4392-a739-b50eb9cfe930

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtMultiplicativity
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PartialDerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_mul_partialDeriv_mem_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_mem_logDerivIdeal_of_ne
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_le_partialDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_mem_partialDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDerivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_derivation_apply_eq_sum_partialDeriv
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_partialDeriv_comm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_coordBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_inducedBasis_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_JacobianCriterion_tensorKaehlerBasis_mapBaseChange
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_iSup_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivation_apply_mem_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_logDerivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_tangentDerivations_span_singleton
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.coordBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.inducedBasis_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.JacobianCriterion.tensorKaehlerBasis_mapBaseChange
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply


section
namespace FunctorialResolution.EmbeddedResolution
namespace EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
private theorem derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal [Fintype ι] (h : ι) (I : Ideal S) :
    derivIdeal k I ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ⊔ partialDerivIdeal k ι S h I := by
  rw [derivIdeal_le_iff]
  refine ⟨(le_logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I).trans le_sup_left, ?_⟩
  intro D g hg
  rw [derivation_apply_eq_sum_partialDeriv k ι S D g]
  refine Ideal.sum_mem _ ?_
  intro i _
  by_cases hi : i = h
  · rw [hi]
    exact Submodule.mem_sup_right
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg))
  · exact Submodule.mem_sup_left
      (Ideal.mul_mem_left _ _ (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hg))
private theorem mem_idealInfComapPartialDeriv_iff (h : ι) (K : Ideal S) (g : S) :
    g ∈ idealInfComapPartialDeriv k ι S h K ↔ g ∈ K ∧ partialDeriv k ι S h g ∈ K := Iff.rfl
private theorem partialDerivIdeal_logDerivIdeal_le [Fintype ι] [DecidableEq ι] (h : ι) (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I) ≤
      logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) (partialDerivIdeal k ι S h I) := by
  have key : logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S)) I ≤
      idealInfComapPartialDeriv k ι S h
        (logDerivIdeal k (Ideal.span ({coord k ι S h} : Set S))
          (partialDerivIdeal k ι S h I)) := by
    rw [logDerivIdeal_le_iff]
    constructor
    · intro g hg
      rw [mem_idealInfComapPartialDeriv_iff]
      refine ⟨?_, ?_⟩
      · exact le_logDerivIdeal k _ _ (le_partialDerivIdeal k ι S h I hg)
      · exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hg)
    · intro D hD y hy
      rw [mem_idealInfComapPartialDeriv_iff]
      have hDmem : D (coord k ι S h) ∈ Ideal.span ({coord k ι S h} : Set S) :=
        (mem_tangentDerivations_span_singleton k (coord k ι S h) D).mp hD
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hDmem
      refine ⟨?_, ?_⟩
      · exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
          (derivation_apply_mem_logDerivIdeal k _ I D hD hy)
      · rw [derivation_apply_eq_sum_partialDeriv k ι S D y]
        rw [map_sum]
        refine Ideal.sum_mem _ ?_
        intro i _
        rw [Derivation.leibniz]
        refine Submodule.add_mem _ ?_ ?_
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul, ← hc, mul_assoc]
            refine Ideal.mul_mem_left _ _ ?_
            exact coord_mul_partialDeriv_mem_logDerivIdeal k ι S h
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul, partialDeriv_comm k ι S h i y]
            refine Ideal.mul_mem_left _ _ ?_
            exact partialDeriv_mem_logDerivIdeal_of_ne k ι S hi
              (partialDerivIdeal k ι S h I)
              (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
        · by_cases hi : i = h
          · rw [hi, smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact le_logDerivIdeal k _ _ (partialDeriv_mem_partialDerivIdeal k ι S h I hy)
          · rw [smul_eq_mul]
            refine Ideal.mul_mem_right _ _ ?_
            exact logDerivIdeal_mono k _ (le_partialDerivIdeal k ι S h I)
              (partialDeriv_mem_logDerivIdeal_of_ne k ι S hi I hy)
  refine partialDerivIdeal_le k ι S h ?_ ?_
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff k ι S h _ g).mp (key hg)).1
  · intro g hg
    exact ((mem_idealInfComapPartialDeriv_iff k ι S h _ g).mp (key hg)).2
private theorem partialDerivIdeal_logDerivIdealIterate_le [Fintype ι] [DecidableEq ι] (h : ι) (m : ℕ)
    (I : Ideal S) :
    partialDerivIdeal k ι S h
        (logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m I) ≤
      logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) m
        (partialDerivIdeal k ι S h I) := by
  induction m with
  | zero => exact le_of_eq (by simp only [logDerivIdealIterate_zero])
  | succ m ih =>
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact (partialDerivIdeal_logDerivIdeal_le k ι S h _).trans (logDerivIdeal_mono k _ ih)
end EtaleCoordinates
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.EtaleCoordinates
variable (k : Type*) [CommRing k] (ι : Type*) (S : Type*) [CommRing S]
  [Algebra (MvPolynomial ι k) S] [Algebra k S] [IsScalarTower k (MvPolynomial ι k) S]
  [Algebra.FormallyEtale (MvPolynomial ι k) S]
namespace FunctorialResolution.EmbeddedResolution.EtaleCoordinates
theorem _root_.solution [Fintype ι] [DecidableEq ι]
    (h : ι) (n : ℕ) (J : Ideal S) :
    derivIdealIterate k n J ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n - l)
          (partialDerivIdealIterate k ι S h l J) := by
  induction n with
  | zero =>
      rw [derivIdealIterate_zero]
      exact le_iSup₂ (f := fun m (_ : m ≤ 0) =>
        logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (0 - m)
          (partialDerivIdealIterate k ι S h m J)) 0 le_rfl
  | succ n ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun l => ?_
      refine le_trans (derivIdeal_iSup_le k _) ?_
      refine iSup_le fun hl => ?_
      refine le_trans (derivIdeal_le_logDerivIdeal_sup_partialDerivIdeal k ι S h _) ?_
      refine sup_le ?_ ?_
      · rw [← logDerivIdealIterate_succ, show n - l + 1 = n + 1 - l from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) l (by omega)
      · refine le_trans (partialDerivIdeal_logDerivIdealIterate_le k ι S h (n - l) _) ?_
        rw [← partialDerivIdealIterate_succ, show n - l = n + 1 - (l + 1) from by omega]
        exact le_iSup₂ (f := fun m (_ : m ≤ n + 1) =>
          logDerivIdealIterate k (Ideal.span ({coord k ι S h} : Set S)) (n + 1 - m)
            (partialDerivIdealIterate k ι S h m J)) (l + 1) (by omega)
end FunctorialResolution.EmbeddedResolution.EtaleCoordinates
