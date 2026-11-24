-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.det_eq_det_submatrix_of_row_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:02:01.088823+00:00
-- url     : https://prove2.me/submissions/56d83071-3c14-4d3b-8608-d6833fa52ffe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothHypersurfaceLocalCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_DerivationLiftAndDeterminant
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
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
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
end
section
variable {R : Type*} [CommRing R]
end
section
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
end
section
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
private theorem det_eq_det_submatrix_succ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ b : Fin (n + 1), M 0 b = if b = 0 then (1 : R) else 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [h, Fin.succAbove_zero]
  · intro b _ hb
    simp [h b, hb]
  · intro hb
    exact absurd (Finset.mem_univ (0 : Fin (n + 1))) hb
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (e : ι ≃ Fin (n + 1)) (M : Matrix ι ι R)
    (h : ∀ b : ι, M (e.symm 0) b = if b = e.symm 0 then (1 : R) else 0) :
    M.det =
      (M.submatrix (fun i : Fin n => e.symm i.succ) (fun i : Fin n => e.symm i.succ)).det := by
  have hN : ∀ b : Fin (n + 1),
      (M.submatrix e.symm e.symm) 0 b = if b = 0 then (1 : R) else 0 := by
    intro b
    simp only [Matrix.submatrix_apply]
    rw [h (e.symm b)]
    by_cases hb : b = 0
    · simp [hb]
    · have hne : ¬ (e.symm b = e.symm 0) := fun hc => hb (e.symm.injective hc)
      rw [if_neg hne, if_neg hb]
  have h2 := det_eq_det_submatrix_succ (M.submatrix e.symm e.symm) hN
  rw [Matrix.det_submatrix_equiv_self] at h2
  rw [h2, Matrix.submatrix_submatrix]
  rfl
end FunctorialResolution.EmbeddedResolution
