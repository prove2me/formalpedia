-- Prove2me | solution 1 for Formalism.DivisionValues.orthogonal_projection_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:38.085913+00:00
-- url     : https://prove2.me/submissions/423ef8c4-57ee-4c60-a94d-3a388bbfbebf

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_isOrthProj_formula
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_isOrthProj_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : OrthProjExists := by
  intro K _ _ _ v0 hc0 n d H hPD E hE
  have hc : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hc0
  have hH : Hᴴ = H := by
    ext i j
    apply v0.embedding.injective
    have h1 := hPD.1.apply i j
    simp only [Matrix.map_apply] at h1
    simp only [Matrix.conjTranspose_apply]
    rw [hc, starRingEnd_apply, h1]
  have hdet : IsUnit H.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 := hPD.det_pos
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero] at h1
    exact lt_irrefl _ h1
  have hmap : ∀ u : Fin n → K, star (fun i => v0.embedding (u i)) ⬝ᵥ
      ((H.map v0.embedding) *ᵥ (fun i => v0.embedding (u i))) = v0.embedding (star u ⬝ᵥ (H *ᵥ u)) := by
    intro u
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, hc, starRingEnd_apply, Matrix.map_apply]
  have hZ : IsUnit (Eᴴ * H * E).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨z, hz, hz0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hz0
    have h2 : star (E *ᵥ z) ⬝ᵥ (H *ᵥ (E *ᵥ z)) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hz0]
      simp
    have hu : E *ᵥ z ≠ 0 := fun h => hz (hE (by rw [h, Matrix.mulVec_zero]))
    have hne : (fun i => v0.embedding ((E *ᵥ z) i)) ≠ 0 := by
      intro h
      apply hu
      funext i
      have h5 := congrFun h i
      simp only [Pi.zero_apply, map_eq_zero] at h5
      simpa using h5
    have h3 : 0 < star (fun i => v0.embedding ((E *ᵥ z) i)) ⬝ᵥ
        ((H.map v0.embedding) *ᵥ (fun i => v0.embedding ((E *ᵥ z) i))) := by
      first
        | exact hPD.dotProduct_mulVec_pos hne
        | exact (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 _ hne
    rw [hmap, h2, map_zero] at h3
    exact lt_irrefl _ h3
  exact ⟨hH, hdet, hZ, isOrthProj_formula H E hZ, fun Pr hO => isOrthProj_unique hZ hO⟩
end Formalism.DivisionValues
