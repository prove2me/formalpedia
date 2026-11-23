-- Prove2me | solution 1 for Formalism.DivisionValues.gram_determinant_quotient_metric
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:30.222887+00:00
-- url     : https://prove2.me/submissions/42387295-bb09-4772-8c6a-c05d1bd1ea8e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjTransposeEqOfPosDef
import Theorems.Thm_Formalism_DivisionValues_R0_map_inv_field
import Theorems.Thm_Formalism_DivisionValues_R0_conjTranspose_map
import Theorems.Thm_Formalism_DivisionValues_R0_conjTranspose_eq_of_posDef
import Theorems.Thm_Formalism_DivisionValues_R0_gramMat_conjTranspose

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
open R0
namespace Formalism.DivisionValues
theorem _root_.solution : GramDeterminantQuotientMetric := by
  intro K _ _ _ _ K0 hCM v0 hv0 n D H hK0 hpos P hsurj XQ hQ e
  have hH : Hᴴ = H := conjTranspose_eq_of_posDef v0 hv0 H (hpos v0)
  have hΓ : (quotGram P H)ᴴ = quotGram P H := by
    unfold quotGram
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH, Matrix.mul_assoc]
  have hΓmap : (quotGram P H).map v0.embedding = ((XQ v0)⁻¹)ᴴ * (XQ v0)⁻¹ := by
    rw [(hQ v0).2]
    unfold quotGram
    rw [map_inv_field, Matrix.map_mul, Matrix.map_mul, map_inv_field, conjTranspose_map v0.embedding hv0]
  refine ⟨?_, ?_⟩
  · unfold gramR
    rw [← Matrix.det_conjTranspose, gramMat_conjTranspose _ hΓ e]
  · unfold gramR gram Formalism.HN.gramPl
    rw [RingHom.map_det]
    congr 1
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Formalism.HermitianLatticesTheory.majAt,
      Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    have hY : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (x y : Fin D → ℂ),
        ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i := by
      intro Y x y
      have e1 : ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = star (Y *ᵥ x) ⬝ᵥ (Y *ᵥ y) := rfl
      have e2 : ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i = star x ⬝ᵥ ((Yᴴ * Y) *ᵥ y) := rfl
      rw [e1, e2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [hY, ← hΓmap]
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply, hv0']
    rfl
end Formalism.DivisionValues
