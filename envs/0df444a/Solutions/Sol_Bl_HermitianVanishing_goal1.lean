-- Prove2me | solution 1 for Bl.HermitianVanishing.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:18:24.668886+00:00
-- url     : https://prove2.me/submissions/a01db1fd-1558-433d-a7bf-b77b6594de6a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Bl.HermitianVanishing
open scoped ComplexOrder in
private lemma key_zero {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ)
    (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (hH : (H.map φ).PosDef) (y : Fin n → K)
    (hy : dotProduct (star y) (Matrix.mulVec H y) = 0) : y = 0 := by
  by_contra hne
  have hy' : (fun i => φ (y i)) ≠ 0 := by
    intro h0
    apply hne
    funext i
    have := congrFun h0 i
    exact φ.injective (by simpa using this)
  have hpos := hH.dotProduct_mulVec_pos hy'
  have h1 : φ (dotProduct (star y) (Matrix.mulVec H y)) =
      dotProduct (star (fun i => φ (y i))) (Matrix.mulVec (H.map φ) fun i => φ (y i)) := by
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply,
      hφ, starRingEnd_apply]
  rw [hy, map_zero] at h1
  rw [← h1] at hpos
  exact lt_irrefl _ hpos
open scoped ComplexOrder in
private lemma herm_of {K : Type} [Field K] [StarRing K] (φ : K →+* ℂ)
    (hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a)) {n : ℕ} (H : Matrix (Fin n) (Fin n) K)
    (hH : (H.map φ).PosDef) : H.conjTranspose = H := by
  ext i j
  apply φ.injective
  rw [Matrix.conjTranspose_apply, hφ, starRingEnd_apply]
  simpa using hH.isHermitian.apply i j
end Bl.HermitianVanishing
end

set_option autoImplicit false
open Bl Bl.HermitianVanishing
namespace Bl.HermitianVanishing
theorem _root_.solution :
  Formalism.DivisionValues.OrthProjExists := by
  unfold Formalism.DivisionValues.OrthProjExists
  intro K _ _ _ v0 hconj n d H hH E hE
  have hφ : ∀ a, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hconj
  have hHerm : H.conjTranspose = H := herm_of v0.embedding hφ H hH
  have hdetH : IsUnit H.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : Matrix.mulVec H (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := key_zero v0.embedding hφ H hH (x - y) (by rw [h0, dotProduct_zero])
    exact sub_eq_zero.mp this
  have hMu : IsUnit (E.conjTranspose * H * E).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have h0 : Matrix.mulVec (E.conjTranspose * H * E) (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : dotProduct (star (x - y)) (Matrix.mulVec (E.conjTranspose * H * E) (x - y)) = 0 := by
      rw [h0, dotProduct_zero]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec] at h1
    have h2 := key_zero v0.embedding hφ H hH (Matrix.mulVec E (x - y)) h1
    rw [Matrix.mulVec_sub, sub_eq_zero] at h2
    exact hE h2
  refine ⟨hHerm, hdetH, hMu, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMu]
  · have h3 : E.conjTranspose * H * (E * ((E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H)))
        = E.conjTranspose * H := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hMu, Matrix.one_mul]
    rw [Matrix.mul_sub, Matrix.mul_one, h3, sub_self]
  · intro Pr hPr
    obtain ⟨_, h2⟩ := hPr
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, ← Matrix.mul_assoc] at h2
    calc Pr = ((E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H * E)) * Pr := by
          rw [Matrix.nonsing_inv_mul _ hMu, Matrix.one_mul]
      _ = (E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H * E * Pr) := Matrix.mul_assoc _ _ _
      _ = (E.conjTranspose * H * E)⁻¹ * (E.conjTranspose * H) := congrArg _ h2.symm
end Bl.HermitianVanishing
