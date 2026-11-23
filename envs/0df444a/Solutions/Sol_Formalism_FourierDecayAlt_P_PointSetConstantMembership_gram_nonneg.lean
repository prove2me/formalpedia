-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PointSetConstantMembership.gram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:37.347817+00:00
-- url     : https://prove2.me/submissions/b0647dc8-018d-483e-bfc8-3276941fc704

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointSetConstantMembership

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PointSetConstantMembership
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PointSetConstantMembership
theorem _root_.solution {α : Type} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Finset α) (k : α → α → ℂ) (V : α → H)
    (hk : ∀ a : α → ℂ, 0 ≤ (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y).re) :
    0 ≤ (∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ).re := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix P P ℂ, Matrix.gram ℂ (fun p : P => V p.1) = star B * B := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (Matrix.posSemidef_gram ℂ (fun p : P => V p.1)).nonneg
  have hG : ∀ p (hp : p ∈ P) p' (hp' : p' ∈ P),
      ⟪V p, V p'⟫_ℂ = ∑ j, conj (B j ⟨p, hp⟩) * B j ⟨p', hp'⟩ := by
    intro p hp p' hp'
    have := congrFun (congrFun hB ⟨p, hp⟩) ⟨p', hp'⟩
    simpa [Matrix.gram, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] using this
  set a : P → α → ℂ := fun j p => if h : p ∈ P then B j ⟨p, h⟩ else 0 with ha
  have e : ∑ p ∈ P, ∑ p' ∈ P, k p p' * ⟪V p, V p'⟫_ℂ
      = ∑ j, ∑ x ∈ P, ∑ y ∈ P, conj (a j x) * k x y * a j y := by
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    rw [hG p hp p' hp', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha, dif_pos hp, dif_pos hp']
    ring
  rw [e, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => hk (a j)
end Formalism.FourierDecayAlt.P.PointSetConstantMembership
