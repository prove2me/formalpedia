-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.ShapeCovering.signed_minors_alg_independent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:42.638681+00:00
-- url     : https://prove2.me/submissions/976add40-4709-4481-ad8f-8623c37d3bcd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_CovDet
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
noncomputable section
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
private theorem cvd_adj {B : Type*} [CommRing B] {m : ℕ} (M : Matrix (Fin (m + 1)) (Fin (m + 1)) B)
    (i : Fin (m + 1)) :
    M.adjugate 0 i = (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => M (i.succAbove a) b.succ) := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  simp only [Fin.val_zero, add_zero, Fin.succAbove_zero]
  rfl
private theorem cvdN_det {F : Type*} [Field F] {k : ℕ} (z : Fin (k + 2) → F) (h0 : z 0 ≠ 0) :
    (cvdN z).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp [cvdN, Fin.succ_ne_zero, Fin.succ_succ_ne_one, h0]
  · intro i j hij
    have h1 : i ≠ 0 := by
      rintro rfl
      exact absurd hij (Fin.not_lt_zero _)
    have h2 : i ≠ j := ne_of_gt hij
    simp [cvdN, h1, h2]
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
theorem _root_.solution : SignedMinorsAlgIndependent := by
  intro K _ m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  let L := FractionRing (MvPolynomial (Fin (k + 1 + 1)) K)
  let ι : MvPolynomial (Fin (k + 1 + 1)) K →ₐ[K] L := IsScalarTower.toAlgHom K _ L
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  let z : Fin (k + 1 + 1) → L := fun i => ι (X i)
  have hz : AlgebraicIndependent K z := (MvPolynomial.algebraicIndependent_X _ _ :
    AlgebraicIndependent K (X : Fin (k + 1 + 1) → MvPolynomial (Fin (k + 1 + 1)) K)).map' hι
  have hz0 : z 0 ≠ 0 := (map_ne_zero_iff ι hι).mpr (MvPolynomial.X_ne_zero (R := K) (0 : Fin (k + 1 + 1)))
  let N := cvdN z
  have hN : N.det = 1 := cvdN_det z hz0
  let Q := N⁻¹
  have hQ : Q.adjugate = N := by
    have h1 : N * Q = 1 := Matrix.mul_nonsing_inv N (by rw [hN]; exact isUnit_one)
    have h2 : Q * Q.adjugate = 1 := by
      rw [Matrix.mul_adjugate, Matrix.det_nonsing_inv, hN, Ring.inverse_one, one_smul]
    calc Q.adjugate = (N * Q) * Q.adjugate := by rw [h1, one_mul]
      _ = N := by rw [mul_assoc, h2, mul_one]
  let f : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K →ₐ[K] L :=
    aeval fun v => Fin.lastCases 0 (fun b : Fin (k + 1) => Q v.1 b.succ) v.2
  apply AlgebraicIndependent.of_comp f
  convert hz using 1
  funext i
  show f (covY K (k + 1) i) = z i
  have hzi : Q.adjugate 0 i = z i := by
    rw [hQ]
    simp [N, cvdN]
  rw [← hzi, cvd_adj]
  simp only [covY, map_mul, map_pow, map_neg, map_one]
  congr 1
  refine (AlgHom.map_det f (Matrix.of fun a b : Fin (k + 1) =>
    (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (k + 1 + 1) × Fin (k + 1 + 1)) K))).trans ?_
  congr 1
  ext a b
  simp [f]
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
