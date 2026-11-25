-- Prove2me | solution 1 for Formalism.MainNotions.G.ValuationFitting.smith_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:15:49.089864+00:00
-- url     : https://prove2.me/submissions/95ecd04b-a031-4263-a76e-bd190c92d81d

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Theorems.Thm_Formalism_MainNotions_G_ValuationFitting_Em_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_smith_mat
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_pi
import Theorems.Thm_ReciprocityTheory_PGsh_Up_hasLen_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ValuationFitting
open ReciprocityTheory.PGsh.Up
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
namespace Formalism.MainNotions.G.ValuationFitting
theorem _root_.solution (hv : v.Integers R) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) :
    ∃ (P : Matrix (Fin m) (Fin m) R) (Q : Matrix (Fin h) (Fin h) R) (a' : Fin m → R),
      IsUnit P.det ∧ IsUnit Q.det ∧ P * α * Q = Matrix.diagonal a' * Em R m h ∧
      (∀ j : Fin m, h ≤ (j : ℕ) → a' j = 0) ∧ ∏ j, v (algebraMap R C (a' j)) = x := by
  obtain ⟨P, Q, a, hP, hQ, hPAQ⟩ := Smith.smith_mat hv m h α
  set a' : Fin m → R := fun j => if (j : ℕ) < h then a j else 0 with ha'
  have hD : P * α * Q = Matrix.diagonal a' * Em R m h := by
    ext j k
    rw [hPAQ, Matrix.diagonal_mul, Em, Matrix.of_apply]
    by_cases hkj : (k : ℕ) = (j : ℕ)
    · have hj : (j : ℕ) < h := hkj ▸ k.isLt
      simp [hkj, ha', hj]
    · simp [hkj]
  refine ⟨P, Q, a', hP, hQ, hD, fun j hj => by simp [ha', not_lt.mpr hj], ?_⟩
  have hQs : LinearMap.range Q.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro y
    refine ⟨Q⁻¹ *ᵥ y, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]
  let eP : (Fin m → R) ≃ₗ[R] (Fin m → R) := Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP)
  have h1 : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) =
      LinearMap.range (P * α * Q).mulVecLin := by
    rw [← LinearMap.range_comp, Matrix.mulVecLin_mul, LinearMap.range_comp_of_range_eq_top _ hQs,
      Matrix.mulVecLin_mul]
    rfl
  have h2 : LinearMap.range (Matrix.diagonal a' * Em R m h).mulVecLin =
      Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R)) := by
    ext y
    simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Submodule.mem_pi, Set.mem_univ, true_implies,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨w, rfl⟩ j
      refine ⟨(Em R m h *ᵥ w) j, ?_⟩
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, mul_comm]
    · intro hy
      choose t ht using hy
      refine ⟨fun k => if hk : (k : ℕ) < m then t ⟨k, hk⟩ else 0, ?_⟩
      funext j
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Em_mulVec, ← ht j]
      by_cases hj : (j : ℕ) < h <;> simp [ha', hj, mul_comm]
  have hrange : (LinearMap.range α.mulVecLin).map (eP : (Fin m → R) →ₗ[R] (Fin m → R)) =
      Submodule.pi Set.univ (fun j => (Ideal.span {a' j} : Submodule R R)) := by
    rw [h1, hD, h2]
  let e := Submodule.Quotient.equiv _ _ eP hrange
  obtain ⟨d, c, ⟨e0⟩, hc⟩ := ReciprocityTheory.PGsh.Up.hasLen_pi v a'
  exact (ReciprocityTheory.PGsh.Up.hasLen_unique hv hx ⟨d, c, ⟨e.trans e0⟩, hc⟩).symm
end Formalism.MainNotions.G.ValuationFitting
