-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:01.686039+00:00
-- url     : https://prove2.me/submissions/0c87758a-aff5-41b6-b43a-cce3acce54be

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjS_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_mul_conjS
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjAct_C

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool)
    (H : MvPolynomial (LVar ι ζ n) L) :
    conjAct (RingHom.id L) isVec S g gi last (sharpHom isVec S g gi H) = tw isVec S g gi last H := by
  suffices hh : (conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last).comp
      (sharpHom isVec S g gi).toRingHom = tw isVec S g gi last from by
    rw [← hh]; rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [tw, conjAct_C, sharpHom]
  · intro x
    rcases x with ⟨i, a⟩ | z
    · by_cases h1 : i ∈ S
      · by_cases h3 : isVec i
        · have e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
              Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) a := by
            simp [sharpHom, h1, h3]
          have e2 : (⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) ∘
              fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
              Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b)))) (conjS _ g gi last 1) := by
            funext b
            simp [conjAct, h1, h3]
          have e3 : (g.map C).map ⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) = g.map (cc _ L) := by
            ext p q
            simp [conjAct_C]
          have e4 : (g.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).map
              ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) =
              g.map (cc _ L) := by
            ext p q
            simp
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]
          rw [e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, conjS_mul _ h, ← Matrix.vecMul_vecMul,
            diagS, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]
          congr 1
          by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]
        · have e1 : sharpHom isVec S g gi (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
              Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose a := by
            simp [sharpHom, h1, h3]
          have e2 : (⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) ∘
              fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
              Matrix.vecMul (fun b => LaurentPolynomial.C (X (Sum.inl (i, b))))
                (conjS _ g gi last (-1)).transpose := by
            funext b
            simp [conjAct, h1, h3]
          have e3 : ((gi.map C).transpose).map ⇑(conjAct (ζ := ζ) (RingHom.id L) isVec S g gi last) =
              (gi.map (cc _ L)).transpose := by
            ext p q
            simp [conjAct_C]
          have e4 : ((gi.map (C : L →+* MvPolynomial (LVar ι ζ n) L)).transpose).map
              ⇑(LaurentPolynomial.C : _ →+* LaurentPolynomial (MvPolynomial (LVar ι ζ n) L)) =
              (gi.map (cc _ L)).transpose := by
            ext p q
            simp
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, tw, coe_eval₂Hom, eval₂_X]
          rw [e1, RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, mul_conjS _ h,
            Matrix.transpose_mul, ← Matrix.vecMul_vecMul,
            diagS, Matrix.diagonal_transpose, Matrix.vecMul_diagonal, RingHom.map_vecMul, e4, mul_comm]
          congr 1
          by_cases h2 : (if last then a.val + 1 = n else a.val = 0) <;> simp [wtX, h1, h2, h3]
      · simp [tw, conjAct, sharpHom, wtX, h1]
    · simp [tw, conjAct, sharpHom, wtX]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
