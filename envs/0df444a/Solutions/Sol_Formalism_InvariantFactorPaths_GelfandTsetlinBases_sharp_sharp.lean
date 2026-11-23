-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sharp_sharp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:41.919439+00:00
-- url     : https://prove2.me/submissions/f82a102c-614a-4513-876f-07e2be180ee2

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe

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
theorem _root_.solution {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (H : MvPolynomial (LVar ι ζ n) L) :
    sharpHom isVec S g gi (sharpHom isVec S gi g H) = H := by
  suffices hh : (sharpHom (ζ := ζ) isVec S g gi).comp (sharpHom isVec S gi g) = AlgHom.id L _ from by
    have := congrArg (fun f => f H) hh
    simpa using this
  apply MvPolynomial.algHom_ext
  intro x
  rcases x with ⟨i, a⟩ | z
  · by_cases h1 : i ∈ S
    · by_cases h3 : isVec i
      · have e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C) a := by
          simp [sharpHom, h1, h3]
        have e2 : (⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom ∘
            fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C) := by
          funext b
          simp [sharpHom, h1, h3]
        have e3 : (gi.map C).map ⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom = gi.map C := by
          ext p q
          simp [sharpHom]
        rw [AlgHom.comp_apply, e1]
        change (sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _
        rw [RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, h,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.vecMul_one]
        rfl
      · have e1 : sharpHom isVec S gi g (X (Sum.inl (i, a)) : MvPolynomial (LVar ι ζ n) L) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (g.map C).transpose a := by
          simp [sharpHom, h1, h3]
        have e2 : (⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom ∘
            fun b => (X (Sum.inl (i, b)) : MvPolynomial (LVar ι ζ n) L)) =
            Matrix.vecMul (fun b => X (Sum.inl (i, b))) (gi.map C).transpose := by
          funext b
          simp [sharpHom, h1, h3]
        have e3 : ((g.map C).transpose).map ⇑(sharpHom (ζ := ζ) isVec S g gi).toRingHom =
            (g.map C).transpose := by
          ext p q
          simp [sharpHom]
        rw [AlgHom.comp_apply, e1]
        change (sharpHom (ζ := ζ) isVec S g gi).toRingHom _ = _
        rw [RingHom.map_vecMul, e2, e3, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, ← Matrix.map_mul, h,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.vecMul_one]
        rfl
    · simp [sharpHom, h1]
  · simp [sharpHom]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
