-- Prove2me | solution 1 for Formalism.L2.Th1.H.relIndex_eq_abs_det_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:27:33.29872+00:00
-- url     : https://prove2.me/submissions/0c3a8333-4c13-4615-a436-667e28895e6a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L₁ L₂ : AddSubgroup E) (h : L₁ ≤ L₂) {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℝ E) (h₁ : L₁ = .closure (Set.range b₁)) (h₂ : L₂ = .closure (Set.range b₂)) :
    (L₁.relIndex L₂ : ℝ) = |b₂.det b₁| := by
  classical
  subst h₁ h₂
  rw [← Submodule.span_int_eq_addSubgroupClosure, ← Submodule.span_int_eq_addSubgroupClosure] at h ⊢
  have hle : Submodule.span ℤ (Set.range b₁) ≤ Submodule.span ℤ (Set.range b₂) :=
    fun x hx => h hx
  set S₁ := Submodule.span ℤ (Set.range b₁) with hS₁
  set S₂ := Submodule.span ℤ (Set.range b₂) with hS₂
  let B₂ : Basis ι ℤ S₂ := b₂.restrictScalars ℤ
  let B₁ : Basis ι ℤ S₁ := b₁.restrictScalars ℤ
  let N : Submodule ℤ S₂ := S₁.comap S₂.subtype
  let BN : Basis ι ℤ N := B₁.map (Submodule.comapSubtypeEquivOfLe hle).symm
  haveI : Module.Free ℤ S₂ := Module.Free.of_basis B₂
  haveI : Module.Finite ℤ S₂ := Module.Finite.of_basis B₂
  have key := Submodule.natAbs_det_basis_change B₂ N BN
  have hcard : Nat.card (S₂ ⧸ N) = S₁.toAddSubgroup.relIndex S₂.toAddSubgroup := rfl
  have hrepr : ∀ (m : S₂) (i : ι), ((B₂.repr m i : ℤ) : ℝ) = b₂.repr (m : E) i := fun m i => by
    rw [← Basis.restrictScalars_repr_apply ℤ b₂ m i]; simp [B₂]
  have hv : ∀ j, (((BN j : N) : S₂) : E) = b₁ j := fun j => by
    simp [BN, B₁, Basis.map_apply, Submodule.comapSubtypeEquivOfLe]
    exact Basis.restrictScalars_apply ℤ b₁ j
  have hdet : ((B₂.det (Subtype.val ∘ BN) : ℤ) : ℝ) = b₂.det b₁ := by
    rw [Basis.det_apply, Basis.det_apply]
    rw [show ((Matrix.det (B₂.toMatrix (Subtype.val ∘ BN)) : ℤ) : ℝ)
        = (Int.castRingHom ℝ) (Matrix.det (B₂.toMatrix (Subtype.val ∘ BN))) from rfl,
      RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Basis.toMatrix_apply, Function.comp_apply,
      eq_intCast]
    rw [hrepr, hv]
  rw [← hcard, ← key, ← hdet, Nat.cast_natAbs, Int.cast_abs]
end Formalism.L2.Th1.H
