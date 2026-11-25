-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.span_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:59:47.125435+00:00
-- url     : https://prove2.me/submissions/7dcbc0cc-237d-4651-ac1a-3850a6483a81

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_tmul
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_range
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_Phi_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDA
open TensorProduct Module
variable {K K₁ : Type*} [Field K] [Field K₁] [Algebra K K₁]
attribute [local instance] modT
attribute [local instance] modR
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {R : Type*} [CommRing R] [Algebra R K] [Module R U] [IsScalarTower R K U]
variable (T : Subring K₁) [Algebra R T]
  (hRT : ∀ r : R, ((algebraMap R T r : T) : K₁) = algebraMap K K₁ (algebraMap R K r))
variable [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K]
include hRT
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution (X : Submodule R U) (hX : X.FG) (W : Submodule K U) :
    Submodule.span T (Submodule.span K₁ (tm K K₁ '' (W : Set U)) : Set (K₁ ⊗[K] U)) ⊓
        Submodule.span T (tm K K₁ '' (X : Set U)) =
      Submodule.span T (tm K K₁ '' ((X ⊓ W.restrictScalars R : Submodule R U) : Set U)) := by
  classical
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_inf] at hz
    obtain ⟨hzW, hzX⟩ := hz
    let fR : U →ₗ[R] U ⧸ W := W.mkQ.restrictScalars R
    let Xb : Submodule R (U ⧸ W) := X.map fR
    let g : X →ₗ[R] Xb := fR.submoduleMap X
    have hg : Function.Surjective g := LinearMap.submoduleMap_surjective fR X
    have hz0 : W.mkQ.baseChange K₁ z = 0 := by
      refine Submodule.span_induction (p := fun z _ => W.mkQ.baseChange K₁ z = 0) ?_ ?_ ?_ ?_ hzW
      · intro y hy
        refine Submodule.span_induction (p := fun y _ => W.mkQ.baseChange K₁ y = 0) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨w, hw, rfl⟩
          show W.mkQ.baseChange K₁ ((1 : K₁) ⊗ₜ[K] w) = 0
          rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).2 hw,
            TensorProduct.tmul_zero]
        · simp
        · intro a b _ _ ha hb
          rw [map_add, ha, hb, add_zero]
        · intro c a _ ha
          rw [map_smul, ha, smul_zero]
      · simp
      · intro a b _ _ ha hb
        rw [map_add, ha, hb, add_zero]
      · intro t a _ ha
        show W.mkQ.baseChange K₁ ((t : K₁) • a) = 0
        rw [map_smul, ha, smul_zero]
    have hzR : z ∈ LinearMap.range (Phi T hRT X) := by
      rw [Phi_range]
      exact hzX
    obtain ⟨w, rfl⟩ := hzR
    have hsq : ∀ w, Phi T hRT Xb (g.baseChange T w) = W.mkQ.baseChange K₁ (Phi T hRT X w) := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul t x =>
        rw [LinearMap.baseChange_tmul, Phi_tmul, Phi_tmul]
        show (t : K₁) • tm K K₁ ((g x : Xb) : U ⧸ W) = W.mkQ.baseChange K₁ ((t : K₁) • (1 : K₁) ⊗ₜ[K] (x : U))
        rw [map_smul, LinearMap.baseChange_tmul]
        rfl
      | add a c ha hc =>
        rw [map_add, map_add, map_add, map_add, ha, hc]
    have hw0 : g.baseChange T w = 0 := by
      apply Phi_injective T hRT Xb (hX.map _)
      rw [hsq, map_zero]
      exact hz0
    have hex : Function.Exact (LinearMap.ker g).subtype g :=
      LinearMap.exact_iff.2 (Submodule.range_subtype _).symm
    have hw0' : g.lTensor T w = 0 := by
      rw [← congrFun (LinearMap.baseChange_eq_ltensor (A := T) g) w]
      exact hw0
    obtain ⟨v, rfl⟩ := (lTensor_exact T hex hg w).1 hw0'
    clear hzW hzX hz0 hw0 hw0'
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, Phi_tmul]
      have hyW : ((y : X) : U) ∈ W := by
        have hy : g (y : X) = 0 := y.2
        have h' : W.mkQ ((y : X) : U) = 0 := congrArg Subtype.val hy
        exact (Submodule.Quotient.mk_eq_zero W).1 h'
      exact Submodule.smul_mem _ t (Submodule.subset_span ⟨(y : X), ⟨(y : X).2, hyW⟩, rfl⟩)
    | add a c ha hc =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hc
  · rw [Submodule.span_le]
    rintro _ ⟨x, ⟨hxX, hxW⟩, rfl⟩
    refine ⟨?_, Submodule.subset_span ⟨x, hxX, rfl⟩⟩
    exact Submodule.subset_span (Submodule.subset_span ⟨x, hxW, rfl⟩)
end Formalism.L2.Pj.QAt.TieLDA
