-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDA.length_tensor_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:23.576137+00:00
-- url     : https://prove2.me/submissions/02c5d93f-5633-40c7-aa99-a7087e638863

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_length_self_eq_top
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDA_length_quot_span_pow

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
namespace Formalism.L2.Pj.QAt.TieLDA
theorem _root_.solution {R T : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Algebra R T]
    (N : Type*) [AddCommGroup N] [Module R N] [Module.Finite R N] (h : Module.length R N = ⊤) :
    Module.length T (T ⊗[R] N) = ⊤ := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum R N
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    have h1 := f.length_eq
    rw [h, Module.length_prod, (DirectSum.linearEquivFunOnFintype R ι (fun i => R ⧸ R ∙ p i ^ e i)).length_eq,
      Module.length_pi_of_fintype] at h1
    have h0 : Module.length R (Fin 0 →₀ R) = 0 := by
      first
        | exact Module.length_eq_zero_iff.2 inferInstance
        | exact Module.length_eq_zero
    rw [h0, zero_add] at h1
    have h2 : ∑ i, Module.length R (R ⧸ R ∙ p i ^ e i) = ((∑ i, e i : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => length_quot_span_pow (hp i) (e i)
    rw [h2] at h1
    exact ENat.coe_ne_top _ h1.symm
  · let g : N →ₗ[R] R := (Finsupp.lapply ⟨0, hn⟩) ∘ₗ (LinearMap.fst R _ _) ∘ₗ f.toLinearMap
    have hg : Function.Surjective g := by
      intro r
      refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ r, 0), ?_⟩
      simp [g]
    let φ : T ⊗[R] N →ₗ[T] T := (TensorProduct.AlgebraTensorModule.rid R T T).toLinearMap ∘ₗ g.baseChange T
    have hφ : Function.Surjective φ := by
      have hb : Function.Surjective (g.baseChange T) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective T hg
      exact (TensorProduct.AlgebraTensorModule.rid R T T).surjective.comp hb
    have hle := Module.length_le_of_surjective φ hφ
    rw [length_self_eq_top] at hle
    exact top_le_iff.1 hle
end Formalism.L2.Pj.QAt.TieLDA
