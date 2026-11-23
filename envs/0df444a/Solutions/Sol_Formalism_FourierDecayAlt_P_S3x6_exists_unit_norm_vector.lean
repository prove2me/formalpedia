-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.exists_unit_norm_vector
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:05.10926+00:00
-- url     : https://prove2.me/submissions/2e3ed7a8-8868-42a7-b2e0-1e50d306be3c

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
variable {V : Type} [AddCommGroup V] [Module K V]
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution (hσ : Inv σ) {h : V →ₛₗ[σ] V →ₗ[K] K} (hh : Herm h)
    (hne : ∃ u v, h u v ≠ 0) : ∃ v, h v v = 1 := by
  have h1 : ∃ v, h v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, v, huv⟩ := hne
    obtain ⟨l, hl⟩ := hσ.trace_one
    have h2 := hcon (u + (l / h u v) • v)
    have h3 : h (u + (l / h u v) • v) (u + (l / h u v) • v) =
        h u u + (l / h u v) * h u v + σ (l / h u v) * h v u + σ (l / h u v) * ((l / h u v) * h v v) := by
      simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring
    rw [h3, hcon u, hcon v, ← hh u v, ← map_mul, div_mul_cancel₀ _ huv] at h2
    simp only [mul_zero, add_zero, zero_add] at h2
    rw [hl] at h2
    exact one_ne_zero h2
  obtain ⟨v, hv⟩ := h1
  obtain ⟨y, hy⟩ := hσ.norm_surj (h v v) (hh v v)
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hv
    rw [← hy]
    simp
  refine ⟨y⁻¹ • v, ?_⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  rw [← hy, map_inv₀]
  have : σ y ≠ 0 := by
    intro h0
    apply hv
    rw [← hy, h0, zero_mul]
  field_simp
end Formalism.FourierDecayAlt.P.S3x6
