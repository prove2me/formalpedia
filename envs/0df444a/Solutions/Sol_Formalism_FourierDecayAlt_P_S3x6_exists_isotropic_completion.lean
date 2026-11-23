-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.exists_isotropic_completion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:04.738806+00:00
-- url     : https://prove2.me/submissions/58d00611-a595-4e2d-a255-d3ef2bb2f5ab

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_right_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_left_alt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_functionals_surjective

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
theorem _root_.solution (hσ : Inv σ) (h : V →ₛₗ[σ] V →ₗ[K] K) (hh : Herm h) (hn : Nondeg h) {a : ℕ}
    (x : Fin a → V) (hx : LinearIndependent K x) (N : Fin a → K) (i0 : Fin a) (hN : N i0 ≠ 0)
    (hGN : ∀ i, h (x i) (∑ j, N j • x j) = 0) :
    ∃ m, (∀ i, h (x i) m = if i = i0 then 1 else 0) ∧ h m m = 0 ∧
      m ∉ Submodule.span K (Set.range x) := by
  obtain ⟨m0, hm0⟩ := form_functionals_surjective hσ h hn x hx (fun i => if i = i0 then 1 else 0)
  obtain ⟨l, hl⟩ := hσ.trace_one
  set u := ∑ j, N j • x j with hu
  have hux : ∀ i, h u (x i) = 0 := by
    intro i
    rw [← hh, hGN]; simp
  have huu : h u u = 0 := by
    conv_lhs => rw [hu]
    rw [form_sum_left_alt]
    exact Finset.sum_eq_zero (fun j _ => by rw [hGN, mul_zero])
  have hum : h u m0 = σ (N i0) := by
    rw [hu, form_sum_left_alt]
    simp [hm0]
  have hs : σ (N i0) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hN
  have hmu : h m0 u = N i0 := by
    rw [← hh u m0, hum, hσ.invol]
  have ht : σ (h m0 m0) = h m0 m0 := hh m0 m0
  refine ⟨m0 + (-(l * h m0 m0) / N i0) • u, ?_, ?_, ?_⟩
  · intro i
    rw [map_add, map_smul, hGN, smul_zero, add_zero, hm0]
  · simp only [map_add, LinearMap.add_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, huu, hum,
      hmu, smul_eq_mul, map_div₀, map_neg, map_mul, ht]
    have hl' : σ l = 1 - l := by rw [← hl]; ring
    rw [hl']
    field_simp
    ring
  · intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
    have h1 : h u (∑ i, c i • x i) = 0 := by
      rw [form_sum_right_alt]
      exact Finset.sum_eq_zero (fun j _ => by rw [hux, mul_zero])
    rw [hc, map_add, map_smul, huu, smul_zero, add_zero, hum] at h1
    exact hs h1
end Formalism.FourierDecayAlt.P.S3x6
