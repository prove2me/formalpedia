-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.form_functionals_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:43.515313+00:00
-- url     : https://prove2.me/submissions/fd22860c-f65f-43c1-8f2d-01777ed80f40

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_form_sum_left_alt

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
theorem _root_.solution (hσ : Inv σ) (h : V →ₛₗ[σ] V →ₗ[K] K) (hn : Nondeg h) {ι : Type} [Fintype ι]
    [DecidableEq ι] (x : ι → V) (hx : LinearIndependent K x) (r : ι → K) :
    ∃ m, ∀ i, h (x i) m = r i := by
  let Φ : V →ₗ[K] (ι → K) := LinearMap.pi (fun i => h (x i))
  have htop : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have key : ∀ v, ∑ i, h (x i) v * f (fun j => if i = j then 1 else 0) = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hf ⟨v, rfl⟩
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      simpa [Φ] using h1
    have h2 : ∑ i, σ (f (fun j => if i = j then 1 else 0)) • x i = 0 := by
      apply hn
      intro v
      rw [form_sum_left_alt]
      simp only [hσ.invol]
      refine Eq.trans ?_ (key v)
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have hc := Fintype.linearIndependent_iff.1 hx _ h2
    apply hf0
    refine LinearMap.ext (fun w => ?_)
    rw [LinearMap.pi_apply_eq_sum_univ f w]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have h3 := hc i
    rw [map_eq_zero] at h3
    rw [h3, smul_zero]
  have : r ∈ LinearMap.range Φ := by rw [htop]; trivial
  obtain ⟨m, hm⟩ := this
  exact ⟨m, fun i => by rw [← hm]; rfl⟩
end Formalism.FourierDecayAlt.P.S3x6
