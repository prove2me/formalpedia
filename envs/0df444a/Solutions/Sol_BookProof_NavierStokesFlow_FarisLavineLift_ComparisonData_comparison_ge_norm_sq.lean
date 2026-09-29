-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:17:01.49113+00:00
-- url     : https://prove2.me/submissions/760e310e-f37e-400f-8aa6-a08fc5beed66

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift
open BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)
set_option autoImplicit false

private theorem comparison_quad (v : c.D) :
    (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re
      = (∑ i, ‖((c.mom i v : c.D) : F)‖ ^ 2) + (∑ i, ‖((c.drift i v : c.D) : F)‖ ^ 2)
        + ‖(v : F)‖ ^ 2 := by
  have hs (A : c.D →ₗ[ℂ] c.D) (hA : FullEsa.IsSymmetricDom A) :
      (inner ℂ (v : F) ((A (A v) : c.D) : F)).re = ‖((A v : c.D) : F)‖ ^ 2 := by
    rw [← hA v (A v)]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  simp only [ComparisonData.comparison, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_add, Submodule.coe_sum,
    inner_add_right, inner_sum, Complex.add_re, Complex.re_sum]
  simp_rw [hs _ (c.mom_symm _), hs _ (c.drift_symm _)]
  have hv : (inner ℂ (v : F) (v : F)).re = ‖(v : F)‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hv]


theorem solution (v : c.D) :
    ‖(v : F)‖ ^ 2 ≤ (inner ℂ ((v : F)) ((c.comparison v : c.D) : F) : ℂ).re := by
  rw [comparison_quad]
  have h1 : 0 ≤ ∑ i, ‖((c.mom i v : c.D) : F)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : 0 ≤ ∑ i, ‖((c.drift i v : c.D) : F)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith
#print axioms solution
