-- Prove2me | solution 1 for BookProof.ChapterMajoranaProp61.prop61_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T06:23:22.006931+00:00
-- url     : https://prove2.me/submissions/f3998891-632c-4f11-8d07-9ed21031946e

-- Generated from ChapterMajoranaProp61.lean — solution of BookProof.ChapterMajoranaProp61.prop61_isUnit
import Mathlib
import Definitions.Def_ChapterMajoranaProp61
import Theorems.Thm_BookProof_ChapterMajoranaProp61_prop61_star_mul_self
import Theorems.Thm_BookProof_ChapterMajoranaProp61_prop61_mul_star_self
open BookProof.ChapterMajoranaProp61














variable {𝒜 : Type*} [Ring 𝒜] [StarRing 𝒜] [Algebra ℝ 𝒜] [StarModule ℝ 𝒜]




variable (U H g E N Ni : 𝒜) (m : ℝ)
  (hU₁ : star U * U = 1) (hU₂ : U * star U = 1)
  (hg_sa : star g = g) (hg2 : g * g = 1)
  (hH_sa : star H = H)
  (hanti : H * g + g * H = (2 * m) • (1 : 𝒜))
  (hE_sa : star E = E)
  (hE2 : E * E = U * (H * H) * star U)
  (hEA : E * Aop U H g = Aop U H g * E)
  (hN_sa : star N = N)
  (hN2 : N * N = (2 : ℝ) • (E * E) + (2 * m) • E)
  (hNi₁ : N * Ni = 1) (hNi₂ : Ni * N = 1)
  (hNE : N * E = E * N)
  (hNA : N * Aop U H g = Aop U H g * N)

include hU₁ hU₂ hg_sa hg2 hH_sa hanti hE_sa hE2 hEA hN_sa hN2 hNi₁ hNi₂ hNE hNA

set_option maxHeartbeats 1000000 in
theorem solution : IsUnit (Uprime U H g E Ni) :=
  ⟨⟨Uprime U H g E Ni, star (Uprime U H g E Ni),
        prop61_mul_star_self U H g E N Ni m hU₁ hU₂ hg_sa hg2 hH_sa hanti hE_sa hE2 hEA
          hN_sa hN2 hNi₁ hNi₂,
        prop61_star_mul_self U H g E N Ni m hU₁ hU₂ hg_sa hg2 hH_sa hanti hE_sa hE2 hEA
          hN_sa hN2 hNi₁ hNi₂ hNE hNA⟩,
      rfl⟩
