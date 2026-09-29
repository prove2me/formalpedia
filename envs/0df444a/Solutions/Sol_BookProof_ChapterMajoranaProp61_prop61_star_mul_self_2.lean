-- Prove2me | solution 2 for BookProof.ChapterMajoranaProp61.prop61_star_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T06:21:27.98291+00:00
-- url     : https://prove2.me/submissions/515c1c18-543a-421e-b406-ae1d19282b5b

-- Generated from ChapterMajoranaProp61.lean — solution of BookProof.ChapterMajoranaProp61.prop61_star_mul_self
import Mathlib
import Definitions.Def_ChapterMajoranaProp61
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
set_option maxHeartbeats 2000000 in
-- the proof below is a large finite computation; the default heartbeat budget
-- is not enough to elaborate it
theorem solution :
    star (Uprime U H g E Ni) * Uprime U H g E Ni = 1 := by

  -- By the properties of the adjoint and the given hypotheses, we can simplify the expression.
  have h_simp : (E + star (Aop U H g)) * (E + Aop U H g) = N * N := by
    simp_all only [Aop, star_mul, star_star, mul_add, add_mul]
    simp_all only [← eq_sub_iff_add_eq', ← mul_assoc]
    simp_all only [mul_assoc, mul_sub, Algebra.mul_smul_comm, mul_one, sub_mul,
      Algebra.smul_mul_assoc, one_mul, sub_sub_cancel]
    simp only [two_smul, add_assoc, add_sub_assoc, left_eq_add]
    abel1
  -- By the properties of the adjoint and the given hypotheses, we can simplify the expression
  -- further.
  have h_simp' : star Ni = Ni := by
    have h_star_Ni : star Ni * N = 1 := by
      rw [ ← star_one, ← hNi₁, star_mul, hN_sa ]
    apply_fun ( · * Ni ) at h_star_Ni; simp_all [ mul_assoc ]
  have h_simp'' : Ni * (E + star (Aop U H g)) = (E + star (Aop U H g)) * Ni := by
    have h_simp'' : Ni * E = E * Ni := by
      apply_fun (fun x => Ni * x) at hNE; simp_all [ mul_assoc ]
      grind
    have h_simp''' : Ni * star (Aop U H g) = star (Aop U H g) * Ni := by
      have h_simp''' : N * star (Aop U H g) = star (Aop U H g) * N := by
        apply_fun star at hNA; simp_all [ mul_assoc, star_mul ]
      apply_fun (fun x => Ni * x) at h_simp'''
      grind
    simp_all [ mul_add, add_mul ]
  convert congr_arg ( fun x => Ni * Ni * x ) h_simp using 1
  · simp [ Uprime, mul_assoc, h_simp' ]
    simp [ ← mul_assoc, hE_sa, h_simp'' ]
  · grind
