-- Prove2me | solution 1 for BookProof.ChapterRadialLaplacian.deriv_sqrt_comp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:40:23.41887+00:00
-- url     : https://prove2.me/submissions/6a3470e2-bf1b-45fa-9e58-25803012762f

-- Generated from ChapterRadialLaplacian.lean — solution of BookProof.ChapterRadialLaplacian.deriv_sqrt_comp
import Mathlib
import Definitions.Def_ChapterRadialLaplacian
import Theorems.Thm_BookProof_ChapterRadialLaplacian_diffAt_deriv_of_contDiffAt_two
open BookProof.ChapterRadialLaplacian




open Filter Laplacian InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContDiffAt ℝ 2 g r) :
    deriv (fun q => g (Real.sqrt q)) (r ^ 2) = deriv g r * (1 / (2 * r)) ∧
    deriv (deriv fun q => g (Real.sqrt q)) (r ^ 2)
      = deriv (deriv g) r * (1 / (2 * r)) * (1 / (2 * r)) + deriv g r * (-(1 / (4 * r ^ 3))) := by

  have hr' : r ≠ 0 := ne_of_gt hr
  have hsq : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
  have hgev : ∀ᶠ s in nhds r, DifferentiableAt ℝ g s := by
    filter_upwards [hg.eventually (by simp)] with s hs using hs.differentiableAt (by norm_num)
  have hcont' : Tendsto Real.sqrt (nhds (r ^ 2)) (nhds r) := by
    have h := (Real.continuous_sqrt).continuousAt (x := r ^ 2)
    rwa [ContinuousAt, hsq] at h
  have hqev : ∀ᶠ q in nhds (r ^ 2), DifferentiableAt ℝ g (Real.sqrt q) := hcont'.eventually hgev
  have hpos : ∀ᶠ q in nhds (r ^ 2), q ≠ 0 := isOpen_ne.mem_nhds (pow_ne_zero 2 hr')
  have hderiv : (deriv fun q => g (Real.sqrt q)) =ᶠ[nhds (r ^ 2)]
      fun q => deriv g (Real.sqrt q) * (1 / (2 * Real.sqrt q)) := by
    filter_upwards [hqev, hpos] with q hq hq0
    exact (hq.hasDerivAt.comp q (Real.hasDerivAt_sqrt hq0)).deriv
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * r)) (r ^ 2) := by
    have h := Real.hasDerivAt_sqrt (x := r ^ 2) (pow_ne_zero 2 hr')
    rwa [hsq] at h
  constructor
  · have h := hderiv.self_of_nhds
    simpa [hsq] using h
  · have h1 : HasDerivAt (fun q => deriv g (Real.sqrt q))
        (deriv (deriv g) r * (1 / (2 * r))) (r ^ 2) := by
      have hd : HasDerivAt (deriv g) (deriv (deriv g) r) (Real.sqrt (r ^ 2)) := by
        rw [hsq]; exact (diffAt_deriv_of_contDiffAt_two hg).hasDerivAt
      exact hd.comp (r ^ 2) hs
    have hsinv : HasDerivAt (fun q : ℝ => (Real.sqrt q)⁻¹) (-(1 / (2 * r)) / r ^ 2) (r ^ 2) := by
      have h := hs.inv (by rw [hsq]; exact hr')
      rwa [hsq] at h
    have h2 : HasDerivAt (fun q : ℝ => 1 / (2 * Real.sqrt q)) (-(1 / (4 * r ^ 3))) (r ^ 2) := by
      have h := hsinv.const_mul (1 / 2 : ℝ)
      have hfun : (fun q : ℝ => (1 / 2 : ℝ) * (Real.sqrt q)⁻¹)
          = fun q : ℝ => 1 / (2 * Real.sqrt q) := by
        funext q; rw [one_div, one_div, mul_inv]
      rw [hfun] at h
      convert h using 1 <;> (first | rfl | (field_simp; ring))
    have hprod : HasDerivAt (fun q : ℝ => deriv g (Real.sqrt q) * (1 / (2 * Real.sqrt q)))
        (deriv (deriv g) r * (1 / (2 * r)) * (1 / (2 * Real.sqrt (r ^ 2)))
          + deriv g (Real.sqrt (r ^ 2)) * (-(1 / (4 * r ^ 3)))) (r ^ 2) := h1.mul h2
    rw [hderiv.deriv_eq, hprod.deriv, hsq]
