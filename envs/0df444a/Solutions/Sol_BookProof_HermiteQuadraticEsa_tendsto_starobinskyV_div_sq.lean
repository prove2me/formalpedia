-- Prove2me | solution 1 for BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:12:55.790571+00:00
-- url     : https://prove2.me/submissions/0d1fec49-b48f-40b0-aa85-06da8b980109

-- Generated from ChapterHermiteQuadraticEsa.lean — theorem BookProof.HermiteQuadraticEsa.tendsto_starobinskyV_div_sq
import Mathlib
import Definitions.Def_ChapterHermiteQuadraticEsa
open BookProof.HermiteQuadraticEsa














open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (M alpha : ℝ) :
    Filter.Tendsto (fun phi : ℝ => starobinskyV M alpha phi / phi ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (M ^ 2 / (24 * alpha))) := by
  set k : ℝ := Real.sqrt (2 / 3) / M with hk
  have hg : ∀ phi : ℝ, starobinskyV M alpha phi / phi ^ 2
      = M ^ 4 / (16 * alpha) * ((1 - Real.exp (-(k * phi))) / phi) ^ 2 := by
    intro phi
    unfold starobinskyV
    rw [hk]
    field_simp
  have hderiv : HasDerivAt (fun phi : ℝ => 1 - Real.exp (-(k * phi))) k 0 := by
    have h1 : HasDerivAt (fun phi : ℝ => -(k * phi)) (-k) 0 := by
      convert hasDerivAt_const_mul (x := (0 : ℝ)) (-k) using 1 <;> first | rfl | (funext phi; ring)
    have h2 := (Real.hasDerivAt_exp (-(k * 0))).comp 0 h1
    simpa using h2.const_sub 1
  have hslope : Filter.Tendsto
      (fun phi : ℝ => (1 - Real.exp (-(k * phi))) / phi) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds k) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hderiv
    refine h.congr fun phi => ?_
    simp [slope_def_field, div_eq_inv_mul, sub_zero]
  have hsq : Filter.Tendsto (fun phi : ℝ => M ^ 4 / (16 * alpha)
      * ((1 - Real.exp (-(k * phi))) / phi) ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (M ^ 4 / (16 * alpha) * k ^ 2)) :=
    ((hslope.pow 2).const_mul _)
  have hval : M ^ 4 / (16 * alpha) * k ^ 2 = M ^ 2 / (24 * alpha) := by
    have hk2 : k ^ 2 = (2 / 3) / M ^ 2 := by
      rw [hk, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    rw [hk2]
    field_simp
    ring
  rw [← hval]
  exact hsq.congr fun phi => (hg phi).symm

#print axioms solution
