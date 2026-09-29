-- Prove2me | solution 1 for ConvexOptimization.self_concordant_add_linear
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:34:38.202222+00:00
-- url     : https://prove2.me/submissions/98b840a8-cc94-4377-aa47-cda78e6ddeb2

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsSelfConcordantOn Ω f)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    IsSelfConcordantOn Ω (fun x => f x + ⟪c, x⟫ + r) := by
  obtain ⟨hconv, hcd, hineq⟩ := hf
  have hΩc : Convex ℝ Ω := hconv.1
  -- The added affine part is convex and `C^∞`.
  have hlinConv : ConvexOn ℝ Ω (fun z : EuclideanSpace ℝ (Fin n) => ⟪c, z⟫) := by
    refine ⟨hΩc, fun p _ q _ a b _ _ _ => ?_⟩
    simp only [inner_add_right, real_inner_smul_right, smul_eq_mul]
    exact le_rfl
  have hlinCd : ContDiffOn ℝ 3 (fun z : EuclideanSpace ℝ (Fin n) => ⟪c, z⟫) Ω :=
    ((innerSL ℝ c).contDiff).contDiffOn
  refine ⟨(hconv.add hlinConv).add (convexOn_const r hΩc),
    (hcd.add hlinCd).add contDiffOn_const, ?_⟩
  intro x hx v
  -- Along the line `t ↦ x + t • v` the added part is affine in `t`.
  have hℓsmooth : ContDiff ℝ (3 : ℕ) (fun t : ℝ => x + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hφ : ContDiffAt ℝ (3 : ℕ) (fun t : ℝ => f (x + t • v)) 0 := by
    have hfx : ContDiffAt ℝ (3 : ℕ) f ((fun t : ℝ => x + t • v) 0) := by
      simpa using hcd.contDiffAt (hΩo.mem_nhds hx)
    simpa [Function.comp_def] using hfx.comp (0 : ℝ) hℓsmooth.contDiffAt
  set A : ℝ := ⟪c, x⟫ + r with hA
  set B : ℝ := ⟪c, v⟫ with hB
  have hqeq : (fun t : ℝ => ⟪c, x + t • v⟫ + r) = fun t : ℝ => A + t * B := by
    funext t
    rw [hA, hB]
    simp only [inner_add_right, real_inner_smul_right]
    ring
  have hq : ContDiffAt ℝ (3 : ℕ) (fun t : ℝ => ⟪c, x + t • v⟫ + r) 0 := by
    rw [hqeq]
    exact (contDiff_const.add (contDiff_id.mul contDiff_const)).contDiffAt
  -- An affine function of `t` has vanishing second and third derivatives.
  have hderiv1 : deriv (fun t : ℝ => A + t * B) = fun _ => B := by
    funext t
    exact (by simpa using ((hasDerivAt_id t).mul_const B).const_add A :
      HasDerivAt (fun t : ℝ => A + t * B) B t).deriv
  have hq2 : iteratedDeriv 2 (fun t : ℝ => ⟪c, x + t • v⟫ + r) 0 = 0 := by
    rw [hqeq, show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv1]
    simp
  have hq3 : iteratedDeriv 3 (fun t : ℝ => ⟪c, x + t • v⟫ + r) 0 = 0 := by
    rw [hqeq, show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hderiv1]
    simp
  -- Split the restricted function and transport the self-concordance inequality.
  have hsplit : (fun t : ℝ => f (x + t • v) + ⟪c, x + t • v⟫ + r)
      = fun t : ℝ => f (x + t • v) + (⟪c, x + t • v⟫ + r) := by
    funext t; ring
  have e3 : iteratedDeriv 3 (fun t : ℝ => f (x + t • v) + ⟪c, x + t • v⟫ + r) 0
      = iteratedDeriv 3 (fun t : ℝ => f (x + t • v)) 0 := by
    rw [hsplit, iteratedDeriv_fun_add hφ hq, hq3, add_zero]
  have e2 : iteratedDeriv 2 (fun t : ℝ => f (x + t • v) + ⟪c, x + t • v⟫ + r) 0
      = iteratedDeriv 2 (fun t : ℝ => f (x + t • v)) 0 := by
    rw [hsplit, iteratedDeriv_fun_add (hφ.of_le (by norm_num)) (hq.of_le (by norm_num)),
      hq2, add_zero]
  rw [e2, e3]
  exact hineq x hx v
