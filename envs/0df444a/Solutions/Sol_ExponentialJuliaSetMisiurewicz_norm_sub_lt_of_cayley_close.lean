-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.norm_sub_lt_of_cayley_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:19.313708+00:00
-- url     : https://prove2.me/submissions/a4a22f0d-413f-4dc0-86af-18e44d6a204e

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_cayleyUp_inv
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_cayleyUp_ne_one

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution
    {p : ℂ} (hp : p + Complex.I ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ w : ℂ, w + Complex.I ≠ 0 →
      ‖(w - Complex.I) / (w + Complex.I) - (p - Complex.I) / (p + Complex.I)‖ < ε →
      ‖w - p‖ < η := by
  have hne : (1 : ℂ) - (p - Complex.I) / (p + Complex.I) ≠ 0 := by
    intro hc
    refine cayleyUp_ne_one hp ?_
    linear_combination -hc
  have hcont : ContinuousAt (fun u : ℂ => Complex.I * (1 + u) / (1 - u))
      ((p - Complex.I) / (p + Complex.I)) := by
    refine ContinuousAt.div ?_ ?_ hne
    · exact (continuous_const.mul (continuous_const.add continuous_id)).continuousAt
    · exact (continuous_const.sub continuous_id).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨ε, hε, hball⟩ := hcont η hη
  refine ⟨ε, hε, fun w hw hclose => ?_⟩
  have hd : dist ((w - Complex.I) / (w + Complex.I))
      ((p - Complex.I) / (p + Complex.I)) < ε := by
    rwa [dist_eq_norm]
  have h1 := hball hd
  rw [dist_eq_norm, cayleyUp_inv hw, cayleyUp_inv hp] at h1
  exact h1
end ExponentialJuliaSetMisiurewicz
