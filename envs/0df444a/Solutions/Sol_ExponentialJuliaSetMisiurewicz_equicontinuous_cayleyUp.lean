-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.equicontinuous_cayleyUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:57.780446+00:00
-- url     : https://prove2.me/submissions/ad7d5e6d-4292-4e38-99af-f6aa826e5baf

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_equicontinuous_of_bounded
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_norm_cayleyUp_lt_one
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_differentiableOn_cayleyUp

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    {T : Set ℕ} (hT : ∀ n ∈ T, ∀ z ∈ ball c (2 * ρ), 0 < (expIterate n z).im)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ n : T, ∀ x ∈ ball c ρ, ∀ y ∈ ball c ρ, ‖x - y‖ < δ →
      ‖(expIterate n.1 x - Complex.I) / (expIterate n.1 x + Complex.I)
        - (expIterate n.1 y - Complex.I) / (expIterate n.1 y + Complex.I)‖ < ε := by
  refine equicontinuous_of_bounded (F := fun n : T => fun w =>
      (expIterate n.1 w - Complex.I) / (expIterate n.1 w + Complex.I)) hρ
    (fun n => differentiableOn_cayleyUp (fun z hz => hT n.1 n.2 z hz))
    (fun n w hw => le_of_lt (norm_cayleyUp_lt_one (hT n.1 n.2 w hw))) hε
end ExponentialJuliaSetMisiurewicz
