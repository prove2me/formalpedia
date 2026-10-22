-- Prove2me | solution 1 for FreeSamples.Revenue.lemma_1_i
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:12:05.965969+00:00
-- url     : https://prove2.me/submissions/8d41e662-4518-4251-9e7c-7ba9189d4870

import Mathlib
import Definitions.Def_FreeSamples_Revenue_Setting
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal
open FreeSamples.Revenue

theorem solution (p : Params) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => p.buyerVar s) (-(p.buyerVar t) ^ 2 / p.σsq) (Set.Ici t) t := by
  have hv := p.σ₀sq_pos
  have hs := p.σsq_pos
  have hden : p.σ₀sq * t + p.σsq ≠ 0 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => p.σ₀sq * s + p.σsq) p.σ₀sq t := by
    simpa using ((hasDerivAt_id t).const_mul p.σ₀sq).add_const p.σsq
  have h2 := (hasDerivAt_const t (p.σ₀sq * p.σsq)).div h1 hden
  have hf : (fun s : ℝ => p.buyerVar s) = fun s => p.σ₀sq * p.σsq / (p.σ₀sq * s + p.σsq) := by
    funext s; rfl
  have h3 : HasDerivAt (fun s : ℝ => p.buyerVar s)
      (-(p.buyerVar t) ^ 2 / p.σsq) t := by
    rw [hf]
    refine h2.congr_deriv ?_
    unfold Params.buyerVar postVar
    field_simp
    ring
  exact h3.hasDerivWithinAt
