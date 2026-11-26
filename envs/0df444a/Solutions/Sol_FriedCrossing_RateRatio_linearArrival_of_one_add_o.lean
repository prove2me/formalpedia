-- Prove2me | solution 1 for FriedCrossing.RateRatio.linearArrival_of_one_add_o
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:09:41.057288+00:00
-- url     : https://prove2.me/submissions/b3adffbc-873c-4ada-ad4f-49c85f52f25e

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
import Theorems.Thm_FriedCrossing_RateRatio_eventually_ne_nhdsNE

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.RateRatio
namespace FriedCrossing.RateRatio
theorem _root_.solution {f e : ℝ → ℝ} {c σ : ℝ}
    (hf : ∀ τ, f τ = c * (τ - σ) * (1 + e τ)) (he : Tendsto e (𝓝[≠] σ) (𝓝 0)) :
    LinearArrival f c σ := by
  have h : Tendsto (fun τ => c * (1 + e τ)) (𝓝[≠] σ) (𝓝 (c * (1 + 0))) :=
    (tendsto_const_nhds.add he).const_mul c
  rw [add_zero, mul_one] at h
  refine h.congr' ((eventually_ne_nhdsNE σ).mono fun τ hτ => ?_)
  have hne : τ - σ ≠ 0 := sub_ne_zero.mpr hτ
  change c * (1 + e τ) = f τ / (τ - σ)
  rw [hf τ]
  field_simp
end FriedCrossing.RateRatio
