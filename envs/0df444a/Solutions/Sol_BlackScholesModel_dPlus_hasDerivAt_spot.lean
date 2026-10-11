-- Prove2me | solution 1 for BlackScholesModel.dPlus_hasDerivAt_spot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T14:09:27.230837+00:00
-- url     : https://prove2.me/submissions/b0f9b724-6eef-4ba0-b965-80fc5bb9197f

import Mathlib
import Definitions.Def_BlackScholesModel_Core

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (S K r σ τ : ℝ)
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    HasDerivAt (fun s => dPlus s K r σ τ)
      (1 / (S * σ * Real.sqrt τ)) S := by
  have hS0 : S ≠ 0 := ne_of_gt hS
  have hK0 : K ≠ 0 := ne_of_gt hK
  have hroot : Real.sqrt τ ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hτ)
  have hden : σ * Real.sqrt τ ≠ 0 :=
    mul_ne_zero (ne_of_gt hσ) hroot
  have hratio : HasDerivAt (fun s : ℝ => s / K) (1 / K) S :=
    (hasDerivAt_id S).div_const K
  have hlog : HasDerivAt (fun s : ℝ => Real.log (s / K))
      ((1 / K) / (S / K)) S :=
    hratio.log (div_ne_zero hS0 hK0)
  have hnum : HasDerivAt
      (fun s : ℝ => Real.log (s / K) + (r + σ ^ 2 / 2) * τ)
      ((1 / K) / (S / K)) S :=
    hlog.add_const _
  have hraw : HasDerivAt
      (fun s : ℝ => (Real.log (s / K) + (r + σ ^ 2 / 2) * τ) /
        (σ * Real.sqrt τ))
      (((1 / K) / (S / K)) / (σ * Real.sqrt τ)) S :=
    hnum.div_const _
  have hcoeff :
      ((1 / K) / (S / K)) / (σ * Real.sqrt τ) =
      1 / (S * σ * Real.sqrt τ) := by
    field_simp [hS0, hK0, hden]
    try ring
  rw [hcoeff] at hraw
  simpa only [dPlus] using hraw