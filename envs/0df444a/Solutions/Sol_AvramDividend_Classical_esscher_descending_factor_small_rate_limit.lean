-- Prove2me | solution 1 for AvramDividend.Classical.esscher_descending_factor_small_rate_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:52:55.098163+00:00
-- url     : https://prove2.me/submissions/b462e5cf-3815-49e9-9013-02e10ec3c54e

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.NhdsWithin
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- Analytic p-down-to-zero interface for an all-beta finite-rate descending factor. -/
theorem solution
    (root D : ℝ → ℝ) (gβ m β : ℝ)
    (hm : 0 < m) (hβ : 0 < β) (hgβ : 0 < gβ)
    (hroot0 : Tendsto root (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hratio : Tendsto (fun p : ℝ => p / root p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m))
    (hfactor :
      D =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun p : ℝ => (p / root p) * ((root p - β) / (p - gβ)))) :
    Tendsto D (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (m * β / gβ)) := by
  have hpzero : Tendsto (fun p : ℝ => p)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun p : ℝ => root p - β)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 - β)) :=
    hroot0.sub tendsto_const_nhds
  have hden : Tendsto (fun p : ℝ => p - gβ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 - gβ)) :=
    hpzero.sub tendsto_const_nhds
  have hden_ne : (0 : ℝ) - gβ ≠ 0 := by
    linarith
  have hfrac :
      Tendsto (fun p : ℝ => (root p - β) / (p - gβ))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds ((0 - β) / (0 - gβ))) := by
    convert hnum.div hden hden_ne using 1
    ext p
    simp only [Pi.div_apply]
  have hprod := hratio.mul hfrac
  have hlim : Tendsto
      (fun p : ℝ => (p / root p) * ((root p - β) / (p - gβ)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (m * β / gβ)) := by
    simpa only [zero_sub, neg_div_neg_eq, mul_div_assoc] using hprod
  exact hlim.congr' hfactor.symm
