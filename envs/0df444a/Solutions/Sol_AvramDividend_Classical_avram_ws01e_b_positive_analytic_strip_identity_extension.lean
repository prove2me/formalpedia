-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_positive_analytic_strip_identity_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:31:20.66572+00:00
-- url     : https://prove2.me/submissions/365398e6-1bfc-46f7-ad00-2cfc3a79a5f4

import Mathlib
import Mathlib.Analysis.Analytic.Uniqueness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open scoped Topology

theorem solution
    (f g : ℝ → ℝ) (b : ℝ) (hb : 0 < b)
    (hf : AnalyticOnNhd ℝ f (Ioi (0 : ℝ)))
    (hg : AnalyticOnNhd ℝ g (Ioi (0 : ℝ)))
    (hstrip : ∀ β : ℝ, 0 < β → β < b → f β = g β) :
    ∀ β : ℝ, 0 < β → f β = g β := by
  have hmid : b / 2 ∈ Ioo (0 : ℝ) b := by
    change 0 < b / 2 ∧ b / 2 < b
    constructor <;> linarith
  have hlocal : f =ᶠ[𝓝 (b / 2)] g := by
    filter_upwards [isOpen_Ioo.mem_nhds hmid] with β hβ
    exact hstrip β hβ.1 hβ.2
  have hglobal : EqOn f g (Ioi (0 : ℝ)) :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_Ioi
      (by change 0 < b / 2; linarith) hlocal
  intro β hβ
  exact hglobal hβ
