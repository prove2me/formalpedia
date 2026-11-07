-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_renewal_cdf_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:36:08.966197+00:00
-- url     : https://prove2.me/submissions/1b2eba57-caca-4761-add5-ccd608b190f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (ν : Measure ℝ)
    (hFin : ∀ x : ℝ, 0 ≤ x → ν (Ioc (0 : ℝ) x) < ⊤) :
    MonotoneOn (fun x : ℝ => if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0)
      (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hle : ν (Ioc (0 : ℝ) x) ≤ ν (Ioc (0 : ℝ) y) := by
    apply measure_mono
    intro z hz
    exact ⟨hz.1, le_trans hz.2 hxy⟩
  have hx0 : (0 : ℝ) ≤ x := Set.mem_Ici.mp hx
  have hy0 : (0 : ℝ) ≤ y := Set.mem_Ici.mp hy
  change (if 0 ≤ x then (ν (Ioc (0 : ℝ) x)).toReal else 0) ≤
    (if 0 ≤ y then (ν (Ioc (0 : ℝ) y)).toReal else 0)
  rw [if_pos hx0, if_pos hy0]
  exact ENNReal.toReal_mono (ne_of_lt (hFin y hy0)) hle
