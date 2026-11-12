-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb71_covariance_limit_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:11:49.03393+00:00
-- url     : https://prove2.me/submissions/921adac6-0712-415b-8b08-00620598422b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology

/-- Diagonal second moments and cross moments with the same limit give zero
    two-grid squared-difference energy. -/
theorem solution
    (a : ℕ → ℝ) (b : ℕ × ℕ → ℝ) (v : ℝ)
    (ha : Tendsto a atTop (𝓝 v))
    (hb : Tendsto b atTop (𝓝 v)) :
    Tendsto (fun nm : ℕ × ℕ => a nm.1 + a nm.2 - 2 * b nm)
      atTop (𝓝 (0 : ℝ)) := by
  have hfst : Tendsto (fun nm : ℕ × ℕ => nm.1) atTop atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_fst (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hsnd : Tendsto (fun nm : ℕ × ℕ => nm.2) atTop atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hsum : Tendsto (fun nm : ℕ × ℕ => a nm.1 + a nm.2)
      atTop (𝓝 (v + v)) := (ha.comp hfst).add (ha.comp hsnd)
  have hmul : Tendsto (fun nm : ℕ × ℕ => (2 : ℝ) * b nm)
      atTop (𝓝 (2 * v)) := tendsto_const_nhds.mul hb
  have hv : v + v - 2 * v = 0 := by ring
  simpa only [hv] using hsum.sub hmul
