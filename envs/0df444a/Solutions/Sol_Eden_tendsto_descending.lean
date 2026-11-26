-- Prove2me | solution 1 for Eden.tendsto_descending
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:16.027894+00:00
-- url     : https://prove2.me/submissions/11ced558-8e0d-47e0-b750-c0b0e075761f

import Definitions.Def_Eden_OrderedStationarySpectrum
import Mathlib.Data.Multiset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_Eden_Sorting
import Theorems.Thm_Eden_continuous_descending

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {n : ℕ} {f : ℝ → Fin n → ℝ} {a : Fin n → ℝ}
    (h : ∀ i, Tendsto (fun t => f t i) atTop (𝓝 (a i))) :
    Tendsto (fun t => descending (f t)) atTop (𝓝 (descending a)) :=
  (continuous_descending n).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)
end Eden
