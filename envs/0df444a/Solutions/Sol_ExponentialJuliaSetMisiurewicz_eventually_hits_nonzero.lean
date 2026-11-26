-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventually_hits_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:31.685381+00:00
-- url     : https://prove2.me/submissions/4cf456b4-6211-49f6-9015-1f23f910aac0

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {U : Set ℂ} (hU : IsOpen U) (hUne : U.Nonempty)
    {w : ℂ} (hw : w ≠ 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z ∈ U, expIterate n z = w := by
  obtain ⟨N, hN⟩ := eventually_covers_compact hU hUne
    (isCompact_singleton (x := w)) (by simpa using hw.symm)
  exact ⟨N, fun n hn => hN n hn (Set.mem_singleton w)⟩
end ExponentialJuliaSetMisiurewicz
