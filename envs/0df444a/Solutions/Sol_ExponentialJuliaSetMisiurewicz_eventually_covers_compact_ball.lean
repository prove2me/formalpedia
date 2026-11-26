-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.eventually_covers_compact_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:32.733165+00:00
-- url     : https://prove2.me/submissions/04bba1d9-eec6-467a-9cdd-76bf4c8f4791

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_eventually_covers_compact

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {c : ℂ} {r : ℝ} (hr : 0 < r)
    {K : Set ℂ} (hK : IsCompact K) (hK0 : (0 : ℂ) ∉ K) :
    ∃ N : ℕ, ∀ n ≥ N, K ⊆ expIterate n '' ball c r :=
  eventually_covers_compact isOpen_ball ⟨c, mem_ball_self hr⟩ hK hK0
end ExponentialJuliaSetMisiurewicz
