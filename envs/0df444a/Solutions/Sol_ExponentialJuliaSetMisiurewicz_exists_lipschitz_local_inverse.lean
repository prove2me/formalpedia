-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exists_lipschitz_local_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:08.78916+00:00
-- url     : https://prove2.me/submissions/99f103d5-cb5b-4d9c-a216-90a17b305613

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {f : ℂ → ℂ} {a : ℂ}
    (hf : HasStrictDerivAt f (deriv f a) a) (hne : deriv f a ≠ 0) :
    ∃ g : ℂ → ℂ, ∃ C : ℝ≥0, ∃ s : ℝ, 0 < s ∧
      g (f a) = a ∧ LipschitzOnWith C g (ball (f a) s) ∧
      ∀ z ∈ ball (f a) s, f (g z) = z := by
  -- The strict inverse-function theorem supplies an inverse and a local Lipschitz bound.
  let g := hf.localInverse f (deriv f a) a hne
  have hga : g (f a) = a := hf.eventually_left_inverse hne |>.self_of_nhds
  have hg := hf.to_localInverse hne
  obtain ⟨C, V, hV, hCV⟩ := hg.hasStrictFDerivAt.exists_lipschitzOnWith
  obtain ⟨s, hs, hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hV (hf.eventually_right_inverse hne))
  exact ⟨g, C, s, hs, hga, hCV.mono (fun z hz => (hsub hz).1),
    fun z hz => (hsub hz).2⟩
end ExponentialJuliaSetMisiurewicz
