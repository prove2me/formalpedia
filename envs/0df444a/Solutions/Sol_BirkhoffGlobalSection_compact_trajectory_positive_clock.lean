-- Prove2me | solution 1 for BirkhoffGlobalSection.compact_trajectory_positive_clock
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:25:40.902988+00:00
-- url     : https://prove2.me/submissions/7678595e-f1d7-429c-a24b-1e47a67ab4ed

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

import Theorems.Thm_TimeChange_compact_positive_rate_bounds
import Theorems.Thm_TimeChange_complete_positive_clock
open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {S : Type*} [TopologicalSpace S]
    (K : Set S) (hK : IsCompact K) (r : S → ℝ) (hr : ContinuousOn r K)
    (hpos : ∀ x ∈ K, 0 < r x) (y : ℝ → S) (hy : Continuous y)
    (hyK : ∀ t, y t ∈ K) :
    ∃ clock : ℝ ≃o ℝ,
      clock 0 = 0 ∧ (∀ t, HasDerivAt clock (r (y t)) t) ∧
      (∀ t, clock t = ∫ s in (0 : ℝ)..t, r (y s)) := by
  obtain ⟨m, M, hm, hbounds⟩ :=
    TimeChange.compact_positive_rate_bounds K hK ⟨y 0, hyK 0⟩ r hr hpos
  obtain ⟨clock, hz, hd, _, hi⟩ := TimeChange.complete_positive_clock (fun t => r (y t))
    (hr.comp_continuous hy hyK) m hm (fun t => (hbounds (y t) (hyK t)).1)
  exact ⟨clock, hz, hd, hi⟩
