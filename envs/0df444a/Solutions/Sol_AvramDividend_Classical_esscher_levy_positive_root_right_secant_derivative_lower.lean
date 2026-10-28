-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_positive_root_right_secant_derivative_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T20:03:37.159436+00:00
-- url     : https://prove2.me/submissions/f9d96623-af15-493b-ad8d-5c7255ed3b81

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Field.Basic
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- A finite positive Esscher-root right slope is strictly positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ m : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q)
    (hsec : Tendsto
      (fun h : ℝ => (X.ψ (φ + h) - X.ψ φ) / h)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m)) :
    q / φ ≤ m ∧ 0 < m := by
  have he :
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        q / φ ≤ (X.ψ (φ + h) - X.ψ φ) / h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hx := levy_psi_root_shifted_increment_lower
      X q φ h hq hφ hh hroot
    apply (le_div_iff₀ hh).2
    simpa only [hroot] using hx
  have hm : q / φ ≤ m := ge_of_tendsto hsec he
  exact ⟨hm, lt_of_lt_of_le (div_pos hq hφ) hm⟩
