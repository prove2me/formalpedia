-- Prove2me | solution 1 for AvramDividend.Classical.esscher_levy_positive_root_derivative_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:57:46.213121+00:00
-- url     : https://prove2.me/submissions/5c5fbabb-e0b8-4284-8fd1-57ece21d5c1e

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The genuine shifted Lévy secant bounds the derivative at a positive root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi m : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hderiv : HasDerivAt X.ψ m phi) :
    q / phi ≤ m ∧ 0 < m := by
  have hslope :
      Tendsto (fun h : ℝ => h⁻¹ • (X.ψ (phi + h) - X.ψ phi))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds m) :=
    hderiv.tendsto_slope_zero_right
  have hbound : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      q / phi ≤ h⁻¹ • (X.ψ (phi + h) - X.ψ phi) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hsec := levy_psi_root_shifted_increment_lower
      X q phi h hq hphi hh hroot
    have hquot : q / phi ≤ (X.ψ (phi + h) - q) / h :=
      (le_div_iff₀ hh).2 hsec
    rw [hroot]
    change q / phi ≤ h⁻¹ * (X.ψ (phi + h) - q)
    convert hquot using 1 <;> ring
  have hm : q / phi ≤ m := ge_of_tendsto hslope hbound
  exact ⟨hm, lt_of_lt_of_le (div_pos hq hphi) hm⟩
