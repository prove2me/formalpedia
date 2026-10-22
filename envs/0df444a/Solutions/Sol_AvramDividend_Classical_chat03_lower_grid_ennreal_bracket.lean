-- Prove2me | solution 1 for AvramDividend.Classical.chat03_lower_grid_ennreal_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:44:15.022004+00:00
-- url     : https://prove2.me/submissions/62afd3cf-d353-4dcc-90b4-cbc9173a42c7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_mesh_approximation
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
For every sufficiently fine mesh, the actual ENNReal lower grid infimum
is finite and approaches the strict continuous lower-passage infimum
from above.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ) (τ : ℝ≥0)
    (hτ : IsGLB {t : ℝ≥0 | X.X t ω < lower} τ)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ h : ℝ≥0,
      0 < h → h < δ →
      (τ : ℝ≥0∞) ≤
        (⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * h) ω < lower then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) ∧
      (⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * h) ω < lower then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) < ((τ + ε : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨δ, hδ, hgrid⟩ :=
    chat03_strict_lower_exit_mesh_approximation X ω lower τ hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨k, _, hkhi, hkCross⟩ := hgrid h hh hhd
  constructor
  · refine le_iInf fun j => ?_
    split_ifs with hj
    · exact ENNReal.coe_le_coe.mpr (hτ.1 hj)
    · exact le_top
  · calc
      (⨅ j : ℕ,
        if X.X ((j : ℝ≥0) * h) ω < lower then
          (((j : ℝ≥0) * h) : ℝ≥0∞)
        else ∞) ≤
          (if X.X ((k : ℝ≥0) * h) ω < lower then
            (((k : ℝ≥0) * h) : ℝ≥0∞)
          else ∞) := iInf_le _ k
      _ = (((k : ℝ≥0) * h) : ℝ≥0∞) := if_pos hkCross
      _ < ((τ + ε : ℝ≥0) : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.mpr hkhi
