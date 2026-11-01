-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_truncated_negative_jump_times_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:29:42.597539+00:00
-- url     : https://prove2.me/submissions/883fc2fc-ea31-4c2c-82e2-90638a1410bf

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᵐ ω ∂P,
      Set.Finite {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω} := by
  filter_upwards
    [avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual X hBV]
    with ω hbudget
  classical
  let A : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
    ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω}
  change A.Finite
  by_contra hnfin
  have hinf : A.Infinite := hnfin
  have hεpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hεne : ENNReal.ofReal ε ≠ 0 := ne_of_gt hεpos
  have hresFinite :
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  obtain ⟨n, hn⟩ :=
    ENNReal.exists_nat_mul_gt hεne hresFinite
  obtain ⟨S, hSA, hcard⟩ := hinf.exists_subset_card_eq n
  have hSvalid : ∀ u ∈ S, 0 < u ∧ u ≤ T := by
    intro u hu
    rcases hSA hu with ⟨hu0, huT, _⟩
    exact ⟨hu0, huT⟩
  have hsumLower :
      (∑ u ∈ S, ENNReal.ofReal ε) ≤
      (∑ u ∈ S, ENNReal.ofReal
        (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)) := by
    apply Finset.sum_le_sum
    intro u hu
    exact ENNReal.ofReal_le_ofReal (hSA hu).2.2
  have hsumConst :
      (∑ u ∈ S, ENNReal.ofReal ε) =
        (n : ℝ≥0∞) * ENNReal.ofReal ε := by
    simp [hcard, nsmul_eq_mul]
  have hsumBudget := hbudget T S hSvalid
  have hcontr :
      (n : ℝ≥0∞) * ENNReal.ofReal ε ≤
      ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) := by
    calc
      _ = ∑ u ∈ S, ENNReal.ofReal ε := hsumConst.symm
      _ ≤ ∑ u ∈ S, ENNReal.ofReal
          (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω) := hsumLower
      _ ≤ _ := hsumBudget
  exact (not_le_of_gt hn) hcontr
