-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_intrinsic_negative_band_finite_uniform_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:53:31.435527+00:00
-- url     : https://prove2.me/submissions/54c1ceb1-ef39-4dd8-a924-62bc59d210d9

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
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
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (ε : ℝ), 0 < ε →
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) < ⊤ := by
  filter_upwards
    [avram_wave4_04a_bv_actual_finite_source_jump_magnitudes_le_residual X hBV]
    with ω hbudget
  intro T ε hε
  classical
  have hfinite :
      Set.Finite {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω} := by
    let E : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω}
    change E.Finite
    by_contra hnfin
    have hinf : E.Infinite := hnfin
    have hεpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    have hεne : ENNReal.ofReal ε ≠ 0 := ne_of_gt hεpos
    have hresFinite :
        ENNReal.ofReal ((T : ℝ) * X.drift - X.X T ω) ≠ ∞ :=
      ENNReal.ofReal_ne_top
    obtain ⟨n, hn⟩ :=
      ENNReal.exists_nat_mul_gt hεne hresFinite
    obtain ⟨S, hSE, hcard⟩ := hinf.exists_subset_card_eq n
    have hSvalid : ∀ u ∈ S, 0 < u ∧ u ≤ T := by
      intro u hu
      rcases hSE hu with ⟨hu0, huT, _⟩
      exact ⟨hu0, huT⟩
    have hsumLower :
        (∑ u ∈ S, ENNReal.ofReal ε) ≤
        (∑ u ∈ S, ENNReal.ofReal
          (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact ENNReal.ofReal_le_ofReal (hSE hu).2.2
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
            (Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω) :=
          hsumLower
        _ ≤ _ := hsumBudget
    exact (not_le_of_gt hn) hcontr
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω 0 T (Iic (-ε)) measurableSet_Iic]
  let A : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Iic (-ε)}
  have hsub :
      A ⊆ {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        ε ≤ Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω} := by
    intro u hu
    rcases hu with ⟨huPos, _, huT, _, huBand⟩
    change X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ -ε at huBand
    exact ⟨huPos, huT, by linarith⟩
  have hAfin : A.Finite := hfinite.subset hsub
  change ((A.encard : ℝ≥0∞) < ⊤)
  obtain ⟨n, hn⟩ := hAfin.exists_encard_eq_coe
  rw [hn]
  simp
