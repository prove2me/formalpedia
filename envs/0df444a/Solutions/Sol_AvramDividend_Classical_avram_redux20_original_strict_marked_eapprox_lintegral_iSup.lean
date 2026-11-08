-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux20_original_strict_marked_eapprox_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:18:24.740027+00:00
-- url     : https://prove2.me/submissions/613036ac-bf58-4c7d-92c2-002cc0753421

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_redux20_finite_mark_eapprox_pullback
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! Borel mark losses on the actual strict intrinsic jump measure are simple limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let μ := (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    (⨆ n : ℕ, ∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then MeasureTheory.SimpleFunc.eapprox g n p.2 else 0 ∂μ) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then g p.2 else 0 ∂μ) := by
  classical
  let μ := (Measure.count.restrict {u : ℝ≥0 |
    0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let S : Finset ℝ≥0 :=
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let δ : ℝ≥0 → ℝ := fun u => X.X u ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  have h_n (n : ℕ) :
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
        then MeasureTheory.SimpleFunc.eapprox g n p.2 else 0 ∂μ) =
      ∑ u ∈ S, MeasureTheory.SimpleFunc.eapprox g n (δ u) := by
    have hm : Measurable
        (fun y : ℝ => MeasureTheory.SimpleFunc.eapprox g n y) :=
      (MeasureTheory.SimpleFunc.eapprox g n).measurable
    exact avram_redux20_original_strict_marked_borel_weight_finite_sum
      X ω T k (fun y => MeasureTheory.SimpleFunc.eapprox g n y) hm
  have h_full :
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
        then g p.2 else 0 ∂μ) = ∑ u ∈ S, g (δ u) :=
    avram_redux20_original_strict_marked_borel_weight_finite_sum X ω T k g hg
  change (⨆ n : ℕ, ∫⁻ p : ℝ≥0 × ℝ,
    if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
    then MeasureTheory.SimpleFunc.eapprox g n p.2 else 0 ∂μ) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then g p.2 else 0 ∂μ)
  calc
    (⨆ n : ℕ, ∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then MeasureTheory.SimpleFunc.eapprox g n p.2 else 0 ∂μ) =
        ⨆ n : ℕ, ∑ u ∈ S, MeasureTheory.SimpleFunc.eapprox g n (δ u) := by
          congr 1
          funext n
          exact h_n n
    _ = ∑ u ∈ S, g (δ u) :=
      avram_redux20_finite_mark_eapprox_pullback S δ g hg
    _ = _ := h_full.symm
