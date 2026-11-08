-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn13_original_strict_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:26:47.073197+00:00
-- url     : https://prove2.me/submissions/2f27abfe-6aab-4334-8d56-06e2b6fe9a2f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_cadlag_mark_weight_lintegral_borel
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn13_original_magnitude_ofReal_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The product of actual original strict negative jump factors is a Borel
function of the adapted coordinate path through its finite magnitude sum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    let L : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      (1 - Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Measurable W := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let ε : ℝ := 1 / ((k : ℝ) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let W : Ω → ℝ := fun ω => ∏ u ∈ S ω,
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let M : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (-y)
  let g : ℝ → ℝ≥0∞ := fun y => if y < -ε then φ y else 0
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hg : Measurable g := by
    exact Measurable.ite
      (measurableSet_lt measurable_id measurable_const) hφ measurable_const
  obtain ⟨F, hF, hFpath⟩ :=
    avram_bv_jump8_cadlag_mark_weight_lintegral_borel T g hg
  have hc (t : ℝ≥0) : Measurable (fun ω : Ω => X.X t ω) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hPath : Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) :=
    (@measurable_pi_iff Ω ℝ≥0 (fun _ : ℝ≥0 => ℝ)
      mΩ (fun _ => inferInstance) _).2 hc
  have hMeas : Measurable (fun ω : Ω =>
      Real.exp (-(F (fun t : ℝ≥0 => X.X t ω)).toReal)) :=
    Real.continuous_exp.measurable.comp
      ((ENNReal.measurable_toReal.comp (hF.comp hPath)).neg)
  have hReal (ω : Ω) : 0 ≤ M ω ∧
      (∑ u ∈ S ω, φ (X.X u ω - Function.leftLim
        (fun v : ℝ≥0 => X.X v ω) u)) = ENNReal.ofReal (M ω) := by
    simpa only [T, S, M, φ] using
      (avram_bv_jump8_turn13_original_magnitude_ofReal_sum X hX hBV k n ω)
  have hEq (ω : Ω) : F (fun t : ℝ≥0 => X.X t ω) =
      ENNReal.ofReal (M ω) := by
    let μ : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u))
    have hsum : (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -ε then φ p.2 else 0 ∂μ) =
        ∑ u ∈ S ω, φ (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) := by
      simpa only [T, ε, φ, S, μ] using
        (avram_redux20_original_strict_marked_borel_weight_finite_sum
          X ω T k φ hφ)
    calc
      F (fun t : ℝ≥0 => X.X t ω) =
          ∫⁻ p : ℝ≥0 × ℝ, if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂μ := by
            simpa only [μ] using hFpath _ (X.rightCont ω) (X.leftLim ω)
      _ = ∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -ε then φ p.2 else 0 ∂μ := by
            apply lintegral_congr
            intro p
            by_cases ht : 0 < p.1 ∧ p.1 ≤ T
            · by_cases hb : p.2 < -ε
              · simp [g, ht, hb]
              · simp [g, ht, hb]
            · have hnot : ¬ (0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -ε) := by
                intro hp
                exact ht ⟨hp.1, hp.2.1⟩
              simp [ht, hnot]
      _ = ∑ u ∈ S ω, φ (X.X u ω - Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u) := hsum
      _ = ENNReal.ofReal (M ω) := (hReal ω).2
  have hProd (ω : Ω) : W ω = Real.exp (-M ω) := by
    simp only [W, M, ← Real.exp_sum, Finset.sum_neg_distrib, neg_neg]
  change Measurable W
  convert hMeas using 1
  funext ω
  rw [hEq ω, ENNReal.toReal_ofReal (hReal ω).1]
  exact hProd ω
