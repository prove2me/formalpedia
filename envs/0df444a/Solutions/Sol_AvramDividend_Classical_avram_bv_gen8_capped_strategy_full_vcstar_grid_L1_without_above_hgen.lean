-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_capped_strategy_full_vcstar_grid_L1_without_above_hgen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:37:32.658243+00:00
-- url     : https://prove2.me/submissions/647bcd7c-22d1-4721-8648-22bf6302ef5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact capped BV generator-grid L1 certificate without any above-cap HJB bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ cstar W)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (cstar W) D)
    (u : ℕ → ℕ → ℝ≥0) :
    let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      let Z : ℝ := Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator (vcstar W) Z - q * vcstar W Z) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P := by
  let H : ℕ → ℕ → Ω → ℝ := fun n i ω =>
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change ∀ n, (∀ ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0) ∧
    Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) P
  have hcell : ∀ n i ω, H n i ω = 0 := by
    intro n i ω
    let Z : ℝ := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    change (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator (vcstar W) Z - q * vcstar W Z) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0) = 0
    by_cases hact : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧ 0 < Z
    · have hb := avram_bv_gen8_original_postright_reserve_leftLim_closed_cap
        X x (cstar W) hxc D hD ω (u n i) (Or.inr hact.1)
      have hle : Z ≤ (cstar W).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hc)).mp hb.2
      have hg : X.generator (vcstar W) Z - q * vcstar W Z = 0 := by
        by_cases hlt : Z < (cstar W).toReal
        · exact (generator_vcstar_eq_zero_bv_unconditional_20261026
            X hX hBV q hq W hW hcpos Z ⟨hact.2, hlt⟩).2
        · have heq : Z = (cstar W).toReal :=
            le_antisymm hle (le_of_not_gt hlt)
          rw [heq]
          exact (avram_wave4_p3_vcstar_generator_eq_zero_at_positive_cap_without_above_control
            X hX q hq W hW hc hcpos (Or.inr (Or.inl hBV))).2
      rw [if_pos hact, hg]
      ring
    · simp only [if_neg hact]
  have hs : ∀ n ω, (∑ i ∈ Finset.range (n + 1), H n i ω) = 0 := by
    intro n ω
    apply Finset.sum_eq_zero
    intro i hi
    exact hcell n i ω
  intro n
  refine ⟨hs n, ?_⟩
  have heq : (fun ω => ∑ i ∈ Finset.range (n + 1), H n i ω) =
    (fun _ : Ω => (0 : ℝ)) := by
    funext ω
    exact hs n ω
  rw [heq]
  exact integrable_zero Ω ℝ P
