-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB203_generic_good_mesh_times_from_two_null_levels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:18:48.970956+00:00
-- url     : https://prove2.me/submissions/6a0a9d59-0163-4e89-879b-b18b6ecf5319

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
import Theorems.Thm_AvramDividend_Classical_avram_gbB165_time_level_null_implies_ae_avoids_level
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Pathwise good times once the two spatial occupation atoms are excluded. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (Y : ℝ≥0 → Ω → ℝ)
    (hCount : ∀ᵐ ω ∂P,
      Set.Countable {s : ℝ≥0 | ¬ ContinuousAt
        (fun u : ℝ≥0 => Y u ω) s})
    (n : ℕ) (a b : ℝ) (ρ : Ω → ℝ≥0)
    (hOccA : ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = a} = 0)
    (hOccB : ∀ᵐ ω ∂P,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧
        Y (Real.toNNReal t) ω = b} = 0)
    (w : ℝ → ℝ)
    (hDeriv : ∀ y ∈ Ioo a b, ContinuousAt (deriv w) y) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂(volume.restrict
      (Ioo (0 : ℝ) (n : ℝ))),
      ContinuousAt (fun s : ℝ => Y (Real.toNNReal s) ω) t ∧
      Y (Real.toNNReal t) ω ≠ a ∧
      Y (Real.toNNReal t) ω ≠ b ∧
      t ≠ (ρ ω : ℝ) ∧
      (Y (Real.toNNReal t) ω ∈ Ioo a b →
        ContinuousAt (deriv w) (Y (Real.toNNReal t) ω)) := by
  have hCont : ∀ᵐ ω ∂P,
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
        ContinuousAt (fun s : ℝ => Y (Real.toNNReal s) ω) t := by
    filter_upwards [hCount] with ω hc
    exact avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
      (fun s : ℝ≥0 => Y s ω) hc n
  have hAEa : ∀ᵐ ω ∂P,
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
        Y (Real.toNNReal t) ω ≠ a := by
    filter_upwards [hOccA] with ω hω
    exact avram_gbB165_time_level_null_implies_ae_avoids_level
      n (fun t : ℝ => Y (Real.toNNReal t) ω) a hω
  have hAEb : ∀ᵐ ω ∂P,
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
        Y (Real.toNNReal t) ω ≠ b := by
    filter_upwards [hOccB] with ω hω
    exact avram_gbB165_time_level_null_implies_ae_avoids_level
      n (fun t : ℝ => Y (Real.toNNReal t) ω) b hω
  have hRho (ω : Ω) :
      ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
        t ≠ (ρ ω : ℝ) := by
    apply (ae_iff).2
    simp
  filter_upwards [hCont, hAEa, hAEb] with ω hc ha hb
  filter_upwards [hc, ha, hb, hRho ω] with t ht hta htb htr
  exact ⟨ht, hta, htb, htr, fun hy => hDeriv _ hy⟩

