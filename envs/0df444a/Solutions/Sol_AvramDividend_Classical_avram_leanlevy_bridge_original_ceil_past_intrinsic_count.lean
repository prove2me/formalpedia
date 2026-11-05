-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_past_intrinsic_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:29:58.78621+00:00
-- url     : https://prove2.me/submissions/1b434482-8a51-4b26-b51a-4c45a1ec92e2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k) (i : ℕ)
    (s : ℝ≥0) (hsT : s ≤ T)
    (hs : (s : ℝ) = (i : ℝ) * (T : ℝ) / (k : ℝ))
    (n : ℕ)
    (F : Finset ℝ≥0)
    (hF : F = (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset)
    (hpos : ∀ u ∈ F, (0 : ℝ≥0) < u) :
    (((F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i)).card : ℕ) : ℝ≥0∞) =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 s ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := by
  have hT' : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hk' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hs_mul : (s : ℝ) * (k : ℝ) = (i : ℝ) * (T : ℝ) := by
    rw [hs]
    field_simp
  have hceil (u : ℝ≥0) :
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i ↔ u ≤ s := by
    rw [Nat.ceil_le]
    have hreal : (u : ℝ) * (k : ℝ) / (T : ℝ) ≤ (i : ℝ) ↔
        (u : ℝ) ≤ (s : ℝ) := by
      rw [div_le_iff₀ hT']
      rw [← hs_mul]
      exact mul_le_mul_iff_of_pos_right hk'
    exact hreal.trans (by exact_mod_cast (Iff.rfl : u ≤ s ↔ u ≤ s))
  have hfilter :
      F.filter (fun u : ℝ≥0 => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ i) =
      F.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ s) := by
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hle⟩
      exact ⟨hu, hpos u hu, (hceil u).mp hle⟩
    · rintro ⟨hu, _, hle⟩
      exact ⟨hu, (hceil u).mpr hle⟩
  rw [hfilter, hF]
  symm
  exact avram_p2_e_compensator_original_window_count_finset_filter
    X ω 0 s T (by exact zero_le) hsT n