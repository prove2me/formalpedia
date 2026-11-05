-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_marked_mesh_index_in_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:37:06.279734+00:00
-- url     : https://prove2.me/submissions/7c42ce18-b34b-456a-b300-62c04a0b944b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
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
    (T : ℝ≥0) (hT : 0 < T) (n k : ℕ) (hk : 0 < k) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    ∀ u ∈ F,
      0 < Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ∧
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) ≤ k := by
  dsimp only
  intro u hu
  have hu' : 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1)) := by simpa using hu
  rcases hu' with ⟨hu0, huT, _⟩
  have hTreal : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hu0real : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu0
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hscaledPos : (0 : ℝ) <
      (u : ℝ) * (k : ℝ) / (T : ℝ) := by positivity
  have hnatPos : 0 <
      Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) := by
    by_contra hh
    have hz : Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = 0 :=
      Nat.eq_zero_of_not_pos hh
    have hceil := Nat.le_ceil ((u : ℝ) * (k : ℝ) / (T : ℝ))
    have hbad : (u : ℝ) * (k : ℝ) / (T : ℝ) ≤ 0 := by
      simpa [hz] using hceil
    exact (not_le_of_gt hscaledPos) hbad
  have huTR : (u : ℝ) ≤ (T : ℝ) := by exact_mod_cast huT
  have hmul := mul_le_mul_of_nonneg_right huTR (le_of_lt hkreal)
  have hscaledLe :
      (u : ℝ) * (k : ℝ) / (T : ℝ) ≤ (k : ℝ) := by
    apply (div_le_iff₀ hTreal).mpr
    nlinarith [hmul]
  exact ⟨hnatPos, Nat.ceil_le.mpr hscaledLe⟩
