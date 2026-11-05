-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_ceil_cell_intrinsic_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:26:54.211285+00:00
-- url     : https://prove2.me/submissions/cf3693b6-15a0-4933-9847-eeca0ef4a46f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_real_mesh_ceiling_cell_iff
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_window_count_finset_filter
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ≥0) (hT : 0 < T)
    (k : ℕ) (hk : 0 < k) (i : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (hs : (s : ℝ) = (i : ℝ) * (T : ℝ) / (k : ℝ))
    (ht : (t : ℝ) = ((i + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ))
    (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    (((F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = i + 1)).card : ℕ) : ℝ≥0∞) =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  have hTr : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hcell (u : ℝ≥0) :
      (Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = i + 1) ↔
        s < u ∧ u ≤ t := by
    have h := avram_p4_f_assembly_real_mesh_ceiling_cell_iff
      (u : ℝ) (T : ℝ) hTr k i hk
    rw [← hs, ← ht] at h
    constructor
    · intro hu
      obtain ⟨hleft, hright⟩ := h.mp hu
      exact ⟨by exact_mod_cast hleft, by exact_mod_cast hright⟩
    · rintro ⟨hleft, hright⟩
      apply h.mpr
      exact ⟨by exact_mod_cast hleft, by exact_mod_cast hright⟩
  have hfilter :
      F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = i + 1) =
      F.filter (fun (u : ℝ≥0) => s < u ∧ u ≤ t) := by
    ext u
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => hcell u)
  change
    (((F.filter (fun (u : ℝ≥0) => Nat.ceil ((u : ℝ) * (k : ℝ) / (T : ℝ)) = i + 1)).card : ℕ) : ℝ≥0∞) =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  rw [hfilter]
  exact (avram_p2_e_compensator_original_window_count_finset_filter
    X ω s t T hst htT n).symm
