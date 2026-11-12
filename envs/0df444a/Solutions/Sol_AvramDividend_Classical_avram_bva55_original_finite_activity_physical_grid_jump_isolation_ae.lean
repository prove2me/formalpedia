-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva55_original_finite_activity_physical_grid_jump_isolation_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:52:27.438134+00:00
-- url     : https://prove2.me/submissions/b6956317-f101-4f95-bee1-5c419cef8c20

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_bva50_original_physical_u_grid_finite_jump_cell_isolation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology

/-- Original finite-activity Levy jump times eventually occupy distinct physical grid cells. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (S : ℝ≥0) (hS : 0 < S) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = (S : ℝ) * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, ∀ s t : ℝ≥0,
      0 < s → s ≤ S → X.X s ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) s ≠ 0 →
      0 < t → t ≤ S → X.X t ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) t ≠ 0 →
      u n i ≤ s → s < u n (i + 1) →
      u n i ≤ t → t < u n (i + 1) → s = t := by
  have hSource :=
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae X hActivity
  filter_upwards [hSource] with ω hω
  let J : Set ℝ≥0 := {v | 0 < v ∧ v ≤ S ∧
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}
  have hJ : J.Finite := hω S
  let F : Finset ℝ := hJ.toFinset.image (fun v : ℝ≥0 => (v : ℝ))
  have hSreal : 0 < (S : ℝ) := by exact_mod_cast hS
  have hcell := avram_bva50_original_physical_u_grid_finite_jump_cell_isolation
    F (S : ℝ) hSreal u huniform
  filter_upwards [hcell] with n hn
  intro i s t hs0 hsS hsJump ht0 htS htJump hsl hsr htl htr
  have hsJ : s ∈ J := ⟨hs0, hsS, hsJump⟩
  have htJ : t ∈ J := ⟨ht0, htS, htJump⟩
  have hsF : (s : ℝ) ∈ F := by
    simp only [F, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨s, hsJ, rfl⟩
  have htF : (t : ℝ) ∈ F := by
    simp only [F, Finset.mem_image, Set.Finite.mem_toFinset]
    exact ⟨t, htJ, rfl⟩
  have hsl' : (u n i : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsl
  have hsr' : (s : ℝ) < (u n (i + 1) : ℝ) := by exact_mod_cast hsr
  have htl' : (u n i : ℝ) ≤ (t : ℝ) := by exact_mod_cast htl
  have htr' : (t : ℝ) < (u n (i + 1) : ℝ) := by exact_mod_cast htr
  exact NNReal.coe_injective
    (hn i (s : ℝ) (t : ℝ) hsF htF hsl' hsr' htl' htr')
