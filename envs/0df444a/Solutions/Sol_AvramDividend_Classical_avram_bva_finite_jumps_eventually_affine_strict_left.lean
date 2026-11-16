-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finite_jumps_eventually_affine_strict_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:00:47.282773+00:00
-- url     : https://prove2.me/submissions/aba0bbe7-3094-4b6d-b7f7-2769e3cb5b0a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_finite_marks_last_prior_gap
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t,
        f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s)
    (u : ℝ≥0) (hu : u ∈ hFinite.toFinset) :
    ∃ a : ℝ, f =ᶠ[𝓝[<] u]
      (fun s : ℝ≥0 => a + drift * (s : ℝ)) := by
  have huval : 0 < u ∧ u ≤ T := by
    have h := hFinite.mem_toFinset.mp hu
    exact ⟨h.1, h.2.1⟩
  obtain ⟨r, hr, hPrior⟩ :=
    avram_bva_finite_marks_last_prior_gap hFinite.toFinset u huval.1
  let a : ℝ := f r - (r : ℝ) * drift
  have hEq : ∀ s : ℝ≥0, r < s → s < u →
      f s = a + drift * (s : ℝ) := by
    intro s hrs hsu
    have hNo : ∀ v ∈ Ioc r s,
        f v - Function.leftLim f v = 0 := by
      intro v hv
      by_contra hne
      have hvS : v ∈ hFinite.toFinset := by
        apply hFinite.mem_toFinset.mpr
        exact ⟨lt_of_le_of_lt zero_le hv.1,
          le_trans hv.2 (le_trans (le_of_lt hsu) huval.2), hne⟩
      have hvr := hPrior v hvS (lt_of_le_of_lt hv.2 hsu)
      exact (not_lt_of_ge hvr) hv.1
    have hid := hFlat r s (le_of_lt hrs)
      (le_trans (le_of_lt hsu) huval.2) hNo
    dsimp [a]
    linarith
  refine ⟨a, ?_⟩
  have hOpen : Ioi r ∈ 𝓝 u := isOpen_Ioi.mem_nhds hr
  have hEv : Ioi r ∈ 𝓝[<] u := mem_nhdsWithin_of_mem_nhds hOpen
  filter_upwards [hEv, self_mem_nhdsWithin] with s hrs hsu
  exact hEq s hrs hsu
