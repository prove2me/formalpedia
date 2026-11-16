-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_single_physical_jump_drift_deficit_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:55:47.298215+00:00
-- url     : https://prove2.me/submissions/e95ab63b-403f-4aed-bf1f-e989413b8801

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_leftLim_affine_of_eventuallyEq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal Topology
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T a : ℝ≥0)
    (h0 : f 0 = 0) (ha : 0 < a) (haT : a ≤ T)
    (hOnly : ∀ u ∈ Set.Ioc (0 : ℝ≥0) T,
        f u - Function.leftLim f u ≠ 0 → u = a)
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t, f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    Function.leftLim f a - f a = (T : ℝ) * drift - f T := by
  have hBefore : ∀ r : ℝ≥0, r < a →
      f r = (r : ℝ) * drift := by
    intro r hr
    have hNo : ∀ u ∈ Ioc (0 : ℝ≥0) r,
        f u - Function.leftLim f u = 0 := by
      intro u hu
      by_contra hne
      have heq := hOnly u ⟨hu.1, hu.2.trans (le_of_lt hr |>.trans haT)⟩ hne
      exact (ne_of_lt (hu.2.trans_lt hr)) heq
    have hb := hFlat 0 r zero_le (le_trans (le_of_lt hr) haT) hNo
    have hz : f (0 : ℝ≥0) = 0 := h0
    norm_num [hz] at hb
    linarith
  haveI : (𝓝[<] a).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, ha⟩
  have hEvent : f =ᶠ[𝓝[<] a]
      (fun s : ℝ≥0 => (0 : ℝ) + drift * (s : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    calc
      f u = (u : ℝ) * drift := hBefore u hu
      _ = 0 + drift * (u : ℝ) := by ring
  have hLeft : Function.leftLim f a = (0 : ℝ) + drift * (a : ℝ) :=
    avram_bv_leftLim_affine_of_eventuallyEq
      f a 0 drift hEvent
  have hNoAfter : ∀ u ∈ Ioc a T,
      f u - Function.leftLim f u = 0 := by
    intro u hu
    by_contra hne
    have heq := hOnly u ⟨lt_trans ha hu.1, hu.2⟩ hne
    exact (ne_of_gt hu.1) heq
  have hAfter := hFlat a T haT (le_refl _) hNoAfter
  simp only [zero_add] at hLeft
  linarith
