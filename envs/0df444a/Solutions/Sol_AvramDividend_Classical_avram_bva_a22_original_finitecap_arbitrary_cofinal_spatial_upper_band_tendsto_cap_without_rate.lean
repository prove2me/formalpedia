-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:53:59.451366+00:00
-- url     : https://prove2.me/submissions/1f0125da-2b68-435c-a15e-e6a56b4abd23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (L : ℝ) (hL : 0 < L)
    (hCL : C = ENNReal.ofReal L)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto b atTop (𝓝 L) := by
  have hb (n : ℕ) : b n < L := by
    have hm : b n ∈ Icc (a n / 2) (b n) :=
      ⟨by linarith [ha n, hab n], le_rfl⟩
    have hi : ENNReal.ofReal (b n) < C := (hinside n hm).2
    rw [hCL] at hi
    exact (ENNReal.ofReal_lt_ofReal_iff hL).mp hi
  apply tendsto_order.2
  constructor
  · intro e he
    let y : ℝ := max (L / 2) ((e + L) / 2)
    have hypos : 0 < y :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hyL : y < L :=
      max_lt (by linarith) (by linarith)
    have hey : e < y :=
      lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hycap : ENNReal.ofReal y < C := by
      rw [hCL]
      exact (ENNReal.ofReal_lt_ofReal_iff hL).mpr hyL
    obtain ⟨N, hN⟩ := hcover y hypos hycap
    filter_upwards [eventually_ge_atTop N] with n hn
    exact lt_of_lt_of_le hey (hN n hn).2
  · intro e he
    exact Filter.Eventually.of_forall (fun n => lt_trans (hb n) he)
