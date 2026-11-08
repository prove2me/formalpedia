-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps16_real_upperlim_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:14:45.592091+00:00
-- url     : https://prove2.me/submissions/ed266331-5994-4f9f-b00f-a6136b3d334a

import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal
noncomputable section

/-- A one-sided real upper limit remains one-sided after the continuous,
monotone nonnegative embedding into extended nonnegative reals. The shift
is the integrable Lévy-Taylor envelope used by the original-process bridge. -/
theorem solution (r : ℕ → ℝ) (a L : ℝ)
    (hupper : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, r n ≤ L + ε) :
    Filter.limsup (fun n : ℕ => ENNReal.ofReal (a + r n)) atTop ≤
      ENNReal.ofReal (a + L) := by
  apply (Filter.limsup_le_iff).2
  intro b hb
  have hopen : IsOpen {t : ℝ | ENNReal.ofReal t < b} :=
    isOpen_Iio.preimage ENNReal.continuous_ofReal
  obtain ⟨ε, hε, hball⟩ :=
    (Metric.isOpen_iff.mp hopen) (a + L) hb
  have hε2 : 0 < ε / 2 := by linarith
  have hr : a + L + ε / 2 ∈ Metric.ball (a + L) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hpos : 0 ≤ (a + L + ε / 2) - (a + L) := by linarith
    rw [abs_of_nonneg hpos]
    linarith
  have hnear : ENNReal.ofReal (a + L + ε / 2) < b := hball hr
  filter_upwards [hupper (ε / 2) hε2] with n hn
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) hnear
