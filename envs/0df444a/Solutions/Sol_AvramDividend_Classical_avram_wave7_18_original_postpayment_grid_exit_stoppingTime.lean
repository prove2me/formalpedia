-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_postpayment_grid_exit_stoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:21:32.162095+00:00
-- url     : https://prove2.me/submissions/f431ce84-c5cb-42ec-bff5-e497eedd23fc

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕.rightCont (clock k))
    (lower upper : ℝ) (m : ℕ) (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (x + X.X (clock k) ω - rightLimit D (clock k) ω - upper)
        (lower - (x + X.X (clock k) ω - rightLimit D (clock k) ω)))
      (Set.Ioi (0 : ℝ)) 0 m ω) :
    IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by
  let Z : ℕ → Ω → ℝ := fun k ω =>
    x + X.X (clock k) ω - rightLimit D (clock k) ω
  let Y : ℕ → Ω → ℝ := fun k ω =>
    max (Z k ω - upper) (lower - Z k ω)
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (Z k)
    rw [hH k]
    exact (postPaymentReserve_cadlag_adapted X x D hD).2.2 (clock k)
  have hY : Adapted H Y := by
    intro k
    exact ((hZ k).sub measurable_const).max
      (measurable_const.sub (hZ k))
  intro i
  have hhit := (hY.isStoppingTime_hittingBtwn
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    (n := 0) (n' := m)) i
  convert hhit using 1
  ext ω
  simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
  rw [hK ω]
  change ((hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω : ℕ) : WithTop ℕ) ≤ (i : WithTop ℕ) ↔
    hittingBtwn Y (Set.Ioi (0 : ℝ)) 0 m ω ≤ i
  constructor <;> intro h <;> exact_mod_cast h
