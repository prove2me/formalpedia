-- Prove2me | solution 1 for AvramDividend.Classical.postPaymentReserve_grid_exit_stopped_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T06:40:48.093664+00:00
-- url     : https://prove2.me/submissions/a80e1875-981d-4140-b8ce-fdfa40b71fee

import Mathlib
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping
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
    Measurable (fun ω =>
      x + X.X (clock (K ω)) ω - rightLimit D (clock (K ω)) ω) ∧
    Measurable (fun ω => (clock (K ω) : ℝ)) := by
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
  have hτ : IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by
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
  have hZstop : Measurable (fun ω => Z (K ω) ω) := by
    have hp := hZ.stronglyAdapted.isStronglyProgressive_of_discrete
    have hms := measurable_stoppedValue hp hτ
    have hm := hms.mono hτ.measurableSpace_le le_rfl
    change Measurable (fun ω => Z (K ω) ω) at hm
    exact hm
  have hV : StronglyAdapted H (fun k (_ : Ω) => (clock k : ℝ)) :=
    stronglyAdapted_const' H (fun k => (clock k : ℝ))
  have hVstop : Measurable (fun ω => (clock (K ω) : ℝ)) := by
    have hp := hV.isStronglyProgressive_of_discrete
    have hms := measurable_stoppedValue hp hτ
    have hm := hms.mono hτ.measurableSpace_le le_rfl
    change Measurable (fun ω => (clock (K ω) : ℝ)) at hm
    exact hm
  exact ⟨hZstop, hVstop⟩
