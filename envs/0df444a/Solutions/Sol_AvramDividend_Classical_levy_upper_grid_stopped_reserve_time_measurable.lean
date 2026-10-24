-- Prove2me | solution 1 for AvramDividend.Classical.levy_upper_grid_stopped_reserve_time_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:18:56.660981+00:00
-- url     : https://prove2.me/submissions/3b524063-1035-4fa4-8a0d-2d43eb54d136

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : Filtration ℕ mΩ)
    (hH : ∀ k, H k = 𝓕 (clock k))
    (z : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => X.X (clock k) ω) (Ioi z) 0 m ω) :
    Measurable (fun ω => X.X (clock (K ω)) ω) ∧
    Measurable (fun ω => (clock (K ω) : ℝ)) := by
  let Z : ℕ → Ω → ℝ := fun k ω => X.X (clock k) ω
  have hZ : Adapted H Z := by
    intro k
    change Measurable[H k] (X.X (clock k))
    rw [hH k]
    exact X.adapted (clock k)
  have hτ : IsStoppingTime H (fun ω => (K ω : WithTop ℕ)) := by
    intro i
    have hhit := (hZ.isStoppingTime_hittingBtwn
      (s := Ioi z) measurableSet_Ioi (n := 0) (n' := m)) i
    convert hhit using 1
    ext ω
    simp only [Set.mem_setOf_eq, WithTop.coe_le_coe]
    rw [hK ω]
    change ((hittingBtwn Z (Ioi z) 0 m ω : ℕ) : WithTop ℕ) ≤
      (i : WithTop ℕ) ↔ hittingBtwn Z (Ioi z) 0 m ω ≤ i
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
