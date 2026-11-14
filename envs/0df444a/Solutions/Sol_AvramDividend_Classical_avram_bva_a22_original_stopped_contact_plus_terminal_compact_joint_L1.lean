-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_stopped_contact_plus_terminal_compact_joint_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:12:54.530441+00:00
-- url     : https://prove2.me/submissions/2cb06215-3a8f-406b-acf1-c3c2d5f75d7e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDs : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 < q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Contact : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal - δ n)
              ((min (ruinTime X x D ω) (S : ℝ≥0∞)).toReal),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ∈ Icc c d ∧
         (x + X.X S ω - rightLimit D S ω) ∈ Icc c d ∧
          0 ≤ w (x + X.X S ω - rightLimit D S ω) then
        max (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, Integrable (Err m) P) →
    (∀ m, Integrable (fun ω => Contact m ω + Err m ω) P) ∧
    Tendsto (fun m => ∫ ω, Contact m ω + Err m ω ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  intro δ S Contact Err hErrI
  obtain ⟨hContactI, hContactZero⟩ :=
    avram_bva97_original_BV_cash_contact_L1_mean_zero_exact
      X x C D hD q hq T hT
  have hTerminalZero :=
    avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
      X hBV x D hDs w q (le_of_lt hq)
      c d L hL hLip T hT u huniform hErrI
  refine ⟨?_, ?_⟩
  · intro m
    exact (hContactI m).add (hErrI m)
  · have heq :
        (fun m => ∫ ω, Contact m ω + Err m ω ∂P) =
        (fun m => (∫ ω, Contact m ω ∂P) +
          (∫ ω, Err m ω ∂P)) := by
      funext m
      exact integral_add (hContactI m) (hErrI m)
    rw [heq]
    have hsum : Tendsto
        (fun m => (∫ ω, Contact m ω ∂P) +
          (∫ ω, Err m ω ∂P))
        atTop (𝓝 ((0 : ℝ) + 0)) :=
      hContactZero.add hTerminalZero
    simpa only [add_zero] using hsum
