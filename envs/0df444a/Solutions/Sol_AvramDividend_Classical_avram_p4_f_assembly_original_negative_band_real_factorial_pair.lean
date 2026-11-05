-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_negative_band_real_factorial_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:57:49.416282+00:00
-- url     : https://prove2.me/submissions/554e2610-8b36-4e1a-8f69-7364d2ab02eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    J.toReal * (J.toReal - 1) =
      2 * (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ) := by
  classical
  let F : Finset ℝ≥0 :=
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
  let J : ℝ≥0∞ :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
  let K : ℕ :=
    ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card
  change J.toReal * (J.toReal - 1) = 2 * (K : ℝ)
  have hSource :=
    avram_p4_f_assembly_original_negative_band_factorial_pair_identity X ω T n
  change J = (F.card : ℝ≥0∞) ∧ (F.card * (F.card - 1)) / 2 = K at hSource
  have hRealCount : J.toReal = (F.card : ℝ) := by
    rw [hSource.1]
    simp
  have hNat : 2 * K = F.card * (F.card - 1) := by
    calc
      2 * K = K * 2 := Nat.mul_comm _ _
      _ = ((F.card * (F.card - 1)) / 2) * 2 := by rw [hSource.2]
      _ = F.card * (F.card - 1) :=
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self F.card)
  have hReal : (2 : ℝ) * (K : ℝ) =
      (F.card : ℝ) * ((F.card : ℝ) - 1) := by
    have hCast := congrArg (fun k : ℕ => (k : ℝ)) hNat
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hCast
    by_cases hz : F.card = 0
    · have hK : K = 0 := by simpa [hz] using hNat
      simp [hz, hK]
    · have hk : 1 ≤ F.card := Nat.one_le_iff_ne_zero.mpr hz
      simpa only [Nat.cast_sub hk, Nat.cast_one] using hCast
  rw [hRealCount]
  exact hReal.symm
