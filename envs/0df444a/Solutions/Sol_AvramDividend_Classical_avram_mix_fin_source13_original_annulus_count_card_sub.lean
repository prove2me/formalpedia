-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin_source13_original_annulus_count_card_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:38:57.985651+00:00
-- url     : https://prove2.me/submissions/be3982e1-6cc5-4587-9876-d90d6d972634

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_nested_cutoff_annulus_count_additive
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite physical annulus count is precisely the difference of nested finite cutoff cardinalities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) (ω : Ω) :
    let c : ℝ := -(1 / ((n : ℝ) + 1))
    let d : ℝ := -(1 / ((m : ℝ) + 1))
    let k : ℕ → ℕ := fun i =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T i).toFinset.card
    let J : Set ℝ → ℝ≥0∞ := fun B =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    J (Ioc c d) = ((k m - k n : ℕ) : ℝ≥0∞) := by
  let c : ℝ := -(1 / ((n : ℝ) + 1))
  let d : ℝ := -(1 / ((m : ℝ) + 1))
  let k : ℕ → ℕ := fun i =>
    (avram_wave7_06_original_negative_band_marked_times_finite X ω T i).toFinset.card
  let J : Set ℝ → ℝ≥0∞ := fun B =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  change J (Ioc c d) = ((k m - k n : ℕ) : ℝ≥0∞)
  have hSplit := avram_mixed_source13_original_nested_cutoff_annulus_count_additive
    X T n m hnm ω
  change J (Iic d) = J (Iic c) + J (Ioc c d) at hSplit
  have hFullM :=
    (avram_p4_f_assembly_original_negative_band_factorial_pair_identity X ω T m).1
  have hFullN :=
    (avram_p4_f_assembly_original_negative_band_factorial_pair_identity X ω T n).1
  change J (Iic d) = (k m : ℝ≥0∞) at hFullM
  change J (Iic c) = (k n : ℝ≥0∞) at hFullN
  have hLe : k n ≤ k m := by
    have hENN : (k n : ℝ≥0∞) ≤ (k m : ℝ≥0∞) := by
      calc
        (k n : ℝ≥0∞) = J (Iic c) := hFullN.symm
        _ ≤ J (Iic c) + J (Ioc c d) := le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ J (Ioc c d) from zero_le)
        _ = J (Iic d) := hSplit.symm
        _ = (k m : ℝ≥0∞) := hFullM
    exact_mod_cast hENN
  have hNat : k n + (k m - k n) = k m := Nat.add_sub_of_le hLe
  have hCast :
      (k n : ℝ≥0∞) + ((k m - k n : ℕ) : ℝ≥0∞) = (k m : ℝ≥0∞) := by
    exact_mod_cast hNat
  have hEq :
      (k n : ℝ≥0∞) + J (Ioc c d) =
        (k n : ℝ≥0∞) + ((k m - k n : ℕ) : ℝ≥0∞) := by
    calc
      (k n : ℝ≥0∞) + J (Ioc c d) =
          J (Iic c) + J (Ioc c d) := by rw [hFullN]
      _ = J (Iic d) := hSplit.symm
      _ = (k m : ℝ≥0∞) := hFullM
      _ = (k n : ℝ≥0∞) + ((k m - k n : ℕ) : ℝ≥0∞) := hCast.symm
  have hFiniteLeft : (k n : ℝ≥0∞) ≠ ⊤ := by simp
  have hSubEq :=
    congrArg (fun z : ℝ≥0∞ => z - (k n : ℝ≥0∞)) hEq
  simpa only [ENNReal.add_sub_cancel_left hFiniteLeft] using hSubEq
