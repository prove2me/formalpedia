-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:57:56.896083+00:00
-- url     : https://prove2.me/submissions/87ef2b49-4617-44b0-b8ba-7264bf11505d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For the literal stopped prepayment reserve, the C² Taylor remainder
has a global negative-mark L¹ quadratic Lévy majorant, with no monotonicity
assumption. Near zero use C²; far from zero use the genuine source L² envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (p : ℝ≥0 × Ω) (z : ℝ), z < 0 →
        |HS (p,z)| ≤ M * min 1 (z ^ 2) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  change ∃ M : ℝ, 0 ≤ M ∧
    ∀ (p : ℝ≥0 × Ω) (z : ℝ), z < 0 →
      |HS (p,z)| ≤ M * min 1 (z ^ 2)
  obtain ⟨r, A, hr, hrle, hA, hnear⟩ :=
    avram_wave5_03b_actual_ruin_stopped_source_generator_near_C2_L1_envelope
      X x D hD w C u v δ hw (by linarith) huv hv
  have hw1 : ContDiffOn ℝ 1 w (Ioo 0 C) := hw.of_le (by norm_num)
  obtain ⟨K, hK, hquad⟩ :=
    avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
      X w 0 C u v δ hw1 hw_cont hw_neg hu (by linarith) hv
      (le_of_lt hu) hδ hδone (le_of_lt huv)
  have hmin (z : ℝ) : 0 ≤ min (1 : ℝ) (z ^ 2) :=
    le_min (by norm_num) (sq_nonneg z)
  have hH (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      (H (p,z)) ^ 2 ≤ K * min 1 (z ^ 2) := by
    by_cases hb : Y p ∈ Icc (u + δ) v
    · have hb' : u + δ ≤ Y p ∧ Y p ≤ v := hb
      have hExpr : H (p,z) = w (Y p + z) - w (Y p) -
          (if -1 < z then z * deriv w (Y p) else 0) := by
        simp [H, Set.mem_Icc, hb']
      rw [hExpr]
      exact hquad (Y p) hb z hz
    · have hb' : ¬ (u + δ ≤ Y p ∧ Y p ≤ v) := hb
      have hExpr : H (p,z) = 0 := by
        simp [H, Set.mem_Icc, hb']
      simpa [hExpr] using mul_nonneg hK (hmin z)
  have hsq (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      (HS (p,z)) ^ 2 ≤ K * min 1 (z ^ 2) := by
    by_cases hs : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · simpa [HS, hs] using hH p z hz
    · simpa [HS, hs] using mul_nonneg hK (hmin z)
  have hsmall (p : ℝ≥0 × Ω) (z : ℝ) (hz : z ∈ Ioo (-r) 0) :
      |HS (p,z)| ≤ A * z ^ 2 := by
    by_cases hb : Y p ∈ Icc (u + δ) v
    · exact hnear p hb z hz
    · have hb' : ¬ (u + δ ≤ Y p ∧ Y p ≤ v) := hb
      have hH : H (p,z) = 0 := by simp [H, Set.mem_Icc, hb']
      have hzero : HS (p,z) = 0 := by simp [HS, hH]
      simpa [hzero] using mul_nonneg hA (sq_nonneg z)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  let B : ℝ := (1 + K) / (r ^ 2)
  have hB : 0 ≤ B := div_nonneg (by linarith) (le_of_lt hr2)
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro p z hz
  by_cases hzne : -r < z
  · have hzr : z ∈ Ioo (-r) 0 := ⟨hzne, hz⟩
    have hrone : r ≤ 1 := le_trans hrle (min_le_right _ _)
    have hzleft : -1 < z := by linarith
    have hzsq : z ^ 2 ≤ 1 := by
      have hleft : 0 ≤ 1 + z := by linarith
      have hright : 0 ≤ 1 - z := by linarith
      nlinarith [mul_nonneg hleft hright]
    have hminsq : min (1 : ℝ) (z ^ 2) = z ^ 2 := min_eq_right hzsq
    calc
      |HS (p,z)| ≤ A * z ^ 2 := hsmall p z hzr
      _ = A * min 1 (z ^ 2) := by rw [hminsq]
      _ ≤ (A + B) * min 1 (z ^ 2) := by
        nlinarith [mul_nonneg hB (hmin z)]
  · have hrone : r ≤ 1 := le_trans hrle (min_le_right _ _)
    have hzle : z ≤ -r := le_of_not_gt hzne
    have hr2one : r ^ 2 ≤ 1 := by nlinarith
    have hzsq : r ^ 2 ≤ z ^ 2 := by
      have hleft : z + r ≤ 0 := by linarith
      have hright : z - r ≤ 0 := by linarith
      nlinarith [mul_nonneg_of_nonpos_of_nonpos hleft hright]
    have hminlo : r ^ 2 ≤ min (1 : ℝ) (z ^ 2) :=
      le_min hr2one hzsq
    have hsqK : (HS (p,z)) ^ 2 ≤ K := by
      calc
        _ ≤ K * min 1 (z ^ 2) := hsq p z hz
        _ ≤ K * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) hK
        _ = K := by ring
    have habsq : |HS (p,z)| ^ 2 = (HS (p,z)) ^ 2 := sq_abs _
    have hlarge : |HS (p,z)| ≤ 1 + K := by
      nlinarith [sq_nonneg (|HS (p,z)| - 1)]
    have hBmin : 1 + K ≤ B * min 1 (z ^ 2) := by
      calc
        1 + K = B * r ^ 2 := by
          have hr2ne : r ^ 2 ≠ 0 := ne_of_gt hr2
          dsimp [B]
          field_simp [hr2ne]
        _ ≤ B * min 1 (z ^ 2) :=
          mul_le_mul_of_nonneg_left hminlo hB
    calc
      |HS (p,z)| ≤ 1 + K := hlarge
      _ ≤ B * min 1 (z ^ 2) := hBmin
      _ ≤ (A + B) * min 1 (z ^ 2) := by
        nlinarith [mul_nonneg hA (hmin z)]
