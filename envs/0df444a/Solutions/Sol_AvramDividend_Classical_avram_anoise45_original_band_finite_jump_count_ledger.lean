-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise45_original_band_finite_jump_count_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T15:07:01.82295+00:00
-- url     : https://prove2.me/submissions/ced18780-3356-4bb0-abde-9cc5ef2c11b9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- A single original-process finite set identifies all physical cell counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let j : Ω → ℝ≥0 → ℝ := fun ω u => X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j ω u ≠ 0}).map
          (fun u : ℝ≥0 => (u, j ω u))) (Ioc s t ×ˢ C k i)
      ∀ ω : Ω, ∃ F : Finset ℝ≥0,
        (∀ u ∈ F, j ω u ∈ B) ∧
        (∀ k i, J k i ω =
          ((F.filter (fun u => j ω u ∈ C k i)).card : ℝ≥0∞)) ∧
        ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) +
          (((t - s : ℝ≥0) : ℝ) * (∫ z in B, z ∂X.ν))) =
          ∑ u ∈ F, j ω u := by
  classical
  intro n s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let j : Ω → ℝ≥0 → ℝ := fun ω u => X.X u ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j ω u ≠ 0}).map
      (fun u : ℝ≥0 => (u, j ω u))) (Ioc s t ×ˢ C k i)
  change ∀ ω : Ω, ∃ F : Finset ℝ≥0,
    (∀ u ∈ F, j ω u ∈ B) ∧
    (∀ k i, J k i ω = ((F.filter (fun u => j ω u ∈ C k i)).card : ℝ≥0∞)) ∧
    ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) +
      (((t - s : ℝ≥0) : ℝ) * (∫ z in B, z ∂X.ν))) =
      ∑ u ∈ F, j ω u
  intro ω
  obtain ⟨Ft, hFt, hIt⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω t n
  obtain ⟨Fs, hFs, hIs⟩ :=
    avram_p4_h_gaussian_original_smallband_signed_integral_eq_finite_jump_sum
      X ω s n
  have hHt :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω =
        (∑ u ∈ Ft, j ω u) - (t : ℝ) * (∫ z in B, z ∂X.ν) := by
    simp only [avram_p4_h_gaussian_intrinsic_small_band_compensated]
    rw [hIt]
  have hHs :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω =
        (∑ u ∈ Fs, j ω u) - (s : ℝ) * (∫ z in B, z ∂X.ν) := by
    simp only [avram_p4_h_gaussian_intrinsic_small_band_compensated]
    rw [hIs]
  have hSubset : Fs ⊆ Ft := by
    intro u hu
    obtain ⟨hu0, hus, hzlo, hzhi⟩ := (hFs u).mp hu
    exact (hFt u).mpr ⟨hu0, le_trans hus hst, hzlo, hzhi⟩
  let F : Finset ℝ≥0 := Ft \ Fs
  have hFmem (u : ℝ≥0) :
      u ∈ F ↔ 0 < u ∧ s < u ∧ u ≤ t ∧ j ω u ∈ B := by
    simp only [F, Finset.mem_sdiff]
    constructor
    · rintro ⟨hut, hus⟩
      obtain ⟨hu0, hut', hzlo, hzhi⟩ := (hFt u).mp hut
      have hsu : s < u := by
        by_contra hns
        have hu_le_s : u ≤ s := le_of_not_gt hns
        exact hus ((hFs u).mpr ⟨hu0, hu_le_s, hzlo, hzhi⟩)
      exact ⟨hu0, hsu, hut', ⟨hzlo, hzhi⟩⟩
    · rintro ⟨hu0, hsu, hut, hz⟩
      constructor
      · exact (hFt u).mpr ⟨hu0, hut, hz.1, hz.2⟩
      · intro hus
        exact (not_le_of_gt hsu) ((hFs u).mp hus).2.1
  have hFband : ∀ u ∈ F, j ω u ∈ B := by
    intro u hu
    exact ((hFmem u).mp hu).2.2.2
  have hCount (k i : ℕ) :
      J k i ω = ((F.filter (fun u => j ω u ∈ C k i)).card : ℝ≥0∞) := by
    have hCi : MeasurableSet (C k i) := by
      dsimp [C, B]
      exact measurableSet_Ioc.inter measurableSet_Ioc
    have hMark :=
      avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω s t (C k i) hCi
    have hCiSub : C k i ⊆ B := by
      intro z hz
      exact hz.1
    have hNeg : ∀ z : ℝ, z ∈ B → z ≠ 0 := by
      intro z hz
      have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ne_of_lt (lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp))
    have hSet :
        {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
          j ω u ≠ 0 ∧ j ω u ∈ C k i} =
        (F.filter (fun u => j ω u ∈ C k i) : Set ℝ≥0) := by
      ext u
      simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
      constructor
      · rintro ⟨hu0, hsu, hut, _, hC⟩
        exact ⟨(hFmem u).mpr ⟨hu0, hsu, hut, hCiSub hC⟩, hC⟩
      · rintro ⟨huF, hC⟩
        obtain ⟨hu0, hsu, hut, _⟩ := (hFmem u).mp huF
        exact ⟨hu0, hsu, hut, hNeg _ (hCiSub hC), hC⟩
    dsimp only [J, j]
    rw [hMark, hSet]
    change ((Set.encard (↑(F.filter (fun u => j ω u ∈ C k i)) : Set ℝ≥0) : ℕ∞) : ℝ≥0∞) = _
    rw [Set.encard_coe_eq_coe_finsetCard]
    rfl
  refine ⟨F, hFband, hCount, ?_⟩
  have hSum : (∑ u ∈ Ft, j ω u) - (∑ u ∈ Fs, j ω u) =
      ∑ u ∈ F, j ω u := by
    have hpartition := Finset.sum_sdiff hSubset (f := j ω)
    dsimp only [F]
    rw [← hpartition]
    ring
  have hdt : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
    exact_mod_cast NNReal.coe_sub hst
  dsimp only [j] at hHt hHs hSum
  rw [hHt, hHs]
  rw [hdt]
  linear_combination hSum
