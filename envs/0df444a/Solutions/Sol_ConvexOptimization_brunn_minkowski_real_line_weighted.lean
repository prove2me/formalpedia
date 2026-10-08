-- Prove2me | solution 1 for ConvexOptimization.brunn_minkowski_real_line_weighted
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T06:15:03.219876+00:00
-- url     : https://prove2.me/submissions/39b6f265-a72d-4718-b472-0e857c429180

import Mathlib

open scoped RealInnerProductSpace ENNReal Pointwise
open MeasureTheory Set

private theorem volume_add_compact
    (K L : Set ℝ) (hK : IsCompact K) (hL : IsCompact L)
    (hKn : K.Nonempty) (hLn : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  let a : ℝ := sInf K
  let b : ℝ := sSup L
  have haK : a ∈ K := by simpa [a] using hK.sInf_mem hKn
  have hbL : b ∈ L := by simpa [b] using hL.sSup_mem hLn
  have ha_le : ∀ x ∈ K, a ≤ x := by
    intro x hx
    exact (hK.isLeast_sInf hKn).2 hx
  have hle_b : ∀ y ∈ L, y ≤ b := by
    intro y hy
    exact (hL.isGreatest_sSup hLn).2 hy
  let U : Set ℝ := K + {b}
  let V : Set ℝ := {a} + L
  have hUKL : U ⊆ K + L := by
    exact add_subset_add Subset.rfl (singleton_subset_iff.mpr hbL)
  have hVKL : V ⊆ K + L := by
    exact add_subset_add (singleton_subset_iff.mpr haK) Subset.rfl
  have hUV : U ∩ V ⊆ {a + b} := by
    intro z hz
    rcases hz.1 with ⟨x, hx, y, hy, hxy⟩
    rcases hz.2 with ⟨u, hu, v, hv, huv⟩
    simp only [mem_singleton_iff] at hy hu ⊢
    subst y
    subst u
    have hxle : x ≤ a := by linarith [hle_b v hv]
    have hxa : x = a := le_antisymm hxle (ha_le x hx)
    subst x
    simpa using hxy.symm
  have hUmeas : MeasurableSet U := by
    simpa [U, add_singleton] using
      (measurableEmbedding_addRight b).measurableSet_image' hK.measurableSet
  have hVmeas : MeasurableSet V := by
    simpa [V, singleton_add] using
      (measurableEmbedding_addLeft a).measurableSet_image' hL.measurableSet
  have hUint : volume U = volume K := by
    simp [U, add_singleton, image_add_right]
  have hVint : volume V = volume L := by
    simp [V, singleton_add, image_add_left]
  calc
    volume K + volume L = volume U + volume V := by rw [hUint, hVint]
    _ = volume (U ∪ V) + volume (U ∩ V) := (measure_union_add_inter U hVmeas).symm
    _ = volume (U ∪ V) := by
      rw [measure_mono_null hUV (measure_singleton (a + b)), add_zero]
    _ ≤ volume (K + L) := measure_mono (union_subset hUKL hVKL)

private theorem volume_add_ge
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  let KA := {K : Set ℝ // K ⊆ A ∧ IsCompact K}
  let KB := {K : Set ℝ // K ⊆ B ∧ IsCompact K}
  let mA : KA → ℝ≥0∞ := fun K ↦ volume (K : Set ℝ)
  let mB : KB → ℝ≥0∞ := fun K ↦ volume (K : Set ℝ)
  haveI : Nonempty KA := ⟨⟨∅, empty_subset A, isCompact_empty⟩⟩
  haveI : Nonempty KB := ⟨⟨∅, empty_subset B, isCompact_empty⟩⟩
  have hAi : volume A = ⨆ K : KA, mA K := by
    rw [hA.measure_eq_iSup_isCompact]
    apply le_antisymm
    · apply iSup_le
      intro K
      apply iSup_le
      intro hKA
      apply iSup_le
      intro hK
      exact le_iSup_of_le (⟨K, hKA, hK⟩ : KA) (le_refl _)
    · apply iSup_le
      intro K
      exact le_iSup_of_le (K : Set ℝ) <|
        le_iSup_of_le K.2.1 <| le_iSup_of_le K.2.2 (le_refl _)
  have hBi : volume B = ⨆ K : KB, mB K := by
    rw [hB.measure_eq_iSup_isCompact]
    apply le_antisymm
    · apply iSup_le
      intro K
      apply iSup_le
      intro hKB
      apply iSup_le
      intro hK
      exact le_iSup_of_le (⟨K, hKB, hK⟩ : KB) (le_refl _)
    · apply iSup_le
      intro K
      exact le_iSup_of_le (K : Set ℝ) <|
        le_iSup_of_le K.2.1 <| le_iSup_of_le K.2.2 (le_refl _)
  rw [hAi, hBi]
  apply ENNReal.iSup_add_iSup_le
  intro K L
  by_cases hKn : Set.Nonempty (K : Set ℝ)
  · by_cases hLn : Set.Nonempty (L : Set ℝ)
    · calc
        mA K + mB L ≤ volume ((K : Set ℝ) + (L : Set ℝ)) :=
          volume_add_compact K L K.2.2 L.2.2 hKn hLn
        _ ≤ volume (A + B) := measure_mono (add_subset_add K.2.1 L.2.1)
    · have hL0 : (L : Set ℝ) = ∅ := not_nonempty_iff_eq_empty.mp hLn
      obtain ⟨b, hb⟩ := hBn
      calc
        mA K + mB L = volume (K : Set ℝ) + volume ({b} : Set ℝ) := by simp [mA, mB, hL0]
        _ ≤ volume ((K : Set ℝ) + {b}) :=
          volume_add_compact K {b} K.2.2 isCompact_singleton hKn (singleton_nonempty b)
        _ ≤ volume (A + B) :=
          measure_mono (add_subset_add K.2.1 (singleton_subset_iff.mpr hb))
  · have hK0 : (K : Set ℝ) = ∅ := not_nonempty_iff_eq_empty.mp hKn
    by_cases hLn : Set.Nonempty (L : Set ℝ)
    · obtain ⟨a, ha⟩ := hAn
      calc
        mA K + mB L = volume ({a} : Set ℝ) + volume (L : Set ℝ) := by simp [mA, mB, hK0]
        _ ≤ volume ({a} + (L : Set ℝ)) :=
          volume_add_compact {a} L isCompact_singleton L.2.2 (singleton_nonempty a) hLn
        _ ≤ volume (A + B) :=
          measure_mono (add_subset_add (singleton_subset_iff.mpr ha) L.2.1)
    · have hL0 : (L : Set ℝ) = ∅ := not_nonempty_iff_eq_empty.mp hLn
      simp [mA, mB, hK0, hL0]

/-- The weighted one-dimensional Brunn--Minkowski inequality, packaged with
the exact signature of a prospective Prove2Me child theorem. -/
theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAn : A.Nonempty) (hBn : B.Nonempty) :
    ENNReal.ofReal (1 - l) * volume A + ENNReal.ofReal l * volume B ≤
      volume ((1 - l) • A + l • B) := by
  have hal : 0 ≤ 1 - l := (sub_pos.mpr hl1).le
  have hbl : 0 ≤ l := hl0.le
  have h := volume_add_ge ((1 - l) • A) (l • B)
    (hA.const_smul₀ (1 - l))
    (hB.const_smul₀ l) hAn.smul_set hBn.smul_set
  have hscaleA : volume ((1 - l) • A) = ENNReal.ofReal (1 - l) * volume A := by
    simpa using MeasureTheory.Measure.addHaar_smul_of_nonneg volume hal A
  have hscaleB : volume (l • B) = ENNReal.ofReal l * volume B := by
    simpa using MeasureTheory.Measure.addHaar_smul_of_nonneg volume hbl B
  rwa [hscaleA, hscaleB] at h
