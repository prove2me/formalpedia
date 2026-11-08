-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn13_original_unit_partition_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:27:10.22121+00:00
-- url     : https://prove2.me/submissions/f9ab643b-7910-4866-a75b-83774018fb6b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let J : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
    let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
      ∏ u ∈ (J ω).filter (fun u =>
        (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ ω : Ω, (∏ u ∈ J ω,
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
      ∏ i : Fin (n + 1), C i ω := by
  classical
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let J : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
  let f : Ω → ℝ≥0 → ℝ := fun ω u =>
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∏ u ∈ (J ω).filter (fun u =>
      (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T), f ω u
  change ∀ ω : Ω, (∏ u ∈ J ω, f ω u) = ∏ i : Fin (n + 1), C i ω
  intro ω
  have hJpos (u : ℝ≥0) (hu : u ∈ J ω) : 0 < u ∧ u ≤ 1 := by
    have hmem : u ∈ {v : ℝ≥0 | 0 < v ∧ v ≤ (1 : ℝ≥0) ∧
      X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v <
        -(1 / ((k : ℝ) + 1))} := by
      simpa only [J, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hu
    exact ⟨hmem.1, hmem.2.1⟩
  have hrec (m : ℕ) :
      (∏ u ∈ (J ω).filter (fun u => u ≤ (m : ℝ≥0) * T), f ω u) =
      ∏ i ∈ Finset.range m,
        (∏ u ∈ (J ω).filter (fun u =>
          (i : ℝ≥0) * T < u ∧ u ≤ ((i : ℝ≥0) + 1) * T), f ω u) := by
    induction m with
    | zero =>
        have hempty : (J ω).filter (fun u => u ≤ (0 : ℝ≥0)) = ∅ := by
          ext u
          constructor
          · intro hu
            obtain ⟨hJ, hle⟩ := Finset.mem_filter.mp hu
            have hpos : 0 < u := (hJpos u hJ).1
            exact False.elim ((not_le_of_gt hpos) hle)
          · intro hu
            simpa using hu
        simp only [Nat.cast_zero, zero_mul, Finset.range_zero,
          Finset.prod_empty, hempty]
    | succ m ih =>
        let R : Finset ℝ≥0 := (J ω).filter
          (fun u => u ≤ ((m + 1 : ℕ) : ℝ≥0) * T)
        let p : ℝ≥0 → Prop := fun u => u ≤ (m : ℝ≥0) * T
        have hmono : (m : ℝ≥0) * T ≤ ((m + 1 : ℕ) : ℝ≥0) * T := by
          gcongr
          exact Nat.le_succ m
        have hleft : R.filter p = (J ω).filter p := by
          ext u
          simp only [R, p, Finset.mem_filter]
          constructor
          · rintro ⟨⟨hu, -⟩, hp⟩
            exact ⟨hu, hp⟩
          · rintro ⟨hu, hp⟩
            exact ⟨⟨hu, le_trans hp hmono⟩, hp⟩
        have hright : R.filter (fun u => ¬ p u) =
            (J ω).filter (fun u =>
              (m : ℝ≥0) * T < u ∧ u ≤ ((m : ℝ≥0) + 1) * T) := by
          ext u
          simp only [R, p, Finset.mem_filter, not_le, Nat.cast_add, Nat.cast_one]
          constructor
          · rintro ⟨⟨hu, htop⟩, hlow⟩
            exact ⟨hu, hlow, by simpa using htop⟩
          · rintro ⟨hu, hlow, htop⟩
            exact ⟨⟨hu, by simpa using htop⟩, hlow⟩
        have hsplit : (∏ u ∈ R.filter p, f ω u) *
            (∏ u ∈ R.filter (fun u => ¬ p u), f ω u) =
            ∏ u ∈ R, f ω u :=
          Finset.prod_filter_mul_prod_filter_not R p (f ω)
        change (∏ u ∈ R, f ω u) = _
        rw [← hsplit, hleft, hright, ih]
        simp only [Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]
  have hunit : (((n + 1 : ℕ) : ℝ≥0) * T) = 1 := by
    have hd : (n : ℝ≥0) + 1 ≠ 0 := by positivity
    dsimp [T]
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  have hfull : (J ω).filter
      (fun u => u ≤ (((n + 1 : ℕ) : ℝ≥0) * T)) = J ω := by
    ext u
    simp only [Finset.mem_filter, hunit]
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, (hJpos u hu).2⟩
  have h := hrec (n + 1)
  rw [hfull] at h
  rw [h]
  simp only [Finset.prod_fin_eq_prod_range, C, Nat.cast_add, Nat.cast_one]
  apply Finset.prod_congr rfl
  intro i hi
  have hlt : i < n + 1 := Finset.mem_range.mp hi
  simp [hlt]
