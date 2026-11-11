-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise39_original_dyadic_mark_partition_count_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:01:02.791069+00:00
-- url     : https://prove2.me/submissions/c3561bad-6d28-45d2-a120-3d246f8c4c3b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_intrinsic_finite_disjoint_mark_partition_sum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Disjoint original dyadic negative-mark count and intensity budgets. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ n k : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → Set ℝ := fun i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → Ω → ℝ≥0∞ := fun i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C i)
      let N : Ω → ℝ≥0∞ := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ Iio (0 : ℝ))
      (∀ ω, (∑ i ∈ Finset.range (2 ^ k), J i ω) ≤ N ω) ∧
        (∑ i ∈ Finset.range (2 ^ k), X.ν (C i)) ≤ X.ν (Iio (0 : ℝ)) := by
  classical
  intro n k s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → Set ℝ := fun i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let J : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ C i)
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 t ×ˢ Iio (0 : ℝ))
  have hCmeas (i : ℕ) : MeasurableSet (C i) := by
    dsimp [C, B]
    exact measurableSet_Ioc.inter measurableSet_Ioc
  have hBsub : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp)
  have hCdisj (i j : ℕ) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    have hsub (a : ℕ) : C a ⊆
        Ioc (-1 + (a : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((a : ℝ) + 1) / (2 : ℝ) ^ k) := by
      intro z hz
      exact hz.2
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hq : ((i : ℝ) + 1) / (2 : ℝ) ^ k ≤
          (j : ℝ) / (2 : ℝ) ^ k := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.succ_le_of_lt hij'
        · positivity
      exact (Set.Ioc_disjoint_Ioc_of_le (add_le_add_right hq (-1))).mono
        (hsub i) (hsub j)
    · have hq : ((j : ℝ) + 1) / (2 : ℝ) ^ k ≤
          (i : ℝ) / (2 : ℝ) ^ k := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.succ_le_of_lt hji'
        · positivity
      exact ((Set.Ioc_disjoint_Ioc_of_le (add_le_add_right hq (-1))).mono
        (hsub j) (hsub i)).symm
  have hNuSum :
      (∑ i ∈ Finset.range (2 ^ k), X.ν (C i)) ≤ X.ν (Iio (0 : ℝ)) := by
    have heq : X.ν (⋃ i ∈ Finset.range (2 ^ k), C i) =
        ∑ i ∈ Finset.range (2 ^ k), X.ν (C i) :=
      measure_biUnion_finset
        (by intro i hi j hj hij; exact hCdisj i j hij)
        (by intro i hi; exact hCmeas i)
    rw [←heq]
    apply measure_mono
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨i, hz⟩
    rcases Set.mem_iUnion.mp hz with ⟨hi, hz⟩
    exact hBsub hz.1
  have hCountSum (ω : Ω) :
      (∑ i ∈ Finset.range (2 ^ k), J i ω) ≤ N ω := by
    have h := avram_p4_b_smalljump_original_intrinsic_finite_disjoint_mark_partition_sum
      X (Finset.range (2 ^ k)) s t C
      (by intro i hi; exact hCmeas i)
      (by intro i hi j hj hij; exact hCdisj i j hij) ω
    calc
      (∑ i ∈ Finset.range (2 ^ k), J i ω) =
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s t ×ˢ (⋃ i ∈ Finset.range (2 ^ k), C i)) := by
              simpa only [J] using h.symm
      _ ≤ N ω := by
        dsimp [N]
        apply measure_mono
        intro p hp
        have hs0 : (0 : ℝ≥0) ≤ s := by positivity
        refine ⟨⟨lt_of_le_of_lt hs0 hp.1.1, hp.1.2⟩, ?_⟩
        rcases Set.mem_iUnion.mp hp.2 with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hi with ⟨hMem, hMark⟩
        exact hBsub hMark.1
  exact ⟨hCountSum, hNuSum⟩
