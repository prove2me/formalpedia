-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord8_t10_equalcell_marked_product_iIndep
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:52:59.374672+00:00
-- url     : https://prove2.me/submissions/a51fa924-4a6d-4a3b-9aaa-05f40f61c04f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_cell_product_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_cell_product_indep_past

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
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
    iIndepFun C P ∧ ∀ i, AEStronglyMeasurable (C i) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let J : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset
  let C : Fin (n + 1) → Ω → ℝ := fun i ω =>
    ∏ u ∈ (J ω).filter (fun u =>
      (i.val : ℝ≥0) * T < u ∧ u ≤ ((i.val : ℝ≥0) + 1) * T),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  change iIndepFun C P ∧ ∀ i, AEStronglyMeasurable (C i) P
  have hT : ((n : ℝ≥0) + 1) * T = 1 := by
    dsimp [T]
    exact mul_div_cancel₀ 1 (by positivity)
  have htime (i : Fin (n + 1)) :
      ((i.val : ℝ≥0) + 1) * T ≤ 1 := by
    have hi : i.val + 1 ≤ n + 1 := Nat.succ_le_of_lt i.isLt
    have hcast : ((i.val : ℝ≥0) + 1) ≤ (n : ℝ≥0) + 1 := by
      exact_mod_cast hi
    calc
      _ ≤ ((n : ℝ≥0) + 1) * T :=
        mul_le_mul_of_nonneg_right hcast (by positivity)
      _ = 1 := hT
  have hstep (i : Fin (n + 1)) :
      (i.val : ℝ≥0) * T ≤ ((i.val : ℝ≥0) + 1) * T :=
    mul_le_mul_of_nonneg_right (by simp) (by positivity)
  have hCmeas (i : Fin (n + 1)) :
      Measurable[𝓕 (((i.val : ℝ≥0) + 1) * T)] (C i) := by
    simpa only [C, J] using
      avram_route_runner_g_original_cell_product_filtration_measurable
        X ((i.val : ℝ≥0) * T) (((i.val : ℝ≥0) + 1) * T)
        (hstep i) (htime i) k
  have hfin (S : Finset (Fin (n + 1))) :
      ∀ sets : Fin (n + 1) → Set ℝ,
        (∀ i ∈ S, MeasurableSet (sets i)) →
          P (⋂ i ∈ S, C i ⁻¹' sets i) =
            ∏ i ∈ S, P (C i ⁻¹' sets i) := by
    induction S using Finset.induction_on_max with
    | empty =>
        intro sets hsets
        simp
    | insert a S hmax ih =>
        intro sets hsets
        have ha : a ∉ S := by
          intro ha
          exact (lt_irrefl a) (hmax a ha)
        let A : Set Ω := ⋂ i ∈ S, C i ⁻¹' sets i
        have hA : MeasurableSet[𝓕 ((a.val : ℝ≥0) * T)] A := by
          apply Finset.measurableSet_biInter S
          intro i hi
          have hlt : i.val + 1 ≤ a.val :=
            Nat.succ_le_iff.mpr ((Fin.lt_def).mp (hmax i hi))
          have hcast : ((i.val : ℝ≥0) + 1) ≤ (a.val : ℝ≥0) := by
            exact_mod_cast hlt
          have hle : ((i.val : ℝ≥0) + 1) * T ≤ (a.val : ℝ≥0) * T :=
            mul_le_mul_of_nonneg_right hcast (by positivity)
          exact ((hCmeas i).mono (𝓕.mono hle) le_rfl)
            (hsets i (Finset.mem_insert_of_mem hi))
        have hHm : Measurable[𝓕 ((a.val : ℝ≥0) * T)]
            (fun ω : Ω => if ω ∈ A then (1 : ℝ) else 0) :=
          Measurable.ite hA measurable_const measurable_const
        have hInd : IndepFun
            (fun ω : Ω => if ω ∈ A then (1 : ℝ) else 0) (C a) P := by
          simpa only [C, J] using
            avram_route_runner_g_original_cell_product_indep_past X
              ((a.val : ℝ≥0) * T) (((a.val : ℝ≥0) + 1) * T)
              (hstep a) (htime a) k _ hHm
        have hOne : ((fun ω : Ω => if ω ∈ A then (1 : ℝ) else 0) ⁻¹'
            ({1} : Set ℝ)) = A := by
          ext ω
          by_cases hω : ω ∈ A <;> simp [hω]
        have hmul : P (A ∩ C a ⁻¹' sets a) =
            P A * P (C a ⁻¹' sets a) := by
          have h := hInd.measure_inter_preimage_eq_mul
            ({1} : Set ℝ) (sets a) (by simp)
            (hsets a (Finset.mem_insert_self a S))
          simpa only [hOne] using h
        have hset : (⋂ i ∈ insert a S, C i ⁻¹' sets i) =
            A ∩ C a ⁻¹' sets a := by
          change (⋂ i ∈ insert a S, C i ⁻¹' sets i) =
            (⋂ i ∈ S, C i ⁻¹' sets i) ∩ C a ⁻¹' sets a
          rw [Finset.set_biInter_insert]
          exact inter_comm _ _
        calc
          P (⋂ i ∈ insert a S, C i ⁻¹' sets i) =
              P (A ∩ C a ⁻¹' sets a) := congrArg P hset
          _ = P A * P (C a ⁻¹' sets a) := hmul
          _ = ∏ i ∈ insert a S, P (C i ⁻¹' sets i) := by
            have hsub : ∀ i ∈ S, MeasurableSet (sets i) := by
              intro i hi
              exact hsets i (Finset.mem_insert_of_mem hi)
            rw [Finset.prod_insert ha, ← ih sets hsub]
            exact mul_comm _ _
  constructor
  · refine (iIndepFun_iff_measure_inter_preimage_eq_mul).2 ?_
    intro S sets hsets
    exact hfin S sets hsets
  · intro i
    exact ((hCmeas i).mono (𝓕.le _) le_rfl).aestronglyMeasurable
