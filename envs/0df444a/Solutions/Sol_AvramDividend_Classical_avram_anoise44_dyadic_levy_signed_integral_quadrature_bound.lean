-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise44_dyadic_levy_signed_integral_quadrature_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T14:40:20.745574+00:00
-- url     : https://prove2.me/submissions/a6aff0eb-fd09-42c0-8bc2-8c3c9fd4ff59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Finite Lévy dyadic signed quadrature on the original negative-mark measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n k : ℕ,
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → Set ℝ := fun i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      |(∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) * (X.ν (C i)).toReal) -
        (∫ z in B, z ∂X.ν)| ≤
        (1 / (2 : ℝ) ^ k) * (X.ν B).toReal := by
  classical
  intro n k
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → Set ℝ := fun i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  have hBmeas : MeasurableSet B := measurableSet_Ioc
  have hCmeas (i : ℕ) : MeasurableSet (C i) := by
    dsimp [C, B]
    exact measurableSet_Ioc.inter measurableSet_Ioc
  have hBsub : B ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lt_of_le_of_lt hz.2 (neg_lt_zero.mpr hp)
  have hBfin : X.ν B ≠ ⊤ := by
    apply ne_top_of_lt
    exact lt_of_le_of_lt (measure_mono hBsub) (lt_top_iff_ne_top.mpr hFinite)
  have hCfin (i : ℕ) : X.ν (C i) ≠ ⊤ := by
    apply ne_top_of_lt
    exact lt_of_le_of_lt (measure_mono (fun z hz => hBsub hz.1))
      (lt_top_iff_ne_top.mpr hFinite)
  have hCover : (⋃ i ∈ Finset.range (2 ^ k), C i) = B := by
    apply Set.Subset.antisymm
    · intro z hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨hi, hz⟩
      exact hz.1
    · intro z hz
      have hz0 : z ≤ 0 := le_of_lt (hBsub hz)
      obtain ⟨i, hi, hCell⟩ := avram_anoise43_unit_dyadic_halfopen_cover k z hz.1 hz0
      exact Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hi, ⟨hz, hCell⟩⟩⟩
  have hBandBound : ∀ z ∈ B, |z| ≤ (1 : ℝ) := by
    intro z hz
    have hz0 : z ≤ 0 := le_of_lt (hBsub hz)
    rw [abs_of_nonpos hz0]
    linarith [hz.1]
  have hBInt : IntegrableOn (fun z : ℝ => z) B X.ν := by
    apply Measure.integrableOn_of_bounded hBfin continuous_id.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hBmeas] with z hz
    simpa using hBandBound z hz
  have hCellInt (i : ℕ) : IntegrableOn (fun z : ℝ => z) (C i) X.ν :=
    hBInt.mono_set (by intro z hz; exact hz.1)
  have hDisj (i j : ℕ) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    have hsub (a : ℕ) : C a ⊆
        Ioc (-1 + (a : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((a : ℝ) + 1) / (2 : ℝ) ^ k) := by
      intro z hz; exact hz.2
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
  have hIntegralPartition : (∫ z in B, z ∂X.ν) =
      ∑ i ∈ Finset.range (2 ^ k), (∫ z in C i, z ∂X.ν) := by
    rw [← hCover]
    apply integral_biUnion_finset (Finset.range (2 ^ k))
    · intro i hi; exact hCmeas i
    · intro i hi j hj hij; exact hDisj i j hij
    · intro i hi; exact hCellInt i
  let δ : ℝ := 1 / (2 : ℝ) ^ k
  let w : ℕ → ℝ := fun i => -1 + (i : ℝ) / (2 : ℝ) ^ k
  have hCellError (i : ℕ) (hi : i ∈ Finset.range (2 ^ k)) :
      |w i * (X.ν (C i)).toReal - (∫ z in C i, z ∂X.ν)| ≤
        δ * (X.ν (C i)).toReal := by
    letI : IsFiniteMeasure (X.ν.restrict (C i)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (hCfin i)⟩
    have hc : IntegrableOn (fun _ : ℝ => w i) (C i) X.ν := integrable_const _
    have heq : w i * (X.ν (C i)).toReal - (∫ z in C i, z ∂X.ν) =
        -(∫ z in C i, (z - w i) ∂X.ν) := by
      rw [integral_sub (hCellInt i) hc, setIntegral_const]
      simp only [Measure.real, Measure.restrict_apply_univ]
      ring
    have hAE : ∀ᵐ z ∂(X.ν.restrict (C i)), ‖z - w i‖ ≤ δ := by
      filter_upwards [ae_restrict_mem (hCmeas i)] with z hz
      simpa only [Real.norm_eq_abs, w, C, δ] using
        avram_anoise34_dyadic_mark_cell_endpoint_error n k i z hz
    have hnorm := norm_integral_le_of_norm_le_const hAE
    rw [heq, abs_neg]
    simpa only [Measure.real, Measure.restrict_apply_univ, Real.norm_eq_abs] using hnorm
  have hNuSum : (∑ i ∈ Finset.range (2 ^ k), (X.ν (C i)).toReal) =
      (X.ν B).toReal := by
    have hMeasure : X.ν (⋃ i ∈ Finset.range (2 ^ k), C i) =
        ∑ i ∈ Finset.range (2 ^ k), X.ν (C i) := by
      apply measure_biUnion_finset
      · intro i hi j hj hij; exact hDisj i j hij
      · intro i hi; exact hCmeas i
    rw [hCover] at hMeasure
    have hf : ∀ i ∈ Finset.range (2 ^ k), X.ν (C i) ≠ ⊤ := by
      intro i hi; exact hCfin i
    rw [← ENNReal.toReal_sum hf, ← hMeasure]
  calc
    |(∑ i ∈ Finset.range (2 ^ k), w i * (X.ν (C i)).toReal) -
        (∫ z in B, z ∂X.ν)| =
        |∑ i ∈ Finset.range (2 ^ k),
          (w i * (X.ν (C i)).toReal - (∫ z in C i, z ∂X.ν))| := by
          rw [hIntegralPartition, Finset.sum_sub_distrib]
    _ ≤ ∑ i ∈ Finset.range (2 ^ k),
          |w i * (X.ν (C i)).toReal - (∫ z in C i, z ∂X.ν)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (2 ^ k), δ * (X.ν (C i)).toReal := by
      apply Finset.sum_le_sum
      intro i hi; exact hCellError i hi
    _ = δ * (X.ν B).toReal := by rw [← Finset.mul_sum, hNuSum]
