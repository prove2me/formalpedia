-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:22:03.182192+00:00
-- url     : https://prove2.me/submissions/9c0e0a99-e86f-4321-acea-d1b42a6c0d17

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n → StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ i : ℕ, i < n → dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    ∃ F : Ω → ℝ≥0∞, Measurable[𝓕 T] F ∧
      (∀ᵐ ω ∂P, F ω = ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) := by
  classical
  let J : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ (Set.univ : Set ℝ))
  have hEvents (k : ℕ) : ∃ E : Set Ω, MeasurableSet[𝓕 T] E ∧ (∀ᵐ ω ∂P, (J ω = (k : ℝ≥0∞) ↔ ω ∈ E)) := by
    simpa only [J] using
      (avram_wave4_04a_actual_original_jump_count_k_filtration_measurable_version_on_fine_grids
        X hBV hFinite T hT grid hGrid hMesh hBound k)
  let E : ℕ → Set Ω := fun k => Classical.choose (hEvents k)
  have hEm (k : ℕ) : MeasurableSet[𝓕 T] (E k) :=
    (Classical.choose_spec (hEvents k)).1
  have hEa (k : ℕ) : ∀ᵐ ω ∂P, (J ω = (k : ℝ≥0∞) ↔ ω ∈ E k) :=
    (Classical.choose_spec (hEvents k)).2
  let F : Ω → ℝ≥0∞ := fun ω => ∑' k : ℕ, if ω ∈ E k then (k : ℝ≥0∞) else 0
  have hFm : Measurable[𝓕 T] F := by
    exact Measurable.ennreal_tsum (fun k => Measurable.ite (hEm k) measurable_const measurable_const)
  have hEaAll : ∀ᵐ ω ∂P, ∀ k : ℕ, (J ω = (k : ℝ≥0∞) ↔ ω ∈ E k) :=
    ae_all_iff.mpr hEa
  have hNat : ∀ᵐ ω ∂P, ∃ k : ℕ, J ω = (k : ℝ≥0∞) := by
    filter_upwards [avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae X hBV hFinite] with ω hfin
    let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Set.univ}
    have hS : S.Finite := by
      apply (hfin T).subset
      intro u ⟨huPos, _, huLe, huJump, _⟩
      exact ⟨huLe, huPos, huJump⟩
    refine ⟨S.ncard, ?_⟩
    have hJ := avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard X ω 0 T (Set.univ : Set ℝ) MeasurableSet.univ
    change J ω = (S.encard : ℝ≥0∞) at hJ
    rw [hJ]
    exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) hS.encard_eq_coe
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hEaAll, hNat] with ω hEq hK
  rcases hK with ⟨k, hk⟩
  have hCases (j : ℕ) : (ω ∈ E j) ↔ j = k := by
    constructor
    · intro hj
      have hval : J ω = (j : ℝ≥0∞) := (hEq j).mpr hj
      have heq : (j : ℝ≥0∞) = (k : ℝ≥0∞) := hval.symm.trans hk
      exact_mod_cast heq
    · intro hj
      subst j
      exact (hEq k).mp hk
  have hF : F ω = (k : ℝ≥0∞) := by
    calc
      F ω = ∑' j : ℕ, if j = k then (j : ℝ≥0∞) else 0 := by
        apply tsum_congr; intro j; simp only [F, hCases j]
      _ = (k : ℝ≥0∞) := tsum_ite_eq k (fun j : ℕ => (j : ℝ≥0∞))
  exact hF.trans hk.symm
