-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:37:07.874831+00:00
-- url     : https://prove2.me/submissions/d450bc76-0ea1-4b10-9a93-f5ba7aca04d2

import Mathlib
import Mathlib.Data.Nat.Find
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_first_ceiling_clock_mesh_error

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite grid is a true original-filtration stopping ceiling, uniformly within its own mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (N : ℕ → ℕ) (hN : ∀ k, (n : ℝ≥0) ≤ e k (N k))
    (δ : ℕ → ℝ≥0) (h0 : ∀ k, e k 0 = 0)
    (hStep : ∀ k i, e k (i + 1) ≤ e k i + δ k)
    (𝓖 : ℕ → Filtration ℕ mΩ)
    (h𝓖 : ∀ k, 𝓖 k =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e k i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he k hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e k i) } : Filtration ℕ mΩ)) :
    ∃ K : ℕ → Ω → ℕ, ∀ k,
      IsStoppingTime (𝓖 k) (fun ω => (K k ω : WithTop ℕ)) ∧
      (∀ ω, (K k ω : WithTop ℕ) ≤ (N k : WithTop ℕ)) ∧
      (∀ ω,
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ e k (K k ω) ∧
        e k (K k ω) ≤
          (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal + δ k) := by
  classical
  let τ : Ω → ℝ≥0 :=
    fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro ω
    rfl
  have hRuin : IsStoppingTime 𝓕.rightCont (ruinTime X x D) :=
    ruinTime_stopping_rightCont_filtration X x D hD
  have hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    avram_wave7_08_actual_truncated_clock_stopping_of_ruin_stopping
      X x D n hRuin
  have hτN : ∀ k ω, τ ω ≤ e k (N k) := by
    intro k ω
    have hn : τ ω ≤ (n : ℝ≥0) :=
      (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
    exact hn.trans (hN k)
  let cover : ∀ k ω, ∃ j : ℕ, τ ω ≤ e k j :=
    fun k ω => ⟨N k, hτN k ω⟩
  let K : ℕ → Ω → ℕ := fun k ω =>
    @Nat.find (fun j : ℕ => τ ω ≤ e k j)
      (Classical.decPred (fun j : ℕ => τ ω ≤ e k j)) (cover k ω)
  refine ⟨K, ?_⟩
  intro k
  have hEB := avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
    X x D n τ hτeq hτstop (e k) (he k) (N k) (hτN k)
  change (∀ i, MeasurableSet[𝓕.rightCont (e k i)]
      {ω : Ω | K k ω ≤ i}) ∧
    (∀ ω, K k ω ≤ N k) at hEB
  have hStop := avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
    X x D n τ hτeq (e k) (he k) (𝓖 k) (h𝓖 k) (K k)
    hEB.1 (N k) hEB.2
  have hMesh := avram_p4_e_localise_original_first_ceiling_clock_mesh_error
    X x D n τ hτeq (e k) (he k) (N k) (hτN k)
    (δ k) (h0 k) (hStep k)
  exact ⟨hStop.1, hStop.2, hMesh⟩
