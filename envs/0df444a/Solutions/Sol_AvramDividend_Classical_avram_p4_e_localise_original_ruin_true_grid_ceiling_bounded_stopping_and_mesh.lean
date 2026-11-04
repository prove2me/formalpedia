-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_ruin_true_grid_ceiling_bounded_stopping_and_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:47:01.586193+00:00
-- url     : https://prove2.me/submissions/760084fa-b052-4347-8051-d1d753e9a079

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

/-- Genuine original ruin-clipped source admits a bounded stopping ceiling within one grid mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (N : ℕ) (hN : (n : ℝ≥0) ≤ e N)
    (δ : ℝ≥0) (h0 : e 0 = 0)
    (hStep : ∀ i, e (i + 1) ≤ e i + δ)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ)) :
    ∃ K : Ω → ℕ,
      IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      (∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ)) ∧
      (∀ ω, (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤ e (K ω) ∧
        e (K ω) ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal + δ) := by
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
  have hτN : ∀ ω, τ ω ≤ e N := by
    intro ω
    have hn : τ ω ≤ (n : ℝ≥0) :=
      (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
    exact hn.trans hN
  let cover : ∀ ω, ∃ j : ℕ, τ ω ≤ e j := fun ω => ⟨N, hτN ω⟩
  let K : Ω → ℕ := fun ω =>
    @Nat.find (fun j : ℕ => τ ω ≤ e j)
      (Classical.decPred (fun j : ℕ => τ ω ≤ e j)) (cover ω)
  have hEB := avram_p4_e_localise_original_truncated_ruin_grid_ceiling_index_adapted
    X x D n τ hτeq hτstop e he N hτN
  change (∀ i, MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω ≤ i}) ∧
    (∀ ω, K ω ≤ N) at hEB
  have hStopBound := avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
    X x D n τ hτeq e he 𝓖 h𝓖 K hEB.1 N hEB.2
  refine ⟨K, hStopBound.1, hStopBound.2, ?_⟩
  have hMesh := avram_p4_e_localise_original_first_ceiling_clock_mesh_error
    X x D n τ hτeq e he N hτN δ h0 hStep
  intro ω
  exact hMesh ω