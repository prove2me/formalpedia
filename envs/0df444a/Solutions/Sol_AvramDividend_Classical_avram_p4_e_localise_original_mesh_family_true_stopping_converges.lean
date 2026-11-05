-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_mesh_family_true_stopping_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:45:33.726454+00:00
-- url     : https://prove2.me/submissions/fa430178-d4fe-4f66-aa54-73f7361cf88c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original stopped clock is the limit of true bounded stopping ceilings on varying grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (n : ℕ)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (N : ℕ → ℕ) (hN : ∀ k, (n : ℝ≥0) ≤ e k (N k))
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (h0 : ∀ k, e k 0 = 0)
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
    ∃ K : ℕ → Ω → ℕ,
      (∀ k, IsStoppingTime (𝓖 k)
        (fun ω => (K k ω : WithTop ℕ))) ∧
      (∀ k ω, (K k ω : WithTop ℕ) ≤ (N k : WithTop ℕ)) ∧
      (∀ ω, Tendsto (fun k => e k (K k ω)) atTop
        (𝓝 ((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal))) := by
  obtain ⟨K, hInfo⟩ :=
    avram_p4_e_localise_original_every_mesh_true_bounded_stopping_and_error
      X x D hD n e he N hN δ h0 hStep 𝓖 h𝓖
  refine ⟨K, (fun k => (hInfo k).1), (fun k ω => (hInfo k).2.1 ω), ?_⟩
  let τ : Ω → ℝ≥0 :=
    fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro ω
    rfl
  have hLower : ∀ k ω, τ ω ≤ e k (K k ω) :=
    fun k ω => ((hInfo k).2.2 ω).1
  have hUpper : ∀ k ω, e k (K k ω) ≤ τ ω + δ k :=
    fun k ω => ((hInfo k).2.2 ω).2
  exact avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
    X x D n τ hτeq e K δ hδ hLower hUpper
