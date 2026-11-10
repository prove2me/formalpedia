-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_lower_exit_debut_sup_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:32:01.903619+00:00
-- url     : https://prove2.me/submissions/c14c4dab-4b99-48e9-ba18-07af2cb79726

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The candidate first-zero-contact time built from original lower-exit
clocks is an original right-continuous-filtration stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → WithTop ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont σ)
    (r : ℕ → ℝ≥0)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U)
    (δ : ℕ → ℝ) :
    let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)
    IsStoppingTime 𝓕.rightCont (fun ω => ⨆ n : ℕ, ρ n ω) ∧
      ∀ ω, (⨆ n : ℕ, ρ n ω) ≤ σ ω := by
  dsimp
  have hρ (n : ℕ) : IsStoppingTime 𝓕.rightCont
      (fun ω => min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)) :=
    (avram_gclose16_original_sampled_preexit_clipped_clock_floor
      X x D hD σ hσstop r hgrid (δ n)).1
  constructor
  · intro t
    have hset :
        {ω : Ω | (⨆ n : ℕ, min (σ ω) (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
          then (r k : WithTop ℝ≥0) else ⊤)) ≤ (t : WithTop ℝ≥0)} =
        ⋂ n : ℕ, {ω : Ω | min (σ ω) (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
          then (r k : WithTop ℝ≥0) else ⊤) ≤ (t : WithTop ℝ≥0)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, iSup_le_iff]
    change MeasurableSet[𝓕.rightCont t]
      {ω : Ω | (⨆ n : ℕ, min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)) ≤ (t : WithTop ℝ≥0)}
    rw [hset]
    exact MeasurableSet.iInter (fun n => hρ n t)
  · intro ω
    apply iSup_le
    intro n
    exact (avram_gclose16_original_sampled_preexit_clipped_clock_floor
      X x D hD σ hσstop r hgrid (δ n)).2.1 ω
