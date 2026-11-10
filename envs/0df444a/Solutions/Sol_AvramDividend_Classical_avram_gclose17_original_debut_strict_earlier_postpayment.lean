-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_debut_strict_earlier_postpayment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:32:27.333142+00:00
-- url     : https://prove2.me/submissions/63f00a9b-6ed5-4ed3-a2ae-668b233bb044

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gclose16_original_sampled_preexit_clipped_clock_floor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Every strict physical prefix of the supremum of clipped original lower-exit
clocks has positive actual postpayment reserve. No terminal contact is assumed. -/
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
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) :
    let ρ : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)
    ∀ ω (T : ℝ≥0), (T : WithTop ℝ≥0) < (⨆ n : ℕ, ρ n ω) →
      ∀ s : ℝ≥0, s < T →
        0 < x + X.X s ω - rightLimit D s ω := by
  classical
  dsimp
  intro ω T hT s hs
  have hpick : ∃ n : ℕ, (T : WithTop ℝ≥0) <
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤) := by
    by_contra hnone
    have hupper : (⨆ n : ℕ, min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)) ≤ (T : WithTop ℝ≥0) := by
      apply iSup_le
      intro n
      exact le_of_not_gt (fun hn => hnone ⟨n, hn⟩)
    exact (not_le_of_gt hT) hupper
  rcases hpick with ⟨n, hn⟩
  have hfloor :=
    (avram_gclose16_original_sampled_preexit_clipped_clock_floor
      X x D hD σ hσstop r hgrid (δ n)).2.2 ω T (le_of_lt hn) s hs
  exact lt_of_lt_of_le (hδpos n) hfloor
