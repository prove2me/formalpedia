-- Prove2me | solution 2 for AvramDividend.Classical.shifted_future_strip_implies_drawdown_guard
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:39:39.266967+00:00
-- url     : https://prove2.me/submissions/512888ed-6250-4eaa-b9a1-47260821b71f

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! A future path confined to a strip has reflected drawdown below its width. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a ε : ℝ) (ω : Ω) (u T : ℝ≥0)
    (hUpper : ∀ r : ℝ≥0, r ≤ T →
      X.X (u + r) ω - X.X u ω ≤ ε)
    (hLower : ∀ r : ℝ≥0, r ≤ T →
      ε - a ≤ X.X (u + r) ω - X.X u ω) :
    ∀ t : ℝ≥0, t ≤ T →
      sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
        X.X (u + t) ω ≤ a := by
  intro t ht
  let A : Set ℝ :=
    (fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t
  have hAne : A.Nonempty := by
    refine ⟨X.X (u + 0) ω, ?_⟩
    exact ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, zero_le⟩, rfl⟩
  have hAupper : ∀ x ∈ A, x ≤ X.X u ω + ε := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrT : r ≤ T := le_trans hr.2 ht
    have h := hUpper r hrT
    linarith
  have hSup : sSup A ≤ X.X u ω + ε :=
    csSup_le hAne hAupper
  have hMin := hLower t ht
  change sSup A - X.X (u + t) ω ≤ a
  linarith
