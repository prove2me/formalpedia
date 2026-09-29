-- Prove2me | solution 1 for FamousTheorems.prokhorov
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:17:48.239906+00:00
-- url     : https://prove2.me/submissions/a185c48a-bda7-4c74-aaa3-da3380a38173

import Mathlib

theorem solution {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]
    {u : ℕ → NNReal} {K : ℕ → Set E} (C : NNReal) (hu : Filter.Tendsto u Filter.atTop (nhds 0))
    (hK : ∀ n, IsCompact (K n)) (h : NormalSpace E ∨ Monotone K) :
    IsCompact {μ : MeasureTheory.FiniteMeasure E | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} :=
  isCompact_setOfPred_finiteMeasure_mass_le_compl_isCompact_le C hu hK h
