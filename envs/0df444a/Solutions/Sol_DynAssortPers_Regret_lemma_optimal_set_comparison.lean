-- Prove2me | solution 1 for DynAssortPers.Regret.lemma_optimal_set_comparison
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:53:45.217185+00:00
-- url     : https://prove2.me/submissions/fa41e5e8-e700-4526-9c3a-3016de6cab2a

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL
import Theorems.Thm_DynAssortPers_Regret_lemma_revenue_lipschitz

open DynAssortPers.Regret

theorem solution {n : ℕ} (K : ℕ) (w θ θ' : Fin n → ℝ)
    (S S' : Finset (Fin n)) (hS : IsOptimal w θ K S) (hS' : IsOptimal w θ' K S') :
    revenue S w θ - (1 / 2) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' ≤
      revenue S' w θ := by
  have h1 := lemma_revenue_lipschitz K S' hS'.1 w θ θ'
  have h2 := lemma_revenue_lipschitz K S hS.1 w θ θ'
  have h3 := hS'.2 S hS.1
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.2]
