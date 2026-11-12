-- Prove2me | solution 1 for BunkbedAux.alt_block_sum
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T02:13:16.254483+00:00
-- url     : https://prove2.me/submissions/cc9a83eb-b3b2-4457-af29-2816ef276107

import Theorems.Thm_BunkbedAux_wzGraph_abc_eq_alt
import Theorems.Thm_BunkbedFalse_hollom_alt_probs
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

lemma alt_count (y : Fin 10 × Fin 2) (m : ℚ)
    (h : altProb hollomE hollomT ((0 : Fin 10), (0 : Fin 2)) y = m / 64) :
    (∑ σ : Fin 6 → Fin 2, if (altBBGraph hollomE hollomT σ).Reachable
      ((0 : Fin 10), (0 : Fin 2)) y then (1 : ℚ) else 0) = m := by
  rw [altProb] at h
  have hc : (2 : ℚ) ^ Fintype.card (Fin 6) = 64 := by norm_num
  rw [hc] at h
  field_simp at h
  exact h

/-- The `A`-block sum: over the 64 all-minus configurations the net indicator difference is 1. -/
theorem solution :
    (∑ σ : Fin 6 → Fin 2,
        ((if (wzGraph hollomTriple hollomT
              (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)).Reachable
            ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (1 : Fin 2)) then (1 : ℚ) else 0)
        - (if (wzGraph hollomTriple hollomT
              (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c)).Reachable
            ((0 : Fin 10), (0 : Fin 2)) ((9 : Fin 10), (0 : Fin 2)) then (1 : ℚ) else 0))) = 1 := by
  have hg : ∀ σ : Fin 6 → Fin 2, wzGraph hollomTriple hollomT
      (fun p => if p.2 = σ p.1 then WZ.abc else WZ.a_b_c) = altBBGraph hollomE hollomT σ :=
    fun σ => BunkbedAux.wzGraph_abc_eq_alt σ
  simp only [hg, Finset.sum_sub_distrib]
  rw [alt_count _ 13 BunkbedFalse.hollom_alt_probs.2,
      alt_count _ 12 BunkbedFalse.hollom_alt_probs.1]
  norm_num
