-- Prove2me | solution 1 for GenCountSampleLLL.insertion_product_resampling_balance
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:06:01.742201+00:00
-- url     : https://prove2.me/submissions/fb2a1a1c-fc40-41d9-86bc-15707c125dfe

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal
open GenCountSampleLLL

theorem solution (I : Inst) (U : Finset (Fin I.n)) (σ τ : I.Assign) :
    I.nuA σ * I.nuU U τ = I.nuU U σ * I.nuA (I.merge U τ σ) := by
  unfold Inst.nuA Inst.nuU
  have hp (x : I.Assign) : (∏ v ∈ U, (I.ν v (x v)).toReal) =
      ∏ v : Fin I.n, if v ∈ U then (I.ν v (x v)).toReal else 1 := by
    rw [← Finset.prod_filter]
    simp
  rw [hp τ, hp σ, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases h : v ∈ U <;> simp [h, Inst.merge] <;> ring

