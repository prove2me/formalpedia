-- Prove2me | solution 1 for ContextualAuctions.PoA.first_order
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:16:37.881794+00:00
-- url     : https://prove2.me/submissions/1b50cfeb-8929-4820-8d0d-d34e3ae5392a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_Setting
import Theorems.Thm_ContextualAuctions_PoA_dual_derivative

open MeasureTheory
open ContextualAuctions.PoA

theorem solution (M : ContextualAuctions.PoA.Model) (hM : M.Standing)
    (hr : ∀ α ∈ M.A, M.r α = 0)
    (μ : ContextualAuctions.PoA.Buyer M → ℝ) (hμ : ContextualAuctions.PoA.IsPacing M μ)
    (θ : ContextualAuctions.PoA.Buyer M) (hθ : θ ∈ ContextualAuctions.PoA.Theta M) (tstar : ℝ)
    (ht : 0 ≤ tstar) (hmin : IsMinOn (ContextualAuctions.PoA.qDual M μ θ) (Set.Ici 0) tstar) :
    ContextualAuctions.PoA.payment M (ContextualAuctions.PoA.beta M μ)
        (ContextualAuctions.PoA.bidAt M μ θ tstar) ≤ θ.2 ∧
      tstar * (θ.2 - ContextualAuctions.PoA.payment M (ContextualAuctions.PoA.beta M μ)
        (ContextualAuctions.PoA.bidAt M μ θ tstar)) = 0 := by
  set f' := θ.2 - payment M (beta M μ) (bidAt M μ θ tstar) with hf'
  have hd : HasDerivWithinAt (qDual M μ θ) f' (Set.Ici 0) tstar :=
    ContextualAuctions.PoA.dual_derivative M hM hr μ hμ θ hθ tstar ht
  have hloc : IsLocalMinOn (qDual M μ θ) (Set.Ici 0) tstar := hmin.localize
  have hF := hd.hasFDerivWithinAt
  -- direction `+1` is feasible
  have h1 : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) tstar := by
    apply mem_posTangentConeAt_of_segment_subset
    intro z hz
    rw [segment_eq_Icc (by linarith)] at hz
    exact le_trans ht hz.1
  -- direction `-tstar` is feasible
  have h2 : (-tstar : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) tstar := by
    apply mem_posTangentConeAt_of_segment_subset
    intro z hz
    rw [segment_symm, segment_eq_Icc (by linarith)] at hz
    simp only [Set.mem_Ici]
    linarith [hz.1]
  have n1 := hloc.hasFDerivWithinAt_nonneg hF h1
  have n2 := hloc.hasFDerivWithinAt_nonneg hF h2
  simp at n1 n2
  refine ⟨by linarith, ?_⟩
  nlinarith [mul_nonneg ht n1]
