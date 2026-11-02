-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsE.integral_mconvex_iff_integral_argmin
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T02:09:23.273113+00:00
-- url     : https://prove2.me/submissions/dfe9ae3c-b632-4cd9-9702-e1ab6d19cdc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_LinearWeightR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_MConvexIntegralR
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_IsMZeroZR
import Theorems.Thm_DiscreteConvex_MConvexFunctionsE_mconvex_four_characterizations

open Classical
open scoped Pointwise
open DiscreteConvex.MConvexFunctionsE

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem solution (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (hdom : (DomR f).Nonempty) :
    MConvexIntegralR f ↔
      ∀ p : V → ℝ, (ArgMinOn (LinearWeightR f (fun v => -p v))).Nonempty →
        IsMZeroZR (ArgMinOn (LinearWeightR f (fun v => -p v))) := by
  have h03 : MExchangeAxiomR f ↔
      ∀ p : V → ℝ, (ArgMinOn (LinearWeightR f (fun v => -p v))).Nonempty →
        IsMZeroR (ArgMinOn (LinearWeightR f (fun v => -p v))) :=
    (mconvex_four_characterizations f hpoly hdom).out 0 3
  unfold MConvexIntegralR IntegralPolyhedralFunction IsMZeroZR
  rw [h03]
  constructor
  · rintro ⟨h1, h2⟩ p hp
    exact ⟨h1 p hp, h2 (fun v => -p v) hp⟩
  · intro h
    refine ⟨fun p hp => (h p hp).1, fun p hp => ?_⟩
    have hneg : (fun v => -(-p v)) = p := by funext v; ring
    have hp' : (ArgMinOn (LinearWeightR f (fun v => -(-p v)))).Nonempty := by
      rwa [hneg]
    have h2 := (h (fun v => -p v) hp').2
    rwa [hneg] at h2
