-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.edgeFactors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:56.6138+00:00
-- url     : https://prove2.me/submissions/bea98b0a-fffe-43f9-9270-ba335f692fca

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_edge_factor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_kDel_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Formalism.FourierDecayAlt.P.Sz4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Sz.EdgeFactors := by
  intro c de hc hw
  refine ⟨fun i h2 hik h => edge_factor c de hc hw i h2 hik h, fun ht => ?_⟩
  have hk := hc.hk
  have hcard : (Icc 2 c.k).card = c.k - 1 := by rw [Nat.card_Icc]; omega
  have hpos : 0 ≤ c.a - c.v 1 := by
    have := kDel_pos c hc
    linarith [hc.ha]
  constructor
  · calc (c.a - c.v 1) ^ (c.k - 1) = ∏ _i ∈ Icc 2 c.k, (c.a - c.v 1) := by
          rw [Finset.prod_const, hcard]
      _ ≤ _ := by
          refine Finset.prod_le_prod (fun _ _ => hpos) fun i hi => ?_
          rw [mem_Icc] at hi
          exact (edge_factor c de hc hw i hi.1 hi.2 (Or.inr ht)).1
  · calc _ ≤ ∏ _i ∈ Icc 2 c.k, (2 * (c.a - c.v 1)) := by
          refine Finset.prod_le_prod (fun i hi => ?_) fun i hi => ?_
          · rw [mem_Icc] at hi
            exact hpos.trans (edge_factor c de hc hw i hi.1 hi.2 (Or.inr ht)).1
          · rw [mem_Icc] at hi
            exact (edge_factor c de hc hw i hi.1 hi.2 (Or.inr ht)).2
      _ = _ := by rw [Finset.prod_const, hcard]
end Formalism.FourierDecayAlt.P
