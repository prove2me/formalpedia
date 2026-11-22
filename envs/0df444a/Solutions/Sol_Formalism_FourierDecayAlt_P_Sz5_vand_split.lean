-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.vand_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:07.079932+00:00
-- url     : https://prove2.me/submissions/4a271137-d699-4b04-9ac2-ae1e9138ff5a

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_prod_Ioc_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_Icc_one_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (p q : ℕ) (x : ℕ → ℝ) :
    Vand (p + q) x = Vand p x * (∏ i ∈ Icc 1 p, ∏ j ∈ Icc 1 q, (x i - x (j + p))) *
      Vand q (fun j => x (j + p)) := by
  unfold Vand
  simp only [Icc_one_eq]
  have h1 : ∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc i (p + q), (x i - x j)
      = (∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc i p, (x i - x j)) *
        ∏ i ∈ Ioc 0 p, ∏ j ∈ Ioc 0 q, (x i - x (j + p)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    rw [Finset.mem_Ioc] at hi
    rw [← Finset.prod_Ioc_consecutive _ hi.2 (Nat.le_add_right p q)]
    congr 1
    have hs := prod_Ioc_shift (fun j => x i - x j) p 0 q
    rw [zero_add, Nat.add_comm q p] at hs
    exact hs
  have h2 : ∏ i ∈ Ioc p (p + q), ∏ j ∈ Ioc i (p + q), (x i - x j)
      = ∏ i ∈ Ioc 0 q, ∏ j ∈ Ioc i q, (x (i + p) - x (j + p)) := by
    have hs := prod_Ioc_shift (fun i => ∏ j ∈ Ioc i (p + q), (x i - x j)) p 0 q
    rw [zero_add, Nat.add_comm q p] at hs
    rw [hs]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hs2 := prod_Ioc_shift (fun j => x (i + p) - x j) p i q
    rw [Nat.add_comm q p] at hs2
    exact hs2
  rw [← Finset.prod_Ioc_consecutive _ (Nat.zero_le p) (Nat.le_add_right p q), h1, h2]
end Formalism.FourierDecayAlt.P.Sz5
