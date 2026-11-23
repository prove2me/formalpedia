-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_PairSplit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:12.494935+00:00
-- url     : https://prove2.me/submissions/400d4783-6806-49c4-b263-417de0ca0425

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_summable_re
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_norm_sq_tsum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
open Classical
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : PairSplit := by
  intro τ Rw I H H₁ _ _ _ _ _ _ X hA hO hS0
  set Z : τ × τ → ℝ := fun p => (inner ℂ (X.vec p.1) (X.vec p.2)).re with hZdef
  have hZ : Summable Z := summable_re X.vec hA.2.1
  have c1 : ∀ S : Set τ, X.PhiEq S = X.pairSum (X.allPairs S) := by
    intro S
    unfold Terms.PhiEq Terms.pairSum
    congr 1
    have hi : ∀ i, ‖X.vecPart S i‖ ^ 2 = ∑' p : τ × τ,
        (if X.io (X.rowOf p.1) = i then
          (if p.1 ∈ S ∧ p.2 ∈ S ∧ X.io (X.rowOf p.2) = X.io (X.rowOf p.1) then Z p else 0) else 0) := by
      intro i
      unfold Terms.vecPart
      rw [norm_sq_tsum]
      · apply tsum_congr; intro p
        by_cases h1 : X.io (X.rowOf p.1) = i <;> by_cases h2 : X.io (X.rowOf p.2) = i <;>
          by_cases h3 : p.1 ∈ S <;> by_cases h4 : p.2 ∈ S <;>
          simp [Set.indicator, h1, h2, h3, h4, hZdef]
      · simp_rw [norm_indicator_eq_indicator_norm]
        exact hA.2.1.indicator _
    simp_rw [hi]
    rw [← Summable.tsum_finsetSum]
    · apply tsum_congr; intro p
      rw [Finset.sum_ite_eq]
      simp only [mem_univ, if_true]
      by_cases h3 : p.1 ∈ S <;> by_cases h4 : p.2 ∈ S <;>
        by_cases h5 : X.rowOf p.1 = X.rowOf p.2 <;>
        simp [Set.indicator, Terms.allPairs, h3, h4, h5]
      all_goals first
        | rfl
        | (intro h6
           have := hO p.1 p.2 h6.symm h5
           simp [hZdef, this])
    · intro i _
      refine Summable.of_norm_bounded hZ.norm (fun p => ?_)
      split_ifs <;> simp
  refine ⟨c1, ?_, ?_⟩
  · rw [c1]
    unfold Terms.pairSum
    rw [← mul_add, ← mul_add, ← Summable.tsum_add (hZ.indicator _) (hZ.indicator _),
      ← Summable.tsum_add ((hZ.indicator _).add (hZ.indicator _)) (hZ.indicator _)]
    congr 1
    apply tsum_congr; intro p
    by_cases h : p ∈ X.allPairs X.genSet
    · have h1 : 1 ≤ X.s0 p.1 p.2 := hS0 p.1 p.2 h.2.2 h.1.1 h.2.1.1
      by_cases h2 : X.s0 p.1 p.2 = 1
      · by_cases h3 : X.scal p.1 p.2 <;>
          simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h, h2, h3] <;> rfl
      · have h4 : 2 ≤ X.s0 p.1 p.2 := by omega
        simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h, h2, h4]; rfl
    · simp [Set.indicator, Terms.big, Terms.nsc, Terms.sc, h]
  · rw [c1]
    unfold Terms.pairSum
    rw [← mul_add, ← Summable.tsum_add (hZ.indicator _) (hZ.indicator _)]
    congr 1
    apply tsum_congr; intro p
    by_cases h : p ∈ X.allPairs X.ngSet
    · have h1 : 1 ≤ X.s0 p.1 p.2 := hS0 p.1 p.2 h.2.2 h.1.1 h.2.1.1
      by_cases h2 : X.s0 p.1 p.2 = 1
      · simp [Set.indicator, Terms.big, Terms.one, h, h2]; rfl
      · have h4 : 2 ≤ X.s0 p.1 p.2 := by omega
        simp [Set.indicator, Terms.big, Terms.one, h, h2, h4]; rfl
    · simp [Set.indicator, Terms.big, Terms.one, h]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
