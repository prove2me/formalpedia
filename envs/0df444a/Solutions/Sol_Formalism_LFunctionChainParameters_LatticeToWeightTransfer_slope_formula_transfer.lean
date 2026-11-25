-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.slope_formula_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:27.86083+00:00
-- url     : https://prove2.me/submissions/e491192d-fb6f-4087-bd71-87b8236e3ef9

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_slope_via_lengths


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution : LatticeSlopeComparison := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX σ τ M N β hM hM0 hN hrk hβ S eR l sg' tau len hoff he hl hsg
    htau hlen
  classical
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  obtain ⟨-, -, h1, h2⟩ := slopeLatticeData.slope_via_lengths K V ι b X hX σ τ M N β hM hM0 hN hrk hβ
  have hd : (rkK M : ℝ) ≠ 0 := by exact_mod_cast (slopeLatticeData.rkK_pos hM0).ne'
  have hSg : slopeLatticeData.sgSum σ τ = UnitWeightPartition.Sg S l sg' tau := by
    unfold slopeLatticeData.sgSum UnitWeightPartition.Sg
    have hsub : σ.support ∪ τ.support ⊆ S := by
      intro w hw
      by_contra hS
      obtain ⟨a, b', -⟩ := hoff w hS
      rcases Finset.mem_union.1 hw with h | h
      · exact (Finsupp.mem_support_iff.1 h) a
      · exact (Finsupp.mem_support_iff.1 h) b'
    have hstep : ∑ w ∈ σ.support ∪ τ.support, 2 * slopeLatticeData.ell w * ((σ w : ℝ) - (τ w : ℝ))
        = ∑ w ∈ S, 2 * slopeLatticeData.ell w * ((σ w : ℝ) - (τ w : ℝ)) := by
      refine Finset.sum_subset hsub fun w _ hw => ?_
      rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hw
      rw [hw.1, hw.2]; simp
    refine Eq.trans ?_ (hstep.trans ?_)
    · exact Finset.sum_congr (by congr) fun _ _ => rfl
    · refine Finset.sum_congr rfl fun w hw => ?_
      have := (he w hw).ne'
      rw [hl w hw, hsg w hw, htau w hw]
      field_simp
  have hBe : ∑ᶠ w : slopeLatticeData.FinPl K, 2 * slopeLatticeData.ell w * β w = UnitWeightPartition.BeSum S l (rkK M : ℝ) len tau := by
    rw [finsum_eq_sum_of_support_subset (s := S)]
    · unfold UnitWeightPartition.BeSum UnitWeightPartition.be
      refine Finset.sum_congr rfl fun w hw => ?_
      have := (he w hw).ne'
      rw [hl w hw, hlen w hw, htau w hw]
      field_simp
      ring
    · intro w hw
      by_contra hS
      rw [Function.mem_support, (hoff w hS).2.2, mul_zero] at hw
      exact hw rfl
  rw [← hSg, ← hBe]
  exact ⟨h1, h2⟩
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
