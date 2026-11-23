-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_tri_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:56.254942+00:00
-- url     : https://prove2.me/submissions/2983ea0e-2313-46bd-bc29-1446254fab51

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K ι : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [PartialOrder ι]
    (T : ι → ι → K) (hT : ∀ i j, ‖T i j‖ ≤ 1) (hd : ∀ i, T i i = 1) (h0 : ∀ i j, ¬ i ≤ j → T i j = 0)
    (c : ι → K) (hc : ∀ i, ‖∑ j, c j * T i j‖ ≤ 1) : ∀ i, ‖c i‖ ≤ 1 := by
  classical
  intro i
  induction i using (wellFounded_gt (α := ι)).induction with
  | _ i ih =>
    have h1 : c i = (∑ j, c j * T i j) - ∑ j ∈ Finset.univ.erase i, c j * T i j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hd]; ring
    rw [h1, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc i) ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
    intro j hj
    by_cases hij : i ≤ j
    · have hlt : i < j := lt_of_le_of_ne hij (Finset.ne_of_mem_erase hj).symm
      rw [norm_mul]
      exact mul_le_one₀ (ih j hlt) (norm_nonneg _) (hT i j)
    · rw [h0 i j hij]; simp
end Formalism.DworkPowerSeriesWeights
