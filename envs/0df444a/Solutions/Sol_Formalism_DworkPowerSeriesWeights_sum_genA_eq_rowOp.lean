-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sum_genA_eq_rowOp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:34.271422+00:00
-- url     : https://prove2.me/submissions/3095af86-1d07-40ca-a539-22a1bca08055

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sum_ZV_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d] (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (s : ZMod d) (i : Fin N0) (b : Fin N1) :
    (∑ j : ZV d N0 N1, MvPolynomial.C (genA TT T (s, i, b) j) * MvPolynomial.X j :
      MvPolynomial (ZV d N0 N1) K) = rowOp (N1 := N1) TT T s i b := by
  classical
  rw [sum_ZV_slice s b]
  · simp only [genA, rowOp, effMat, eq_self_iff_true, and_self, ↓reduceIte]
    by_cases h : s ∈ TT ∧ i.val = 0
    · simp only [if_pos h]
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hk]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · simp only [if_neg h]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split_ifs <;> simp
  · intro y hy
    simp only [genA]
    rw [if_neg hy, map_zero, zero_mul]
end Formalism.DworkPowerSeriesWeights
