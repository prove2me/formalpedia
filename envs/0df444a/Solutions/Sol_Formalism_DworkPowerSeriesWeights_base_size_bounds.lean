-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.base_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:58.969802+00:00
-- url     : https://prove2.me/submissions/0c3d6f51-1c82-4cba-b3a1-ef073f7e0b72

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow

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
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SizesB := by
  intro H _ _ TT c wt wt' f k b b' hcard hk hb hb' hc1 hc2 hwt hwt'
  constructor
  · have h1 : ∀ t, c t ≤ 4 * k * b' + (if t ∈ TT then 2 * b else 0) := by
      intro t
      split_ifs with h
      · exact hc2 t h
      · rw [add_zero]; exact hc1 t h
    calc (∑ t, c t) ≤ ∑ t, (4 * k * b' + (if t ∈ TT then 2 * b else 0)) :=
          Finset.sum_le_sum fun t _ => h1 t
      _ = 2 * (TT.card : ℝ) * b + 2 * f * k * b' := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
            Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          ring
  · have hf : 0 ≤ f := by
      have : (0 : ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
      linarith
    have h0 : 0 ≤ ∑ t, min (wt t) (wt' t) :=
      Finset.sum_nonneg fun t _ => le_min (hwt t).1 (hwt' t)
    have h1 : (∑ t, min (wt t) (wt' t)) ≤ f * b' := by
      calc (∑ t, min (wt t) (wt' t)) ≤ ∑ _t : H, 2 * b' :=
            Finset.sum_le_sum fun t _ => (min_le_left _ _).trans (hwt t).2
        _ = f * b' := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
            ring
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ (k - 1) / 2), abs_of_nonneg h0]
    have hfb : 0 ≤ f * b' := mul_nonneg hf hb'
    calc (k - 1) / 2 * ∑ t, min (wt t) (wt' t) ≤ (k - 1) / 2 * (f * b') :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ k * (f * b') := mul_le_mul_of_nonneg_right (by linarith) hfb
      _ = f * k * b' := by ring
end Formalism.DworkPowerSeriesWeights
