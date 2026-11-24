-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sizesB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:17:54.045374+00:00
-- url     : https://prove2.me/submissions/88cbdf81-b3b2-401f-a3f9-21507744177c

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneRow
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_IntegralOperatorsOnJets
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GaussB
import Definitions.Def_Formalism_GaussJetBounds_FinalB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : SizesB := by
  unfold SizesB
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'
  have hf0 : 0 ≤ f := by
    have : (0:ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have h1 : ∀ t, c t ≤ 4 * k * b' + (if t ∈ TT then 2 * b else 0) := by
      intro t
      by_cases ht : t ∈ TT
      · rw [if_pos ht]; exact hc2 t ht
      · rw [if_neg ht, add_zero]; exact hc1 t ht
    calc (∑ t, c t) ≤ ∑ t, (4 * k * b' + (if t ∈ TT then 2 * b else 0)) :=
          Finset.sum_le_sum (fun t _ => h1 t)
      _ = (Fintype.card H : ℝ) * (4 * k * b') + (TT.card : ℝ) * (2 * b) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
      _ = 2 * (TT.card : ℝ) * b + 2 * f * k * b' := by rw [hf]; ring
  · have hS0 : 0 ≤ ∑ t, min (wt t) (wt' t) :=
      Finset.sum_nonneg (fun t _ => le_min (hw t).1 (hw' t))
    have hS1 : ∑ t, min (wt t) (wt' t) ≤ f * b' := by
      calc ∑ t, min (wt t) (wt' t) ≤ ∑ _t : H, 2 * b' :=
            Finset.sum_le_sum (fun t _ => (min_le_left _ _).trans (hw t).2)
        _ = f * b' := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hf]; ring
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hS1), mul_nonneg hf0 hb',
        mul_nonneg (mul_nonneg hf0 hb') (by linarith : (0:ℝ) ≤ k + 1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) hS0,
        mul_nonneg (mul_nonneg hf0 (by linarith : (0:ℝ) ≤ k)) hb']
end Formalism.DworkPowerSeriesWeights
