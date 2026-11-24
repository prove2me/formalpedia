-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.imported_results_hold
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:21.818164+00:00
-- url     : https://prove2.me/submissions/ade30e28-3493-4432-93cd-2547ce908f14

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DerivedCoefficientIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.LE.PImportsHold := by
  intro hPR hFit S hL hfit hnL hRO w hlen
  have hL0 : 0 < S.L := by linarith
  have hN1 : (1:ℝ) ≤ S.Ntot := by
    have : 1 ≤ S.Ntot := by omega
    exact_mod_cast this
  have hαβ : S.α < S.β := by nlinarith
  have hmid := (hFit S hL hfit).1 w.length hlen
  have hJ : ∀ Y ∈ (S.step w).J,
      Y ∈ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro Y hY
    apply hmid
    have hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hY
    rw [S.step_a, S.step_L] at hY'
    exact hY'
  have hPfun : (S.step w).P = fun Y => ∏ s, (Y + S.lam s) := funext (S.step_P w)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hPfun]
    exact (continuous_finset_prod Finset.univ
      (fun s _ => continuous_id.add continuous_const)).continuousOn
  · intro Y hY
    rw [S.step_P]
    refine Finset.prod_ne_zero_iff.mpr (fun s _ => ?_)
    intro h0
    have hYm := hJ Y hY
    apply hRO s
    refine ⟨?_, ?_⟩ <;> nlinarith [hYm.1, hYm.2]
  · intro Y s hY hYs
    have hYm := hJ Y hY
    have hYsm := hJ (Y + s) hYs
    have hY' : Y ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hY
    have hYs' : Y + s ∈ Set.Icc (S.step w).a ((S.step w).a + (S.step w).L) := hYs
    rw [S.step_L] at hY' hYs'
    have key := hPR (S.k + 2 * S.r + 1) S.lam S.α S.β S.L (Y + s) (-s) hαβ
      (fun t ht => hRO t ⟨ht.1.le, ht.2.le⟩) hL0.le hnL
      (by rw [abs_neg]; exact abs_le.mpr ⟨by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2], by linarith [hY'.1, hY'.2, hYs'.1, hYs'.2]⟩)
      hYsm.1 hYsm.2 (by linarith [hYm.1]) (by linarith [hYm.2])
    simp only [add_neg_cancel_right] at key
    rw [S.step_P, S.step_P]
    exact key
end Formalism.FourierDecayAlt.P
