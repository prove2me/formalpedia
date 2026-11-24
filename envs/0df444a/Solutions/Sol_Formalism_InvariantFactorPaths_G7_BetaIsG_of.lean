-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.BetaIsG_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:17.489907+00:00
-- url     : https://prove2.me/submissions/95edb6d8-a8b9-436d-88b3-8923361ac3e7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLiftLeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_divAB_of_suppOK

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (h0 : StepZero) (h1 : StepI) (h2 : StepII) (hH : StepH) (h3 : StepIII)
    (h4 : StepIV) (hSw : SwapRules) (hS : SimeqRules) : BetaIsG := by
  intro K _ _ _ _ p σ hU hζ F hF be hbe
  obtain ⟨G, hGs, hGbe, hG1, hG2⟩ := h0 K p σ hU hζ F hF be hbe
  have hp2 : 2 ≤ p := hU.2.1.le
  obtain ⟨hss, hsupp, hdivsw, -, -, -⟩ := hSw K p σ G 0 0 hp2
  obtain ⟨c, hc, hcG⟩ := h1 K p σ hU F hF G hGs hG1 hG2
  obtain ⟨c', hc', hcG'⟩ := h1 K p σ hU F hF (swap2 G) (hsupp hGs) hG2 (by rw [hss]; exact hG1)
  have hdG : DivAB G := divAB_of_suppOK hGs
  have hI1 := h2 K p σ hU F hF G c hdG hG1 hc hcG
  have hI2 := h2 K p σ hU F hF (swap2 G) c' (hdivsw hdG) hG2 hc' hcG'
  have hHs := hH K p σ hU F hF G (σ c) (σ c') hGs hI1 hI2
  have e1 : c + σ c' = 0 := h3 K p σ hU G c c' hc hc' hcG hHs
  have hHs' : Integral (Hser p σ (swap2 G) (σ c') (σ c)) := by
    rw [(hSw K p σ G (σ c) (σ c') hp2).2.2.2.2.2]
    exact (hSw K p σ (Hser p σ G (σ c) (σ c')) 0 0 hp2).2.2.2.1 hHs
  have e2 : c' + σ c = 0 := h3 K p σ hU (swap2 G) c' c hc' hc hcG' hHs'
  have hA : σ c' = -c := by linear_combination e1
  have hB : σ c' = -σ (σ c) := by
    rw [show c' = -σ c by linear_combination e2, map_neg]
  have hσσ : σ (σ c) = c := by linear_combination hB - hA
  rw [hA] at hHs
  have hSimG : Simeq G (Gser p c (σ c)) := h4 K p σ hU G c hdG hσσ hHs
  obtain ⟨-, hsymm, htrans, -, -⟩ := hS K (Fin 2)
  exact ⟨c, hc, hσσ, htrans _ _ _ (hsymm _ _ hGbe) hSimG⟩
end Formalism.InvariantFactorPaths.G7
