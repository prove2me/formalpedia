-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.satEmb_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:53.833247+00:00
-- url     : https://prove2.me/submissions/70af9530-f2e7-4e9c-b527-a1442a56b941

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
theorem _root_.solution (d N0 : ℕ) (s t : ZMod d) (v w : Fin N0 × Fin N0) (h : satEmb d N0 s v = satEmb d N0 t w) :
    s = t ∧ v = w := by
  simp only [satEmb, Prod.mk.injEq] at h
  exact ⟨h.1, Prod.ext h.2.2 h.2.1⟩
end Formalism.DworkPowerSeriesWeights
