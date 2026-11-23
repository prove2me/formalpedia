-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.norm_l_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:46.570453+00:00
-- url     : https://prove2.me/submissions/a239b6ca-7d68-4f42-a578-ff5688df562f

import Definitions.Def_Formalism_GaussJetBounds_StatementV
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CoefficientBoundMembership
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_TheoremAMatrixEntries

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) [hl : Fact l.Prime] : ‖(l : ℂ_[l])‖ < 1 := by
  have h : ‖(((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l])‖ = ‖(l : ℚ_[l])‖ := PadicComplex.norm_extends' l _
  have h2 : (((l : ℚ_[l]) : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by
    simp
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one
end Formalism.DworkPowerSeriesWeights
