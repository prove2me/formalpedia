-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.nrm_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:48.534803+00:00
-- url     : https://prove2.me/submissions/1b6d73bd-340d-49f2-8510-a33ed72c394b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrm_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrmFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_num_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    Nrm P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1)) = -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l - 1) := by
  by_cases h : ∃ π', Up P l π π'
  · obtain ⟨π', hU⟩ := h
    have hp := nrm_pos P hP l hl π π' hU
    have hD : ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1)) ≠ 0 := by
      intro h0
      unfold Nrm at hp
      rw [h0, div_zero] at hp
      exact lt_irrefl _ hp
    unfold Nrm
    exact div_mul_cancel₀ _ hD
  · rw [(nrmFacts P hP l hl π).2.1 h, num_zero P hP l hl π h]; simp
end Formalism.FourierDecayAlt.P.Mx3
