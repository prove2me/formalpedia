-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.coValue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:40.975627+00:00
-- url     : https://prove2.me/submissions/74d6df97-4224-4ee6-94ed-26664287f462

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_chebPt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_lagCo_affine
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_lagCo_nd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChebCoValue := by
  intro α β n hαβ hn j
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : 0 < β - α := by linarith
  have e : Formalism.SA.C.chebPt α β (m + 1) = fun i => (α + β) / 2 + (β - α) / 2 * nd (m + 1) i := by
    funext i; exact chebPt_eq α β (m + 1) i
  rw [e, lagCo_affine, lagCo_nd]
  have : ((β - α) / 2)⁻¹ = 2 / (β - α) := by rw [inv_div]
  rw [this, Nat.add_sub_cancel]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
