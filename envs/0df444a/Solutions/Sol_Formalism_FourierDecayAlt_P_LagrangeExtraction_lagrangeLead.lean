-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LagrangeExtraction.lagrangeLead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:40.092171+00:00
-- url     : https://prove2.me/submissions/e05064e5-4a8c-4a86-9c30-7fda153f838e

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LagrangeExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_sum_lagCo_mul_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LagrangeExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.LagrangeExtraction
theorem _root_.solution : LagrangeLead := by
  intro d y hy V _ _ a
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have : ∀ k : Fin (d + 1), (∑ j, lagCo y j * y j ^ (k : ℕ)) = if k = Fin.last d then 1 else 0 := by
    intro k
    rw [ChebyshevExtremalPolynomials.sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.2)]
    simp [Fin.ext_iff]
  simp [this]
end Formalism.FourierDecayAlt.P.LagrangeExtraction
