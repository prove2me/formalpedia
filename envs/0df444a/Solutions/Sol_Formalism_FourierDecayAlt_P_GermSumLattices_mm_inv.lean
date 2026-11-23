-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.mm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:50.552803+00:00
-- url     : https://prove2.me/submissions/09b08a20-bf1e-46ef-8fad-2064a781958a

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_mm_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution (h : MM R) (z : Kˣ) : modK R ((z⁻¹ : Kˣ) : K) = (modK R (z : K))⁻¹ := by
  have h1 := (h z z⁻¹).2
  rw [Units.mul_inv, mm_one h] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm
end Formalism.FourierDecayAlt.P.GermSumLattices
