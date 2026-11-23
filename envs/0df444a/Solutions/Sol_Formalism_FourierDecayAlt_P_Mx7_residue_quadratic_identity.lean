-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.residue_quadratic_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:51.88097+00:00
-- url     : https://prove2.me/submissions/c7fcd2d8-4998-47ce-aefa-037b422378cf

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_qC_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrm_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_realPoints


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1),
    -((P.T : ℂ) * P.T') * (q1P P).eval (-((rho P π l : ℂ) + 1)) - (Nrm P l π : ℂ) *
      ((∏ j ∈ Icc 1 (P.k - 1), (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ))) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1))) = 0 := by
  intro l hl
  have hk := congrArg (fun x : ℝ => (x : ℂ)) (Mx3.nrm_key P hP l hl π)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_one] at hk
  have hq := (Mx3.realPoints P π (-rho P π l - 1)).2
  have e0 : ((-rho P π l - 1 : ℝ) : ℂ) = -((rho P π l : ℂ) + 1) := by push_cast; ring
  rw [e0] at hq
  rw [← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e1, e2]
  linear_combination hk
end Formalism.FourierDecayAlt.P.Mx7
