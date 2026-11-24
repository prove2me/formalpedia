-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.leading_cofactor_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:52.7578+00:00
-- url     : https://prove2.me/submissions/d91f706d-bb39-4ca0-86bb-2462b7d3da85

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mulQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_prodQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m q : ℕ} {tt : E → ℂ}
  {xx : E → Fin (m + 1) → ℂ} {yy : E → UT (m + 2) → ℂ} {u : E} {Q : ℝ}
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (h2 : (2 : ℝ) ^ q ≤ Q) (hx : ∀ k, DB q (fun v => xx v k) u Q 1) :
    DB q (fun v => cof0XY m (xx v, yy v)) u (Q ^ (2 * m + 3)) 1 := by
  simp only [cof0XY]
  have h1 := DB.prodQ (f := fun k v => xx v k) (Finset.univ : Finset (Fin (m + 1)))
    (fun k _ => by simpa using hx k) zero_le_one h2
  have h0 : DB q (fun _ : E => ((-1 : ℂ)) ^ m) u (Q ^ 0) 1 := DB.const q _ u (by simp) zero_le_one
  have h3 := h0.mulQ h1 zero_le_one h2
  have e : 0 + 2 * (Finset.univ : Finset (Fin (m + 1))).card + 1 = 2 * m + 3 := by simp; ring
  rwa [e] at h3
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
