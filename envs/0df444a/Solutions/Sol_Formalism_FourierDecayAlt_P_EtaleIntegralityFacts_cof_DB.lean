-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.cof_DB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:50.577486+00:00
-- url     : https://prove2.me/submissions/888651d7-44d2-4533-ae45-626b7fa0457a

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_def
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_powle
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mulQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_sumQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_pow_DB
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_tpow_DB

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
theorem _root_.solution (h1Q : 1 ≤ Q) (h2 : (2 : ℝ) ^ q ≤ Q) (hm : ((m : ℝ) + 1) ≤ Q) (ht : DB q tt u Q 1)
    (hx : ∀ k, DB q (fun v => xx v k) u Q 1) (hy : ∀ e, DB q (fun v => yy v e) u Q 1) :
    DB q (fun v => cofXY m (tt v) (xx v, yy v)) u (Q ^ (3 * m + 3)) 1 := by
  have hQ0 : 0 ≤ Q := le_trans (by positivity) h2
  simp only [cofXY_def]
  refine DB.sumQ (a := 3 * m + 2) _ (fun j hj => ?_) zero_le_one hQ0 (by simpa using hm)
  have hj' := Finset.mem_range.mp hj
  exact ((pow_DB h2 hm hx hy j 0).mulQ (tpow_DB h2 ht (m - j)) zero_le_one h2).powle h1Q (by omega) zero_le_one
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
