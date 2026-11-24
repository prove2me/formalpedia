-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.K_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:39.325722+00:00
-- url     : https://prove2.me/submissions/609c058a-d3e8-4549-a825-68dd2676e84e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_x_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_DerivBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_det_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution (m : ℕ) (Kc : Set ℂ) (Φ : Mat (m + 1 + 1) → V) (A K : ℝ) (k : ℕ)
    (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) {D z : ℂ} (hD : D ∈ Kc)
    (hz : z ≠ 0) : 0 ≤ K := by
  have hc : cofXY m 0 ((fun _ => z, 0) : XY m) ≠ 0 := by
    rw [← norm_pos_iff, cofXY_zero]
    exact pow_pos (norm_pos_iff.mpr hz) _
  have h1 := (DB_of_DerivBound h (Nat.zero_le k) (det_mem m Kc hD 0 _ hc)).nonneg
  have h2 : 0 < ‖MXY m D 0 ((fun _ => z, 0) : XY m)‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz) (x_le_MXY m D 0 ((fun _ => z, 0) : XY m) 0)
  have h3 : 0 < min 1 (‖MXY m D 0 ((fun _ => z, 0) : XY m)‖ ^ (-A)) :=
    lt_min one_pos (Real.rpow_pos_of_pos h2 _)
  by_contra hK
  push Not at hK
  have := mul_neg_of_neg_of_pos hK h3
  linarith
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
