-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit.K_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:38.377655+00:00
-- url     : https://prove2.me/submissions/e24697ad-eeb6-4cfb-9703-558bdd645f84

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_x_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_matrix_xy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {m k : ℕ} {Kc : Set ℂ} {A K : ℝ}
    {Φ : Mat (m + 1 + 1) → V}
    (hΦ : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ) {D z : ℂ} (hD : D ∈ Kc)
    (hz : z ≠ 0) : 0 ≤ K := by
  have hc : cofXY m 0 (fun _ => z, (0 : UT (m + 2) → ℂ)) ≠ 0 := by
    intro h
    have h2 := cofXY_zero m z (0 : UT (m + 2) → ℂ)
    rw [h, norm_zero] at h2
    exact (pow_pos (norm_pos_iff.2 hz) (m + 1)).ne h2
  have hdet : detM (MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))) ∈ detSet (m + 1) Kc :=
    ⟨D, hD, (det_matrix_xy m D 0 _ hc).symm⟩
  have hM : 0 < ‖MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))‖ :=
    lt_of_lt_of_le (norm_pos_iff.2 hz) (x_le_MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ)) 0)
  have h := (hΦ _ hdet).2 0 (Nat.zero_le _)
  have h2 : 0 ≤ K * min 1 (‖MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))‖ ^ (-A)) :=
    (norm_nonneg _).trans h
  have h3 : 0 < min 1 (‖MXY m D 0 (fun _ => z, (0 : UT (m + 2) → ℂ))‖ ^ (-A)) :=
    lt_min one_pos (Real.rpow_pos_of_pos hM _)
  exact nonneg_of_mul_nonneg_left h2 h3
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
