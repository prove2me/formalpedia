-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.cont_g
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:39.629612+00:00
-- url     : https://prove2.me/submissions/9c5fcbac-0809-4205-834b-75823e4b51a0

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_MXY_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_det_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_ampE_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_superSum


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
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (m : ℕ) (β : ℂ) (Kc : Set ℂ)
    (Φ : Mat (m + 1 + 1) → V) (bd : Mat (m + 1 + 1) → ℝ) (k : ℕ) (h : DerivBound k (detSet (m + 1) Kc) bd Φ)
    {D z : ℂ} (hD : D ∈ Kc) (hz : z ≠ 0) (hzD : z ^ (m + 2) = (-1) ^ (m + 3) * D) :
    Continuous (fun y : UT (m + 2) → ℂ => ampE β m Φ D 0 (fun _ => z, y)) := by
  have e : (fun y : UT (m + 2) → ℂ => ampE β m Φ D 0 (fun _ => z, y)) = fun y =>
      (((‖z‖ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) • (psi β (superSum (strictUpper y) / z) •
        Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))) := by
    funext y
    exact ampE_zero m β Φ D z y hz hzD
  rw [e]
  have hpath : Continuous (fun y : UT (m + 2) → ℂ =>
      (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y) :
        Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)) :=
    continuous_const.matrix_mul (continuous_const.add (G7.continuous_strictUpper _))
  have hΦc : Continuous (fun y : UT (m + 2) → ℂ =>
      Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))) := by
    rw [continuous_iff_continuousAt]
    intro y
    have hc : cofXY m 0 ((fun _ => z, y) : XY m) ≠ 0 := by
      rw [← norm_pos_iff, cofXY_zero]
      exact pow_pos (norm_pos_iff.mpr hz) _
    have h1 := (h _ (det_mem m Kc hD 0 _ hc)).1.continuousAt
    rw [MXY_zero m D z y hz hzD] at h1
    exact ContinuousAt.comp (g := Φ) h1 hpath.continuousAt
  have hps : Continuous (fun y : UT (m + 2) → ℂ => psi β (superSum (strictUpper y) / z)) :=
    (G7.continuous_psi β).comp
      (((G7.continuous_superSum (m + 1)).comp (G7.continuous_strictUpper _)).div_const z)
  exact (hps.smul hΦc).const_smul _
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
