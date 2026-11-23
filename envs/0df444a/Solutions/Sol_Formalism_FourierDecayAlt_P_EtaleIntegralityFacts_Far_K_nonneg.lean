-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far.K_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:41.584611+00:00
-- url     : https://prove2.me/submissions/d3821ffb-f4dd-4d1c-a176-21ad65046342

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_G2_det_wMat_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_entry_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {m k : ℕ} {Kc : Set ℂ} {A K : ℝ}
    {Φ : Mat (m + 1 + 1) → V} (h : DerivBound k (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ)
    {D : ℂ} (hD : D ∈ Kc) (hD0 : D ≠ 0) : 0 ≤ K := by
  set d : ℂ := (wMat (m + 1)).det * D with hd
  have hd0 : d ≠ 0 := mul_ne_zero (G2.det_wMat_ne_zero _) hD0
  let Z : Mat (m + 1 + 1) := Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) 0 d)
  have hdet : detM Z = d := by
    show Matrix.det (Matrix.of Z) = d
    have : (Matrix.of Z : Matrix (Fin (m + 1 + 1)) (Fin (m + 1 + 1)) ℂ) =
        Matrix.diagonal (Function.update (fun _ => (1 : ℂ)) 0 d) := rfl
    rw [this, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  have hmem : detM Z ∈ detSet (m + 1) Kc := by
    rw [hdet]; exact ⟨D, hD, rfl⟩
  have h0 := (h Z hmem).2 0 (Nat.zero_le _)
  have hZ : 0 < ‖Z‖ := by
    have h1 : ‖Z 0 0‖ ≤ ‖Z‖ := G7.norm_entry_le Z 0 0
    have h2 : Z 0 0 = d := by simp [Z]
    rw [h2] at h1
    exact lt_of_lt_of_le (norm_pos_iff.2 hd0) h1
  have hmin : 0 < min 1 (‖Z‖ ^ (-A)) := lt_min one_pos (Real.rpow_pos_of_pos hZ _)
  by_contra hK
  have hK' : K < 0 := not_le.1 hK
  have : K * min 1 (‖Z‖ ^ (-A)) < 0 := mul_neg_of_neg_of_pos hK' hmin
  have h3 := le_trans (norm_nonneg _) h0
  exact absurd h3 (not_le.2 this)
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far
