-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitTailEstimates.tailBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:38.321353+00:00
-- url     : https://prove2.me/submissions/ef63aa39-1bbd-4979-a207-328e426484f7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitTailEstimates
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_min_le_maxpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_tail_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_coordMap_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_orbM_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_detM_orbM
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_norm_blockIntegrand
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_finrank_block_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitTailEstimates_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_embedding_coordMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_jacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_muBlock_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitTailEstimates
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7
namespace Formalism.FourierDecayAlt.P.OrbitTailEstimates
theorem _root_.solution : TailBound := by
  intro m β
  refine ⟨∫ q : BlockCoord (m + 1), (max 1 ‖q‖) ^ (-((Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) + 1))
    ∂(muBlock β (m + 1)), ?_⟩
  intro V _ _ _ Φ A K τ t c hA hτ ht hΦ hvan
  have ht0 : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4) := by positivity
    linarith
  have hb : ∀ p : BlockCoord (m + 1),
      ‖Φ (orbM (m + 1) t c p)‖ ≤ K * min 1 (‖orbM (m + 1) t c p‖ ^ (-A)) := by
    intro p
    have h3 := (hΦ (orbM (m + 1) t c p) (by rw [detM_orbM]; exact Set.mem_singleton _)).2 0 le_rfl
    rwa [norm_iteratedFDeriv_zero] at h3
  have hK : 0 ≤ K := K_nonneg (ht0.trans_le (norm_orbM_ge m t c 0)) (norm_nonneg _) (hb 0)
  set T : ℝ := max 1 τ with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hpt : ∀ p : BlockCoord (m + 1),
      ‖blockIntegrand β (m + 1) Φ t c p‖ ≤ K * (max T ‖coordMap (m + 1) t p‖) ^ (-A) := by
    intro p
    rw [norm_blockIntegrand]
    rcases lt_or_ge ‖orbM (m + 1) t c p‖ τ with h | h
    · rw [hvan p h, norm_zero]; positivity
    · refine (hb p).trans (mul_le_mul_of_nonneg_left ((min_le_maxpow A _).trans ?_) hK)
      refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
      refine max_le (max_le (le_max_left _ _) (h.trans (le_max_right _ _))) ?_
      exact (norm_coordMap_le (m + 1) t c p).trans (le_max_right _ _)
  obtain ⟨k, hk⟩ := muBlock_eq β (m + 1)
  have i1 : SecondCountableTopology ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
  have i2 : BorelSpace ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
  have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
  have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨hI, hle⟩ := tail_smul volume (muBlock β (m + 1)) k hk T A hT1 (by rw [finrank_block_cast]; exact hA)
  have hJ := jacobian (m + 1) β t ht
  have hI' : Integrable (fun p : BlockCoord (m + 1) => (max T ‖coordMap (m + 1) t p‖) ^ (-A))
      (muBlock β (m + 1)) := by
    have h2 : Integrable (fun q : BlockCoord (m + 1) => (max T ‖q‖) ^ (-A))
        (Measure.map (coordMap (m + 1) t) (muBlock β (m + 1))) := hJ ▸ hI.smul_measure_nnreal
    exact (embedding_coordMap _ t ht).integrable_map_iff.1 h2
  have hint : ∫ p : BlockCoord (m + 1), (max T ‖coordMap (m + 1) t p‖) ^ (-A) ∂(muBlock β (m + 1)) =
      (‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * ∫ q : BlockCoord (m + 1), (max T ‖q‖) ^ (-A) ∂(muBlock β (m + 1)) := by
    rw [← (embedding_coordMap _ t ht).integral_map (fun q : BlockCoord (m + 1) => (max T ‖q‖) ^ (-A)), hJ,
      integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul]
  calc ‖OmBlock β (m + 1) Φ t c‖
      ≤ ∫ p : BlockCoord (m + 1), K * (max T ‖coordMap (m + 1) t p‖) ^ (-A) ∂(muBlock β (m + 1)) :=
        norm_integral_le_of_norm_le (hI'.const_mul K) (Filter.Eventually.of_forall hpt)
    _ = K * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ *
          ∫ q : BlockCoord (m + 1), (max T ‖q‖) ^ (-A) ∂(muBlock β (m + 1))) := by
        rw [integral_const_mul, hint]
    _ ≤ K * ((‖t‖ ^ ((m + 1) * (m + 4)))⁻¹ * (T ^ ((Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) - A) *
          ∫ q : BlockCoord (m + 1), (max 1 ‖q‖) ^ (-((Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) + 1))
            ∂(muBlock β (m + 1)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) hK
    _ = _ := by rw [finrank_block_cast]; ring
end Formalism.FourierDecayAlt.P.OrbitTailEstimates
