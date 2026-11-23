-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.omConverges
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:58.861071+00:00
-- url     : https://prove2.me/submissions/92c208dd-4cc3-41fd-9935-70f1079a294c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_muPi_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_jacobian
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_strictUpper_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_embedding_coordMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_min_le_bracket
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_integrable_comp_bracket
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_muBlock_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_blk
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_superSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_continuous_subSum
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_coord_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_norm_long_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_finrank_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_finrank_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_additive_character_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_orbit
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_weyl_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_dimension_count
import Theorems.Thm_Formalism_FourierDecayAlt_P_matrix_entries
import Theorems.Thm_Formalism_FourierDecayAlt_P_scale_product_measure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution : OmConverges := by
  intro m β A K hA V _ _ _ Φ t c ht hc hΦ
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 4) := by positivity
    linarith
  have hb : ∀ Z : Mat (m + 1 + 1), detM Z = (wMat (m + 1)).det * (c * t ^ (m + 1)) →
      ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ |K| * (2 ^ A * (1 + ‖Z‖) ^ (-A)) := by
    intro Z hZ
    obtain ⟨h1, h2⟩ := hΦ Z (by rw [hZ]; exact Set.mem_singleton _)
    refine ⟨h1.continuousAt, ?_⟩
    have h3 := h2 0 le_rfl
    rw [norm_iteratedFDeriv_zero] at h3
    calc ‖Φ Z‖ ≤ K * min 1 (‖Z‖ ^ (-A)) := h3
      _ ≤ |K| * min 1 (‖Z‖ ^ (-A)) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (le_min zero_le_one (Real.rpow_nonneg (norm_nonneg _) _))
      _ ≤ _ := mul_le_mul_of_nonneg_left (min_le_bracket A _ hA0 (norm_nonneg _)) (abs_nonneg K)
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → |K| * (2 ^ A * (1 + y) ^ (-A)) ≤ |K| * (2 ^ A * (1 + x) ^ (-A)) := by
    intro x y hx hxy
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (abs_nonneg K)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  constructor
  · set M : BlockCoord (m + 1) → Mat (m + 1 + 1) :=
      fun p => lowRow p.1 * ptBlock (m + 1) t c * blk (G.upper p.2.1) p.2.2 0 1 with hM
    have hlow : Continuous (fun p : BlockCoord (m + 1) => lowRow p.1) :=
      continuous_blk continuous_const continuous_const continuous_fst continuous_const
    have hup : Continuous (fun p : BlockCoord (m + 1) => blk (G.upper p.2.1) p.2.2 0 1) :=
      continuous_blk ((continuous_upper _).comp (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd) continuous_const continuous_const
    have hMc : Continuous M := (hlow.matrix_mul continuous_const).matrix_mul hup
    have hdet : ∀ p, detM (M p) = (wMat (m + 1)).det * (c * t ^ (m + 1)) :=
      fun p => det_orbit.1 (m + 1) t c p
    have hcont : Continuous (blockIntegrand β (m + 1) Φ t c) := by
      unfold blockIntegrand
      refine Continuous.smul ?_ ?_
      · exact ((continuous_psi β).comp ((continuous_subSum _).comp hlow)).mul
          ((continuous_psi β).comp ((continuous_superSum _).comp hup))
      · exact continuous_iff_continuousAt.2 fun p =>
          ContinuousAt.comp (f := M) (hb (M p) (hdet p)).1 hMc.continuousAt
    obtain ⟨k, hk⟩ := muBlock_eq β (m + 1)
    have hfr : (Module.finrank ℝ (BlockCoord (m + 1)) : ℝ) < A := by
      rw [finrank_block]
      have e : (((m + 1) * (m + 1 + 3) : ℕ) : ℝ) = ((m : ℝ) + 1) * ((m : ℝ) + 4) := by push_cast; ring
      rw [e]; exact hA
    have i1 : SecondCountableTopology ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
    have i2 : BorelSpace ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ)) := inferInstance
    have i3 : BorelSpace (BlockCoord (m + 1)) := inferInstance
    have j1 : (volume : Measure ((UT (m + 1) → ℂ) × (Fin (m + 1) → ℂ))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure _ _
    have j2 : (volume : Measure (BlockCoord (m + 1))).IsAddHaarMeasure :=
      Measure.prod.instIsAddHaarMeasure _ _
    have hI := integrable_comp_bracket volume (muBlock β (m + 1)) k _ hk (coordMap (m + 1) t)
      (embedding_coordMap _ t ht) (jacobian (m + 1) β t ht) A hfr
    refine Integrable.mono' ((hI.const_mul (2 ^ A)).const_mul |K|) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    have hn : ‖blockIntegrand β (m + 1) Φ t c p‖ = ‖Φ (M p)‖ := by
      unfold blockIntegrand
      rw [norm_smul, norm_mul, (additive_character_psi β _ 0).2.1, (additive_character_psi β _ 0).2.1, one_mul, one_mul]
    rw [hn]
    refine (hb (M p) (hdet p)).2.trans (hmono _ _ (norm_nonneg _) ?_)
    refine norm_coord_le t (c + p.1 ⬝ᵥ (wMat (m + 1) *ᵥ (t • p.2.2))) (t • p.2.1) (t • p.2.2)
      (rhoOf t p.1 p.2.1) (M p) ?_
    rw [strictUpper_smul]
    exact matrix_entries (m + 1) t c p
  · intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hz
      exact (mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero hc (pow_ne_zero _ ht))) hz.symm
    set M : (UT (m + 1 + 1) → ℂ) → Mat (m + 1 + 1) := fun v => ptLong (m + 1 + 1) z * G.upper v with hM
    have hMc : Continuous M := continuous_const.matrix_mul (continuous_upper _)
    have hdet : ∀ v, detM (M v) = (wMat (m + 1)).det * (c * t ^ (m + 1)) := by
      intro v
      have h1 : detM (M v) = (wMat (m + 1 + 1)).det * z ^ (m + 2) := det_orbit.2 (m + 1 + 1) z v
      rw [h1, (det_weyl_matrix (m + 1)).1, hz]
      have h2 : (-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 3) = 1 := by
        rw [← pow_add]; exact Even.neg_one_pow ⟨m + 2, by ring⟩
      linear_combination ((wMat (m + 1)).det * (c * t ^ (m + 1))) * h2
    have hcont : Continuous (fun v : UT (m + 1 + 1) → ℂ =>
        psi β (superSum (G.upper v)) • Φ (ptLong (m + 1 + 1) z * G.upper v)) := by
      refine Continuous.smul ?_ ?_
      · exact (continuous_psi β).comp ((continuous_superSum _).comp (continuous_upper _))
      · exact continuous_iff_continuousAt.2 fun v =>
          ContinuousAt.comp (f := M) (hb (M v) (hdet v)).1 hMc.continuousAt
    have hfr : (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < A := by
      rw [finrank_pi, (dimension_count (m + 1 + 1)).1]
      have e : (((m + 1 + 1) * (m + 1 + 1 - 1) : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
        simp only [Nat.add_sub_cancel]; push_cast; ring
      rw [e]
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hI := integrable_comp_bracket volume (muPi β (UT (m + 1 + 1))) _ _ (muPi_eq β _)
      (fun v => z • v) (measurableEmbedding_const_smul₀ hz0) (scale_product_measure β z _ hz0) A hfr
    refine Integrable.mono' ((hI.const_mul (2 ^ A)).const_mul |K|) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => ?_)
    rw [norm_smul, (additive_character_psi β _ 0).2.1, one_mul]
    exact (hb (M v) (hdet v)).2.trans (hmono _ _ (norm_nonneg _) (norm_long_le z v (M v) rfl))
end Formalism.FourierDecayAlt.P.G7
