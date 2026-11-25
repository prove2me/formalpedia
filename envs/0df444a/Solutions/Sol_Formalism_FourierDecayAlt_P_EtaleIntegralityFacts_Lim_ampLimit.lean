-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.ampLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:47:57.040555+00:00
-- url     : https://prove2.me/submissions/b97d02f3-6e6b-414b-a2e6-1f8fc2e906af

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_arith
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_geom
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_core__d5ba8d45886d
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_Phi_DB
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_f_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_f_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_ampE_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_g_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_diff_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_int_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_cont_g
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_arith
import Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_geom
import Theorems.Thm_Formalism_FourierDecayAlt_P_amplitude_continuous_at_critical
import Theorems.Thm_Formalism_FourierDecayAlt_P_majorant_y


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
set_option maxHeartbeats 1000000
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution : AmpLimit := by
  obtain ⟨a, b, hcore⟩ := core'
  refine ⟨4 * (a + b) + 1, ?_⟩
  intro m β Kc hK h0 ε hε0 hε
  obtain ⟨t₁, c, Rz, ht₁0, ht₁1, hc0, hRz, hgeom⟩ := geom m Kc hK h0 ε hε0 hε
  obtain ⟨t₂, ht₂0, hcont⟩ := amplitude_continuous_at_critical m β Kc hK h0 ε hε0 hε
  obtain ⟨Cm, hmaj⟩ := majorant_y m (4 * (m + 2) * (a + b)) β
  set cW : ℝ := (4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c with hcW
  have hcW0 : 0 ≤ cW := by positivity
  set C₃ : ℝ := cW ^ (a + b) + (2 / c) ^ 2 with hC₃
  have hC₃0 : 0 ≤ C₃ := by positivity
  refine ⟨3 * C₃ * Cm, min t₁ t₂, lt_min ht₁0 ht₂0, ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t D z ht htle hD hzD
  obtain ⟨hA0, hA1, hA2⟩ := arith a b m hε0 hε hA
  obtain ⟨hz0, hzR, hDR, hcz, hcof, hM⟩ := hgeom D hD z hzD t ht (htle.trans (min_le_left _ _))
  have ht0 : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have ht1 : ‖t‖ ≤ 1 := (htle.trans (min_le_left _ _)).trans ht₁1
  have hK0 : 0 ≤ K := K_nonneg m Kc Φ A K k hΦ hD hz0
  obtain ⟨hmi, hmI, hmT⟩ := hmaj A hA1
  set T : ℝ := ‖t‖ ^ (-ε) with hT
  have hT1 : 1 ≤ T := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by linarith)
  set maj : (UT (m + 2) → ℂ) → ℝ := fun y => (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * (max 1 ‖y‖) ^ (-A) with hmajdef
  have hmx0 : ∀ y : UT (m + 2) → ℂ, 0 ≤ (max 1 ‖y‖) ^ (-A) := fun y =>
    Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
  have hmaj0 : ∀ y, 0 ≤ maj y := fun y => mul_nonneg (by positivity) (hmx0 y)
  have hmxle : ∀ y : UT (m + 2) → ℂ, (max 1 ‖y‖) ^ (-A) ≤ maj y := fun y =>
    le_mul_of_one_le_left (hmx0 y) (one_le_pow₀ (by linarith [norm_nonneg y]))
  have hne : ∀ (y : UT (m + 2) → ℂ) (τ' : ℂ), c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖ →
      cofXY m τ' (fun _ => z, y) ≠ 0 := fun y τ' h => by
    rw [← norm_pos_iff]
    linarith
  have hCm0 : 0 ≤ Cm := le_trans (integral_nonneg hmaj0) hmI
  have hprod : ∏ _k : Fin (m + 1), z ≠ 0 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_ne_zero _ hz0

  have hfb : ∀ y : UT (m + 2) → ℂ, ‖ampIn β m ε Φ D t (fun _ => z, y)‖ ≤ K * C₃ * maj y := by
    intro y
    have h1 := f_bound m β ε Φ D t (fun _ => z, y) (K' := K * (max 1 ‖y‖) ^ (-A)) hc0 ht
      (mul_nonneg hK0 (hmx0 y)) (fun hy => hcof y t hy le_rfl)
      (fun hc => (Phi_DB m Kc Φ A K k 0 hA0 hK0 (Nat.zero_le _) hΦ hD t (fun _ => z, y) hc).norm_le)
    calc ‖ampIn β m ε Φ D t (fun _ => z, y)‖ ≤ (2 / c) ^ 2 * (K * (max 1 ‖y‖) ^ (-A)) := h1
      _ ≤ C₃ * (K * maj y) := by
          refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left (hmxle y) hK0) (mul_nonneg hK0 (hmx0 y)) hC₃0
          rw [hC₃]
          have : 0 ≤ cW ^ (a + b) := by positivity
          linarith
      _ = K * C₃ * maj y := by ring
  have hc00 : ∀ y : UT (m + 2) → ℂ, cofXY m 0 ((fun _ => z, y) : XY m) ≠ 0 := fun y => by
    rw [← norm_pos_iff, cofXY_zero]
    exact pow_pos (norm_pos_iff.mpr hz0) _
  have hgb : ∀ y : UT (m + 2) → ℂ, ‖ampE β m Φ D 0 (fun _ => z, y)‖ ≤ K * C₃ * maj y := by
    intro y
    have h1 := g_bound m β Φ D z y (K' := K * (max 1 ‖y‖) ^ (-A)) hc0 hcz
      (Phi_DB m Kc Φ A K k 0 hA0 hK0 (Nat.zero_le _) hΦ hD 0 (fun _ => z, y) (hc00 y)).norm_le
    calc ‖ampE β m Φ D 0 (fun _ => z, y)‖ ≤ (2 / c) ^ 2 * (K * (max 1 ‖y‖) ^ (-A)) := h1
      _ ≤ C₃ * (K * maj y) := by
          refine mul_le_mul ?_ (mul_le_mul_of_nonneg_left (hmxle y) hK0) (mul_nonneg hK0 (hmx0 y)) hC₃0
          rw [hC₃]
          have : 0 ≤ cW ^ (a + b) := by positivity
          linarith
      _ = K * C₃ * maj y := by ring
  have hin : ∀ y : UT (m + 2) → ℂ, y ∉ {y : UT (m + 2) → ℂ | T ≤ ‖y‖} →
      ‖ampIn β m ε Φ D t (fun _ => z, y) - ampE β m Φ D 0 (fun _ => z, y)‖ ≤ K * C₃ * ‖t‖ * maj y := by
    intro y hy
    have hyT : ‖y‖ ≤ T := by
      exact (not_le.mp hy).le
    rw [f_eq m β ε Φ D t (fun _ => z, y) ht hprod (hM y hyT)]
    have h1 := diff_bound hcore m β D z t y (K' := K * (max 1 ‖y‖) ^ (-A)) Φ hc0 hRz hz0 hzR hDR hcz ht1
      (fun τ' hτ' => hcof y τ' (by linarith) hτ')
      (fun τ' hτ' => Phi_DB m Kc Φ A K k 1 hA0 hK0 hk hΦ hD τ' (fun _ => z, y)
        (hne y τ' (hcof y τ' (by linarith) hτ')))
    refine h1.trans ?_
    calc K * (max 1 ‖y‖) ^ (-A) * cW ^ (a + b) * (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * ‖t‖
        = cW ^ (a + b) * (K * ‖t‖ * maj y) := by rw [hmajdef]; ring
      _ ≤ C₃ * (K * ‖t‖ * maj y) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg hK0 ht0.le) (hmaj0 y))
          rw [hC₃]
          have : 0 ≤ (2 / c) ^ 2 := by positivity
          linarith
      _ = K * C₃ * ‖t‖ * maj y := by ring
  have hΦ0 : DerivBound 0 (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ := fun Z hZ =>
    ⟨(hΦ Z hZ).1.of_le (by exact_mod_cast Nat.zero_le k), fun j hj => (hΦ Z hZ).2 j (hj.trans (Nat.zero_le k))⟩
  have hfc := hcont V Φ _ hΦ0 t D z ht (htle.trans (min_le_right _ _)) hD hzD
  have hgc := cont_g m β Kc Φ _ k hΦ hD hz0 hzD
  have hS : MeasurableSet {y : UT (m + 2) → ℂ | T ≤ ‖y‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hmain := int_bound (muPi β (UT (m + 2))) (fun y => ampIn β m ε Φ D t (fun _ => z, y))
    (fun y => ampE β m Φ D 0 (fun _ => z, y)) maj _ hS hfc.aestronglyMeasurable hgc.aestronglyMeasurable hmi hmaj0
    (mul_nonneg hK0 hC₃0) ht0.le hfb hgb hin
  have hgint : ∫ y : UT (m + 2) → ℂ, ampE β m Φ D 0 (fun _ => z, y) ∂(muPi β (UT (m + 2))) =
      (((‖z‖ ^ (2 * (m + 1)))⁻¹ : ℝ) : ℂ) •
        ∫ y : UT (m + 2) → ℂ, psi β (superSum (strictUpper y) / z) •
          Φ (wMat (m + 2) * (z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) + strictUpper y))
          ∂(muPi β (UT (m + 2))) := by
    rw [← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact ampE_zero m β Φ D z y hz0 hzD
  rw [← hgint]
  refine hmain.trans ?_
  have hTx : T ^ (((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A) ≤ ‖t‖ := by
    rw [hT, ← Real.rpow_mul ht0.le]
    calc ‖t‖ ^ (-ε * (((4 * (m + 2) * (a + b) : ℕ) : ℝ) + ((m : ℝ) + 2) * ((m : ℝ) + 1) - A)) ≤ ‖t‖ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hA2
      _ = ‖t‖ := Real.rpow_one _
  have htail := (hmT T hT1).trans (mul_le_mul_of_nonneg_left hTx hCm0)
  have hB0 : 0 ≤ K * C₃ := mul_nonneg hK0 hC₃0
  calc K * C₃ * ‖t‖ * ∫ y, maj y ∂(muPi β (UT (m + 2))) +
        2 * (K * C₃) * ∫ y in {y : UT (m + 2) → ℂ | T ≤ ‖y‖}, maj y ∂(muPi β (UT (m + 2)))
      ≤ K * C₃ * ‖t‖ * Cm + 2 * (K * C₃) * (Cm * ‖t‖) :=
        add_le_add (mul_le_mul_of_nonneg_left hmI (mul_nonneg hB0 ht0.le))
          (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = 3 * C₃ * Cm * K * ‖t‖ := by ring
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
