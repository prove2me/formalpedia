-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:47.053606+00:00
-- url     : https://prove2.me/submissions/6751aa5d-3d61-40a3-a447-192ca2b8970e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_eventually_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_clm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_y_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_amp_eq_ampE
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_DerivBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_derivBound_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_min_le_max
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_ampIn_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_DB_proj
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Crit_cof_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_critical_cutoff_spec
import Theorems.Thm_Formalism_FourierDecayAlt_P_cutoff_phase_bound
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
theorem _root_.solution : AmpBoundCrit := by
  obtain ⟨a, b, hcore⟩ := core
  refine ⟨4 * (a + 2 * b), ?_⟩
  intro m β Kc hKc h0 δ ε hδ hε0 hε
  obtain ⟨hδ0, hδz⟩ := hδ
  obtain ⟨RD, hRD⟩ : ∃ R, ∀ D ∈ Kc, ‖D‖ ≤ R := hKc.isBounded.exists_norm_le
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 * (m + 1) + 2 := ⟨_, rfl⟩
  rw [← hq]
  obtain ⟨Ccut, hCcut⟩ := cutoff_phase_bound (m + 1 + 1) q
  obtain ⟨hcr1, hcr2, -⟩ := critical_cutoff_spec m δ hδ0
  obtain ⟨Ccrit, hCcrit⟩ := hcr2 q
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = max RD 1 + 2 * δ + 2 := ⟨_, rfl⟩
  have hc2 : 2 ≤ c := by
    have := le_max_right RD 1
    linarith
  have hcRD : RD ≤ c := by
    have := le_max_left RD 1
    linarith
  obtain ⟨cQ, hcQdef⟩ : ∃ cQ : ℝ, cQ = max (2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial) (max c ‖β‖) := ⟨_, rfl⟩
  have hcQ1 : 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ cQ := hcQdef ▸ le_max_left _ _
  have hcQ2 : c ≤ cQ := hcQdef ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hcQ3 : ‖β‖ ≤ cQ := hcQdef ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hcQ0 : 1 ≤ cQ := by linarith
  obtain ⟨cW, hcWdef⟩ : ∃ cW : ℝ, cW = max (cQ ^ (4 * (m + 2))) (2 / δ ^ (m + 1)) := ⟨_, rfl⟩
  have hcW1 : cQ ^ (4 * (m + 2)) ≤ cW := hcWdef ▸ le_max_left _ _
  have hcW2 : 2 / δ ^ (m + 1) ≤ cW := hcWdef ▸ le_max_right _ _
  have hcW0 : 1 ≤ cW := (one_le_pow₀ hcQ0).trans hcW1
  have hδp : 0 < δ ^ (m + 1) := pow_pos hδ0 _
  have hden : 0 < ((m : ℝ) + 1) ^ (m + 1) * c ^ m := by positivity
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = δ ^ (m + 1) / (2 * (((m : ℝ) + 1) ^ (m + 1) * c ^ m)) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  refine ⟨2 ^ q * |Ccrit| * |Ccut| * cW ^ (a + b * q), min 1 (κ ^ 2), lt_min one_pos (by positivity), ?_⟩
  intro V _ _ _ Φ A K k hA hk hΦ t D z ht0 ht hD hz y
  have ht1 : ‖t‖ ≤ 1 := ht.trans (min_le_left _ _)
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hts : ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ δ ^ (m + 1) / 2 := by
    have h1 : Real.sqrt ‖t‖ ≤ κ := by
      rw [← Real.sqrt_sq hκ0.le]
      exact Real.sqrt_le_sqrt (ht.trans (min_le_right _ _))
    calc ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ ((m : ℝ) + 1) ^ (m + 1) * c ^ m * κ :=
          mul_le_mul_of_nonneg_left h1 hden.le
      _ = δ ^ (m + 1) / 2 := by rw [hκdef]; field_simp
  have hzl : 100 * ((m : ℝ) + 2) * δ ≤ ‖z‖ := hδz D hD z hz
  have hz200 : 200 * δ ≤ ‖z‖ := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hzne : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hzR : ‖z‖ ≤ max RD 1 := by
    by_contra hcon
    have h1 : max RD 1 < ‖z‖ := not_le.1 hcon
    have h2 : 1 ≤ ‖z‖ := (le_max_right RD 1).trans h1.le
    have h3 : ‖z‖ ≤ ‖z‖ ^ (m + 2) := le_self_pow₀ h2 (by omega)
    have h4 : ‖z‖ ^ (m + 2) = ‖D‖ := by
      rw [← norm_pow, hz, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h5 := hRD D hD
    have h6 := le_max_left RD 1
    linarith
  have hK : 0 ≤ K := K_nonneg hΦ hD hzne
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = ‖t‖ ^ (-ε) := ⟨_, rfl⟩
  have hτ : 1 ≤ τ := hτdef ▸ Real.one_le_rpow_of_pos_of_le_one_of_nonpos htp ht1 (by linarith)
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = 1 + ‖y‖ := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith [norm_nonneg y]
  obtain ⟨mx, hmxdef⟩ : ∃ mx : ℝ, mx = (max 1 ‖y‖) ^ (-A) := ⟨_, rfl⟩
  have hmx0 : 0 ≤ mx := by rw [hmxdef]; positivity
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = cQ * Y := ⟨_, rfl⟩
  have hQle : ∀ r : ℝ, r ≤ cQ → r ≤ Q := fun r hr => by
    rw [hQdef]; exact hr.trans (le_mul_of_one_le_right (by linarith) hY1)
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = cW * Y ^ (4 * (m + 2)) := ⟨_, rfl⟩
  have hYp : 1 ≤ Y ^ (4 * (m + 2)) := one_le_pow₀ hY1
  have hWle : ∀ r : ℝ, r ≤ cW → r ≤ W := fun r hr => by
    rw [hWdef]; exact hr.trans (le_mul_of_one_le_right (by linarith) hYp)
  have hW1 : 1 ≤ W := hWle 1 hcW0
  have hQW : Q ^ (4 * (m + 2)) ≤ W := by
    rw [hQdef, hWdef, mul_pow]
    exact mul_le_mul_of_nonneg_right hcW1 (by positivity)
  obtain ⟨K', hK'def⟩ : ∃ K' : ℝ, K' = |Ccut| * (K * mx) := ⟨_, rfl⟩
  have hK'0 : 0 ≤ K' := by rw [hK'def]; positivity
  have hP0 : 0 ≤ W ^ b := by positivity
  have hS0 : 0 ≤ 2 ^ q * |Ccrit| * (K' * W ^ a) := by positivity
  have key : ∀ x : Fin (m + 1) → ℂ,
      DB q (fun x : Fin (m + 1) → ℂ => ((critCut δ z x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x
        (2 ^ q * |Ccrit| * (K' * W ^ a)) (W ^ b) := by
    intro x
    by_cases hy : ‖y‖ ≤ 2 * τ
    swap
    · refine DB.of_eventually_zero (Filter.Eventually.of_forall fun v => ?_) hS0 hP0
      show ((critCut δ z v : ℝ) : ℂ) • ampIn β m ε Φ D t (v, y) = 0
      rw [ampIn_zero β m ε Φ D t (v, y) (by rw [← hτdef]; linarith) (by rw [← hτdef]; exact (not_le.1 hy).le),
        smul_zero]
    by_cases hx : ‖x - fun _ => z‖ ≤ 2 * δ
    swap
    · have hopen : IsOpen {v : Fin (m + 1) → ℂ | 2 * δ < ‖v - fun _ => z‖} :=
        isOpen_lt continuous_const (by fun_prop)
      refine DB.of_eventually_zero ?_ hS0 hP0
      filter_upwards [hopen.mem_nhds (not_le.1 hx)] with v hv
      show ((critCut δ z v : ℝ) : ℂ) • ampIn β m ε Φ D t (v, y) = 0
      rw [(hcr1 z v).2.2.2 (le_of_lt hv)]
      simp
    · have hxk : ∀ k, ‖x k - z‖ ≤ 2 * δ := fun k => (norm_le_pi_norm (x - fun _ => z) k).trans hx
      have hxu : ∀ k, ‖x k‖ ≤ c := fun k => by
        have h1 := norm_add_le (x k - z) z
        rw [sub_add_cancel] at h1
        have h2 := hxk k
        linarith
      have hxl : ∀ k, δ ≤ ‖x k‖ := fun k => by
        have h1 := norm_sub_norm_le z (x k)
        rw [norm_sub_rev] at h1
        have h2 := hxk k
        linarith
      obtain ⟨hprod, hcof⟩ := cof_lower m hδ0 hc2 hε0 hε ht0 ht1 hts (x, y) hxu hxl (by rw [← hτdef]; exact hy)
      have hcofne : cofXY m t (x, y) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hcof
        linarith
      have hprodne : ∏ k, x k ≠ 0 := by
        intro h
        change δ ^ (m + 1) ≤ ‖∏ k, x k‖ at hprod
        rw [h, norm_zero] at hprod
        linarith
      have hdet : detM (MXY m D t (x, y)) ∈ detSet (m + 1) Kc := ⟨D, hD, (det_matrix_xy m D t (x, y) hcofne).symm⟩
      have hΦ' := (hCcut V Φ _ _ τ hτ (derivBound_mono hΦ hk)).1
      have hDBΦ : DB q (cutPhi τ Φ) (MXY m D t (x, y)) K' 1 := by
        refine (DB_of_DerivBound hΦ' le_rfl hdet).mono ?_ zero_le_one le_rfl
        have h1 : min 1 (‖MXY m D t (x, y)‖ ^ (-A)) ≤ mx := by
          rw [hmxdef]
          exact min_le_max hA (y_le_MXY m D t (x, y))
        have h2 : 0 ≤ min 1 (‖MXY m D t (x, y)‖ ^ (-A)) := le_min zero_le_one (by positivity)
        calc Ccut * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)))
            ≤ |Ccut| * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A))) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ |Ccut| * (K * mx) := by gcongr
          _ = K' := hK'def.symm
      have hcofW : ‖cofXY m t (x, y)‖⁻¹ ≤ W := by
        refine hWle _ (le_trans ?_ hcW2)
        calc ‖cofXY m t (x, y)‖⁻¹ ≤ (δ ^ (m + 1) / 2)⁻¹ := inv_anti₀ (by positivity) hcof
          _ = 2 / δ ^ (m + 1) := by rw [inv_div]
      have hprodW : ‖∏ k, x k‖⁻¹ ≤ W := by
        refine hWle _ (le_trans ?_ hcW2)
        calc ‖∏ k, x k‖⁻¹ ≤ (δ ^ (m + 1))⁻¹ := inv_anti₀ hδp hprod
          _ ≤ 2 / δ ^ (m + 1) := by
            rw [div_eq_mul_inv]
            have : 0 ≤ (δ ^ (m + 1))⁻¹ := by positivity
            linarith
      have hyQ : ∀ e, ‖y e‖ ≤ Q := fun e => by
        have h1 := norm_le_pi_norm y e
        have h2 : Y ≤ Q := by rw [hQdef]; exact le_mul_of_one_le_left (by linarith) hcQ0
        rw [hYdef] at h2
        linarith
      have hc := hcore (Fin (m + 1) → ℂ) m q β D (fun _ => t) (fun v => v) (fun _ => y) x Q W (hQle _ hcQ1)
        (DB.const q t x (hQle _ (ht1.trans hcQ0)) zero_le_one)
        (fun k => DB_proj q (m + 1) k x (hQle _ ((hxu k).trans hcQ2)) (hQle _ hcQ0))
        (fun e => DB.const q (y e) x (hyQ e) zero_le_one)
        (hQle _ (((hRD D hD).trans hcRD).trans hcQ2)) (hQle _ hcQ3) hQW hcofne hcofW hprodne hprodW V
        (cutPhi τ Φ) K' hDBΦ
      have hamp : DB q (fun v : Fin (m + 1) → ℂ => ampIn β m ε Φ D t (v, y)) x (K' * W ^ a) (W ^ b) := by
        refine hc.congr ?_
        have hev : ∀ᶠ v : Fin (m + 1) → ℂ in 𝓝 x, ∏ k, v k ≠ 0 :=
          ContinuousAt.eventually_ne (g := fun v : Fin (m + 1) → ℂ => ∏ k, v k) (by fun_prop) hprodne
        filter_upwards [hev] with v hv
        show amp β m (cutPhi (‖t‖ ^ (-ε)) Φ) D t (v, y) = _
        rw [← hτdef]
        exact amp_eq_ampE β m _ D t (v, y) ht0 hv
      have hcc0 : DB q (critCut (n := m + 1) δ z) x |Ccrit| 1 :=
        ⟨(hCcrit z).1.contDiffAt, fun j hj => by
          rw [one_pow, mul_one]
          exact ((hCcrit z).2 j hj x).trans (le_abs_self _)⟩
      have hcc : DB q (fun v : Fin (m + 1) → ℂ => ((critCut δ z v : ℝ) : ℂ)) x |Ccrit| (W ^ b) :=
        (hcc0.clm_one Complex.ofRealCLM (by simp)).mono le_rfl zero_le_one (one_le_pow₀ hW1)
      exact hcc.smul hamp hP0
  refine ⟨contDiff_iff_contDiffAt.2 fun x => (key x).1, fun j hj x => ?_⟩
  have hexp : 4 * (m + 2) * (a + b * q) ≤ 4 * (a + 2 * b) * (m + 2) ^ 2 := by
    have h1 : m + 2 ≤ (m + 2) ^ 2 := Nat.le_self_pow two_ne_zero _
    have h2 : 4 * a * (m + 2) ≤ 4 * a * (m + 2) ^ 2 := Nat.mul_le_mul_left _ h1
    have h3 : q = 2 * (m + 2) := by omega
    rw [h3]
    calc 4 * (m + 2) * (a + b * (2 * (m + 2))) = 4 * a * (m + 2) + 8 * b * (m + 2) ^ 2 := by ring
      _ ≤ 4 * a * (m + 2) ^ 2 + 8 * b * (m + 2) ^ 2 := Nat.add_le_add_right h2 _
      _ = 4 * (a + 2 * b) * (m + 2) ^ 2 := by ring
  have hWpow : W ^ a * (W ^ b) ^ j ≤ cW ^ (a + b * q) * Y ^ (4 * (a + 2 * b) * (m + 2) ^ 2) := by
    calc W ^ a * (W ^ b) ^ j = W ^ (a + b * j) := by rw [← pow_mul, ← pow_add]
      _ ≤ W ^ (a + b * q) := pow_le_pow_right₀ hW1 (by gcongr)
      _ = cW ^ (a + b * q) * Y ^ (4 * (m + 2) * (a + b * q)) := by rw [hWdef, mul_pow, ← pow_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hexp) (by positivity)
  calc _ ≤ 2 ^ q * |Ccrit| * (K' * W ^ a) * (W ^ b) ^ j := (key x).2 j hj
    _ = (2 ^ q * |Ccrit| * |Ccut| * K * mx) * (W ^ a * (W ^ b) ^ j) := by rw [hK'def]; ring
    _ ≤ (2 ^ q * |Ccrit| * |Ccut| * K * mx) * (cW ^ (a + b * q) * Y ^ (4 * (a + 2 * b) * (m + 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left hWpow (by positivity)
    _ = _ := by rw [hYdef, hmxdef]; ring
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
