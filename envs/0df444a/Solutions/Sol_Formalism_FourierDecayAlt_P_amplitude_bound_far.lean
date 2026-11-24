-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.amplitude_bound_far
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.755894+00:00
-- url     : https://prove2.me/submissions/37b7e4b7-364e-4f92-851c-cc0551c2ee97

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_eventually_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_affine
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_strict
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_corner_XY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_x_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_y_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rho_le_MXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Xm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Bm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_sm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_amp_eq_ampE
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_of_DerivBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_K_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_supp
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_continuous_cofXY
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_exists_derivBound_nonstationaryCutoff
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_le_norm_sub_of_nonstationaryCutoff_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_arith
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Far_proj_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_cofactor_lower_bound_radius
import Theorems.Thm_Formalism_FourierDecayAlt_P_cutoff_phase_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_matrix_xy
import Theorems.Thm_Formalism_FourierDecayAlt_P_product_lower_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_split_xy_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Far Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.AmpBoundFar := by
  obtain ⟨a, b, hcore⟩ := core
  refine ⟨4 * (a + b), ?_⟩
  intro m β Kc hKc h0 δ ε hδ hε hε' q
  obtain ⟨t₁, c₁, ht₁, hc₁, hCof⟩ := cofactor_lower_bound_radius m Kc hKc h0 2 two_pos
  obtain ⟨t₂, c₂, ht₂, hc₂, hProd⟩ := product_lower_bound m Kc hKc h0 2 two_pos
  obtain ⟨Cc, hCc⟩ := cutoff_phase_bound (m + 1 + 1) q
  obtain ⟨Cf, hCf0, hCf⟩ := exists_derivBound_nonstationaryCutoff m q δ hδ.1
  obtain ⟨RD, hRD⟩ := hKc.isBounded.exists_norm_le
  obtain ⟨cQ, hcQ⟩ : ∃ cQ : ℝ, cQ = 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial + |RD| + ‖β‖ + 2 := ⟨_, rfl⟩
  obtain ⟨cW, hcW⟩ : ∃ cW : ℝ, cW = cQ ^ (4 * (m + 2)) + c₁⁻¹ + c₂⁻¹ := ⟨_, rfl⟩
  have hpos1 : (0 : ℝ) ≤ 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial := by positivity
  have hcQ2 : 2 ≤ cQ := by
    rw [hcQ]; have := abs_nonneg RD; have := norm_nonneg β; linarith
  have hcQ1 : 1 ≤ cQ := by linarith
  have hcW1 : 1 ≤ cW := by
    rw [hcW]
    have h1 : 1 ≤ cQ ^ (4 * (m + 2)) := one_le_pow₀ hcQ1
    have h2 : 0 < c₁⁻¹ := inv_pos.2 hc₁
    have h3 : 0 < c₂⁻¹ := inv_pos.2 hc₂
    linarith
  refine ⟨2 ^ q * Cf * (max Cc 0) * cW ^ (a + b * q), min (min t₁ t₂) 1, c₂,
    lt_min (lt_min ht₁ ht₂) one_pos, hc₂, ?_⟩
  intro V _ _ _ Φ A K k hA hqk hΦ t D ht htt hD y
  have hD0 : D ≠ 0 := fun h => h0 (h ▸ hD)
  have hK : 0 ≤ K := K_nonneg hΦ hD hD0
  have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
  have ht1 : ‖t‖ ≤ 1 := htt.trans (min_le_right _ _)
  have htt₁ : ‖t‖ ≤ t₁ := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htt₂ : ‖t‖ ≤ t₂ := htt.trans ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = ‖t‖ ^ (-ε) := ⟨_, rfl⟩
  have hτ1 : 1 ≤ τ := by
    rw [hτdef]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos htn ht1 (by linarith)
  have hτ0 : 0 < τ := by linarith
  have hτinv : ‖t‖ ^ ε = τ⁻¹ := by rw [hτdef, Real.rpow_neg htn.le, inv_inv]
  rw [← hτdef]

  have key : ∀ x : Fin (m + 1) → ℂ, ampIn β m ε Φ D t (x, y) ≠ 0 →
      ‖y‖ ≤ 2 * τ ∧ (∀ k, ‖x k‖ ≤ 2 * τ) ∧ c₁ * τ⁻¹ ≤ ‖cofXY m t (x, y)‖ ∧ c₂ * τ⁻¹ ≤ ‖∏ k, x k‖ ∧
        ∀ k, c₂ * ‖t‖ ^ (((m : ℝ) + 2) * ε) ≤ ‖x k‖ := by
    intro x hx
    obtain ⟨hc, hM⟩ := supp β m ε Φ D t (x, y) ht hx
    rw [← hτdef] at hM
    have h2τ : (0 : ℝ) ≤ 2 * τ := by positivity
    have hxk : ∀ k, ‖(x, y).1 k‖ ≤ 2 * τ := fun k => (x_le_MXY m D t (x, y) k).trans hM.le
    have hy : ‖(x, y).2‖ ≤ 2 * τ := (y_le_MXY m D t (x, y)).trans hM.le
    have hρ : ‖rhoXY m D t (x, y)‖ ≤ 2 * τ := (rho_le_MXY m D t (x, y)).trans hM.le
    have hxo : ∀ k, xOf (Xm m (x, y)) (Bm m (x, y)) k = x k := (split_xy_matrix m t 0 (x, y)).1
    have hA1 := hCof ε hε hε' D hD t ht htt₁ (Xm m (x, y)) (Bm m (x, y)) (rhoXY m D t (x, y)) (rm m (x, y))
      (sm m (x, y)) (Xm_strict m _) (by rw [← hτdef]; exact fun i j => Xm_le m _ h2τ hxk hy i j)
      (by rw [← hτdef]; exact fun i => Bm_le m _ h2τ hxk hy i) (by rw [← hτdef]; exact hρ)
      (by rw [← hτdef]; exact fun k => rm_le m _ h2τ hxk hy k) (by rw [← hτdef]; exact sm_le m _ h2τ hxk hy)
      (corner_XY m D t (x, y) hc)
    have hA2 := hProd ε hε hε' D hD t ht htt₂ (Xm m (x, y)) (Bm m (x, y)) (rhoXY m D t (x, y)) (rm m (x, y))
      (sm m (x, y)) (Xm_strict m _) (by rw [← hτdef]; exact fun i j => Xm_le m _ h2τ hxk hy i j)
      (by rw [← hτdef]; exact fun i => Bm_le m _ h2τ hxk hy i) (by rw [← hτdef]; exact hρ)
      (by rw [← hτdef]; exact fun k => rm_le m _ h2τ hxk hy k) (by rw [← hτdef]; exact sm_le m _ h2τ hxk hy)
      (corner_XY m D t (x, y) hc)
    simp only [hxo] at hA2
    rw [hτinv] at hA1 hA2
    exact ⟨hy, hxk, hA1, hA2.1, hA2.2⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = cQ * τ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = cW * τ ^ (4 * (m + 2)) := ⟨_, rfl⟩
  have hτp1 : 1 ≤ τ ^ (4 * (m + 2)) := one_le_pow₀ hτ1
  have hW1 : 1 ≤ W := by
    rw [hW]; exact one_le_mul_of_one_le_of_one_le hcW1 hτp1
  have hcQQ : cQ ≤ Q := by rw [hQ]; exact le_mul_of_one_le_right (by linarith) hτ1
  have h2Q : 2 * τ ≤ Q := by rw [hQ]; exact mul_le_mul_of_nonneg_right hcQ2 hτ0.le
  have hinvW : ∀ c v : ℝ, 0 < c → c⁻¹ ≤ cW → c * τ⁻¹ ≤ v → v⁻¹ ≤ W := by
    intro c v hc hcc hv
    have hp : 0 < c * τ⁻¹ := mul_pos hc (inv_pos.2 hτ0)
    calc v⁻¹ ≤ (c * τ⁻¹)⁻¹ := inv_anti₀ hp hv
      _ = c⁻¹ * τ := by rw [mul_inv, inv_inv]
      _ ≤ cW * τ ^ (4 * (m + 2)) :=
          mul_le_mul hcc (le_self_pow₀ hτ1 (by omega)) hτ0.le (by linarith)
      _ = W := hW.symm

  obtain ⟨S, hS⟩ : ∃ S : Set (Fin (m + 1) → ℂ), S = {x | ‖y‖ ≤ 2 * τ ∧ (∀ k, ‖x k‖ ≤ 2 * τ) ∧
      c₁ * τ⁻¹ ≤ ‖cofXY m t (x, y)‖ ∧ c₂ * τ⁻¹ ≤ ‖∏ k, x k‖} := ⟨_, rfl⟩
  have hprodc : Continuous fun v : Fin (m + 1) → ℂ => ∏ k, v k :=
    continuous_finsetProd _ (fun k _ => continuous_apply k)
  have hSc : IsClosed S := by
    rw [hS]
    refine IsClosed.and isClosed_const (IsClosed.and ?_ (IsClosed.and ?_ ?_))
    · simp only [Set.ofPred_forall]
      exact isClosed_iInter fun k => isClosed_le (continuous_apply k).norm continuous_const
    · exact isClosed_le continuous_const (continuous_cofXY m t y).norm
    · exact isClosed_le continuous_const hprodc.norm
  have hDBF : ∀ x : Fin (m + 1) → ℂ,
      DB q (fun x : Fin (m + 1) → ℂ => ((farCut m δ D x : ℝ) : ℂ) • ampIn β m ε Φ D t (x, y)) x
        (2 ^ q * Cf * (max Cc 0 * K * W ^ a)) (W ^ b) := by
    intro x
    by_cases hx : x ∈ S
    · rw [hS] at hx
      obtain ⟨hy, hxk, hcofl, hprodl⟩ := hx
      have hcof : cofXY m t (x, y) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hcofl
        exact absurd hcofl (not_le.2 (mul_pos hc₁ (inv_pos.2 hτ0)))
      have hprod : ∏ k, x k ≠ 0 := by
        intro h
        rw [h, norm_zero] at hprodl
        exact absurd hprodl (not_le.2 (mul_pos hc₂ (inv_pos.2 hτ0)))
      have hΦq : DerivBound q (detSet (m + 1) Kc) (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ := fun Z hZ =>
        ⟨((hΦ Z hZ).1).of_le (by exact_mod_cast hqk), fun j hj => (hΦ Z hZ).2 j (hj.trans hqk)⟩
      have h1 := (hCc V Φ (detSet (m + 1) Kc) _ τ hτ1 hΦq).1
      have hdet : detM (MXY m D t (x, y)) ∈ detSet (m + 1) Kc :=
        ⟨D, hD, (det_matrix_xy m D t (x, y) hcof).symm⟩
      have hΦ' : DB q (cutPhi τ Φ) (MXY m D t (x, y)) (max Cc 0 * K) 1 := by
        refine (DB_of_DerivBound h1 le_rfl hdet).mono ?_ zero_le_one le_rfl
        have hb0 : 0 ≤ K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)) :=
          mul_nonneg hK (le_min zero_le_one (Real.rpow_nonneg (norm_nonneg _) _))
        have hb1 : K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)) ≤ K := mul_le_of_le_one_right hK (min_le_left _ _)
        calc Cc * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A)))
            ≤ max Cc 0 * (K * min 1 (‖MXY m D t (x, y)‖ ^ (-A))) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
          _ ≤ max Cc 0 * K := mul_le_mul_of_nonneg_left hb1 (le_max_right _ _)
      have hDBx : ∀ k, DB q (fun v : Fin (m + 1) → ℂ => v k) x Q 1 := by
        intro k
        have := DB.affine q (ContinuousLinearMap.proj k : (Fin (m + 1) → ℂ) →L[ℝ] ℂ) 0 x (S := Q)
          (by simpa using (hxk k).trans h2Q) ((proj_norm_le _ k).trans (hcQ1.trans hcQQ))
        simpa using this
      have hDBcore := hcore (Fin (m + 1) → ℂ) m q β D (fun _ => t) (fun v => v) (fun _ => y) x Q W
        (le_trans (by rw [hcQ]; have := abs_nonneg RD; have := norm_nonneg β; linarith) hcQQ)
        (DB.const q t x (ht1.trans (hcQ1.trans hcQQ)) zero_le_one) hDBx
        (fun e => DB.const q (y e) x (((norm_le_pi_norm y e).trans hy).trans h2Q) zero_le_one)
        (le_trans (by rw [hcQ]; have := hRD D hD; have := le_abs_self RD; have := norm_nonneg β; linarith) hcQQ)
        (le_trans (by rw [hcQ]; have := abs_nonneg RD; linarith) hcQQ)
        (by
          rw [hQ, hW, mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hcW]
          have h2 : 0 < c₁⁻¹ := inv_pos.2 hc₁
          have h3 : 0 < c₂⁻¹ := inv_pos.2 hc₂
          linarith)
        hcof
        (hinvW c₁ _ hc₁ (by
          rw [hcW]
          have h1 : 0 ≤ cQ ^ (4 * (m + 2)) := by positivity
          have h3 : 0 < c₂⁻¹ := inv_pos.2 hc₂
          linarith) hcofl)
        hprod
        (hinvW c₂ _ hc₂ (by
          rw [hcW]
          have h1 : 0 ≤ cQ ^ (4 * (m + 2)) := by positivity
          have h3 : 0 < c₁⁻¹ := inv_pos.2 hc₁
          linarith) hprodl)
        V (cutPhi τ Φ) (max Cc 0 * K) hΦ'
      have hev : (fun v : Fin (m + 1) → ℂ => ampIn β m ε Φ D t (v, y)) =ᶠ[𝓝 x]
          fun v => ampE β m (cutPhi τ Φ) D t (v, y) := by
        filter_upwards [hprodc.continuousAt.eventually_ne hprod] with v hv
        rw [hτdef]
        exact amp_eq_ampE β m (cutPhi (‖t‖ ^ (-ε)) Φ) D t (v, y) ht hv
      have hAm := hDBcore.congr hev
      have hFar := (hCf D x).mono le_rfl zero_le_one (one_le_pow₀ hW1 : 1 ≤ W ^ b)
      exact hFar.smul hAm (by positivity)
    · refine DB.of_eventually_zero ?_ (by positivity) (by positivity)
      filter_upwards [hSc.isOpen_compl.mem_nhds hx] with x' hx'
      by_contra hne
      apply hx'
      have hne' : ampIn β m ε Φ D t (x', y) ≠ 0 := fun h => hne (by rw [h, smul_zero])
      obtain ⟨h1, h2, h3, h4, _⟩ := key x' hne'
      rw [hS]
      exact ⟨h1, h2, h3, h4⟩
  refine ⟨contDiff_iff_contDiffAt.2 fun x => (hDBF x).1, ?_, ?_⟩
  · intro x hx
    have hne' : ampIn β m ε Φ D t (x, y) ≠ 0 := fun h => hx (by rw [h, smul_zero])
    have hfar : farCut m δ D x ≠ 0 := fun h => hx (by rw [h]; simp)
    obtain ⟨h1, h2, _, _, h5⟩ := key x hne'
    exact ⟨h1, fun k => ⟨h2 k, h5 k⟩, fun z hz => le_norm_sub_of_nonstationaryCutoff_ne_zero m Kc δ hδ D hD x hfar z hz⟩
  · intro j hj x
    have hb := (hDBF x).2 j hj
    have hpow : τ ^ (4 * (a + b) * (m + 2) * (j + 1)) =
        ‖t‖ ^ (-(ε * (((4 * (a + b) : ℕ) : ℝ) * ((m : ℝ) + 2) * ((j : ℝ) + 1)))) := by
      rw [hτdef, ← Real.rpow_natCast, ← Real.rpow_mul htn.le]
      congr 1
      push_cast
      ring
    calc _ ≤ 2 ^ q * Cf * (max Cc 0 * K * W ^ a) * (W ^ b) ^ j := hb
      _ = (2 ^ q * Cf * max Cc 0 * K) * (W ^ a * (W ^ b) ^ j) := by ring
      _ ≤ (2 ^ q * Cf * max Cc 0 * K) * (cW ^ (a + b * q) * τ ^ (4 * (a + b) * (m + 2) * (j + 1))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hW]
          exact arith a b q j m hj cW τ hcW1 hτ1
      _ = _ := by rw [hpow]; ring
end Formalism.FourierDecayAlt.P
