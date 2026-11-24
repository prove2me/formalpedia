-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.card_range_inf_torsion_le_index_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:40.921131+00:00
-- url     : https://prove2.me/submissions/c23c1f9b-88b2-45da-aad7-77bd38a8f774

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_clm_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_expI
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_rhoXY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_MXY_cases
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_powle
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_mulQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_addQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_subQ
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_sm_DB
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_tpow_DB
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cof_DB
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_first_cofactor_derivative_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_remainder_derivative_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_leading_cofactor_derivative_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_normSq_inv_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_psi_eq

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
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ)
    (hQc : 2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q) (ht : DB q tt u Q 1)
    (hx : ∀ k, DB q (fun v => xx v k) u Q 1)
    (hy : ∀ e, DB q (fun v => yy v e) u Q 1) (hD : ‖D‖ ≤ Q) (hβ : ‖β‖ ≤ Q) (hQW : Q ^ (4 * (m + 2)) ≤ W)
    (hc : cofXY m (tt u) (xx u, yy u) ≠ 0) (hcW : ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W)
    (hp : ∏ k, xx u k ≠ 0) (hpW : ‖∏ k, xx u k‖⁻¹ ≤ W)
    (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ)
    (hΦ : DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1) :
    DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ 11) (W ^ 16) := by

  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hf1 : (1 : ℝ) ≤ (q.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero q)
  have hp1 : (1 : ℝ) ≤ (2 : ℝ) ^ q := one_le_pow₀ (by norm_num)
  have hs1 : (4 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by nlinarith
  have hA : (2 : ℝ) ^ q * ((m : ℝ) + 2) ^ 2 ≤ Q :=
    le_trans (le_mul_of_one_le_right (by positivity) hf1) hQc
  have h2 : (2 : ℝ) ^ q ≤ Q := le_trans (le_mul_of_one_le_right (by positivity) (by linarith)) hA
  have hs : ((m : ℝ) + 2) ^ 2 ≤ Q := le_trans (le_mul_of_one_le_left (by positivity) hp1) hA
  have hfQ : (q.factorial : ℝ) ≤ Q :=
    le_trans (le_mul_of_one_le_left (by positivity) (by nlinarith)) hQc
  have h4 : (4 : ℝ) ≤ Q := le_trans hs1 hs
  have h1Q : (1 : ℝ) ≤ Q := by linarith
  have h2Q : (2 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hm : (m : ℝ) + 1 ≤ Q := by nlinarith
  have hm2 : (m : ℝ) + 2 ≤ Q := by nlinarith
  have hQW1 : Q ≤ W := le_trans (le_self_pow₀ h1Q (by omega)) hQW
  have h1W : (1 : ℝ) ≤ W := le_trans h1Q hQW1
  have hW0 : (0 : ℝ) ≤ W := by linarith
  have h2W : (2 : ℝ) ≤ W := le_trans h2Q hQW1
  have h2qW : (2 : ℝ) ^ q ≤ W := le_trans h2 hQW1
  have hfW : (q.factorial : ℝ) ≤ W := le_trans hfQ hQW1
  have toW : ∀ {f : E → ℂ} {a : ℕ}, DB q f u (Q ^ a) 1 → a ≤ 4 * (m + 2) → DB q f u (W ^ 1) 1 := by
    intro f a h ha
    rw [pow_one]
    exact (h.powle h1Q ha zero_le_one).mono hQW zero_le_one le_rfl
  have P2 : (0 : ℝ) ≤ W ^ 2 := by positivity
  have tableLineDegreeTwo : (0 : ℝ) ≤ W ^ 16 := by positivity
  have one2 : (1 : ℝ) ≤ W ^ 2 := one_le_pow₀ h1W
  have up2 : ∀ {f : E → ℂ} {a : ℕ}, DB q f u (W ^ a) 1 → DB q f u (W ^ a) (W ^ 2) :=
    fun h => h.mono le_rfl zero_le_one one2
  have le216 : W ^ 2 ≤ W ^ 16 := pow_le_pow_right₀ h1W (by norm_num)

  have dcof := toW (cof_DB h1Q h2 hm ht hx hy) (by omega)
  have dcof1 := toW (first_cofactor_derivative_bound h1Q h2 hm ht hx hy) (by omega)
  have dcof0 := toW (leading_cofactor_derivative_bound (yy := yy) h2 hx) (by omega)
  have dsm := sm_DB hQ0 hx hy
  have dr1 := remainder_derivative_bound h1Q h2 hm ht hx hy
  have dtQ : DB q tt u (Q ^ 1) 1 := by simpa using ht
  have dDQ : DB q (fun _ : E => D) u (Q ^ 1) 1 := DB.const q D u (by simpa using hD) zero_le_one

  have dN : DB q (fun v => tt v ^ (m + 1) * sm m (xx v, yy v) - D - tt v * r1XY m (tt v) (xx v, yy v)) u
      (W ^ 1) 1 := by
    have a1 := ((tpow_DB h2 ht (m + 1)).mulQ dsm zero_le_one h2).powle h1Q
      (show 2 * (m + 1) + 1 + 1 ≤ 3 * m + 6 by omega) zero_le_one
    have a2 := dDQ.powle h1Q (show 1 ≤ 3 * m + 6 by omega) zero_le_one
    have a3 := (dtQ.mulQ dr1 zero_le_one h2).powle h1Q (show 1 + (3 * m + 4) + 1 ≤ 3 * m + 6 + 1 by omega)
      zero_le_one
    exact toW ((a1.subQ a2 zero_le_one h2Q).subQ a3 zero_le_one h2Q) (by omega)

  have dci : DB q (fun v => (cofXY m (tt v) (xx v, yy v))⁻¹) u (W ^ 3) (W ^ 2) := by
    have h := DB.inv dcof hc hcW (by simpa using h1W) h1W zero_le_one
    refine h.mono ?_ (by positivity) (by rw [pow_one, mul_one, sq])
    calc (q.factorial : ℝ) * (q.factorial * W) ≤ W * (W * W) := by gcongr
      _ = W ^ 3 := by ring
  have hc0 : cof0XY m (xx u, yy u) ≠ 0 := by
    simp only [cof0XY]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hp
  have hc0W : ‖cof0XY m (xx u, yy u)‖⁻¹ ≤ W := by
    simpa [cof0XY, norm_mul, norm_pow] using hpW
  have dc0i : DB q (fun v => (cof0XY m (xx v, yy v))⁻¹) u (W ^ 3) (W ^ 2) := by
    have h := DB.inv dcof0 hc0 hc0W (by simpa using h1W) h1W zero_le_one
    refine h.mono ?_ (by positivity) (by rw [pow_one, mul_one, sq])
    calc (q.factorial : ℝ) * (q.factorial * W) ≤ W * (W * W) := by gcongr
      _ = W ^ 3 := by ring

  have drho : DB q (fun v => rhoXY m D (tt v) (xx v, yy v)) u (W ^ 5) (W ^ 2) := by
    simp only [rhoXY_eq]
    exact (up2 dN).mulQ dci P2 h2qW

  have dg : DB q (fun v => gExt m D (tt v) (xx v, yy v)) u (W ^ 12) (W ^ 2) := by
    simp only [gExt]
    have a1 := ((tpow_DB h2 ht m).mulQ dsm zero_le_one h2).powle h1Q
      (show 2 * m + 1 + 1 ≤ 3 * m + 4 by omega) zero_le_one
    have a2 := toW (a1.subQ dr1 zero_le_one h2Q) (by omega)
    have a3 := a2.mulQ dcof0 zero_le_one h2qW
    have dDW : DB q (fun _ : E => D) u (W ^ 1) 1 :=
      DB.const q D u (by simpa using le_trans hD hQW1) zero_le_one
    have a4 := dDW.mulQ dcof1 zero_le_one h2qW
    have a5 := a3.addQ a4 zero_le_one h2W
    exact ((up2 a5).mulQ dci P2 h2qW).mulQ dc0i P2 h2qW

  have dpsi : DB q (fun v => psi β (gExt m D (tt v) (xx v, yy v))) u (W ^ 1) (W ^ 16) := by
    simp only [psi_eq]
    have dβ : DB q (fun _ : E => β) u (W ^ 1) (W ^ 2) :=
      DB.const q β u (by simpa using le_trans hβ hQW1) P2
    have a1 := dβ.mulQ dg P2 h2qW
    have a2 := DB.clm_one (Complex.reCLM : ℂ →L[ℝ] ℝ) (by simp) a1
    have a3 := DB.comp (DB_expI q _) a2 (one_le_pow₀ h1W) le_rfl P2
    refine a3.mono (by simpa using hfW) (by positivity) (le_of_eq (by ring))

  have dn : DB q (fun v => (((‖cofXY m (tt v) (xx v, yy v)‖ ^ 2)⁻¹ : ℝ) : ℂ)) u (W ^ 7) (W ^ 2) := by
    simp only [normSq_inv_cast]
    exact dci.mulQ (DB.clm_one (Complex.conjCLE : ℂ →L[ℝ] ℂ) (by simp) dci) P2 h2qW
  have dsc := dpsi.mulQ (dn.mono le_rfl P2 le216) tableLineDegreeTwo h2qW

  have dent : ∀ i j : Fin (m + 2), DB q (fun v => MXY m D (tt v) (xx v, yy v) i j) u (W ^ 5) (W ^ 2) := by
    intro i j
    have base : ∀ {f : E → ℂ}, DB q f u Q 1 → DB q f u (W ^ 5) (W ^ 2) := fun h =>
      h.mono (le_trans hQW1 (le_self_pow₀ h1W (by norm_num))) zero_le_one one2
    rcases MXY_cases m i j with h | h | h | ⟨k, h⟩ | ⟨e, h⟩
    · simp only [h]; exact DB.const q 0 u (by simp; positivity) P2
    · simp only [h]; exact base ht
    · simp only [h]; exact drho
    · simp only [h]; exact base (hx k)
    · simp only [h]; exact base (hy e)
  have dM : DB q (fun v => MXY m D (tt v) (xx v, yy v)) u (W ^ 7) (W ^ 2) := by
    have hcard : ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) ≤ W := by
      simp only [Fintype.card_fin]; push_cast; exact le_trans hm2 hQW1
    have r1 : ∀ i : Fin (m + 2), DB q (fun v => MXY m D (tt v) (xx v, yy v) i) u (W ^ 6) (W ^ 2) := by
      intro i
      refine (DB.pi (fun j => dent i j) P2).mono ?_ P2 le_rfl
      calc ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) * W ^ 5 ≤ W * W ^ 5 := by gcongr
        _ = W ^ 6 := by ring
    refine (DB.pi (fun i => r1 i) P2).mono ?_ P2 le_rfl
    calc ((Fintype.card (Fin (m + 2)) : ℕ) : ℝ) * W ^ 6 ≤ W * W ^ 6 := by gcongr
      _ = W ^ 7 := by ring
  have dΦ : DB q (fun v => Φ (MXY m D (tt v) (xx v, yy v))) u (q.factorial * K') (W ^ 16) := by
    have a := DB.comp (g := Φ) (f := fun v => MXY m D (tt v) (xx v, yy v)) hΦ dM (one_le_pow₀ h1W) le_rfl P2
    refine a.mono le_rfl (by positivity) ?_
    calc 1 * W ^ 7 * W ^ 2 = W ^ 9 := by ring
      _ ≤ W ^ 16 := pow_le_pow_right₀ h1W (by norm_num)
  have hK : 0 ≤ K' := hΦ.nonneg
  have fin := DB.smul dsc dΦ tableLineDegreeTwo
  refine fin.mono ?_ tableLineDegreeTwo le_rfl
  calc (2 : ℝ) ^ q * W ^ (1 + 7 + 1) * (q.factorial * K') ≤ W * W ^ (1 + 7 + 1) * (W * K') := by gcongr
    _ = K' * W ^ 11 := by ring
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
