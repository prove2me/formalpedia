-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.siegel_bound_key_rearrange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:55.906937+00:00
-- url     : https://prove2.me/submissions/cf74cbd7-0c16-4297-922e-fcb1ffc7d210

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelBoundSameCharacter
import Theorems.Thm_Formalism_ZeroFreeDirichlet_log_three_mul_le_rpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {C A₁ CL x ℓ a K ε q₁ q : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hKa : K * a ≤ ε / 2) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) (hA₁ : 0 ≤ A₁) (hx : 0 ≤ x) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ CL * Real.log (3 * (q₁ * q)))
    (hkey : 1 / 2 - C * (A₁ * x * ℓ) * (q₁ * q) ^ (K * a) / a ≤ 0) :
    a / (2 * (max C 1 * max A₁ 1 * max CL 1 * (2 * (3 : ℝ) ^ (ε / 2) / ε)) * q₁ ^ ε) * q ^ (-ε) ≤ x := by
  set Q := q₁ * q with hQ
  set L := 2 * (3 : ℝ) ^ (ε / 2) / ε with hLdef
  have hQ1 : 1 ≤ Q := by rw [hQ]; nlinarith
  have hQ0 : 0 ≤ Q := by linarith
  have hL0 : 0 < L := by rw [hLdef]; positivity
  have hk : a / 2 ≤ C * (A₁ * x * ℓ) * Q ^ (K * a) := by
    have h' : 1 / 2 ≤ C * (A₁ * x * ℓ) * Q ^ (K * a) / a := by linarith
    rw [le_div_iff₀ ha] at h'; linarith
  have hlog0 : 0 ≤ Real.log (3 * Q) := Real.log_nonneg (by linarith)
  have hlogL : Real.log (3 * Q) ≤ L * Q ^ (ε / 2) := log_three_mul_le_rpow hQ0 hε
  have hℓ' : ℓ ≤ max CL 1 * (L * Q ^ (ε / 2)) :=
    hℓ.trans ((mul_le_mul_of_nonneg_right (le_max_left CL 1) hlog0).trans
      (mul_le_mul_of_nonneg_left hlogL (by positivity)))
  have hQK : Q ^ (K * a) ≤ Q ^ (ε / 2) := Real.rpow_le_rpow_of_exponent_le hQ1 hKa
  have hW0 : 0 ≤ A₁ * x * ℓ * Q ^ (K * a) := by positivity
  have step1 : C * (A₁ * x * ℓ) * Q ^ (K * a) ≤ max C 1 * (A₁ * x * ℓ * Q ^ (K * a)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left C 1) hW0
  have step2 : A₁ * x * ℓ * Q ^ (K * a)
      ≤ max A₁ 1 * x * (max CL 1 * (L * Q ^ (ε / 2))) * Q ^ (ε / 2) := by
    gcongr
    exact le_max_left A₁ 1
  have hQQ : Q ^ (ε / 2) * Q ^ (ε / 2) = q₁ ^ ε * q ^ ε := by
    rw [← Real.rpow_add (by linarith), add_halves, hQ, Real.mul_rpow (by linarith) (by linarith)]
  set M := max C 1 * max A₁ 1 * max CL 1 * L with hM
  have hM0 : 0 < M := by
    rw [hM]
    have : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max A₁ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max CL 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hmain : a / 2 ≤ M * x * (q₁ ^ ε * q ^ ε) := by
    have h3 := mul_le_mul_of_nonneg_left step2 (le_trans zero_le_one (le_max_right C 1))
    rw [← hQQ, hM]
    calc a / 2 ≤ _ := hk
      _ ≤ _ := step1
      _ ≤ _ := h3
      _ = _ := by ring
  have hq1e : 0 < q₁ ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  have hqe : 0 < q ^ ε := Real.rpow_pos_of_pos (by linarith) ε
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, div_div, div_le_iff₀ (by positivity)]
  nlinarith
end Formalism.ZeroFreeDirichlet
