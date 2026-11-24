-- Prove2me | solution 1 for Formalism.L2.Th1.F.weierstrass_series_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:01.488936+00:00
-- url     : https://prove2.me/submissions/122d4cb1-97ab-4268-800d-dc951eb28e54

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_main
import Theorems.Thm_Formalism_ELL_Lemma2Aux_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries
open TaylorWp
namespace Formalism.L2.Th1.F
theorem _root_.solution : IsWpUnique := by
  intro K _ _ g2 g3 P Q hP hQ
  obtain ⟨-, -, hP⟩ := hP
  obtain ⟨-, -, hQ⟩ := hQ
  have hX : (X : PowerSeries K) ≠ 0 := X_ne_zero
  have hdX : ∀ n : ℕ, X * derivative K ((X : PowerSeries K) ^ n) = (n : PowerSeries K) * X ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_X]
      push_cast
      linear_combination X * ih
  have main : ∀ n : ℕ, X ^ n ∣ P - Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨E, hE⟩ := ih
      have hD : X * (derivative K P - derivative K Q)
          = X ^ n * ((n : PowerSeries K) * E + X * derivative K E) := by
        rw [← map_sub, hE, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        linear_combination E * hdX n
      have hc : ((n : PowerSeries K) * E + X * derivative K E)
            * (-4 + X ^ 3 * (derivative K P + derivative K Q))
          = E * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q) + (1 + X ^ 2 * Q) ^ 2)
              - C g2 * X ^ 4) := by
        apply mul_left_cancel₀ (pow_ne_zero (n + 2) hX)
        have hs := congrArg₂ (· - ·) hP hQ
        simp only [Formalism.L2.Th1.B.dz] at hs
        linear_combination hs
          - X ^ 2 * (-4 + X ^ 3 * (derivative K P + derivative K Q)) * hD
          + X ^ 2 * (4 * ((1 + X ^ 2 * P) ^ 2 + (1 + X ^ 2 * P) * (1 + X ^ 2 * Q)
              + (1 + X ^ 2 * Q) ^ 2) - C g2 * X ^ 4) * hE
      have h0 := congrArg constantCoeff hc
      simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_natCast, map_ofNat, map_one,
        constantCoeff_X, constantCoeff_C] at h0
      have h1 : (4 * (n : K) + 12) * constantCoeff E = 0 := by
        linear_combination -h0
      have h2 : (4 * (n : K) + 12) ≠ 0 := by
        have : ((4 * n + 12 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast at this
        exact this
      have h3 : constantCoeff E = 0 := (mul_eq_zero.mp h1).resolve_left h2
      obtain ⟨E', rfl⟩ := X_dvd_iff.mpr h3
      exact ⟨E', by rw [hE]; ring⟩
  have hz : P - Q = 0 := by
    ext m
    rw [map_zero]
    exact X_pow_dvd_iff.mp (main (m + 1)) m (Nat.lt_succ_self m)
  exact sub_eq_zero.mp hz
end Formalism.L2.Th1.F
