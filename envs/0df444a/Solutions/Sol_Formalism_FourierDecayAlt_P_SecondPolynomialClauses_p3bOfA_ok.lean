-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p3bOfA_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:59.49632+00:00
-- url     : https://prove2.me/submissions/cf7a5914-34ac-4632-9f1b-ce9e2791425c

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.SecondPolynomialClauses
theorem _root_.solution : LeadingBlockBoundFromRecursion := by
  intro K t t' Ntt Nt Nt' S abelian₂ c ht ht' hne hle hNt hNt' hS hLam hc hG hA
  have ho0 : 0 < ‖1 / t - 1 / t'‖ := norm_pos_iff.mpr hne
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hto : ‖1 / t - 1 / t'‖ * ‖t‖ ≤ 2 := by
    have h1 : ‖1 / t - 1 / t'‖ ≤ ‖1 / t‖ + ‖1 / t'‖ := norm_sub_le _ _
    have h2 : ‖1 / t'‖ ≤ 1 / ‖t‖ := by
      rw [norm_div, norm_one]; exact one_div_le_one_div_of_le htpos hle
    have h3 : ‖1 / t‖ = 1 / ‖t‖ := by rw [norm_div, norm_one]
    have h4 : ‖1 / t - 1 / t'‖ ≤ 2 / ‖t‖ := by
      rw [h3] at h1; linarith [show 2 / ‖t‖ = 1 / ‖t‖ + 1 / ‖t‖ by ring]
    exact (le_div_iff₀ htpos).mp h4
  have hL : ‖t‖ * abelian₂ ≤ 2 * abelian₂ / ‖1 / t - 1 / t'‖ := by
    rw [le_div_iff₀ ho0]; nlinarith [mul_le_mul_of_nonneg_left hto hLam]
  have hprod : ∏ a, c a ≤ (abelian₂ ^ 2) ^ K := by
    calc ∏ a, c a ≤ ∏ _a : Fin K, abelian₂ ^ 2 :=
          Finset.prod_le_prod (fun a _ => (hc a).1) (fun a _ => (hc a).2)
      _ = (abelian₂ ^ 2) ^ K := by simp
  have hT : 0 < ‖t‖ ^ (2 * K) := pow_pos htpos _
  have e : ‖t‖ ^ (-(2 * K : ℤ)) = (‖t‖ ^ (2 * K))⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [e] at hA
  have hA' : Nt ≤ ‖t‖ ^ (2 * K) * ((∏ a, c a) * S) := (inv_mul_le_iff₀ hT).mp hA
  have hX0 : 0 ≤ (2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K := pow_nonneg (div_nonneg (by linarith) ho0.le) K
  have hNtX : Nt ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * S := by
    calc Nt ≤ ‖t‖ ^ (2 * K) * ((∏ a, c a) * S) := hA'
      _ ≤ ‖t‖ ^ (2 * K) * ((abelian₂ ^ 2) ^ K * S) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprod hS) hT.le
      _ = ((‖t‖ * abelian₂) ^ K) ^ 2 * S := by ring
      _ ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * S :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg (mul_nonneg (norm_nonneg _) hLam) K)
            (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hLam) hL K) 2) hS
  have hsq : ‖Ntt‖ ^ 2 ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K * ((S + Nt') / 2)) ^ 2 := by
    calc ‖Ntt‖ ^ 2 ≤ Nt * Nt' := hG
      _ ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * S * Nt' := mul_le_mul_of_nonneg_right hNtX hNt'
      _ ≤ ((2 * abelian₂ / ‖1 / t - 1 / t'‖) ^ K) ^ 2 * ((S + Nt') / 2) ^ 2 := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (S - Nt')]) (sq_nonneg _)
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hX0 (by linarith)) two_ne_zero).mp hsq
end Formalism.FourierDecayAlt.P.SecondPolynomialClauses
