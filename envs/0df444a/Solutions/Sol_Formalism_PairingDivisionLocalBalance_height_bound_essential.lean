-- Prove2me | solution 1 for Formalism.PairingDivisionLocalBalance.height_bound_essential
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:24:18.487641+00:00
-- url     : https://prove2.me/submissions/97697835-fd80-48db-87bd-95e1b44c3239

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_SumValuationNat
import Definitions.Def_Formalism_PairingDivisors_PairingDivisorProofs_Height
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_lw_nonneg
import Theorems.Thm_P2M_Formalism_PairingDivisionLocalBalance_weight_sum__2a3905c4f836
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_vw_pow
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_inv
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_PairingDivisionLocalBalance_sum_valuation_nat
import Theorems.Thm_P2M_Formalism_DivisionValues_prod_formula__ad6919c95c2d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)
open Formalism Formalism.PairingDivisionLocalBalance
namespace Formalism.PairingDivisionLocalBalance
theorem _root_.solution : HeightCore := by
  intro K _ _ _ _ a De M nff o vA S N0 ha hDe hD hlo hhi hN hL2
  set β : K := a ^ 12 * (De ^ M)⁻¹ with hβ
  have hβ0 : β ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (inv_ne_zero (pow_ne_zero _ hDe))
  have hvβ : ∀ w : Pl K, vw w β = 12 * (vw w a + M * o w) := by
    intro w
    rw [hβ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ ha) (inv_ne_zero (pow_ne_zero _ hDe)),
      Formalism.DivisionValues.ValuationRepresentative.vw_inv, vw_pow w a ha, vw_pow w De hDe, hD w]
    push_cast; ring
  obtain ⟨pf1, pf2⟩ := Formalism.DivisionValues.prod_formula' K β hβ0
  obtain ⟨n1, n2⟩ := sum_valuation_nat K nff
  obtain ⟨w1, w2, w3⟩ := weight_sum' K S N0
  have hfin : (Function.support fun w : Pl K => lw w * |(vA w : ℝ)|).Finite := by
    refine (pf1.union n1).subset ?_
    intro w hw
    simp only [Function.mem_support, Set.mem_union] at hw ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨c1, c2⟩ := hcon
    have hl : lw w ≠ 0 := left_ne_zero_of_mul hw
    have d1 : vw w β = 0 := by
      have := (mul_eq_zero.mp c1).resolve_left hl; exact_mod_cast this
    have d2 : vw w (nff : K) = 0 := by
      have := (mul_eq_zero.mp c2).resolve_left hl; exact_mod_cast this
    have e1 := hvβ w
    have e2 := hlo w
    have e3 := hhi w
    rw [d2] at e3
    have : vA w = 0 := by omega
    apply hw; rw [this]; simp
  refine ⟨hfin, ?_⟩
  have hpt : ∀ w : Pl K, lw w * |(vA w : ℝ)| ≤
      (1 / 12) * (lw w * (vw w β : ℝ)) + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))
        + 2 * (lw w * wt S N0 w) := by
    intro w
    have h0 := lw_nonneg w
    have h1 : ((vw w β : ℤ) : ℝ) = 12 * ((vw w a : ℝ) + M * o w) := by rw [hvβ w]; push_cast; ring
    have h2 : (vA w : ℝ) ≤ (vw w a : ℝ) + M * o w + M * vw w (nff : K) := by exact_mod_cast hhi w
    have h3 := hL2 w
    have h4 := w3 hN w
    have h5 : |(vA w : ℝ)| ≤ (vA w : ℝ) + 2 * wt S N0 w := by
      rcases abs_cases (vA w : ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
    have h6 : |(vA w : ℝ)| ≤ (1 / 12) * (vw w β : ℝ) + M * vw w (nff : K) + 2 * wt S N0 w := by
      rw [h1]; linarith
    calc lw w * |(vA w : ℝ)| ≤ lw w * ((1 / 12) * (vw w β : ℝ) + M * vw w (nff : K) + 2 * wt S N0 w) :=
          mul_le_mul_of_nonneg_left h6 h0
      _ = _ := by ring
  have s1 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))).Finite :=
    pf1.subset fun w hw => right_ne_zero_of_mul hw
  have s2 : (Function.support fun w : Pl K => (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))).Finite :=
    n1.subset fun w hw => right_ne_zero_of_mul hw
  have s3 : (Function.support fun w : Pl K => (2 : ℝ) * (lw w * wt S N0 w)).Finite :=
    w1.subset fun w hw => right_ne_zero_of_mul hw
  have s12 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))
      + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ))).Finite :=
    (s1.union s2).subset (Function.support_add _ _)
  have s123 : (Function.support fun w : Pl K => (1 / 12 : ℝ) * (lw w * (vw w β : ℝ))
      + (M : ℝ) * (lw w * (vw w (nff : K) : ℝ)) + 2 * (lw w * wt S N0 w)).Finite :=
    (s12.union s3).subset (Function.support_add _ _)
  refine (finsum_le_finsum' hfin s123 hpt).trans (le_of_eq ?_)
  rw [finsum_add_distrib s12 s3, finsum_add_distrib s1 s2, ← mul_finsum, ← mul_finsum,
    ← mul_finsum, ← pf2, n2, w2]
  rfl
end Formalism.PairingDivisionLocalBalance
