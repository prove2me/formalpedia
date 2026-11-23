-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:12.978801+00:00
-- url     : https://prove2.me/submissions/2dfe11e0-3702-4e8b-9076-56a94830e154

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Theorems.Thm_Formalism_CountingSumsFrames_fock_mult_val_le
import Theorems.Thm_Formalism_CountingSumsFrames_fock_val_prod
import Theorems.Thm_Formalism_CountingSumsFrames_fock_L_nonneg
import Theorems.Thm_Formalism_CountingSumsFrames_fock_log_le
import Theorems.Thm_Formalism_CountingSumsFrames_factProd_ne_zero
import Theorems.Thm_Formalism_CountingSumsFrames_fock_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (p : ℕ) [Fact p.Prime] {σ Z : Type} [Fintype σ] [Fintype Z] [DecidableEq Z]
    (letter : σ → Z) (d : Z → ℕ) (N k : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hcard : Fintype.card σ ≤ N * k) (hd : ∀ z, (d z : ℝ) ≤ 2 * a) (α : σ →₀ ℕ)
    (hh : ∀ z, ∑ i ∈ univ.filter (fun i => letter i = z), α i = d z) :
    padicValNat p (factProd α) ≤ padicValNat p (∏ z, (d z).factorial) ∧
      (padicValNat p (∏ z, (d z).factorial) : ℝ) - N * k * (Real.logb p (2 * a + k) + 1) ≤
        padicValNat p (factProd α) := by
  classical
  have hkey := fock_key letter d α hh
  have hne : ∏ z, Nat.multinomial (univ.filter (fun i => letter i = z)) α ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun z _ => (Nat.multinomial_pos _ _).ne'
  set S := ∑ z, padicValNat p (Nat.multinomial (univ.filter (fun i => letter i = z)) α) with hS
  have hV : padicValNat p (∏ z, (d z).factorial) = padicValNat p (factProd α) + S := by
    rw [hkey, padicValNat.mul (factProd_ne_zero α) hne, hS,
      fock_val_prod p univ _ (fun z _ => (Nat.multinomial_pos _ _).ne')]
  refine ⟨by rw [hV]; omega, ?_⟩
  set T := ∑ z, (univ.filter (fun i => letter i = z)).card * Nat.log p (d z) with hT
  have hST : S ≤ T := by
    refine Finset.sum_le_sum fun z _ => ?_
    have := fock_mult_val_le p (⇑α) (univ.filter fun i => letter i = z)
    rwa [hh z] at this
  have hcardsum : ∑ z, (univ.filter (fun i => letter i = z)).card = Fintype.card σ := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (letter x))).symm
  have hTR : (T : ℝ) ≤ N * k * (Real.logb p (2 * a + k) + 1) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hc : ∀ z, (univ.filter (fun i => letter i = z)).card = 0 := by
        intro z
        have := Finset.card_le_univ (univ.filter (fun i => letter i = z))
        subst hk0
        omega
      have : T = 0 := by rw [hT]; simp [hc]
      rw [this, hk0]; simp
    · have hL0 := fock_L_nonneg p k a ha hk0
      rw [hT]; push_cast
      calc ∑ z, ((univ.filter (fun i => letter i = z)).card : ℝ) * (Nat.log p (d z) : ℝ)
          ≤ ∑ z, ((univ.filter (fun i => letter i = z)).card : ℝ) * (Real.logb p (2 * a + k) + 1) :=
            Finset.sum_le_sum fun z _ =>
              mul_le_mul_of_nonneg_left (fock_log_le p k (d z) a ha hk0 (hd z)) (Nat.cast_nonneg _)
        _ = (Fintype.card σ : ℝ) * (Real.logb p (2 * a + k) + 1) := by
            rw [← Finset.sum_mul, ← Nat.cast_sum, hcardsum]
        _ ≤ N * k * (Real.logb p (2 * a + k) + 1) := by
            apply mul_le_mul_of_nonneg_right _ hL0
            exact_mod_cast hcard
  have e1 : (padicValNat p (∏ z, (d z).factorial) : ℝ) = padicValNat p (factProd α) + S := by
    exact_mod_cast hV
  have e2 : (S : ℝ) ≤ T := by exact_mod_cast hST
  linarith
end Formalism.CountingSumsFrames
