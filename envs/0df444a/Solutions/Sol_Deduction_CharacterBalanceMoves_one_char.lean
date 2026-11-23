-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.one_char
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:51.433599+00:00
-- url     : https://prove2.me/submissions/19e27dbb-e501-4cad-ae14-d1e061a88887

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_Deduction_CharacterBalanceMoves_move
import Theorems.Thm_Deduction_CharacterBalanceMoves_triv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalanceMoves
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalanceMoves
theorem _root_.solution (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (y : H → ℝ)
    {x Cd c ρ Ko L R : ℝ} (hx : 3 ≤ x) (hCd : 0 ≤ Cd) (hy : ∀ t ∈ TT, |y t - x| ≤ 1) (hDer : DerivInt D ell Cd)
    (hρ : 0 ≤ ρ) (hKo : 0 ≤ Ko) (h0K : 0 ∈ Kp) (hsg : ∀ ψ ∈ Kp, ψ sgc0 = 1)
    (h2 : ∀ ψ ∈ Kp, (¬ ∀ h : H, ψ (0, h) = 1) → ‖(∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)‖ ≤ ρ * (TT.card : ℝ))
    (hK : ∀ ψ ∈ Kp, ψ ≠ 0 → ‖ell ψ‖ ≤ Ko)
    (h3 : ∀ ψ ∈ PsiA A0, ψ ∉ Kp → ‖ell ψ‖ ≤ L)
    (r1 : Cd ≤ R) (r2 : Real.log (x + 1) + Cd + Ko + ρ * (x * (Real.log x + Cd + Ko)) ≤ R)
    (r3 : Real.log (x + 1) + Cd + L ≤ R)
    (ψ : AddChar (E0 × H) ℂ) (hψ : ψ ∈ PsiA A0) :
    (TT.card : ℝ) * (vv Kp D ell c x ψ - R) ≤ ∑ t ∈ TT, (ψ (e1 t) * GPsi D ell ψ (y t)).re := by
  classical
  by_cases h0 : ψ = 0
  · subst h0
    have hw : wtA c (0 : AddChar (E0 × H) ℂ) = 1 := by
      unfold wtA
      rw [if_pos (fun _ => AddChar.zero_apply _)]
    unfold vv
    rw [if_pos h0K, hw, one_mul, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨hy1, hy2⟩ := abs_le.1 (hy t ht)
    have hG := hDer.2 (y t) x (by linarith) (by linarith)
    have hG' := mul_le_mul_of_nonneg_left (hy t ht) hCd
    have := (abs_le.1 (hG.trans hG')).1
    simp [GPsi]
    linarith
  by_cases hX : ψ ∈ Kp
  · unfold vv
    rw [if_pos hX]
    have h2' : ‖(∑ t ∈ TT, ψ (0, t)) - ((wtA c ψ : ℝ) : ℂ) * (TT.card : ℂ)‖ ≤ ρ * (TT.card : ℝ) := by
      unfold wtA
      split_ifs with h
      · simp only [h, Finset.sum_const, nsmul_eq_mul, mul_one, Complex.ofReal_one, one_mul, sub_self, norm_zero]
        positivity
      · exact h2 ψ hX h
    generalize wtA c ψ = c at h2' ⊢
    have hk : ∀ t, ψ (e1 t) = ψ (0, t) := by
      intro t
      have : (e1 t : E0 × H) = sgc0 + (0, t) := by simp [e1, sgc0]
      rw [this, AddChar.map_add_eq_mul, hsg ψ hX, one_mul]
    simp_rw [hk]
    have e : ∑ t ∈ TT, ψ (0, t) * GPsi D ell ψ (y t) - (c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x
        = ∑ t ∈ TT, ψ (0, t) * (GPsi D ell ψ (y t) - GPsi D ell ψ x)
          + ((∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)) * GPsi D ell ψ x := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
      ring
    have hl := hK ψ hX h0
    have n1 : ‖∑ t ∈ TT, ψ (0, t) * (GPsi D ell ψ (y t) - GPsi D ell ψ x)‖ ≤ (TT.card : ℝ) * (Real.log (x + 1) + Cd + Ko) := by
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun t ht => ?_
      rw [norm_mul, AddChar.norm_apply, one_mul]
      have := move D ell hx hCd (hy t ht) hDer ψ h0
      linarith
    have n2 : ‖((∑ t ∈ TT, ψ (0, t)) - (c : ℂ) * (TT.card : ℂ)) * GPsi D ell ψ x‖
        ≤ ρ * (TT.card : ℝ) * (x * (Real.log x + Cd + Ko)) := by
      rw [norm_mul]
      refine mul_le_mul h2' ((triv D ell hx hCd hDer ψ h0).trans ?_) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have n3 := (norm_add_le _ _).trans (add_le_add n1 n2)
    rw [← e] at n3
    have n4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans n3)).1
    have e2 : ((c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x).re = c * TT.card * (GPsi D ell ψ x).re := by
      rw [show (c : ℂ) * (TT.card : ℂ) = ((c * TT.card : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    rw [Complex.sub_re, e2, Complex.re_sum] at n4
    have n5 := mul_le_mul_of_nonneg_left r2 (Nat.cast_nonneg (α := ℝ) TT.card)
    nlinarith
  · unfold vv
    rw [if_neg hX, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    have k2 := h3 ψ hψ hX
    have k3 := move D ell hx hCd (hy t ht) hDer ψ h0
    have k4 : ‖GPsi D ell ψ (y t)‖ ≤ ‖GPsi D ell ψ x‖ + ‖GPsi D ell ψ (y t) - GPsi D ell ψ x‖ := by
      simpa using norm_add_le (GPsi D ell ψ x) (GPsi D ell ψ (y t) - GPsi D ell ψ x)
    have k5 : ‖ψ (e1 t) * GPsi D ell ψ (y t)‖ ≤ ‖GPsi D ell ψ x‖ + R := by
      rw [norm_mul, AddChar.norm_apply, one_mul]
      linarith
    have := (abs_le.1 ((Complex.abs_re_le_norm _).trans k5)).1
    linarith
end Deduction.CharacterBalanceMoves
