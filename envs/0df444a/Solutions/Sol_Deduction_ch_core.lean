-- Prove2me | solution 1 for Deduction.ch_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:48:24.263072+00:00
-- url     : https://prove2.me/submissions/08cad987-dc69-4924-9ad2-cdacffbb6a13

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_Deduction_CharacterBalanceMoves_sum_vv
import Theorems.Thm_Deduction_CharacterBalanceMoves_one_char
import Theorems.Thm_Deduction_CharacterBalanceMoves_core
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain_size_windows_split
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_derivative_integral_all
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_proposition_size_bound


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
set_option maxHeartbeats 1600000
namespace Deduction
theorem _root_.solution (C ε CE Ko c M : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hc : |c| ≤ 1) : ∃ x1 : ℝ, ∀ x ≥ x1,
    ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (m : ℕ) (D : ArithData H) (S : Finset ℕ)
      (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
      (b b' k aE η X' θ : ℝ) (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)),
      HostFactsS D S → 0 < b → 0 ≤ aE → 0 < k → (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) → x * m ≤ k →
      SizesA A0 TT T2 a w N x b b' η X' θ → ThinScales D ell X' θ → CostWindows x (fPl H) b η θ →
      RestSize ε x (Fintype.card H) TT.card T2.card m b k aE → (∀ s ∈ T2, s ∈ A0) → CharsA ell A0 Kp TT c M Ko CE ε x →
      (∀ u ∈ A0, gapA D N ell TT a w u ≤ x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card H) TT.card T2.card m b k aE) →
      GmA D ell Kp c x ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε) + SigA D ell A0 Kp x := by
  obtain ⟨Cd, hCd, hDer⟩ := derivative_integral_all
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (show 0 < 3 * ε / 8 by positivity)).eventually_ge_atTop 26)
  set A1 : ℝ := 5 + Cd + |Ko| + |M| * (4 + Cd + |Ko|) + 4 * |CE| with hA1
  have hA10 : 0 ≤ A1 := by positivity
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).eventually_ge_atTop (|M| * A1))
  refine ⟨max 3 (max x₁ x₂), fun x hx => ?_⟩
  intro H _ _ _ m D S ell N TT T2 a w b b' k aE η X' θ A0 Kp hHost hb ha hk hm hxm hS hThin hCost hSize hT2 hCh hTop
  obtain ⟨h0K, hKp, hM, hE2, hKo, hE3⟩ := hCh
  have hx3 : 3 ≤ x := le_of_max_le_left hx
  have h26 := hx₁ x (le_of_max_le_left (le_of_max_le_right hx))
  have hbig := hx₂ x (le_of_max_le_right (le_of_max_le_right hx))
  have hx0 : 0 < x := by linarith
  have w1 : 1 ≤ x := by linarith
  have hW : SizeWindows C ε x (Fintype.card H) TT.card T2.card m b k aE
      (x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card H) TT.card T2.card m b k aE) :=
    (size_windows_split _ _ _ _ _ _ _ _ _ _ _).2 ⟨hSize, le_refl _, ⟨hx3, h26⟩, hε, hC,
      Fintype.card_pos, hb, ha, Finset.card_le_univ T2, hm, hxm⟩
  set s : ℝ := x ^ ((1 : ℝ) / 4) with hs
  set e : ℝ := x ^ ε with he
  have hs1 : 1 ≤ s := Real.one_le_rpow w1 (by norm_num)
  have he1 : 1 ≤ e := Real.one_le_rpow w1 hε.le
  have hX : x ^ ((1 : ℝ) / 2 + ε) = s * (s * e) := by
    rw [hs, he, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    ring
  have hρ : x ^ (-1 + ε) * x = e := by
    rw [Real.rpow_add hx0, Real.rpow_neg_one]
    field_simp
    rfl
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg w1
  have hl : Real.log x ≤ 4 * s := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hl1 : Real.log (x + 1) ≤ 5 * s := by
    have h1 : Real.log (x + 1) ≤ Real.log (2 * x) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hse : s ≤ s * e := le_mul_of_one_le_right (by linarith) he1
  have hse1 : 1 ≤ s * e := by linarith
  have up : ∀ z : ℝ, 0 ≤ z → z ≤ z * (s * e) := fun z hz => le_mul_of_one_le_right hz hse1
  have hMe : 0 ≤ |M| * (4 + Cd + |Ko|) * (s * e) := by positivity
  have hCe : 0 ≤ |CE| * (s * e) := by positivity
  have hKe : 0 ≤ |Ko| * (s * e) := by positivity
  have hCde : 0 ≤ Cd * (s * e) := by positivity
  have hR : A1 * (s * e) = 5 * (s * e) + Cd * (s * e) + |Ko| * (s * e) + |M| * (4 + Cd + |Ko|) * (s * e)
      + 4 * (|CE| * (s * e)) := by
    rw [hA1]; ring
  have hρ0 : 0 ≤ x ^ (-1 + ε) := Real.rpow_nonneg hx0.le _
  have r1 : Cd ≤ A1 * (s * e) := by linarith [up Cd hCd]
  have r2 : Real.log (x + 1) + Cd + |Ko| + |M| * x ^ (-1 + ε) * (x * (Real.log x + Cd + |Ko|)) ≤ A1 * (s * e) := by
    have e1 : |M| * x ^ (-1 + ε) * (x * (Real.log x + Cd + |Ko|)) = |M| * ((Real.log x + Cd + |Ko|) * e) := by
      rw [← hρ]; ring
    have e2 : Real.log x + Cd + |Ko| ≤ (4 + Cd + |Ko|) * s := by
      have := le_mul_of_one_le_right hCd hs1
      have := le_mul_of_one_le_right (abs_nonneg Ko) hs1
      linarith
    have e3 : |M| * ((Real.log x + Cd + |Ko|) * e) ≤ |M| * ((4 + Cd + |Ko|) * s * e) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (by linarith)) (abs_nonneg M)
    have e4 : |M| * ((4 + Cd + |Ko|) * s * e) = |M| * (4 + Cd + |Ko|) * (s * e) := by ring
    rw [e1]
    linarith [up Cd hCd, up _ (abs_nonneg Ko)]
  have r3 : Real.log (x + 1) + Cd + |CE| * Real.log x ≤ A1 * (s * e) := by
    have e1 : |CE| * Real.log x ≤ |CE| * (4 * (s * e)) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg CE)
    linarith [up Cd hCd]
  have hone := CharacterBalanceMoves.one_char A0 Kp D ell TT (fun t => a t / b) (c := c) (ρ := |M| * x ^ (-1 + ε)) (Ko := |Ko|)
    (L := |CE| * Real.log x) hx3 hCd hS.2.2.2.2.2.1 (hDer H D ell) (by positivity) (abs_nonneg _) h0K
    (fun ψ h => (hKp ψ h).2)
    (fun ψ h h' => (hE2 ψ h h').trans (by gcongr; exact le_abs_self M))
    (fun ψ h h' => (hKo ψ h h').trans (le_abs_self Ko))
    (fun ψ h h1 => (hE3 ψ h h1).trans (mul_le_mul_of_nonneg_right (le_abs_self CE) hl0))
    r1 r2 r3
  set G : ℝ := GmA D ell Kp c x - SigA D ell A0 Kp x with hG
  have hY : (TT.card : ℝ) * (G - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
      ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (CharacterBalanceMoves.e1 t) * GPsi D ell ψ (a t / b)).re := by
    simp_rw [Complex.re_sum]
    rw [Finset.sum_comm]
    refine le_trans ?_ (Finset.sum_le_sum hone)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, CharacterBalanceMoves.sum_vv A0 Kp (fun ψ h => (hKp ψ h).1), Finset.sum_const,
      nsmul_eq_mul, hX]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have k1 := mul_le_mul_of_nonneg_right (hM.trans (le_abs_self M)) (show 0 ≤ A1 * (s * e) by positivity)
    have k2 := mul_le_mul_of_nonneg_right hbig (show 0 ≤ s * e by positivity)
    have k3 : 0 ≤ s * (s * e) := by positivity
    have k4 : |M| * (A1 * (s * e)) = |M| * A1 * (s * e) := by ring
    linarith
  have hc' := CharacterBalanceMoves.core A0 D S hHost ell N TT T2 a w hx3 hb hS hThin hCost hT2 hTop hY
  have hz := proposition_size_bound _ _ _ _ _ _ _ _ _ _ _ G hW hc'
  linarith
end Deduction
