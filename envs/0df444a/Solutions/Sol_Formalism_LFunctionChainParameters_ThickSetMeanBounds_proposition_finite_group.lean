-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.ThickSetMeanBounds.proposition_finite_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:37.671023+00:00
-- url     : https://prove2.me/submissions/7c94a656-d0e7-473b-a7aa-d4d9bcb98c68

import Definitions.Def_Formalism_SizeWindowBrackets_GrowthBoundGivesRiemannHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_RiemannHypothesisOfPowerBound
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_ThickAverage
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Mathlib.NumberTheory.Chebyshev
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LipschitzWeightAndMinimum
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_De_re
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_fPl_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_card_S_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_norm_avg_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_partner_inPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_mean_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_signal_term
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_balTop_diff
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_wR_thin
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_aR_mem
import Theorems.Thm_Formalism_D5_thick_average_formula
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_partner_inPhi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.ThickSetMeanBounds
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData
namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds
theorem _root_.solution {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] : GrowthInequalityExplicit (H := H) := by
  intro hBal D hD ell N m TT T2 a w x ε b b' η X' θ Cd CL Err hH
  obtain ⟨hx, hb, hη, hX', hb', hbX, hθ, hCd, ha, ⟨hwpos, hwthick, hwthin⟩, hN, hTop, hThin, hLip, hDer, hVal⟩ := hH
  have haB : ∀ t ∈ TT, (x - 1) * b ≤ a t ∧ a t ≤ (x + 1) * b := by
    intro t ht
    obtain ⟨h1, h2⟩ := abs_le.1 (ha t ht)
    constructor
    · have : x - 1 ≤ a t / b := by linarith
      rwa [le_div_iff₀ hb] at this
    · have : a t / b ≤ x + 1 := by linarith
      rwa [div_le_iff₀ hb] at this
  have hapos : ∀ t ∈ TT, 0 < a t := fun t ht => lt_of_lt_of_le (by nlinarith) (haB t ht).1
  have hf := CR.fPl_pos (H := H)

  have hA : topExcess D N ell TT a w = (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      balTop (CR.host D ell) (a t) t (w u0 j) := by
    unfold topExcess
    refine congrArg _ (Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun t ht =>
      Finset.sum_congr rfl fun j _ => ?_)
    have h1 := hBal D hD ell (a t) t (w u0 j) (hapos t ht) (hwpos u0 j) N (fun ρ hρ => hN u0 j t ρ ht hρ)
    have h2 := congrArg Complex.re h1
    rw [Complex.sub_re, Complex.ofReal_re, CR.De_re] at h2
    exact h2

  have hB : ∀ u0 : H, ∀ t ∈ TT, ∀ j : Fin m,
      balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j)
        ≤ balTop (CR.host D ell) (a t) t (w u0 j) + 2 * fPl H * (3 * (x + 1) * (η + 1)) := by
    intro u0 t ht j
    rw [CR.aR_mem TT a ht]
    have hd := CR.balTop_diff (CR.host D ell) (a t) t (w u0 j) (CR.wR T2 b w u0 j) (3 * (x + 1) * (η + 1))
      (by positivity) (by
        intro g hg ψ
        have hρ := CR.partner_inPhi t hg
        by_cases hth : IsThickAt T2 u0 (cconj + g + topPl t)
        · rw [CR.wR_thick T2 b w u0 j _ hth]
          obtain ⟨h1, h2⟩ := hwthick u0 j _ hth
          have hl := hLip ψ (a t) (w u0 j (cconj + g + topPl t)) b (hapos t ht) (hwpos u0 j _ hρ) hb
          rw [min_eq_right h1, abs_of_nonneg (by linarith)] at hl
          refine le_trans hl ?_
          have e1 : 3 * a t / b ≤ 3 * (x + 1) := by
            rw [div_le_iff₀ hb]; nlinarith [(haB t ht).2]
          have e0 : 0 ≤ 3 * a t / b := by have := hapos t ht; positivity
          exact mul_le_mul e1 (by linarith) (by linarith) (by positivity)
        · rw [CR.wR_thin T2 b w u0 j _ hth hρ, sub_self, norm_zero]; positivity)
    have := (abs_le.1 hd).1
    linarith
  have hB' := CR.mean_le TT (fun u0 t j => balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j))
    (fun u0 t j => balTop (CR.host D ell) (a t) t (w u0 j)) _ hB

  have hTA := thick_average_formula (H := H) (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos)

  have hC : ∀ u0 : H, ∀ t ∈ TT, ∀ j : Fin m, (0 : ℝ) ≤
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (CR.aR TT a t / CR.wR T2 b w u0 j (cconj + g + topPl t))).re
        + 2 * fPl H * ((x + 1) * b * θ) := by
    intro u0 t ht j
    rw [CR.aR_mem TT a ht]
    have hn := CR.norm_avg_le (univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)))
      (CR.card_S_le t _ (by
        intro g hg
        rw [Finset.mem_filter] at hg ⊢
        exact ⟨hg.1, hg.2.1⟩))
      (fun g ψ => ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (a t / CR.wR T2 b w u0 j (cconj + g + topPl t)))
      ((x + 1) * b * θ) (by positivity) (by
        intro g hg ψ
        obtain ⟨hg1, hg2⟩ := (Finset.mem_filter.1 hg).2
        have hρ := CR.partner_inPhi t hg1
        rw [CR.wR_thin T2 b w u0 j _ hg2 hρ]
        have hw0 := hwpos u0 j _ hρ
        have hw2 := hwthin u0 j _ hρ hg2
        have hy : X' / 3 ≤ a t / w u0 j (cconj + g + topPl t) := by
          rw [le_div_iff₀ hw0]
          have h1 : X' / 3 * w u0 j (cconj + g + topPl t) ≤ X' / 3 * (2 * b') :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
          have h2 := (haB t ht).1
          nlinarith
        have ht' := hThin ψ _ hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        calc w u0 j (cconj + g + topPl t) * ‖GC (CR.host D ell) ψ (a t / w u0 j (cconj + g + topPl t))‖
            ≤ w u0 j (cconj + g + topPl t) * (a t / w u0 j (cconj + g + topPl t) * θ) :=
              mul_le_mul_of_nonneg_left ht' hw0.le
          _ = a t * θ := by field_simp
          _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right (haB t ht).2 hθ)
    have hre := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) hn)).1
    simp only [mul_assoc] at hre ⊢
    linarith
  have hC' := CR.mean_le TT (fun _ _ _ => (0 : ℝ)) _ _ hC
  have hrest : -((TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ)))
      ≤ restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := by
    simp only [Finset.sum_const_zero, mul_zero] at hC'
    have : restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) = _ := rfl
    unfold restAvg
    show -((TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ))) ≤ (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      ((1 / ((PhiSet (H := H)).card : ℂ)) * ∑ g ∈ univ.filter (fun g : E0 × H =>
        ¬ InPhi (g + topPl t) ∧ ¬ IsThickAt T2 u0 (cconj + g + topPl t)),
      ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((CR.wR T2 b w u0 j (cconj + g + topPl t) : ℝ) : ℂ)
        * GC (CR.host D ell) ψ (CR.aR TT a t / CR.wR T2 b w u0 j (cconj + g + topPl t))).re
    linarith

  have hD' : (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ signal (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := by
    show _ ≤ ((T2.card : ℝ) / Fintype.card H) / 2 * ∑ t ∈ TT, ∑ j : Fin m, b *
      (GC (CR.host D ell) 0 (CR.aR TT a t / b) + GC (CR.host D ell) psC (CR.aR TT a t / b)
        - GC (CR.host D ell) chC (CR.aR TT a t / b) - GC (CR.host D ell) chpsC (CR.aR TT a t / b)).re
    have hs : ∑ t ∈ TT, ∑ _j : Fin m, b * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
        ≤ ∑ t ∈ TT, ∑ j : Fin m, b *
      (GC (CR.host D ell) 0 (CR.aR TT a t / b) + GC (CR.host D ell) psC (CR.aR TT a t / b)
        - GC (CR.host D ell) chC (CR.aR TT a t / b) - GC (CR.host D ell) chpsC (CR.aR TT a t / b)).re := by
      refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
      rw [CR.aR_mem TT a ht]
      exact mul_le_mul_of_nonneg_left (CR.signal_term D ell hx hCd (ha t ht) hDer hVal) hb.le
    have hδ : 0 ≤ ((T2.card : ℝ) / Fintype.card H) / 2 := by positivity
    have := mul_le_mul_of_nonneg_left hs hδ
    refine le_trans (le_of_eq ?_) this
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    unfold delta2; ring

  have hTA' : (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
      balTop (CR.host D ell) (CR.aR TT a t) t (CR.wR T2 b w u0 j)
      = signal (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos)
        + restAvg (CR.host D ell) (CR.nodes TT T2 a b w hb hapos hwpos) := hTA
  rw [← hA, hTA'] at hB'
  have e1 : (TT.card : ℝ) * m * (2 * fPl H * (3 * (x + 1) * (η + 1)))
      = (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1)) := by ring
  have e2 : (TT.card : ℝ) * m * (2 * fPl H * ((x + 1) * b * θ))
      = (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ) := by ring
  rw [e1] at hB'
  rw [e2] at hrest
  linarith
end Formalism.LFunctionChainParameters.ThickSetMeanBounds
