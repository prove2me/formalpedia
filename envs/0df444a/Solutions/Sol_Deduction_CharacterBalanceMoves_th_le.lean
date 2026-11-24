-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.th_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:32.966078+00:00
-- url     : https://prove2.me/submissions/a97ba093-dc6f-4c91-a48d-375717da54a3

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_Formalism_D5_thick_filter
import Theorems.Thm_Formalism_D5_thick_inj
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_De_re
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_GC_host
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_card_S_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_norm_avg_le
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_CR_partner_inPhi
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_partner_inPhi


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
theorem _root_.solution (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (x b b' η X' θ A : ℝ) (u0 t : H) (w : E0 × H → ℝ)
    (hx : 3 ≤ x) (hb : 0 < b) (hη : 0 ≤ η) (hX' : 0 < X') (_hb' : 0 < b') (hbX : b' * X' ≤ x * b) (hθ : 0 ≤ θ)
    (hA : |A / b - x| ≤ 1) (hwpos : ∀ ρ, InPhi ρ → 0 < w ρ)
    (hwthick : ∀ ρ, IsThickAt T2 u0 ρ → b ≤ w ρ ∧ w ρ ≤ b + η + 1)
    (hwthin : ∀ ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w ρ ≤ 2 * b')
    (hThin : ThinScales D ell X' θ) (hLip : LipW D ell) :
    (Th D ell T2 b (A / b) u0 t).re ≤ (De D ell A t w).re + 2 * fPl H * (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hA
  have hA1 : (x - 1) * b ≤ A := by
    have : x - 1 ≤ A / b := by linarith
    rwa [le_div_iff₀ hb] at this
  have hA2 : A ≤ (x + 1) * b := by
    have : A / b ≤ x + 1 := by linarith
    rwa [div_le_iff₀ hb] at this
  have hA0 : 0 < A := lt_of_lt_of_le (by nlinarith) hA1
  have hTh : Th D ell T2 b (A / b) u0 t = (1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0) := by
    unfold Th
    congr 1
    have : ∀ g : E0 × H, ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0)
        = if IsThickAt T2 u0 (cconj + g + topPl t) then
          ∑ ψ : AddChar (E0 × H) ℂ, ψ (-g) * ((b : ℂ) * GPsi D ell ψ (A / b)) else 0 := by
      intro g
      split_ifs <;> simp
    simp_rw [this]
    rw [← Finset.sum_filter, Finset.filter_filter, thick_filter,
      Finset.sum_image (fun s _ s' _ h => thick_inj u0 t (Set.mem_univ s) (Set.mem_univ s') h)]
    rfl
  have hn := CR.norm_avg_le (univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))) (CR.card_S_le t _ (Finset.Subset.refl _))
    (fun g ψ => ((w (cconj + g + topPl t) : ℝ) : ℂ) * GPsi D ell ψ (A / w (cconj + g + topPl t))
      - (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0))
    (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) (by positivity) (by
      intro g hg ψ
      have hρ := CR.partner_inPhi t (Finset.mem_filter.1 hg).2
      have hw0 := hwpos _ hρ
      have p1 : 0 ≤ 3 * (x + 1) * (η + 1) := by positivity
      have p2 : 0 ≤ (x + 1) * b * θ := by positivity
      by_cases hth : IsThickAt T2 u0 (cconj + g + topPl t)
      · simp only [if_pos hth]
        obtain ⟨k1, k2⟩ := hwthick _ hth
        have hl := hLip ψ A (w (cconj + g + topPl t)) b hA0 hw0 hb
        rw [min_eq_right k1, abs_of_nonneg (by linarith)] at hl
        have e1 : 3 * A / b ≤ 3 * (x + 1) := by
          rw [div_le_iff₀ hb]; nlinarith
        have e2 : 3 * A / b * (w (cconj + g + topPl t) - b) ≤ 3 * (x + 1) * (η + 1) :=
          mul_le_mul e1 (by linarith) (by linarith) (by positivity)
        linarith
      · simp only [if_neg hth, sub_zero]
        have hw2 := hwthin _ hρ hth
        have hy : X' / 3 ≤ A / w (cconj + g + topPl t) := by
          rw [le_div_iff₀ hw0]
          have k1 : X' / 3 * w (cconj + g + topPl t) ≤ X' / 3 * (2 * b') :=
            mul_le_mul_of_nonneg_left hw2 (by positivity)
          nlinarith
        have ht' := hThin ψ _ hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        have : w (cconj + g + topPl t) * ‖GPsi D ell ψ (A / w (cconj + g + topPl t))‖ ≤ (x + 1) * b * θ :=
          calc w (cconj + g + topPl t) * ‖GPsi D ell ψ (A / w (cconj + g + topPl t))‖
            ≤ w (cconj + g + topPl t) * (A / w (cconj + g + topPl t) * θ) :=
              mul_le_mul_of_nonneg_left ht' hw0.le
          _ = A * θ := by field_simp
          _ ≤ (x + 1) * b * θ := mul_le_mul_of_nonneg_right hA2 hθ
        linarith)
  have hre := (abs_le.1 (le_trans (Complex.abs_re_le_norm _) hn)).1
  have e : (De D ell A t w).re - (Th D ell T2 b (A / b) u0 t).re = ((1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), ∑ ψ : AddChar (E0 × H) ℂ,
        ψ (-g) * (((w (cconj + g + topPl t) : ℝ) : ℂ) * GPsi D ell ψ (A / w (cconj + g + topPl t))
      - (if IsThickAt T2 u0 (cconj + g + topPl t) then (b : ℂ) * GPsi D ell ψ (A / b) else 0))).re := by
    rw [CR.De_re, hTh]
    unfold balTop
    rw [← Complex.sub_re, ← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg Complex.re (congrArg _ (Finset.sum_congr rfl fun g _ => ?_))
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ψ _ => by rw [CR.GC_host]; ring
  rw [← e] at hre
  linarith
end Deduction.CharacterBalanceMoves
