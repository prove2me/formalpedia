-- Prove2me | solution 1 for Deduction.CharacterBalanceMoves.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:08:41.001014+00:00
-- url     : https://prove2.me/submissions/22f22637-f690-4f70-9f76-66b627c107f8

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_Deduction_CharacterBalanceMoves_sum_Th
import Theorems.Thm_Deduction_CharacterBalanceMoves_th_le
import Theorems.Thm_Deduction_ch_balance
import Theorems.Thm_Formalism_LFunctionChainParameters_ThickSetMeanBounds_lipschitz_weight_all


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
theorem _root_.solution (A0 : AddSubgroup H) (D : ArithData H) (S : Finset ℕ) (hD : HostFactsS D S) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ}
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) {x b b' η X' θ Err Y : ℝ}
    (hx : 3 ≤ x) (hb : 0 < b) (hS : SizesA A0 TT T2 a w N x b b' η X' θ) (hThin : ThinScales D ell X' θ)
    (hC : CostWindows x (fPl H) b η θ) (hT2 : ∀ s ∈ T2, s ∈ A0)
    (hTop : ∀ u0 ∈ A0, gapA D N ell TT a w u0 ≤ Err)
    (hY : (TT.card : ℝ) * Y ≤ ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ (a t / b)).re) :
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * Y ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by
  classical
  obtain ⟨hη, hX', hb', hbX, hθ, ha, hwpos, hwthick, hwthin, hN⟩ := hS
  have hapos : ∀ t ∈ TT, 0 < a t := fun t ht => by
    have h1 : x - 1 ≤ a t / b := by linarith [(abs_le.1 (ha t ht)).1]
    rw [le_div_iff₀ hb] at h1
    nlinarith
  have hK : 2 * fPl H * (3 * (x + 1) * (η + 1) + (x + 1) * b * θ) ≤ 2 * b / x := by
    have h1 := mul_le_mul_of_nonneg_left hC.1 hb.le
    have h2 := hC.2
    have e : 2 * b / x = b * (1 / x) + b / x := by ring
    rw [e]
    nlinarith
  have hu : ∀ u0 ∈ A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u0 t).re ≤ Err + 2 * (TT.card : ℝ) * m * b / x := by
    intro u0 hu0
    have h1 : ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u0 t).re
        ≤ ∑ t ∈ TT, ∑ j : Fin m, (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re + 2 * b / x) := by
      refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
      have k1 := th_le D ell T2 x b b' η X' θ (a t) u0 t (w u0 j) hx hb hη hX' hb' hbX hθ (ha t ht) (hwpos u0 hu0 j)
        (hwthick u0 hu0 j) (hwthin u0 hu0 j) hThin (lipschitz_weight_all H D ell)
      have k2 := congrArg Complex.re (ch_balance D S hD ell (a t) t (w u0 j) (hapos t ht) (hwpos u0 hu0 j) N
        (fun ρ hρ => hN u0 hu0 j t ρ ht hρ))
      rw [Complex.sub_re, Complex.ofReal_re] at k2
      linarith
    simp only [Finset.sum_add_distrib] at h1
    have e : ∑ _t ∈ TT, ∑ _j : Fin m, 2 * b / x = 2 * (TT.card : ℝ) * m * b / x := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring
    rw [e] at h1
    have := hTop u0 hu0
    unfold gapA at this
    linarith
  have hA : (0 : ℝ) < Fintype.card A0 := by exact_mod_cast Fintype.card_pos
  have h1 : ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u t).re
      ≤ (Fintype.card A0 : ℝ) * (Err + 2 * (TT.card : ℝ) * m * b / x) := by
    refine (Finset.sum_le_sum fun (u : A0) _ => hu u u.2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h2 : ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u t).re
      = (Fintype.card A0 : ℝ) * ((m * b * (delta2 T2 / 2)) *
        ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ (e1 t) * GPsi D ell ψ (a t / b)).re) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_sum, ← Complex.re_sum, sum_Th A0 D ell T2 hT2, Complex.re_ofReal_mul]
    ring
  rw [h2] at h1
  have h3 := le_of_mul_le_mul_left h1 hA
  have h4 : 0 ≤ (m : ℝ) * b * (delta2 T2 / 2) := by unfold delta2; positivity
  have h5 := mul_le_mul_of_nonneg_left hY h4
  nlinarith
end Deduction.CharacterBalanceMoves
