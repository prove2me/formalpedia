-- Prove2me | solution 1 for Formalism.DivisionValues.second_complement_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:30.322944+00:00
-- url     : https://prove2.me/submissions/db346c0e-829d-42e1-b6b9-853b1d011e38

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_lw_pos
import Theorems.Thm_Formalism_DivisionValues_places_over_coprime
import Theorems.Thm_Formalism_DivisionValues_second_complement_arithmetic
import Theorems.Thm_Formalism_DivisionValues_second_complement_degree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open PlaceSumConjugation
namespace Formalism.DivisionValues
theorem _root_.solution : Complement2Sum := by
  unfold Complement2Sum
  intro K _ _ _ _ g hg hcop E F hEfin nn cg m Dpi Dp Dm er Eels hE hF hcg hnn hEels Pl _ TT _
    aT w nν δν δpm k hDpi hnν hD
  classical
  have hdeg := second_complement_degree Pl TT aT w nν δν δpm k Dpi Dp Dm hDpi hnν hD
  have hA : ∀ i, |2 * (∑ᶠ (v : HeightOneSpectrum (𝓞 K)) (_ : PlOver (g i) v), lw v * E v) -
      (Dpi - Dp - Dm) * Real.log (g i : ℝ)| ≤ 2 * er * Real.log (g i : ℝ) := fun i =>
    second_complement_arithmetic K (g i) (hg i) E F (nn i) (cg i) m Dpi Dp Dm er (hE i) (hF i) (hcg i)
      (hnn i)
  have hdisj : ∀ v, ¬ (PlOver (g 0) v ∧ PlOver (g 1) v) := fun v =>
    places_over_coprime K (g 0) (g 1) hcop v
  have hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 K) => lw v * E v).Finite :=
    hEfin.subset (fun v hv => by
      rw [Function.mem_support] at hv ⊢; intro h; exact hv (by rw [h, mul_zero]))
  have hsub : ∀ (P : HeightOneSpectrum (𝓞 K) → Prop),
      (Function.support fun v => ∑ᶠ (_ : P v), lw v * E v).Finite := fun P =>
    hsupp.subset (fun v hv => by
      rw [Function.mem_support] at hv ⊢; intro h; apply hv; rw [h]; simp)
  have hsplit : ∀ v : HeightOneSpectrum (𝓞 K), lw v * E v =
      ((∑ᶠ (_ : PlOver (g 0) v), lw v * E v) + ∑ᶠ (_ : PlOver (g 1) v), lw v * E v) +
      ∑ᶠ (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v := by
    intro v
    have hd := hdisj v
    simp only [finsum_eq_if]
    by_cases h0 : PlOver (g 0) v <;> by_cases h1 : PlOver (g 1) v
    · exact absurd ⟨h0, h1⟩ hd
    · have hn : ¬ ∀ i, ¬ PlOver (g i) v := fun h => h 0 h0
      rw [if_pos h0, if_neg h1, if_neg hn]; ring
    · have hn : ¬ ∀ i, ¬ PlOver (g i) v := fun h => h 1 h1
      rw [if_neg h0, if_pos h1, if_neg hn]; ring
    · have hn : ∀ i, ¬ PlOver (g i) v := Fin.forall_fin_two.mpr ⟨h0, h1⟩
      rw [if_neg h0, if_neg h1, if_pos hn]; ring
  have hsum3 : ∑ᶠ v, lw v * E v =
      ((∑ᶠ (v) (_ : PlOver (g 0) v), lw v * E v) + ∑ᶠ (v) (_ : PlOver (g 1) v), lw v * E v) +
      ∑ᶠ (v) (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v := by
    rw [finsum_congr hsplit, finsum_add_distrib, finsum_add_distrib]
    all_goals first
      | exact hsub _
      | exact ((hsub _).union (hsub _)).subset (Function.support_add _ _)
  have hO : |∑ᶠ (v) (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v| ≤ Eels := by
    refine le_trans ?_ hEels
    have hs1 : (Function.support fun v => ∑ᶠ (_ : ∀ i, ¬ PlOver (g i) v), lw v * E v) ⊆
        hsupp.toFinset := by
      intro v hv
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      rw [Function.mem_support] at hv
      intro h; apply hv; rw [h]; simp
    have hs2 : (Function.support fun v => ∑ᶠ (_ : ∀ i, ¬ PlOver (g i) v), lw v * |E v|) ⊆
        hsupp.toFinset := by
      intro v hv
      rw [Set.Finite.coe_toFinset, Function.mem_support]
      rw [Function.mem_support] at hv
      intro h; apply hv
      have hl := lw_pos v
      have hE0 : E v = 0 := by
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hl.ne'
        · exact h'
      rw [hE0]; simp
    rw [finsum_eq_sum_of_support_subset _ hs1, finsum_eq_sum_of_support_subset _ hs2]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun v _ => ?_))
    have hl := lw_pos v
    by_cases hq : ∀ i, ¬ PlOver (g i) v
    · simp only [finsum_eq_if, if_pos hq, abs_mul, abs_of_pos hl, le_refl]
    · simp only [finsum_eq_if, if_neg hq, abs_zero, le_refl]
  have hAB : |(∑ ρ, if ρ ∈ TT then 0 else w ρ) + ∑ ρ, (δν ρ - δpm ρ)| ≤
      (∑ ρ, if ρ ∈ TT then 0 else |w ρ|) + ∑ ρ, (|δν ρ| + |δpm ρ|) := by
    have h1 : |∑ ρ, (if ρ ∈ TT then 0 else w ρ)| ≤ ∑ ρ, (if ρ ∈ TT then 0 else |w ρ|) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum (fun ρ _ => by split_ifs <;> simp))
    have h2 : |∑ ρ, (δν ρ - δpm ρ)| ≤ ∑ ρ, (|δν ρ| + |δpm ρ|) :=
      le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun ρ _ => by
        rw [abs_le]; constructor <;> linarith [le_abs_self (δν ρ), neg_abs_le (δν ρ),
          le_abs_self (δpm ρ), neg_abs_le (δpm ρ)]))
    rw [abs_le] at h1 h2 ⊢; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hL0 : 0 ≤ Real.log (g 0 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 0).ne')
  have hL1 : 0 ≤ Real.log (g 1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (hg 1).ne')
  have hlog : Real.log ((g 0 : ℝ) * (g 1 : ℝ)) = Real.log (g 0 : ℝ) + Real.log (g 1 : ℝ) :=
    Real.log_mul (Nat.cast_ne_zero.mpr (hg 0).ne') (Nat.cast_ne_zero.mpr (hg 1).ne')
  have hLg0 : 0 ≤ Real.log ((g 0 : ℝ) * (g 1 : ℝ)) := by rw [hlog]; linarith
  have hXl : |((∑ ρ, if ρ ∈ TT then 0 else w ρ) + ∑ ρ, (δν ρ - δpm ρ)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ))| ≤
      ((∑ ρ, if ρ ∈ TT then 0 else |w ρ|) + ∑ ρ, (|δν ρ| + |δpm ρ|)) * Real.log ((g 0 : ℝ) * (g 1 : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hLg0]; exact mul_le_mul_of_nonneg_right hAB hLg0
  have hA0 := hA 0
  have hA1 := hA 1
  rw [hdeg] at hA0 hA1
  rw [hsum3]
  rw [hlog] at hXl ⊢
  rw [abs_le] at hA0 hA1 hO hXl ⊢
  constructor <;> linarith [hA0.1, hA0.2, hA1.1, hA1.2, hO.1, hO.2, hXl.1, hXl.2]
end Formalism.DivisionValues
