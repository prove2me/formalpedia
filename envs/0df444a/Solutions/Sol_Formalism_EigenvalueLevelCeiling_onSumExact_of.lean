-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.onSumExact_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:14.971881+00:00
-- url     : https://prove2.me/submissions/94aba287-d779-457c-9182-7b82ff848dba

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_ErrSumGoodExact
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsComposeGeneral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverP
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PrimeLogOverPSqTail
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_AbsorbLocalConditionsOfExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGoodExact) : OnSumExact := by
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD errl herr
  have hG : ∀ p : ℕ, 0 ≤ errGood Y X2 A1 A2 kw T th add p := by
    intro p
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    unfold errGood
    split_ifs <;>
      linarith [div_nonneg hA1 hp, mul_nonneg hkw (hth p), mul_nonneg hT (hadd p),
        div_nonneg hA2 (pow_nonneg hp 2)]
  have hX : ∀ p : ℕ, 0 ≤ (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) := by
    intro p
    split_ifs
    · exact heb p
    · exact hG p
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) *
        (if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w))) := by
    apply Finset.sum_le_sum
    intro w hw
    have hl : 0 ≤ lw w := by
      unfold lw
      exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have hr : (0 : ℝ) ≤ (ramw w : ℝ) :=
      by exact_mod_cast (le_trans zero_le_one (hR K w).2.1)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (herr w hw) hr) hl
  have step2 := hP K S (fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) hX
  have hprime : ∀ p ∈ S.image plc, p.Prime := by
    intro p hp
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hR K w).1
  have hbadpart : ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    have hsub : (S.image plc).filter (fun p => p ∈ Bad) ⊆ Bad := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) * eb p) hsub
      (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
    rwa [Finset.sum_filter] at h
  have hgoodpart : ∑ p ∈ S.image plc,
      (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y) := by
    have h := hE ((S.image plc).filter (fun p => p ∉ Bad))
      (fun p hp => hprime p (Finset.mem_filter.mp hp).1) Y X2 A1 A2 kw T Cth Cadd th add
      hY hX2 hA1 hA2 hkw hT hth hadd hD
    rwa [Finset.sum_filter] at h
  have hsplit : ∑ p ∈ S.image plc, Real.log (p : ℝ) *
        (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) =
      ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) +
      ∑ p ∈ S.image plc,
        (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p ∈ Bad <;> simp [h]
  linarith
end Formalism.EigenvalueLevelCeiling
