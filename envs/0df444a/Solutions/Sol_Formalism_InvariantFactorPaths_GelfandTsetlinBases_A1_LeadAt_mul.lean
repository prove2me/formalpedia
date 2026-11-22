-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:31:35.28589+00:00
-- url     : https://prove2.me/submissions/8cde6c01-b650-4283-9571-c9ef755cb6c7

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A1
section Top
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
private theorem weight_eq_of_le_of_add_eq_lemma {w : σ → M} {γ δ : M} {a b : σ →₀ ℕ}
    (ha : Finsupp.weight w a ≤ γ) (hb : Finsupp.weight w b ≤ δ) (h : Finsupp.weight w (a + b) = γ + δ) :
    Finsupp.weight w a = γ ∧ Finsupp.weight w b = δ := by
  rw [map_add] at h
  have h1 : Finsupp.weight w a = γ := by
    by_contra hne
    have := add_lt_add_of_lt_of_le (lt_of_le_of_ne ha hne) hb
    rw [h] at this
    exact lt_irrefl _ this
  refine ⟨h1, ?_⟩
  rw [h1] at h
  exact le_antisymm (le_of_add_le_add_left h.le) (le_of_add_le_add_left h.ge)
end Top
section Col
variable {R M : Type*} [CommRing R] [AddCommMonoid M] {n : ℕ}
end Col
end A1
namespace A1
end A1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace LeadAt
theorem _root_.solution {w : σ → M} {γ δ : M} {f g tf tg : MvPolynomial σ R}
    (hf : LeadAt w γ f tf) (hg : LeadAt w δ g tg) : LeadAt w (γ + δ) (f * g) (tf * tg) := by
  classical
  obtain ⟨hf1, rfl⟩ := hf
  obtain ⟨hg1, rfl⟩ := hg
  refine ⟨fun e he => ?_, ?_⟩
  · rw [mem_support_iff, coeff_mul] at he
    obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
    have hp' : p.1 + p.2 = e := by
      first
      | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      | exact Finset.mem_antidiagonal.mp hp
      | simpa using hp
    rw [← hp', map_add]
    exact add_le_add (hf1 _ (mem_support_iff.mpr (left_ne_zero_of_mul hne)))
      (hg1 _ (mem_support_iff.mpr (right_ne_zero_of_mul hne)))
  · ext e
    have h1 : IsWeightedHomogeneous w (weightedHomogeneousComponent w γ f) γ := by
      apply weightedHomogeneousComponent_isWeightedHomogeneous
    have h2 : IsWeightedHomogeneous w (weightedHomogeneousComponent w δ g) δ := by
      apply weightedHomogeneousComponent_isWeightedHomogeneous
    have hom := h1.mul h2
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with he
    · rw [coeff_mul, coeff_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p.1 + p.2 = e := by
        first
        | exact Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        | exact Finset.mem_antidiagonal.mp hp
        | simpa using hp
      rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
      by_cases hab : coeff p.1 f ≠ 0 ∧ coeff p.2 g ≠ 0
      · obtain ⟨ha1, ha2⟩ := _root_.Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.weight_eq_of_le_of_add_eq_lemma (hf1 _ (mem_support_iff.mpr hab.1))
          (hg1 _ (mem_support_iff.mpr hab.2)) (by rw [hp']; exact he)
        rw [if_pos ha1, if_pos ha2]
      · have h0 : coeff p.1 f * coeff p.2 g = 0 := by
          rcases not_and_or.mp hab with h | h
          · rw [not_not.mp h, zero_mul]
          · rw [not_not.mp h, mul_zero]
        rw [h0]
        split_ifs <;> simp [h0]
    · by_contra hne
      exact he (hom (Ne.symm hne))
end LeadAt
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
