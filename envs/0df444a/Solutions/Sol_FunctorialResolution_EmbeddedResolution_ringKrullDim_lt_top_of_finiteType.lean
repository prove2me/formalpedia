-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.ringKrullDim_lt_top_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:55.111158+00:00
-- url     : https://prove2.me/submissions/3a07e991-ff37-400c-9ff2-f089338d7311

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_lastIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_MarkedSequenceOfBlowups_toMarkedSequence_toSequenceOfBlowups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_lastIdeal
attribute [local simp] FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.toMarkedSequence_toSequenceOfBlowups


section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem natCast_withBot_ne_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
  intro hcontra
  have h2 : ((n : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
    rw [WithBot.coe_natCast]
    exact hcontra
  have h3 : (n : ℕ∞) = ⊤ := WithBot.coe_injective h2
  simp at h3
private theorem natCast_withBot_lt_top (n : ℕ) : ((n : ℕ) : WithBot ℕ∞) < ⊤ :=
  lt_top_iff_ne_top.mpr (natCast_withBot_ne_top n)
private theorem two_ne_zero_withBotENat : (2 : WithBot ℕ∞) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ∞) : WithBot ℕ∞) = ((0 : ℕ∞) : WithBot ℕ∞) := h
  have h2 : (2 : ℕ∞) = 0 := WithBot.coe_injective h'
  simp at h2
private theorem two_mul_natCast_add_one (m : ℕ) :
    (2 : WithBot ℕ∞) * ((m : ℕ∞) : WithBot ℕ∞) + 1 = (((2 * m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have e2 : (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
  have e1 : (1 : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := rfl
  rw [e2, e1, ← WithBot.coe_mul, ← WithBot.coe_add]
  congr 1
private theorem two_mul_add_one_lt_top {a : WithBot ℕ∞} (h : a ≠ ⊤) : 2 * a + 1 < ⊤ := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.mul_bot two_ne_zero_withBotENat, WithBot.bot_add]
    exact bot_lt_top
  | coe b =>
    induction b using WithTop.recTopCoe with
    | top => exact absurd rfl h
    | coe m =>
      refine lt_of_eq_of_lt ?_ (natCast_withBot_lt_top (2 * m + 1))
      exact two_mul_natCast_add_one m
private theorem ringKrullDim_mvPolynomial_lt_top (k : Type u) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
  induction n with
  | zero =>
    have h0 : ((0 : ℕ) : WithBot ℕ∞) = 0 := Nat.cast_zero
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)),
      ringKrullDim_eq_zero_of_field k, ← h0]
    exact natCast_withBot_lt_top 0
  | succ m ih =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.finSuccEquiv k m).toRingEquiv]
    exact lt_of_le_of_lt Polynomial.ringKrullDim_le (two_mul_add_one_lt_top (ne_of_lt ih))
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (A : Type v) [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹Algebra.FiniteType k A›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective φ.toRingHom hφ) ?_
  exact ringKrullDim_mvPolynomial_lt_top k n
end FunctorialResolution.EmbeddedResolution
