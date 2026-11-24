-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.int_localisation_in_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:49.392157+00:00
-- url     : https://prove2.me/submissions/58733df6-b8ab-4d45-b0b6-36695a210ec8

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_units_of_local_holds
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_isUnit_int_of_not_dvd
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_injective_of_prime_to_units
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_isLocalHom_of_prime_to_units
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : ZLocInO := by
  intro O _ _ _ _ l hl hlO
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.1 hl)
  let R := Localization.AtPrime (Ideal.span {(l : ℤ)})
  have hinj : Function.Injective (algebraMap ℤ R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(l : ℤ)}))
  have hc0 : CharZero R := charZero_of_injective_algebraMap hinj
  have hmem : ∀ t : ℤ, t ∈ (Ideal.span {(l : ℤ)}).primeCompl ↔ ¬ (l : ℤ) ∣ t := by
    intro t
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]
  have hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R) := by
    intro m hm
    have h1 : (m : ℤ) ∈ (Ideal.span {(l : ℤ)}).primeCompl :=
      (hmem _).2 (by exact_mod_cast hm)
    have h2 := IsLocalization.map_units R (⟨(m : ℤ), h1⟩ : (Ideal.span {(l : ℤ)}).primeCompl)
    simpa using h2
  have hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z := by
    intro a
    obtain ⟨⟨z, t⟩, h1⟩ := IsLocalization.surj (Ideal.span {(l : ℤ)}).primeCompl a
    have ht := (hmem _).1 t.2
    simp only [eq_intCast] at h1
    refine ⟨(t : ℤ).natAbs, fun h => ht (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq (t : ℤ) with h | h
    · refine ⟨z, ?_⟩
      rw [← h1, mul_comm]
      congr 1
      rw [← Int.cast_natCast, ← h]
    · refine ⟨-z, ?_⟩
      have h2 : (((t : ℤ).natAbs : ℤ) : R) = -((t : ℤ) : R) := by
        rw [← Int.cast_neg]
        congr 1
        omega
      have h3 : (((t : ℤ).natAbs : ℕ) : R) = -((t : ℤ) : R) := by
        rw [← Int.cast_natCast]
        exact h2
      rw [h3, Int.cast_neg, ← h1]
      ring
  have hdvr : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hl0) R
  have huO := units_of_local_holds O l hl hlO
  have hg : ∀ y : (Ideal.span {(l : ℤ)}).primeCompl, IsUnit (Int.castRingHom O y) := by
    intro y
    rw [eq_intCast]
    exact isUnit_int_of_not_dvd O l huO _ ((hmem _).1 y.2)
  let φ : R →+* O := IsLocalization.lift hg
  exact ⟨R, inferInstance, inferInstance, hdvr, hc0, φ.toAlgebra,
    isLocalHom_of_prime_to_units R O φ l hlO hu hd, injective_of_prime_to_units R O φ l hu hd, hu, hd⟩
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
