-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.lemma_a_integral_of_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:36:54.707+00:00
-- url     : https://prove2.me/submissions/6d492de2-a4bf-44f3-8903-867777170063

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_incl_z_iff_incl_r
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
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution : LemmaAZOfR := by
  intro hR r n hn ν hν l hl
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hP : (Ideal.span {(l : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.1 hl)
  let R := Localization.AtPrime (Ideal.span {(l : ℤ)})
  have hinj : Function.Injective (algebraMap ℤ R) :=
    IsLocalization.injective R (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {(l : ℤ)}))
  have : CharZero R := charZero_of_injective_algebraMap hinj
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
  exact (incl_z_iff_incl_r R l hl hu hd r n hn ν _).2 (hR R r n hn ν hν l hl hu)
end Formalism.CohomologicalDescent.LA
