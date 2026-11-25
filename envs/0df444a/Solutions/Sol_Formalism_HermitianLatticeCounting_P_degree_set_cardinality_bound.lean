-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.degree_set_cardinality_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:58:22.777404+00:00
-- url     : https://prove2.me/submissions/f315bf84-c441-47e0-969d-f4c798690724

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalDS
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CircleIntegralInvSubEqZeroOfOutside
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_degree_increment_bound
import Theorems.Thm_Formalism_QuantumDeterminants_fdegPos
import Theorems.Thm_Formalism_QuantumDeterminants_fdegRatio


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.DegSetBound := by
  intro n μ I hμ hint hgap
  classical
  have hanti : ∀ J : Finset (Fin n), StrictAnti (fun a => μ a + if a ∈ J then (1 : ℝ) else 0) := by
    intro J a b hab
    have := hgap a b hab
    show μ b + (if b ∈ J then (1 : ℝ) else 0) < μ a + if a ∈ J then (1 : ℝ) else 0
    split_ifs <;> linarith
  have hintJ : ∀ J : Finset (Fin n), ∀ a b, ∃ m : ℤ,
      (μ a + if a ∈ J then (1 : ℝ) else 0) - (μ b + if b ∈ J then (1 : ℝ) else 0) = (m : ℝ) := by
    intro J a b
    obtain ⟨m, hm⟩ := hint a b
    by_cases ha : a ∈ J <;> by_cases hb : b ∈ J
    · exact ⟨m, by simp only [ha, hb, if_true]; linarith⟩
    · exact ⟨m + 1, by simp only [ha, hb, if_true, if_false]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [ha, hb, if_true, if_false]; push_cast; linarith⟩
    · exact ⟨m, by simp only [ha, hb, if_false]; linarith⟩
  have fμ := Formalism.QuantumDeterminants.fdegPos n μ hμ.injective
  induction I using Finset.induction_on with
  | empty =>
    have : (fun a => μ a + if a ∈ (∅ : Finset (Fin n)) then (1 : ℝ) else 0) = μ := by
      funext a; simp
    rw [this, div_self fμ.ne']
    simp
  | insert s J hs ih =>
    have hstep : (fun a => μ a + if a ∈ insert s J then (1 : ℝ) else 0) =
        (fun a => μ a + if a ∈ J then (1 : ℝ) else 0) + Pi.single s 1 := by
      funext a
      by_cases ha : a = s
      · subst ha; simp [hs]
      · simp [ha]
    set ν : Fin n → ℝ := fun a => μ a + if a ∈ J then (1 : ℝ) else 0 with hν
    have fν := Formalism.QuantumDeterminants.fdegPos n ν (hanti J).injective
    have hinj' : Function.Injective (ν + Pi.single s 1) := by
      rw [← hstep]; exact (hanti _).injective
    have hr := Formalism.QuantumDeterminants.fdegRatio n ν s (hanti J).injective (hintJ J) hinj'
    have hb := (degree_increment_bound n ν s (hanti J).injective (hintJ J)).1 hinj'
    rw [← hr] at hb
    rw [hstep, Finset.card_insert_of_notMem hs]
    have hn : (0 : ℝ) < n := by
      have : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) s.2
      exact_mod_cast this
    have hprod : Formalism.QuantumDeterminants.fdegHC (ν + Pi.single s 1) / Formalism.QuantumDeterminants.fdegHC μ =
        (Formalism.QuantumDeterminants.fdegHC (ν + Pi.single s 1) / Formalism.QuantumDeterminants.fdegHC ν) * (Formalism.QuantumDeterminants.fdegHC ν / Formalism.QuantumDeterminants.fdegHC μ) := by
      field_simp
    rw [hprod]
    have hq0 : 0 ≤ Formalism.QuantumDeterminants.fdegHC ν / Formalism.QuantumDeterminants.fdegHC μ := (div_pos fν fμ).le
    constructor
    · rw [pow_succ, mul_inv, mul_comm]
      rw [one_div] at hb
      exact mul_le_mul hb.1 ih.1 (by positivity) (le_trans (by positivity) hb.1)
    · rw [pow_succ, mul_comm ((n : ℝ) ^ J.card)]
      exact mul_le_mul hb.2 ih.2 hq0 hn.le
end Formalism.HermitianLatticeCounting.P
