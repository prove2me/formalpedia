-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostConductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:52:03.559027+00:00
-- url     : https://prove2.me/submissions/83b49ffb-33f7-421c-8e00-9bdf8cacbf22

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_dvd_of_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_layer_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_two_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Cond
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostConductor := by
  unfold HostConductor
  intro e q d hH L _ _ ζ a b h m hm
  have hq : q.Prime := hH.1
  have hd : d.Prime := hH.2.1
  have hq8 : q % 8 = 3 := hH.2.2.1
  have hd16 : d % 16 = 7 := hH.2.2.2.1
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero m := ⟨hm.ne'⟩
  have hq4 : q % 4 = 3 := by omega
  have hd4 : d % 4 = 3 := by omega
  have hqd : q ≠ d := by omega
  have hE0 : E0 a b ≤ hostE ζ a b := by
    unfold hostE
    exact le_sup_left
  have haE : a ∈ hostE ζ a b := by
    apply hE0
    unfold E0
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  have hbE : b ∈ hostE ζ a b := by
    apply hE0
    unfold E0
    exact IntermediateField.subset_adjoin ℚ _ (by simp)
  have hcop : Nat.Coprime q d := (Nat.coprime_primes hq hd).mpr hqd
  constructor
  · rintro ⟨φ⟩
    have hsq : ∀ (x : hostE ζ a b) (c : ℕ), (x : L) ^ 2 = -(c : L) →
        (φ x) ^ 2 = -(c : CyclotomicField m ℚ) := by
      intro x c hx
      have hx' : x ^ 2 = -(c : hostE ζ a b) := Subtype.ext (by simpa using hx)
      rw [← map_pow, hx', map_neg, map_natCast]
    have hqm : q ∣ m := dvd_of_sq hq4 (φ ⟨a, haE⟩) (hsq ⟨a, haE⟩ q h.2.1)
    have hdm : d ∣ m := dvd_of_sq hd4 (φ ⟨b, hbE⟩) (hsq ⟨b, hbE⟩ d h.2.2.1)
    have hqdm : q * d ∣ m := hcop.mul_dvd_of_dvd_of_dvd hqm hdm
    by_cases he : e = 0
    · rw [if_pos he]
      exact hqdm
    · rw [if_neg he, mul_assoc]
      have h2m : 2 ^ (e + 2) ∣ m := two_dvd hH he h φ
      have h2q : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).mpr (by omega)
      have h2d : Nat.Coprime 2 d := (Nat.coprime_primes Nat.prime_two hd).mpr (by omega)
      exact (Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h2q h2d)).mul_dvd_of_dvd_of_dvd h2m hqdm
  · intro hdiv
    by_cases he : e = 0
    · subst he
      rw [if_pos rfl] at hdiv
      exact emb_zero hq4 hd4 h (dvd_trans (dvd_mul_right q d) hdiv)
        (dvd_trans (dvd_mul_left d q) hdiv)
    · rw [if_neg he] at hdiv
      obtain ⟨f⟩ := layer_emb hq4 hd4 h
        (dvd_trans (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) hdiv)
        (dvd_trans (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) hdiv)
        (dvd_trans (dvd_mul_left _ _) hdiv)
      exact ⟨f.comp (hostE ζ a b).val⟩
end Formalism.FrobeniusOrbits
