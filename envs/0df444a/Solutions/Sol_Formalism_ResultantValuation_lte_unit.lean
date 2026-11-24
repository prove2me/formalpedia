-- Prove2me | solution 1 for Formalism.ResultantValuation.lte_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:17.986434+00:00
-- url     : https://prove2.me/submissions/1293d46a-27ee-4c08-adfb-659db3fe3ff2

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_WindowValuation
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
import Theorems.Thm_Formalism_ResultantValuation_emultiplicity_eq_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.ResultantValuation
section Padic
variable {l : ℕ} [Fact l.Prime]
private theorem pow_dvd_iff_le_valuation_lemma {x : ℤ_[l]} (hx : x ≠ 0) (n : ℕ) :
    (l : ℤ_[l]) ^ n ∣ x ↔ n ≤ x.valuation := by
  simpa [Ideal.mem_span_singleton] using PadicInt.mem_span_pow_iff_le_valuation x hx n
private theorem not_dvd_one'_lemma_2 : ¬ (l : ℤ_[l]) ∣ 1 := by
  intro h
  have h1 := (pow_dvd_iff_le_valuation_lemma (one_ne_zero : (1 : ℤ_[l]) ≠ 0) 1).1 (by rwa [pow_one])
  rw [PadicInt.valuation_one] at h1
  omega
private theorem prime_l_lemma_3 : Prime (l : ℤ_[l]) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  · intro h
    exact not_dvd_one'_lemma_2 (isUnit_iff_dvd_one.mp h)
  · intro a b hab
    by_cases ha : a = 0
    · left; rw [ha]; exact dvd_zero _
    by_cases hb : b = 0
    · right; rw [hb]; exact dvd_zero _
    have h1 := (pow_dvd_iff_le_valuation_lemma (mul_ne_zero ha hb) 1).1 (by rwa [pow_one])
    rw [PadicInt.valuation_mul ha hb] at h1
    rcases Nat.eq_zero_or_pos a.valuation with h0 | h0
    · right
      have h2 := (pow_dvd_iff_le_valuation_lemma hb 1).2 (by omega)
      rwa [pow_one] at h2
    · left
      have h2 := (pow_dvd_iff_le_valuation_lemma ha 1).2 (by omega)
      rwa [pow_one] at h2
end Padic
end Formalism.ResultantValuation
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.ResultantValuation
namespace Formalism.ResultantValuation
theorem _root_.solution (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    (i : ℕ) (hi : 1 ≤ i) : ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i := by
  classical
  have hp : l.Prime := Fact.out
  have hprime := prime_l_lemma_3 (l := l)
  have hu0 : u - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hu
    omega
  have hdvd : (l : ℤ_[l]) ∣ u - 1 := by
    have h1 := (pow_dvd_iff_le_valuation_lemma hu0 1).2 (by omega)
    rwa [pow_one] at h1
  have hndvd : ¬ (l : ℤ_[l]) ∣ u := by
    intro h
    apply not_dvd_one'_lemma_2 (l := l)
    have h1 := dvd_sub h hdvd
    rwa [sub_sub_cancel] at h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  have hv : padicValNat l (l ^ a * m) = a := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime (hp.odd_of_ne_two hl2) hdvd hndvd a
  rw [one_pow] at h1
  have hdvd2 : (l : ℤ_[l]) ∣ u ^ l ^ a - 1 := by
    refine hdvd.trans ?_
    simpa using sub_dvd_pow_sub_pow u 1 (l ^ a)
  have hndvd2 : ¬ (l : ℤ_[l]) ∣ u ^ l ^ a := fun h => hndvd (hprime.dvd_of_dvd_pow h)
  have hm' : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
    intro h
    have hc : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hst' : (s : ℤ_[l]) * (m : ℤ_[l]) + (t : ℤ_[l]) * (l : ℤ_[l]) = 1 := by
      have h3 := congrArg (Int.cast : ℤ → ℤ_[l]) hst
      push_cast at h3
      exact h3
    apply not_dvd_one'_lemma_2 (l := l)
    rw [← hst']
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)
  have h2 := emultiplicity_pow_sub_pow_of_prime hprime hdvd2 hndvd2 hm'
  rw [one_pow, ← pow_mul] at h2
  have hE : emultiplicity (l : ℤ_[l]) (u ^ (l ^ a * m) - 1) = ((1 + a : ℕ) : ℕ∞) := by
    rw [h2, h1, emultiplicity_eq_valuation hu0, hu]
    norm_cast
  have hne : u ^ (l ^ a * m) - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hE
    exact (ENat.natCast_ne_top (1 + a)) hE.symm
  rw [hv]
  exact_mod_cast (emultiplicity_eq_valuation hne).symm.trans hE
end Formalism.ResultantValuation
