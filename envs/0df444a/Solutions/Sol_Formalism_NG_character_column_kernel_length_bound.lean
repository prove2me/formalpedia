-- Prove2me | solution 1 for Formalism.NG.character_column_kernel_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:44.190794+00:00
-- url     : https://prove2.me/submissions/29892b38-7f3b-4d48-83f2-00b68416b4e0

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelLengthBound
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ProdEraseZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelLengthBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.NG
private lemma padicValInt_eq_emultiplicity (l : ℕ) [hl : Fact l.Prime] {z : ℤ} (hz : z ≠ 0) :
    (padicValInt l z : ℕ∞) = emultiplicity (l : ℤ) z := by
  have hz' : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  rw [show padicValInt l z = padicValNat l z.natAbs from rfl, padicValNat_eq_emultiplicity hz',
    ← Int.natCast_emultiplicity, Int.natCast_natAbs]
  rcases abs_choice z with h | h
  · rw [h]
  · rw [h, emultiplicity_neg]
private lemma padicValInt_pow_sub_one_eq_add (l : ℕ) [hl : Fact l.Prime] (s₀ : ℕ) (hs : 1 ≤ s₀) (hs2 : l = 2 → 2 ≤ s₀)
    (x : ℤ) (hx1 : (l : ℤ) ^ s₀ ∣ x - 1) (hx2 : ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1)
    (n : ℕ) (hn0 : n ≠ 0) :
    x ^ n - 1 ≠ 0 ∧ padicValInt l (x ^ n - 1) = s₀ + padicValNat l n := by
  have hlp := hl.out
  have hE1 : emultiplicity (l : ℤ) (x - 1) = s₀ := emultiplicity_eq_coe.mpr ⟨hx1, hx2⟩
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x := by
    intro h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h hdvd; simpa using this
    exact (Nat.prime_iff_prime_int.mp hlp).not_dvd_one h1
  have hE : emultiplicity (l : ℤ) (x ^ n - 1) = (s₀ : ℕ∞) + emultiplicity l n := by
    rcases hlp.eq_two_or_odd' with h2 | hodd
    · subst h2
      have h4 : (4 : ℤ) ∣ x - 1 := by
        have := (pow_dvd_pow ((2 : ℕ) : ℤ) (hs2 rfl)).trans hx1
        norm_num at this
        exact this
      push_cast at hlx hE1 ⊢
      have := Int.two_pow_sub_pow' n h4 hlx
      rw [one_pow] at this
      have hc := Int.natCast_emultiplicity 2 n
      push_cast at hc
      rw [this, hE1, hc]
    · have := Int.emultiplicity_pow_sub_pow hlp hodd (y := 1) hdvd hlx n
      rw [one_pow] at this
      rw [this, hE1]
  have hfin : emultiplicity (l : ℤ) (x ^ n - 1) = ((s₀ + padicValNat l n : ℕ) : ℕ∞) := by
    rw [hE, ← padicValNat_eq_emultiplicity hn0]
    norm_cast
  have hne : x ^ n - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hfin
    exact ENat.top_ne_coe _ hfin
  refine ⟨hne, ?_⟩
  have := padicValInt_eq_emultiplicity l hne
  rw [hfin] at this
  exact_mod_cast this
end Formalism.NG
end

set_option autoImplicit false
open Finset
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : characterColumnKernelLengthBound := by
  intro l hl s₀ hs hs2 x hx1 hx2 a b hab
  have hlp := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨hne, hv⟩ := padicValInt_pow_sub_one_eq_add l s₀ hs hs2 x hx1 hx2 (b - a) (by omega)
  have hdvd : (l : ℤ) ∣ x - 1 := (dvd_pow_self (l : ℤ) (by omega)).trans hx1
  have hlx : ¬ (l : ℤ) ∣ x ^ a := by
    intro h
    have h' : (l : ℤ) ∣ x := hlp.dvd_of_dvd_pow h
    have h1 : (l : ℤ) ∣ 1 := by have := dvd_sub h' hdvd; simpa using this
    exact hlp.not_dvd_one h1
  have hxa : x ^ a ≠ 0 := fun h ↦ hlx (h ▸ dvd_zero _)
  have e : x ^ b - x ^ a = x ^ a * (x ^ (b - a) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_of_le hab.le, mul_one]
  rw [e, padicValInt.mul hxa hne, padicValInt.eq_zero_of_not_dvd hlx, zero_add, hv]
end Formalism.NG
