-- Prove2me | solution 1 for Formalism.Q3.hostFrob_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:24.513735+00:00
-- url     : https://prove2.me/submissions/9d39d346-7627-47f8-96fc-859214fdb289

import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostFrob

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3
namespace Formalism.Q3
theorem _root_.solution (hF : MQFrob) (hK : KroneckerMeaning) (q : Fin 3 → ℕ) (hq : Hyp3 q)
    (E : Type) [Field E] [NumberField E] (α : Fin 3 → E) (hα : IsHost q α)
    (p : ℕ) [Fact p.Prime] (hpq : ∀ i, p ≠ q i)
    (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : Gal(E/ℚ))
    (H : IsArithFrobAt ℤ σ P) (i : Fin 3) :
    ((galSign α σ i : ℤˣ) : ℤ) = chiQ (q i) p := by
  have hp : p.Prime := Fact.out
  obtain ⟨hqi, hq4⟩ := hq.1 i
  have hne : ∀ j, (-(q j : ℤ)) ≠ 0 := fun j => by
    have := (hq.1 j).1.pos
    omega
  have h := hF 3 E (fun j => -(q j : ℤ)) α hα hne p P σ H i
  by_cases h2 : p = 2
  · subst h2
    have hmod4 : (-(q i : ℤ)) % 4 = 1 := by omega
    have h8 := h.2 rfl hmod4
    have hchi := (hK (q i) hqi hq4).2.1
    have hcop : Int.gcd 2 (q i : ℤ) = 1 := by
      have hodd : Odd (q i) := Nat.odd_iff.mpr (by omega)
      have : Int.gcd ((2 : ℕ) : ℤ) (q i : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact Nat.coprime_two_left.mpr hodd
      exact_mod_cast this
    have hpm : chiQ (q i) 2 = 1 ∨ chiQ (q i) 2 = -1 := by
      unfold chiQ
      exact jacobiSym.eq_one_or_neg_one hcop
    have hc2 : ((2 : ℕ) : ℤ) = 2 := by norm_num
    rw [hc2]
    rcases Int.units_eq_one_or (galSign α σ i) with hs | hs
    · have h7 : q i % 8 = 7 := by
        have := h8.mp hs
        omega
      rw [hs, hchi.mpr h7]
      rfl
    · have h7 : ¬ q i % 8 = 7 := by
        intro h7
        have : galSign α σ i = 1 := h8.mpr (by omega)
        rw [hs] at this
        exact absurd this (by decide)
      have hc : chiQ (q i) 2 = -1 := by
        rcases hpm with hpm | hpm
        · exact absurd (hchi.mp hpm) h7
        · exact hpm
      rw [hs, hc]
      rfl
  · have hnd : ¬ (p : ℤ) ∣ 2 * -(q i : ℤ) := by
      intro hd
      have hd' : p ∣ 2 * q i := by
        have : (p : ℤ) ∣ ((2 * q i : ℕ) : ℤ) := by
          push_cast
          rw [← dvd_neg]
          simpa [mul_neg] using hd
        exact_mod_cast this
      rcases (Nat.Prime.dvd_mul hp).mp hd' with h' | h'
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
      · exact hpq i ((Nat.prime_dvd_prime_iff_eq hp hqi).mp h')
    rw [h.1 hnd]
    exact ((hK (q i) hqi hq4).1 p hp h2 (hpq i)).symm
end Formalism.Q3
