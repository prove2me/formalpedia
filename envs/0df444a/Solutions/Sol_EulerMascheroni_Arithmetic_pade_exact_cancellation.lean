-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.pade_exact_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:11:04.962906+00:00
-- url     : https://prove2.me/submissions/c58aab99-c6ba-4cb4-83dd-2ac546122712

import Definitions.Def_eulerMascheroni_padeTransform
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_determinant_and_nonvanishing
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_denominator_modular_structure
set_option autoImplicit false
open EulerMascheroni.Arithmetic
namespace PadeGcd
lemma q_adjacent_coprime (n : ℕ) : IsCoprime (padeQ n) (padeQ (n+1)) :=
  (pade_denominator_modular_structure n).2.1
lemma q_periodic_mod (m : ℕ) (hm : 0 < m) (n : ℕ) :
    (padeQ (n+m) : ZMod m) = (padeQ n : ZMod m) :=
  (pade_denominator_modular_structure n).2.2 m hm
lemma gcd_exact (n : ℕ) :
    Int.gcd (padeP (n+1)) (padeQ (n+1)) =
      Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2) := by
  have hd := (pade_determinant_and_nonvanishing padeP padeQ (by norm_num [padeP,padeQ,padeSeq])
    (fun n => rfl) (fun n => rfl) n).1
  have hc := q_adjacent_coprime n
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · exact Int.gcd_dvd_right _ _
    · rw [← hd]
      exact dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) _)
        (dvd_mul_of_dvd_left (Int.gcd_dvd_right _ _) _)
  · apply Int.dvd_gcd
    · have hprod : (Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2):ℤ) ∣ padeQ n * padeP (n+1) := by
        rw [← hd] at *
        have h1 := Int.gcd_dvd_right (padeQ (n+1)) (padeQ n*padeP (n+1)-padeQ (n+1)*padeP n)
        have h2 := dvd_mul_of_dvd_left (Int.gcd_dvd_left (padeQ (n+1))
          (padeQ n*padeP (n+1)-padeQ (n+1)*padeP n)) (padeP n)
        have hh := dvd_add h1 h2
        simpa using hh
      obtain ⟨a,b,hab⟩ := hc
      have he : padeP (n+1) = a*(padeQ n*padeP (n+1)) + b*(padeQ (n+1)*padeP (n+1)) := by
        linear_combination -padeP (n+1)*hab
      rw [he]
      exact dvd_add (dvd_mul_of_dvd_right hprod _) (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_left (Int.gcd_dvd_left _ _) _) _)
    · exact Int.gcd_dvd_left _ _
lemma cancellation_modular_criterion (n d : ℕ) (hd : 0 < d) :
    d ∣ Int.gcd (padeP (n+1)) (padeQ (n+1)) ↔
      (d:ℤ) ∣ (n.factorial:ℤ)^2 ∧ (padeQ ((n+1)%d) : ZMod d) = 0 := by
  rw [gcd_exact]
  have hp : Function.Periodic (fun k : ℕ => (padeQ k : ZMod d)) d := q_periodic_mod d hd
  rw [hp.map_mod_nat (n+1), ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h
    have hc : (d:ℤ) ∣ (Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2):ℤ) := by exact_mod_cast h
    exact ⟨hc.trans (Int.gcd_dvd_right _ _), hc.trans (Int.gcd_dvd_left _ _)⟩
  · rintro ⟨h1,h2⟩
    exact Int.dvd_gcd h2 h1
end PadeGcd


theorem solution (n : ℕ) :
    Int.gcd (padeP (n+1)) (padeQ (n+1)) = Int.gcd (padeQ (n+1)) ((n.factorial:ℤ)^2) ∧
    ∀ d : ℕ, 0 < d →
      (d ∣ Int.gcd (padeP (n+1)) (padeQ (n+1)) ↔
        (d:ℤ) ∣ (n.factorial:ℤ)^2 ∧ (padeQ ((n+1)%d) : ZMod d) = 0) := by
  exact ⟨PadeGcd.gcd_exact n, fun d hd => PadeGcd.cancellation_modular_criterion n d hd⟩
#print axioms solution
