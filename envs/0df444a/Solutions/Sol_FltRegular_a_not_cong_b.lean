-- Prove2me | solution 1 for FltRegular.a_not_cong_b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:39.166727+00:00
-- url     : https://prove2.me/submissions/6e75a3b8-0410-470d-aca7-3ace2787bab6

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Definitions.Def_FltRegular_MayAssume_Lemmas
public import Theorems.Thm_FltRegular_p_dvd_c_of_ab_of_anegc

set_option autoImplicit false
@[expose] public section
public section
open Int Finset
open FltRegular
namespace FltRegular
theorem _root_.solution {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p)
    (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧
        ¬↑p ∣ x * y * z := by
  by_cases hab : a ≡ b [ZMOD p]
  swap
  · exact ⟨a, b, c, ⟨h, hgcd, hab, hprod, caseI⟩⟩
  refine ⟨a, -c, -b, ⟨?_, ?_, fun habs ↦ ?_, ?_, ?_⟩⟩
  · have hodd : Odd p := hpri.odd_of_ne_two (by lia)
    rw [hodd.neg_pow, hodd.neg_pow]
    linarith
  · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
      ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm]
  · have hp3 : p ≠ 3 := by lia
    rw [← ZMod.intCast_eq_intCast_iff] at habs hab
    rw [hab] at habs
    rw [ZMod.intCast_eq_intCast_iff] at habs hab
    obtain ⟨n, hn⟩ := p_dvd_c_of_ab_of_anegc hpri hp3 h hab habs
    refine caseI ⟨a * b * n, ?_⟩
    rw [hn]
    ring
  · convert hprod using 1
    ring
  · grind
end FltRegular
