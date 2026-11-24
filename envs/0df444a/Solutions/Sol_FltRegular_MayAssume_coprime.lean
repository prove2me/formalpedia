-- Prove2me | solution 1 for FltRegular.MayAssume.coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:01.452148+00:00
-- url     : https://prove2.me/submissions/10aac568-8e92-4616-ac24-3c555ea7375f

module
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.FieldTheory.Finite.Basic
public import Definitions.Def_FltRegular_MayAssume_Lemmas

set_option autoImplicit false
@[expose] public section
public section
open Int Finset
open FltRegular
open FltRegular.MayAssume
namespace FltRegular.MayAssume
theorem _root_.solution {a b c : ℤ} {n : ℕ} (H : a ^ n + b ^ n = c ^ n) (hprod : a * b * c ≠ 0) :
    letI d := ({a, b, c} : Finset ℤ).gcd id
    (a / d) ^ n + (b / d) ^ n = (c / d) ^ n ∧
      ({a / d, b / d, c / d} : Finset ℤ).gcd id = 1 ∧ a / d * (b / d) * (c / d) ≠ 0 := by
  have ha : a ≠ 0 := by grind
  let s : Finset ℤ := {a, b, c}
  set d : ℤ := s.gcd id
  have hadiv : d ∣ a := gcd_dvd (by grind)
  have hbdiv : d ∣ b := gcd_dvd (by grind)
  have hcdiv : d ∣ c := gcd_dvd (by grind)
  have hdzero : d ≠ 0 := fun hd ↦ by grind [Finset.gcd_eq_zero_iff.1 hd a (by grind)]
  have hdp : d ^ n ≠ 0 := pow_ne_zero _ hdzero
  refine ⟨?_, ?_, fun habs ↦ ?_⟩
  · rwa [← mul_left_inj' hdp, add_mul, ← mul_pow, ← mul_pow, ← mul_pow,
      Int.ediv_mul_cancel hadiv, Int.ediv_mul_cancel hbdiv, Int.ediv_mul_cancel hcdiv]
  · simpa [gcd_eq_gcd_image, d] using
      Finset.gcd_div_id_eq_one (show a ∈ ({a, b, c} : Finset ℤ) by simp) ha
  · simp only [mul_eq_zero] at habs
    rcases habs with ((ha' | hb') | hc') <;>
    grind [Int.eq_zero_of_ediv_eq_zero]
end FltRegular.MayAssume
