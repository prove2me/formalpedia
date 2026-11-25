-- Prove2me | solution 1 for DedekindSubgroups.sig_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:42.066809+00:00
-- url     : https://prove2.me/submissions/c3a47566-d30f-4fcb-9855-c9d533878c0d

module
public import Definitions.Def_DedekindSubgroups_Basic
public import Definitions.Def_DedekindSubgroups_Meyer

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (h k x y : ℕ) (hk : 0 < k) (hxy : x ≤ y) :
    (sig h k y : ℤ) - sig h k x
      = sig h k (y - x) - k * (if sig h k y < sig h k x then 1 else 0) := by
  unfold sig
  set A := h * y
  set B := h * x
  have hAB : h * (y - x) = A - B := Nat.mul_sub h y x
  have hBA : B ≤ A := Nat.mul_le_mul_left h hxy
  rw [hAB]
  have eA := Nat.div_add_mod A k
  have eB := Nat.div_add_mod B k
  have eC := Nat.div_add_mod (A - B) k
  have lA := Nat.mod_lt A hk
  have lB := Nat.mod_lt B hk
  have lC := Nat.mod_lt (A - B) hk
  -- integer version of the three divisions
  have key : ((A % k : ℕ) : ℤ) - (B % k : ℕ) - ((A - B) % k : ℕ)
      = (k : ℤ) * (((A - B) / k : ℕ) - (A / k : ℕ) + (B / k : ℕ)) := by
    have : ((A : ℕ) : ℤ) - (B : ℕ) = ((A - B : ℕ) : ℤ) := by push_cast [hBA]; ring
    have eA' : ((k * (A / k) + A % k : ℕ) : ℤ) = (A : ℤ) := by exact_mod_cast eA
    have eB' : ((k * (B / k) + B % k : ℕ) : ℤ) = (B : ℤ) := by exact_mod_cast eB
    have eC' : ((k * ((A - B) / k) + (A - B) % k : ℕ) : ℤ) = ((A - B : ℕ) : ℤ) := by exact_mod_cast eC
    simp only [Nat.cast_add, Nat.cast_mul] at eA' eB' eC'
    linarith
  set t : ℤ := ((A - B) / k : ℕ) - (A / k : ℕ) + (B / k : ℕ)
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have lA' : ((A % k : ℕ) : ℤ) < k := by exact_mod_cast lA
  have lB' : ((B % k : ℕ) : ℤ) < k := by exact_mod_cast lB
  have lC' : (((A - B) % k : ℕ) : ℤ) < k := by exact_mod_cast lC
  have nA : (0 : ℤ) ≤ ((A % k : ℕ) : ℤ) := by positivity
  have nB : (0 : ℤ) ≤ ((B % k : ℕ) : ℤ) := by positivity
  have nC : (0 : ℤ) ≤ (((A - B) % k : ℕ) : ℤ) := by positivity
  split_ifs with hlt
  · -- σ(y) < σ(x): the multiple of k is -k
    have hlt' : ((A % k : ℕ) : ℤ) < (B % k : ℕ) := by exact_mod_cast hlt
    have ht1 : t < 0 := by
      by_contra hc
      push Not at hc
      have : (0 : ℤ) ≤ (k : ℤ) * t := mul_nonneg hk'.le hc
      linarith
    have ht2 : -1 ≤ t := by
      by_contra hc
      push Not at hc
      have : (k : ℤ) * t ≤ (k : ℤ) * (-2) := by
        apply mul_le_mul_of_nonneg_left _ hk'.le; omega
      linarith
    have : t = -1 := by omega
    rw [this] at key
    linarith
  · have hge : ((B % k : ℕ) : ℤ) ≤ (A % k : ℕ) := by
      exact_mod_cast (not_lt.mp hlt)
    have ht1 : t ≤ 0 := by
      by_contra hc
      push Not at hc
      have : (k : ℤ) * 1 ≤ (k : ℤ) * t := by
        apply mul_le_mul_of_nonneg_left _ hk'.le; omega
      linarith
    have ht2 : 0 ≤ t := by
      by_contra hc
      push Not at hc
      have : (k : ℤ) * t ≤ (k : ℤ) * (-1) := by
        apply mul_le_mul_of_nonneg_left _ hk'.le; omega
      linarith
    have : t = 0 := by omega
    rw [this, mul_zero] at key
    linarith
end DedekindSubgroups
