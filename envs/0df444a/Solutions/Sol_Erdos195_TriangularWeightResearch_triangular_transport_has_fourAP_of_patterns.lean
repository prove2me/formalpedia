-- Prove2me | solution 1 for Erdos195.TriangularWeightResearch.triangular_transport_has_fourAP_of_patterns
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:42:20.937167+00:00
-- url     : https://prove2.me/submissions/794319ff-fc52-4097-b653-4e74bf971c20

import Mathlib
import Definitions.Def_Erdos195_defs
import Definitions.Def_Erdos195_TriangularBinary_Model

namespace Erdos195.TriangularWeightResearch

@[simp] theorem weightValue_zero (a : ℕ → ℤ) : weightValue a 0 = 0 := by
  rw [weightValue]
  simp

@[simp] theorem weightValue_even (a : ℕ → ℤ) (n : ℕ) :
    weightValue a (2*n) = 2 * weightValue (fun j => a (j+1)) n := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [weightValue]
    simp [hn]

@[simp] theorem weightValue_odd (a : ℕ → ℤ) (n : ℕ) :
    weightValue a (2*n+1) = 2 * weightValue (fun j => a (j+1)) n + a 0 := by
  rw [weightValue]
  simp [show (2*n+1)/2=n by omega]

@[simp] theorem weightValue_one (a : ℕ → ℤ) : weightValue a 1 = a 0 := by
  simpa using weightValue_odd a 0

@[simp] theorem weightValue_two (a : ℕ → ℤ) : weightValue a 2 = 2*a 1 := by
  simpa using weightValue_even a 1

@[simp] theorem weightValue_three (a : ℕ → ℤ) : weightValue a 3 = 2*a 1+a 0 := by
  simpa using weightValue_odd a 1

theorem weightValue_scale (a : ℕ → ℤ) (k n : ℕ) :
    weightValue a (2^k*n) = (2:ℤ)^k * weightValue (fun j => a (j+k)) n := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [show 2^(k+1)*n=2*(2^k*n) by ring, weightValue_even, ih]
    simp only [Nat.add_assoc]
    ring

theorem tail_surjective (a : ℕ → ℤ) (ha : Odd (a 0))
    (hs : Function.Surjective (weightValue a)) :
    Function.Surjective (weightValue (fun j => a (j+1))) := by
  intro z
  obtain ⟨n, hn⟩ := hs (2*z)
  by_cases he : n%2=0
  · have en : n=2*(n/2) := by omega
    rw [en, weightValue_even] at hn
    exact ⟨n/2, by linarith⟩
  · have en : n=2*(n/2)+1 := by omega
    rw [en, weightValue_odd] at hn
    obtain ⟨r, hr⟩ := ha
    omega

theorem shifted_surjective (a : ℕ → ℤ) (ha : ∀ j, Odd (a j))
    (hs : Function.Surjective (weightValue a)) (k : ℕ) :
    Function.Surjective (weightValue (fun j => a (j+k))) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h := tail_surjective (fun j => a (j+k)) (by simpa using ha k) ih
    simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h

theorem head_odd_of_surjective (a : ℕ → ℤ)
    (hs : Function.Surjective (weightValue a)) : Odd (a 0) := by
  obtain ⟨n, hn⟩ := hs 1
  by_cases he : n%2=0
  · have en : n=2*(n/2) := by omega
    rw [en, weightValue_even] at hn
    omega
  · have en : n=2*(n/2)+1 := by omega
    rw [en, weightValue_odd] at hn
    refine ⟨-weightValue (fun j => a (j+1)) (n/2), ?_⟩
    omega

theorem shifted_surjective_of_surjective (a : ℕ → ℤ)
    (hs : Function.Surjective (weightValue a)) (k : ℕ) :
    Function.Surjective (weightValue (fun j => a (j+k))) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    have h := tail_surjective (fun j => a (j+k))
      (head_odd_of_surjective _ ih) ih
    simpa only [Nat.add_assoc, Nat.add_comm 1 k] using h

theorem coefficients_odd_of_surjective (a : ℕ → ℤ)
    (hs : Function.Surjective (weightValue a)) (k : ℕ) : Odd (a k) := by
  simpa using head_odd_of_surjective (fun j => a (j+k))
    (shifted_surjective_of_surjective a hs k)

theorem value_bijective_of_transport (p : ℕ ≃ ℕ) (a : ℕ → ℤ) (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = weightValue a (p i)) : Function.Bijective (weightValue a) := by
  constructor
  · intro n m hnm
    have h : f (p.symm n) = f (p.symm m) := by simpa only [hval, Equiv.apply_symm_apply] using hnm
    exact p.symm.injective (f.injective h)
  · intro z
    obtain ⟨i, hi⟩ := f.surjective z
    exact ⟨p i, (hval i).symm.trans hi⟩

theorem weightValue_const (b : ℤ) (n : ℕ) :
    weightValue (fun _ => b) n = b*(n:ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n=0
    · simp [hn]
    rw [weightValue, dif_neg hn, ih (n/2) (by omega)]
    have hcast : (n:ℤ)=2*((n/2:ℕ):ℤ)+((n%2:ℕ):ℤ) := by
      exact_mod_cast (show n=2*(n/2)+n%2 by omega)
    by_cases hm : n%2=0
    · simp only [hm, if_pos, Nat.cast_zero, add_zero] at hcast ⊢
      rw [hcast]
      ring
    · have hm1 : n%2=1 := by omega
      rw [if_neg hm]
      simp only [hm1, Nat.cast_one] at hcast
      rw [hcast]
      ring

end Erdos195.TriangularWeightResearch

namespace Erdos195.SignedDigitResearch

theorem hasMonotoneAP_of_equations (f : ℕ ≃ ℤ) (i j k l : ℕ)
    (hij : i < j) (hjk : j < k) (hkl : k < l)
    (h1 : f i + f k = 2 * f j) (h2 : f j + f l = 2 * f k) :
    HasMonotoneAP f 4 := by
  have e2 : f i + 2 * (f j - f i) = f k := by linarith
  have e3 : f i + 3 * (f j - f i) = f l := by linarith
  refine ⟨[i,j,k,l], ⟨f i, f j-f i, Or.inl ?_⟩, ?_⟩
  · simpa [List.range_succ] using And.intro e2.symm e3.symm
  · simpa [List.pairwise_cons] using
      And.intro (And.intro hij (And.intro (lt_trans hij hjk)
        (lt_trans hij (lt_trans hjk hkl))))
        (And.intro (And.intro hjk (lt_trans hjk hkl)) hkl)

end Erdos195.SignedDigitResearch

open Erdos195 Erdos195.TriangularWeightResearch

theorem solution
    (p : ℕ ≃ ℕ) (a : ℕ → ℤ) (f : ℕ ≃ ℤ)
    (hval : ∀ i, f i = weightValue a (p i))
    (horder : ∀ k n : ℕ, 2 ≤ n →
      p.symm (2^k*3) < p.symm (2^k*2) ∧
      p.symm (2^k*2) < p.symm (2^k*(2*n+1)) ∧
      p.symm (2^k*(2*n+1)) < p.symm (2^k*(2*n))) :
    HasMonotoneAP f 4 := by
  by_contra hfree
  have hs := (value_bijective_of_transport p a f hval).2
  have ha := coefficients_odd_of_surjective a hs
  have hv (n : ℕ) : f (p.symm n) = weightValue a n := by
    simpa using hval (p.symm n)
  have hadj (k : ℕ) : a (k+1) = a k := by
    obtain ⟨n, hn⟩ := shifted_surjective a ha hs (k+1) (a (k+1)-a k)
    by_cases hn0 : n=0
    · simp only [hn0, weightValue_zero] at hn
      omega
    by_cases hn1 : n=1
    · simp only [hn1, weightValue_one, zero_add] at hn
      obtain ⟨r, hr⟩ := ha k
      omega
    exfalso
    apply hfree
    apply SignedDigitResearch.hasMonotoneAP_of_equations f
      (p.symm (2^k*3))
      (p.symm (2^k*2))
      (p.symm (2^k*(2*n+1)))
      (p.symm (2^k*(2*n)))
      (horder k n (by omega)).1
      (horder k n (by omega)).2.1
      (horder k n (by omega)).2.2
    all_goals
      simp only [hv, weightValue_scale, weightValue_three, weightValue_two,
        weightValue_odd, weightValue_even, zero_add]
      simp only [Nat.add_assoc, Nat.add_comm 1 k, hn]
      ring
  have heq : a = fun _ => a 0 := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact (hadj n).trans ih
  rcases le_total 0 (a 0) with hnonneg | hnonpos
  · obtain ⟨n, hn⟩ := hs (-1)
    rw [heq, weightValue_const] at hn
    have hp := mul_nonneg hnonneg (Nat.cast_nonneg (α := ℤ) n)
    omega
  · obtain ⟨n, hn⟩ := hs 1
    rw [heq, weightValue_const] at hn
    have hp := mul_nonpos_of_nonpos_of_nonneg hnonpos (Nat.cast_nonneg (α := ℤ) n)
    omega
