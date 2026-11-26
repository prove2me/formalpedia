-- Prove2me | solution 1 for Erdos287.disjoint_prime_blocks_multiply_subsum_counts
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:00:01.111805+00:00
-- url     : https://prove2.me/submissions/149bcf61-f8e6-4616-9da3-3842b5f2d02b

import Mathlib

open Finset

set_option autoImplicit false

/-- Local numerator choices with distinct residues give distinct rational
sums across a collection of disjoint prime coordinates. -/
theorem solution (I : Finset ℕ) (p L : ℕ → ℕ) (S : ℕ → Finset ℕ)
    (hp : ∀ i ∈ I, (p i).Prime) (hp_inj : Set.InjOn p (↑I : Set ℕ))
    (hL : ∀ i ∈ I, 0 < L i) (hcop : ∀ i ∈ I, ∀ j ∈ I, ¬ p i ∣ L j)
    (hsize : ∀ i ∈ I, ∀ a ∈ S i, a < p i) :
    ((I.pi S).image (fun a => ∑ i ∈ I.attach,
      (a i.val i.property : ℚ) / (p i.val * L i.val : ℕ))).card =
      ∏ i ∈ I, (S i).card := by
  classical
  let n (i : ℕ) := p i * L i
  let Q := ∏ i ∈ I, n i
  let W (i : ℕ) := ∏ j ∈ I.erase i, n j
  let fraction (a : ∀ i ∈ I, ℕ) := ∑ i ∈ I.attach, (a i.val i.property : ℚ) / n i.val
  let clear (a : ∀ i ∈ I, ℕ) := ∑ i ∈ I.attach, W i.val * a i.val i.property
  have hclear (a : ∀ i ∈ I, ℕ) : (Q : ℚ) * fraction a = (clear a : ℚ) := by
    simp only [fraction, clear, mul_sum, Nat.cast_sum]
    apply sum_congr rfl
    intro i _
    have hn : n i.val ≠ 0 := Nat.mul_ne_zero (hp i.val i.property).ne_zero (hL i.val i.property).ne'
    have hQ : Q = W i.val * n i.val := (prod_erase_mul I n i.property).symm
    have hQ' : (Q : ℚ) = (W i.val : ℚ) * n i.val := by exact_mod_cast hQ
    calc
      (Q : ℚ) * ((a i.val i.property : ℚ) / n i.val) =
          ((W i.val : ℚ) * a i.val i.property * n i.val) / n i.val := by
        rw [hQ']
        ring
      _ = (W i.val * a i.val i.property : ℕ) := by
        rw [mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr hn), Nat.cast_mul]
  have hnunit (i : ℕ) (hi : i ∈ I) : ¬ p i ∣ W i := by
    intro hd
    obtain ⟨j, hj, hjd⟩ := ((hp i hi).prime.dvd_finsetProd_iff n).mp hd
    have hjI := mem_of_mem_erase hj
    rcases (hp i hi).dvd_mul.mp hjd with hjp | hjL
    · have hne : p i ≠ p j := fun he => (ne_of_mem_erase hj) (hp_inj hi hjI he).symm
      have hc := (Nat.coprime_primes (hp i hi) (hp j hjI)).mpr hne
      exact ((hp i hi).coprime_iff_not_dvd.mp hc) hjp
    · exact hcop i hi j hjI hjL
  have hred (a : ∀ i ∈ I, ℕ) (i : ↥I) :
      (clear a : ZMod (p i.val)) = (W i.val : ZMod (p i.val)) * (a i.val i.property : ZMod (p i.val)) := by
    simp only [clear, Nat.cast_sum]
    rw [sum_eq_single_of_mem i (mem_attach _ _)]
    · simp only [Nat.cast_mul]
    · intro j _ hji
      have hne : i.val ≠ j.val := fun h => hji (Subtype.ext h.symm)
      have hmem : i.val ∈ I.erase j.val := mem_erase.mpr ⟨hne, i.property⟩
      have hd : p i.val ∣ W j.val := (dvd_mul_right _ _).trans (dvd_prod_of_mem n hmem)
      rw [Nat.cast_mul, (ZMod.natCast_eq_zero_iff (W j.val) _).mpr hd, zero_mul]
  have hinj : Set.InjOn fraction (↑(I.pi S) : Set (∀ i ∈ I, ℕ)) := by
    intro a ha b hb he
    have hab : clear a = clear b := by
      have h : (clear a : ℚ) = (clear b : ℚ) := by rw [← hclear, ← hclear, he]
      exact_mod_cast h
    funext i hi
    have hcast := congrArg (fun x : ℕ => (x : ZMod (p i))) hab
    rw [hred a ⟨i, hi⟩, hred b ⟨i, hi⟩] at hcast
    have hu : IsUnit (W i : ZMod (p i)) := (ZMod.isUnit_iff_coprime _ _).mpr
      (((hp i hi).coprime_iff_not_dvd).mpr (hnunit i hi)).symm
    have hcoord := hu.mul_left_cancel hcast
    have hai := hsize i hi (a i hi) (mem_pi.mp ha i hi)
    have hbi := hsize i hi (b i hi) (mem_pi.mp hb i hi)
    have hvalue := congrArg ZMod.val hcoord
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hai, Nat.mod_eq_of_lt hbi] using hvalue
  change ((I.pi S).image fraction).card = _
  rw [card_image_of_injOn hinj]
  exact Multiset.card_pi _ _

