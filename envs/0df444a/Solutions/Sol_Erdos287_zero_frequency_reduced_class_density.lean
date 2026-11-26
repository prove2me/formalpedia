-- Prove2me | solution 1 for Erdos287.zero_frequency_reduced_class_density
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T18:21:48.813979+00:00
-- url     : https://prove2.me/submissions/e8fedc68-7c39-4046-8664-9d0e33bc4786

import Mathlib

set_option autoImplicit false

private theorem totient_gcd_lcm (a b : ℕ) (ha : 0 < a) :
    (a.gcd b).totient * (a.lcm b).totient = a.totient * b.totient := by
  have hg : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b ha
  have hd : a.gcd b ∣ a.lcm b := (Nat.gcd_dvd_left a b).trans (Nat.dvd_lcm_left a b)
  have hgl := Nat.totient_gcd_mul_totient_mul (a.gcd b) (a.lcm b)
  rw [Nat.gcd_eq_left hd] at hgl
  have hprod : (a * b).totient = (a.lcm b).totient * (a.gcd b) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr hg)
    rw [← Nat.gcd_mul_lcm a b, ← mul_assoc]
    exact hgl
  have hab := Nat.totient_gcd_mul_totient_mul a b
  rw [hprod, ← mul_assoc] at hab
  exact Nat.eq_of_mul_eq_mul_left hg (by simpa only [mul_comm _ (a.gcd b)] using hab)

/-- The zero-frequency density of a specified reduced class modulo `a`,
after imposing coprimality with `b` and normalizing by `φ(b)`. -/
theorem solution (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (r : (ZMod a)ˣ) :
    let L := a.lcm b
    let C := Nat.card {w : (ZMod L)ˣ // ZMod.unitsMap (Nat.dvd_lcm_left a b) w = r}
    (C : ℚ) / ((L : ℚ) * (b.totient : ℚ)) = 1 / ((L : ℚ) * ((a.gcd b).totient : ℚ)) := by
  classical
  dsimp only
  have hL := Nat.lcm_pos ha hb
  let _ : NeZero a := ⟨ha.ne'⟩
  let _ : NeZero (a.lcm b) := ⟨hL.ne'⟩
  let f := ZMod.unitsMap (Nat.dvd_lcm_left a b)
  let C := Nat.card {w : (ZMod (a.lcm b))ˣ // f w = r}
  have hs : Function.Surjective f := ZMod.unitsMap_surjective (Nat.dvd_lcm_left a b)
  have hfiber (v : (ZMod a)ˣ) : Fintype.card {w : (ZMod (a.lcm b))ˣ // f w = v} = C := by
    unfold C
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
    exact MonoidHom.card_fiber_eq_of_mem_range f (hs v) (hs r)
  have hC : a.totient * C = (a.lcm b).totient := by
    calc
      a.totient * C = ∑ _v : (ZMod a)ˣ, C := by
        simp [ZMod.card_units_eq_totient]
      _ = ∑ v : (ZMod a)ˣ, Fintype.card {w : (ZMod (a.lcm b))ˣ // f w = v} := by
        simp_rw [hfiber]
      _ = Fintype.card (Σ v : (ZMod a)ˣ, {w : (ZMod (a.lcm b))ˣ // f w = v}) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (ZMod (a.lcm b))ˣ := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
      _ = (a.lcm b).totient := ZMod.card_units_eq_totient _
  have heq : C * (a.gcd b).totient = b.totient := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr ha)
    calc
      a.totient * (C * (a.gcd b).totient) = (a.gcd b).totient * (a.totient * C) := by ring
      _ = a.totient * b.totient := by rw [hC, totient_gcd_lcm a b ha]
  change (C : ℚ) / _ = 1 / _
  have hqL : (0 : ℚ) < (a.lcm b : ℕ) := by exact_mod_cast hL
  have hqb : (0 : ℚ) < b.totient := by exact_mod_cast Nat.totient_pos.mpr hb
  have hqg : (0 : ℚ) < (a.gcd b).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left b ha)
  rw [div_eq_div_iff (mul_ne_zero hqL.ne' hqb.ne') (mul_ne_zero hqL.ne' hqg.ne')]
  have heq' : (C : ℚ) * ((a.gcd b).totient : ℚ) = (b.totient : ℚ) := by exact_mod_cast heq
  rw [one_mul, mul_left_comm, heq']

