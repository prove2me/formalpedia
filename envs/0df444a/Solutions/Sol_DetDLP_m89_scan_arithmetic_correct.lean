-- Prove2me | solution 1 for DetDLP.m89_scan_arithmetic_correct
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T16:52:09.632074+00:00
-- url     : https://prove2.me/submissions/ed95ff03-c1ee-40a9-8ab2-7eab29ce183f

import Definitions.Def_DetDLP_M89_ScanArithmetic
set_option autoImplicit false
open DetDLP.M89Scan

namespace DetDLP.M89Scan
theorem powBits_cast (p a : ℕ) (bs : List Bool) :
    (powBits p a bs : ZMod p) = (a : ZMod p) ^ Nat.ofDigits 2 (bs.map Bool.toNat) := by
  induction bs generalizing a with
  | nil => simp [powBits, Nat.ofDigits, ZMod.natCast_mod]
  | cons b bs ih =>
    cases b <;> simp [powBits, Nat.ofDigits, ZMod.natCast_mod, ih, pow_add, pow_mul, pow_two]

theorem powMod_cast (p a e : ℕ) : (powMod p a e : ZMod p) = (a : ZMod p) ^ e := by
  rw [powMod, powBits_cast]
  congr 1
  convert Nat.ofDigits_digits 2 e using 2
  rw [Nat.digits_two_eq_bits]
  induction e.bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all

theorem powMod_lt {p : ℕ} (hp : 0 < p) (a e : ℕ) : powMod p a e < p := by
  unfold powMod
  cases e.bits <;> exact Nat.mod_lt _ hp

theorem firstWitness_eq (p : ℕ) [Fact p.Prime] (q : ℕ) (us : List (ZMod p)ˣ) :
    firstWitness p q (us.map unitRep) = unitRep ((us.find? (fun u => decide (u^q ≠ 1))).getD 1) := by
  have hp : p.Prime := Fact.out
  have ht (u : (ZMod p)ˣ) : powMod p (unitRep u) q = 1 ↔ u^q = 1 := by
    have hc := powMod_cast p (unitRep u) q
    simp only [unitRep, ZMod.natCast_zmod_val] at hc
    constructor
    · intro h
      apply Units.val_inj.mp
      change powMod p (u : ZMod p).val q = 1 at h
      simpa [h] using hc.symm
    · intro h
      have hz : (u : ZMod p)^q = 1 := by simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val h
      have hval := congrArg ZMod.val (hc.trans hz)
      change powMod p (u : ZMod p).val q = 1
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (powMod_lt hp.pos _ _), ZMod.val_one] using hval
  induction us with
  | nil => simp [firstWitness, unitRep, ZMod.val_one]
  | cons a us ih =>
    by_cases h : a^q = 1 <;> simp_all [firstWitness, List.find?_cons, ht]

theorem residueProduct_cast (p : ℕ) (xs : List ℕ) :
    (residueProduct p xs : ZMod p) = (xs.map (fun x : ℕ => (x : ZMod p))).prod := by
  induction xs with
  | nil => simp [residueProduct, ZMod.natCast_mod]
  | cons a as ih => simp [residueProduct, ZMod.natCast_mod, ih]
end DetDLP.M89Scan

theorem solution (p : ℕ) [Fact p.Prime] (us : List (ZMod p)ˣ) :
    scan p (p-1).primeFactorsList (us.map unitRep) =
      unitRep (∏ r ∈ (p-1).primeFactors,
        ((us.find? (fun u => decide (u^((p-1)/r) ≠ 1))).getD 1)^((p-1) / r^((p-1).factorization r))) := by
  let fs := (p-1).primeFactorsList
  have hd : fs.dedup.toFinset = (p-1).primeFactors := by
    rw [← Nat.toFinset_factors]; ext r; simp [fs]
  have hp : p.Prime := Fact.out
  have hl : scan p fs (us.map unitRep) < p := by
    have hb (xs : List ℕ) : residueProduct p xs < p := by cases xs <;> exact Nat.mod_lt _ hp.pos
    exact hb _
  rw [← ZMod.val_natCast_of_lt hl]
  change ZMod.val _ = ZMod.val _
  apply congrArg ZMod.val
  rw [← hd, List.prod_toFinset _ fs.nodup_dedup]
  rw [show ∀ xs : List (ZMod p)ˣ, (↑xs.prod : ZMod p) = (xs.map Units.val).prod from map_list_prod (Units.coeHom _) ]
  simp only [scan, residueProduct_cast, List.map_map, Function.comp_apply, Function.comp_def,
    powMod_cast, firstWitness_eq, Nat.primeFactorsList_count_eq, fs, Units.val_pow_eq_pow_val]
  simp [unitRep]


#print axioms solution
