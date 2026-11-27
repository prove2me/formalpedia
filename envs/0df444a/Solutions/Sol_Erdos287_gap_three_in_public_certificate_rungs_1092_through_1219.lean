-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1092_through_1219
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:16:19.219836+00:00
-- url     : https://prove2.me/submissions/5332fd47-eccc-4d4b-8321-3b1434354879

import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Theorems.Thm_Erdos287_proth_prime_certificate
import Theorems.Thm_Erdos287_factorial_prime_rung

open Finset

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Erdos287.CompactRungs

/-- Each step halves the exponent and reduces the intermediate residue. -/
def powModBits (a m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | fuel + 1, e =>
      let x := powModBits a m fuel (e / 2)
      (x * x * (if e % 2 = 0 then 1 else a)) % m

theorem powModBits_eq (a m fuel e : ℕ) (he : e < 2 ^ fuel) :
    powModBits a m fuel e = a ^ e % m := by
  induction fuel generalizing e with
  | zero =>
      have he0 : e = 0 := by simpa using he
      simp [he0, powModBits]
  | succ fuel ih =>
      have hhalf : e / 2 < 2 ^ fuel := by
        apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mpr
        simpa only [pow_succ] using he
      have hparity : (if e % 2 = 0 then 1 else a) = a ^ (e % 2) := by
        rcases Nat.mod_two_eq_zero_or_one e with h | h <;> simp [h]
      have hsplit : e = e / 2 + e / 2 + e % 2 := by omega
      rw [powModBits, ih _ hhalf, hparity,
        ← Nat.mod_mul_mod (a ^ (e / 2) % m * (a ^ (e / 2) % m)) (a ^ (e % 2)) m,
        ← Nat.mul_mod (a ^ (e / 2)) (a ^ (e / 2)) m, Nat.mod_mul_mod]
      conv_rhs => rw [hsplit, pow_add, pow_add]

def powMod (a m e : ℕ) : ℕ := powModBits a m (e.log2 + 1) e

theorem powMod_eq (a m e : ℕ) : powMod a m e = a ^ e % m := by
  apply powModBits_eq
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by decide) e

private def squarePowMod (a m : ℕ) : ℕ → ℕ
  | 0 => a % m
  | t + 1 => let residue := squarePowMod a m t; (residue * residue) % m

private theorem squarePowMod_eq (a m t : ℕ) : squarePowMod a m t = a ^ (2 ^ t) % m := by
  induction t with
  | zero => simp [squarePowMod]
  | succ t ih =>
      rw [squarePowMod, ih, ← Nat.mul_mod, pow_succ, pow_mul, pow_two]

private def shiftedPowMod (a m e t : ℕ) : ℕ := squarePowMod (powMod a m e) m t

private theorem shiftedPowMod_eq (a m e t : ℕ) :
    shiftedPowMod a m e t = a ^ (e * 2 ^ t) % m := by
  rw [shiftedPowMod, squarePowMod_eq, powMod_eq, pow_mul]
  exact (Nat.pow_mod (a ^ e) (2 ^ t) m).symm

private theorem zmod_powMod (a n e : ℕ) :
    (a : ZMod n) ^ e = (powMod a n e : ZMod n) := by
  rw [powMod_eq, ← Nat.cast_pow]
  exact CharP.natCast_eq_natCast_mod (ZMod n) n (a ^ e)

private theorem cast_pred (n : ℕ) (hn : 0 < n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  apply eq_neg_of_add_eq_zero_left
  calc
    ((n - 1 : ℕ) : ZMod n) + 1 = ((n - 1 + 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_add, Nat.cast_one]
    _ = 0 := by rw [Nat.sub_add_cancel hn, ZMod.natCast_self]

structure Rung where
  oddPart : ℕ
  exponent : ℕ
  shift : ℕ
  cofactorCap : ℕ
  firstWitness : ℕ
  secondWitness : ℕ

def Rung.p (r : Rung) : ℕ := r.oddPart * 2 ^ (r.exponent + 1) + 1

def Rung.x (r : Rung) : ℕ := r.p * 2 ^ (r.shift + 1)

def Rung.q (r : Rung) : ℕ := r.x + 1

def Rung.upper (r : Rung) : ℕ := (5 * r.x - 20) / 2

private def Rung.companionPow (r : Rung) : ℕ :=
  squarePowMod (shiftedPowMod r.secondWitness r.q r.oddPart (r.exponent + 1) *
    r.secondWitness % r.q) r.q r.shift

private theorem Rung.companionPow_eq (r : Rung) :
    r.companionPow = powMod r.secondWitness r.q (r.p * 2 ^ r.shift) := by
  rw [Rung.companionPow, squarePowMod_eq, shiftedPowMod_eq, Nat.mod_mul_mod,
    ← pow_succ, powMod_eq, pow_mul]
  exact (Nat.pow_mod (r.secondWitness ^ r.p) (2 ^ r.shift) r.q).symm

/-- Check that this interval extends the interval ending at the given endpoint. -/
def Rung.check (r : Rung) (last : ℕ) : Bool := decide (
  0 < r.oddPart ∧ r.oddPart < 2 ^ (r.exponent + 1) ∧
  shiftedPowMod r.firstWitness r.p r.oddPart r.exponent = r.p - 1 ∧
  r.companionPow = r.q - 1 ∧
  powMod r.secondWitness r.q (2 ^ (r.shift + 1)) ≠ 1 ∧
  r.cofactorCap * r.cofactorCap.factorial < r.p ∧ 4 < r.q ∧
  r.x + 2 ≤ last + 1 ∧ last ≤ r.upper ∧
  r.upper < (r.cofactorCap + 1) * r.p ∧ r.upper < 3 * r.q ∧
  2 * r.upper + 20 ≤ 5 * r.x)

private theorem half_power_eq_neg_one (a n e : ℕ) (hn : 0 < n)
    (h : powMod a n e = n - 1) : (a : ZMod n) ^ e = -1 := by
  rw [zmod_powMod, h, cast_pred n hn]

private theorem second_prime (r : Rung) (hp : r.p.Prime) (hq : 4 < r.q)
    (hh : (r.secondWitness : ZMod r.q) ^ (r.p * 2 ^ r.shift) = -1)
    (hsmall : powMod r.secondWitness r.q (2 ^ (r.shift + 1)) ≠ 1) :
    r.q.Prime := by
  let _ : Fact (1 < r.q) := ⟨by omega⟩
  let _ : NeZero r.q := ⟨by omega⟩
  have hfactor : r.q - 1 = r.p * 2 ^ (r.shift + 1) := by simp [Rung.q, Rung.x]
  have hhalf : r.q - 1 = (r.p * 2 ^ r.shift) * 2 := by
    rw [hfactor, pow_succ, mul_assoc]
  let a : ZMod r.q := r.secondWitness
  have hfull : a ^ (r.q - 1) = 1 := by
    rw [hhalf, pow_mul, show a ^ (r.p * 2 ^ r.shift) = -1 from hh]
    norm_num
  apply lucas_primality r.q a hfull
  intro p hp' hdiv
  rw [hfactor] at hdiv
  rcases hp'.dvd_mul.mp hdiv with h | h
  · have he : p = r.p := (Nat.prime_dvd_prime_iff_eq hp' hp).mp h
    subst p
    rw [hfactor, Nat.mul_comm, Nat.mul_div_cancel _ hp.pos]
    intro heq
    have hvalue := congrArg ZMod.val heq
    have hmod : powMod r.secondWitness r.q (2 ^ (r.shift + 1)) < r.q := by
      rw [powMod_eq]
      exact Nat.mod_lt _ (by omega)
    rw [show a = (r.secondWitness : ZMod r.q) from rfl, zmod_powMod, ZMod.val_natCast,
      Nat.mod_eq_of_lt hmod, ZMod.val_one] at hvalue
    exact hsmall hvalue
  · have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp (hp'.dvd_of_dvd_pow h)
    subst p
    rw [hhalf, Nat.mul_div_cancel _ (by decide : 0 < 2),
      show a ^ (r.p * 2 ^ r.shift) = -1 from hh]
    intro hneg
    have hvalue : ((r.q - 1 : ℕ) : ZMod r.q) = 1 :=
      (cast_pred r.q (by omega)).trans hneg
    have hb := congrArg ZMod.val hvalue
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : r.q - 1 < r.q), ZMod.val_one] at hb
    omega

abbrev HasGap (k : ℕ) (f : ℕ → ℕ) :=
  ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i

theorem rung_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (r : Rung) (last : ℕ) (hcheck : r.check last = true)
    (hlast : last < f (k - 1)) (hupper : f (k - 1) ≤ r.upper) :
    HasGap k f := by
  unfold Rung.check at hcheck
  obtain ⟨hodd, hbound, hpw, hqw, hsmall, hfact, hq4, hlo, _, hhip, hhiq, hband⟩ :=
    of_decide_eq_true hcheck
  rw [shiftedPowMod_eq, ← powMod_eq] at hpw
  rw [Rung.companionPow_eq] at hqw
  have hp1 : 0 < r.p := Nat.zero_lt_succ _
  have hp : r.p.Prime := Erdos287.proth_prime_certificate r.oddPart r.exponent
    r.firstWitness hodd hbound (half_power_eq_neg_one _ _ _ hp1 hpw)
  have hq : r.q.Prime := second_prime r hp hq4
    (half_power_eq_neg_one _ _ _ (by omega) hqw) hsmall
  exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum r.x r.p r.q r.cofactorCap 2
    hp hq ⟨2 ^ (r.shift + 1), rfl⟩ (dvd_refl _) hfact (by simpa using hq4)
    (by omega) (hupper.trans_lt hhip) (hupper.trans_lt hhiq) (by omega)

private def checkIntervals {α : Type} (check : α → ℕ → Bool) (upper : α → ℕ) :
    List α → ℕ → ℕ → Bool
  | [], start, finish => decide (start = finish)
  | r :: tail, start, finish => check r start && checkIntervals check upper tail (upper r) finish

private theorem checkedIntervalsGap {α : Type} (k : ℕ) (f : ℕ → ℕ)
    (check : α → ℕ → Bool) (upper : α → ℕ)
    (sound : ∀ r start, check r start = true → start < f (k - 1) →
      f (k - 1) ≤ upper r → HasGap k f)
    (rungs : List α) (start finish : ℕ)
    (hcheck : checkIntervals check upper rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f := by
  induction rungs generalizing start with
  | nil =>
      have h : start = finish := of_decide_eq_true hcheck
      omega
  | cons r tail ih =>
      obtain ⟨hr, ht⟩ := Bool.and_eq_true_iff.mp hcheck
      by_cases h : f (k - 1) ≤ upper r
      · exact sound r start hr hlow h
      · exact ih (upper r) ht (Nat.lt_of_not_ge h)

def checkChain := checkIntervals Rung.check Rung.upper

theorem chain_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (rungs : List Rung) (start finish : ℕ)
    (hcheck : checkChain rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f :=
  checkedIntervalsGap k f Rung.check Rung.upper
    (rung_gap k hk f hf1 hmono hsum) rungs start finish hcheck hlow hhigh

structure ProthPair where
  oddPart : ℕ
  exponent : ℕ
  leftWitness : ℕ
  rightWitness : ℕ

def ProthPair.left (r : ProthPair) : ℕ := r.oddPart * 2 ^ (r.exponent + 1 + 1) + 1

def ProthPair.right (r : ProthPair) : ℕ := r.oddPart * 2 ^ (r.exponent + 1) + 1

def ProthPair.upper (r : ProthPair) : ℕ := (5 * r.left - 20) / 2

def ProthPair.check (r : ProthPair) (last : ℕ) : Bool := decide (
  0 < r.oddPart ∧ r.oddPart < 2 ^ (r.exponent + 1) ∧
  shiftedPowMod r.leftWitness r.left r.oddPart (r.exponent + 1) = r.left - 1 ∧
  shiftedPowMod r.rightWitness r.right r.oddPart r.exponent = r.right - 1 ∧
  4 < r.left ∧ 96 < r.right ∧
  r.left + 2 ≤ last + 1 ∧ last ≤ r.upper ∧
  r.upper < 3 * r.left ∧ r.upper < 5 * r.right ∧
  2 * r.upper + 20 ≤ 5 * r.left)

private theorem proth_pair_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (r : ProthPair) (last : ℕ) (hcheck : r.check last = true)
    (hlast : last < f (k - 1)) (hupper : f (k - 1) ≤ r.upper) :
    HasGap k f := by
  unfold ProthPair.check at hcheck
  obtain ⟨hodd, hsmall, hlw, hrw, hl4, hr96, hlo, _, hhip, hhiq, hband⟩ :=
    of_decide_eq_true hcheck
  rw [shiftedPowMod_eq, ← powMod_eq] at hlw hrw
  have hsmallLeft : r.oddPart < 2 ^ (r.exponent + 1 + 1) := by
    rw [pow_succ]
    omega
  have hp : r.left.Prime := Erdos287.proth_prime_certificate r.oddPart (r.exponent + 1)
    r.leftWitness hodd hsmallLeft (half_power_eq_neg_one _ _ _ (by omega) hlw)
  have hq : r.right.Prime := Erdos287.proth_prime_certificate r.oddPart r.exponent
    r.rightWitness hodd hsmall (half_power_eq_neg_one _ _ _ (by omega) hrw)
  have hdouble : r.left + 1 = r.right * 2 := by simp [ProthPair.left, ProthPair.right, pow_succ]; ring
  exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum r.left r.left r.right 2 4
    hp hq (dvd_refl _) ⟨2, hdouble⟩ (by simpa using hl4) (by simpa [Nat.factorial] using hr96)
    (by omega) (hupper.trans_lt hhip) (hupper.trans_lt hhiq) (by omega)

def checkProthChain := checkIntervals ProthPair.check ProthPair.upper

theorem proth_chain_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (rungs : List ProthPair) (start finish : ℕ)
    (hcheck : checkProthChain rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f :=
  checkedIntervalsGap k f ProthPair.check ProthPair.upper
    (proth_pair_gap k hk f hf1 hmono hsum) rungs start finish hcheck hlow hhigh

end Erdos287.CompactRungs

open Erdos287.CompactRungs

private def certificateRungs : List Rung :=
  [ ⟨112520323, 1903, 4, 96, 3, 3⟩,
    ⟨66896623, 1907, 2, 24, 3, 3⟩,
    ⟨80701919, 1908, 2, 24, 3, 3⟩,
    ⟨97102177, 1911, 0, 6, 3, 2⟩,
    ⟨116098709, 1908, 4, 96, 3, 3⟩,
    ⟨64169741, 1914, 0, 6, 3, 2⟩,
    ⟨77117767, 1915, 0, 6, 3, 2⟩,
    ⟨93293891, 1916, 0, 6, 3, 2⟩,
    ⟨103646593, 1913, 4, 96, 3, 3⟩,
    ⟨125228861, 1918, 0, 6, 3, 2⟩,
    ⟨77782241, 1920, 0, 6, 3, 2⟩,
    ⟨96915817, 1917, 4, 96, 3, 3⟩,
    ⟨119401679, 1920, 2, 24, 3, 3⟩,
    ⟨63787637, 1922, 2, 24, 3, 3⟩,
    ⟨78123637, 1921, 4, 96, 3, 3⟩,
    ⟨94043309, 1922, 4, 96, 3, 3⟩,
    ⟨116865163, 1927, 0, 6, 3, 2⟩,
    ⟨69118573, 1929, 0, 6, 3, 2⟩,
    ⟨74288939, 1926, 4, 96, 3, 3⟩,
    ⟨88624843, 1927, 4, 96, 3, 3⟩,
    ⟨105703139, 1928, 4, 96, 3, 3⟩,
    ⟨132079303, 1929, 4, 96, 3, 3⟩,
    ⟨69172003, 1931, 4, 96, 3, 3⟩,
    ⟨83103809, 1932, 4, 96, 3, 3⟩,
    ⟨99917047, 1933, 4, 96, 3, 3⟩,
    ⟨118705151, 1938, 0, 6, 3, 2⟩,
    ⟨71220641, 1938, 2, 24, 3, 3⟩,
    ⟨87968953, 1939, 2, 24, 3, 3⟩,
    ⟨108718991, 1942, 0, 6, 3, 2⟩,
    ⟨65599871, 1940, 4, 96, 3, 3⟩,
    ⟨78861091, 1943, 2, 24, 3, 3⟩,
    ⟨96047459, 1942, 4, 96, 3, 3⟩,
    ⟨111369067, 1943, 4, 96, 3, 3⟩,
    ⟨68252077, 1949, 0, 6, 3, 2⟩,
    ⟨84511391, 1950, 0, 6, 3, 2⟩,
    ⟨105151873, 1947, 4, 96, 3, 3⟩,
    ⟨115028099, 1952, 0, 6, 3, 2⟩,
    ⟨71775311, 1950, 4, 96, 3, 3⟩,
    ⟨88445353, 1955, 0, 6, 3, 2⟩,
    ⟨108453911, 1956, 0, 6, 3, 2⟩,
    ⟨63043451, 1954, 4, 96, 3, 3⟩,
    ⟨78533773, 1955, 4, 96, 3, 3⟩,
    ⟨91454459, 1956, 4, 96, 3, 3⟩,
    ⟨112489843, 1957, 4, 96, 3, 3⟩,
    ⟨64611829, 1961, 2, 24, 3, 3⟩,
    ⟨76413431, 1964, 0, 6, 3, 2⟩,
    ⟨89245537, 1961, 4, 96, 3, 3⟩,
    ⟨110878961, 1962, 4, 96, 3, 3⟩,
    ⟨69083579, 1964, 4, 96, 3, 3⟩,
    ⟨85431607, 1969, 0, 6, 3, 2⟩,
    ⟨105752039, 1968, 2, 24, 3, 3⟩,
    ⟨129063553, 1967, 4, 96, 3, 3⟩,
    ⟨73236433, 1971, 2, 24, 3, 3⟩,
    ⟨88555853, 1972, 2, 24, 3, 3⟩,
    ⟨109388887, 1971, 4, 96, 3, 3⟩,
    ⟨68144533, 1973, 4, 96, 3, 3⟩,
    ⟨79636439, 1974, 4, 96, 3, 3⟩,
    ⟨94103803, 1975, 4, 96, 3, 3⟩,
    ⟨117096911, 1978, 2, 24, 3, 3⟩,
    ⟨65490809, 1978, 4, 96, 3, 3⟩,
    ⟨81520723, 1983, 0, 6, 3, 2⟩,
    ⟨97224821, 1980, 4, 96, 3, 3⟩,
    ⟨120038797, 1981, 4, 96, 3, 3⟩,
    ⟨72014053, 1983, 4, 96, 3, 3⟩,
    ⟨87752501, 1986, 2, 24, 3, 3⟩,
    ⟨106692583, 1989, 0, 6, 3, 2⟩,
    ⟨122459219, 1990, 0, 6, 3, 2⟩,
    ⟨76295399, 1988, 4, 96, 3, 3⟩,
    ⟨94114477, 1993, 0, 6, 3, 2⟩,
    ⟨113412713, 1992, 2, 24, 3, 3⟩,
    ⟨67534919, 1992, 4, 96, 3, 3⟩,
    ⟨83788933, 1993, 4, 96, 3, 3⟩,
    ⟨64631753, 1996, 2, 24, 3, 3⟩,
    ⟨77590027, 1995, 4, 96, 3, 3⟩,
    ⟨87996287, 1998, 2, 24, 3, 3⟩,
    ⟨105145303, 2001, 0, 6, 3, 2⟩,
    ⟨129787901, 1998, 4, 96, 3, 3⟩,
    ⟨70409621, 2000, 4, 96, 3, 3⟩,
    ⟨82158871, 2003, 2, 24, 3, 3⟩,
    ⟨102598049, 2004, 2, 24, 3, 3⟩,
    ⟨124003723, 2007, 0, 6, 3, 2⟩,
    ⟨76683961, 2007, 2, 24, 3, 3⟩,
    ⟨95342669, 2008, 2, 24, 3, 3⟩,
    ⟨116650537, 2011, 0, 6, 3, 2⟩,
    ⟨57912661, 2011, 2, 24, 3, 3⟩,
    ⟨70891229, 2012, 2, 24, 3, 3⟩,
    ⟨82252537, 2015, 0, 6, 3, 2⟩,
    ⟨101551529, 2016, 0, 6, 3, 2⟩,
    ⟨126900997, 2017, 0, 6, 3, 2⟩,
    ⟨77660203, 2019, 0, 6, 3, 2⟩,
    ⟨93382451, 2018, 2, 24, 3, 3⟩,
    ⟨103418527, 2017, 4, 96, 3, 3⟩,
    ⟨119896949, 2022, 0, 6, 3, 2⟩,
    ⟨70437461, 2024, 0, 6, 3, 2⟩,
    ⟨84934477, 2021, 4, 96, 3, 3⟩,
    ⟨104687909, 2024, 2, 24, 3, 3⟩,
    ⟨128957167, 2027, 0, 6, 3, 2⟩,
    ⟨79117243, 2029, 0, 6, 3, 2⟩,
    ⟨95449163, 2028, 2, 24, 3, 3⟩,
    ⟨111598159, 2029, 2, 24, 3, 3⟩,
    ⟨68721313, 2033, 0, 6, 3, 2⟩,
    ⟨83202611, 2034, 0, 6, 3, 2⟩,
    ⟨102264229, 2033, 2, 24, 3, 3⟩,
    ⟨126905111, 2032, 4, 96, 3, 3⟩,
    ⟨78348029, 2036, 2, 24, 3, 3⟩,
    ⟨95594533, 2035, 4, 96, 3, 3⟩,
    ⟨116544581, 2038, 2, 24, 3, 3⟩,
    ⟨67665509, 2040, 2, 24, 3, 3⟩,
    ⟨79508683, 2039, 4, 96, 3, 3⟩,
    ⟨85591421, 2044, 0, 6, 3, 2⟩,
    ⟨104739757, 2041, 4, 96, 3, 3⟩,
    ⟨125167589, 2042, 4, 96, 3, 3⟩,
    ⟨77523101, 2046, 2, 24, 3, 3⟩,
    ⟨94360153, 2047, 2, 24, 3, 3⟩,
    ⟨106982999, 2048, 2, 24, 3, 3⟩,
    ⟨127760533, 2051, 0, 6, 3, 2⟩,
    ⟨79717867, 2049, 4, 96, 3, 3⟩,
    ⟨96088799, 2050, 4, 96, 3, 3⟩,
    ⟨111983167, 2053, 2, 24, 3, 3⟩,
    ⟨65773453, 2057, 0, 6, 3, 2⟩,
    ⟨80617679, 2054, 4, 96, 3, 3⟩,
    ⟨97980277, 2057, 2, 24, 3, 3⟩,
    ⟨117487301, 2060, 0, 6, 3, 2⟩,
    ⟨70847321, 2058, 4, 96, 3, 3⟩,
    ⟨88370587, 2063, 0, 6, 3, 2⟩,
    ⟨95813909, 2060, 4, 96, 3, 3⟩,
    ⟨116514841, 2063, 2, 24, 3, 3⟩,
    ⟨72491347, 2063, 4, 96, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 5229796815015366576697891942701585646625564493601204679272022210072835802841231155676411126960264420674995672397192054020585027037987476541775427460915385088890504721076128437851519612114221735394044911772864201981931237321532742253617620712830918235635064805112193002968844062891883874451913594946850478871365471806464497512559518594740887259894500929767260944463177689296121337325998486983670360254940566338521659617566878525575362961002025973880212453622665521631965327089854577722635496218486746517055162242150483296130317847580249985582203920737495618973775952965946201436323910 12282512283357743547184082972052472232871899801761724729897097728447234057054482417041529985835190548416329173907914092601729275248588947883051740038351555601376979400248330609663449090973319330964617678008352565432938066180948716331902925298777254919217282449623348388622830906599212404082504723519637204923647881621139011798736277261197525097681957798909966656711543294783018539950894567751918057134745385634574534860265272419151591034109812864069178604985862149266760289867449827211603545113500203429709538701704745073422383704656992496639851079264996892478782549679833049208017879082276812714643190175500988464687355703496540230 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 5229796815015366576697891942701585646625564493601204679272022210072835802841231155676411126960264420674995672397192054020585027037987476541775427460915385088890504721076128437851519612114221735394044911772864201981931237321532742253617620712830918235635064805112193002968844062891883874451913594946850478871365471806464497512559518594740887259894500929767260944463177689296121337325998486983670360254940566338521659617566878525575362961002025973880212453622665521631965327089854577722635496218486746517055162242150483296130317847580249985582203920737495618973775952965946201436323910 < f (k - 1))
    (hhi : f (k - 1) ≤ 12282512283357743547184082972052472232871899801761724729897097728447234057054482417041529985835190548416329173907914092601729275248588947883051740038351555601376979400248330609663449090973319330964617678008352565432938066180948716331902925298777254919217282449623348388622830906599212404082504723519637204923647881621139011798736277261197525097681957798909966656711543294783018539950894567751918057134745385634574534860265272419151591034109812864069178604985862149266760289867449827211603545113500203429709538701704745073422383704656992496639851079264996892478782549679833049208017879082276812714643190175500988464687355703496540230) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

