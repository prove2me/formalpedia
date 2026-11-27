-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1220_through_1347
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:21:16.786655+00:00
-- url     : https://prove2.me/submissions/0ca00273-cd8c-4d42-b608-f412937a272f

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
  [ ⟨81862967, 2066, 2, 24, 3, 3⟩,
    ⟨94313053, 2067, 2, 24, 3, 3⟩,
    ⟨112786643, 2068, 2, 24, 3, 3⟩,
    ⟨53963549, 2072, 0, 6, 3, 2⟩,
    ⟨64466863, 2071, 2, 24, 3, 3⟩,
    ⟨78421619, 2072, 2, 24, 3, 3⟩,
    ⟨86011027, 2073, 2, 24, 3, 3⟩,
    ⟨101486291, 2074, 2, 24, 3, 3⟩,
    ⟨120004783, 2075, 2, 24, 3, 3⟩,
    ⟨74399653, 2079, 0, 6, 3, 2⟩,
    ⟨89025791, 2078, 2, 24, 3, 3⟩,
    ⟨108855007, 2077, 4, 96, 3, 3⟩,
    ⟨66873979, 2081, 2, 24, 3, 3⟩,
    ⟨76974659, 2080, 4, 96, 3, 3⟩,
    ⟨90780583, 2085, 0, 6, 3, 2⟩,
    ⟨112175171, 2086, 0, 6, 3, 2⟩,
    ⟨60087551, 2088, 0, 6, 3, 2⟩,
    ⟨72389857, 2089, 0, 6, 3, 2⟩,
    ⟨85583909, 2088, 2, 24, 3, 3⟩,
    ⟨98273347, 2091, 0, 6, 3, 2⟩,
    ⟨121882961, 2088, 4, 96, 3, 3⟩,
    ⟨69768659, 2090, 4, 96, 3, 3⟩,
    ⟨87179227, 2093, 2, 24, 3, 3⟩,
    ⟨106964981, 2094, 2, 24, 3, 3⟩,
    ⟨132051373, 2095, 2, 24, 3, 3⟩,
    ⟨77381923, 2095, 4, 96, 3, 3⟩,
    ⟨94143971, 2096, 4, 96, 3, 3⟩,
    ⟨112404403, 2097, 4, 96, 3, 3⟩,
    ⟨70164187, 2101, 2, 24, 3, 3⟩,
    ⟨80819777, 2102, 2, 24, 3, 3⟩,
    ⟨97482823, 2103, 2, 24, 3, 3⟩,
    ⟨118154279, 2106, 0, 6, 3, 2⟩,
    ⟨58365239, 2104, 4, 96, 3, 3⟩,
    ⟨66108433, 2109, 0, 6, 3, 2⟩,
    ⟨80494163, 2108, 2, 24, 3, 3⟩,
    ⟨100333993, 2107, 4, 96, 3, 3⟩,
    ⟨123750551, 2108, 4, 96, 3, 3⟩,
    ⟨76650341, 2114, 0, 6, 3, 2⟩,
    ⟨79404907, 2111, 4, 96, 3, 3⟩,
    ⟨96445469, 2112, 4, 96, 3, 3⟩,
    ⟨120126781, 2115, 2, 24, 3, 3⟩,
    ⟨74026219, 2117, 2, 24, 3, 3⟩,
    ⟨91014479, 2116, 4, 96, 3, 3⟩,
    ⟨105211273, 2121, 0, 6, 3, 2⟩,
    ⟨123344183, 2120, 2, 24, 3, 3⟩,
    ⟨73625141, 2122, 2, 24, 3, 3⟩,
    ⟨91739257, 2125, 0, 6, 3, 2⟩,
    ⟨113231969, 2126, 0, 6, 3, 2⟩,
    ⟨69374861, 2128, 0, 6, 3, 2⟩,
    ⟨83592661, 2127, 2, 24, 3, 3⟩,
    ⟨103956953, 2128, 2, 24, 3, 3⟩,
    ⟨123895267, 2127, 4, 96, 3, 3⟩,
    ⟨72669133, 2133, 0, 6, 3, 2⟩,
    ⟨82917929, 2132, 2, 24, 3, 3⟩,
    ⟨103108843, 2135, 0, 6, 3, 2⟩,
    ⟨124552271, 2136, 0, 6, 3, 2⟩,
    ⟨71829059, 2138, 0, 6, 3, 2⟩,
    ⟨88852747, 2137, 2, 24, 3, 3⟩,
    ⟨109603469, 2140, 0, 6, 3, 2⟩,
    ⟨66067679, 2142, 0, 6, 3, 2⟩,
    ⟨78032203, 2139, 4, 96, 3, 3⟩,
    ⟨95714651, 2140, 4, 96, 3, 3⟩,
    ⟨118511347, 2141, 4, 96, 3, 3⟩,
    ⟨73004053, 2143, 4, 96, 3, 3⟩,
    ⟨86015927, 2146, 2, 24, 3, 3⟩,
    ⟨107441977, 2145, 4, 96, 3, 3⟩,
    ⟨62467303, 2147, 4, 96, 3, 3⟩,
    ⟨74804141, 2148, 4, 96, 3, 3⟩,
    ⟨86435983, 2153, 0, 6, 3, 2⟩,
    ⟨97669133, 2152, 2, 24, 3, 3⟩,
    ⟨120389317, 2155, 0, 6, 3, 2⟩,
    ⟨60853543, 2157, 0, 6, 3, 2⟩,
    ⟨71520791, 2158, 0, 6, 3, 2⟩,
    ⟨86010139, 2157, 2, 24, 3, 3⟩,
    ⟨102605621, 2160, 0, 6, 3, 2⟩,
    ⟨127901533, 2159, 2, 24, 3, 3⟩,
    ⟨77826943, 2163, 0, 6, 3, 2⟩,
    ⟨84216497, 2162, 2, 24, 3, 3⟩,
    ⟨102475843, 2163, 2, 24, 3, 3⟩,
    ⟨119889911, 2162, 4, 96, 3, 3⟩,
    ⟨73138487, 2166, 2, 24, 3, 3⟩,
    ⟨81847933, 2169, 0, 6, 3, 2⟩,
    ⟨98102159, 2170, 0, 6, 3, 2⟩,
    ⟨121361629, 2169, 2, 24, 3, 3⟩,
    ⟨72744337, 2169, 4, 96, 3, 3⟩,
    ⟨90274649, 2170, 4, 96, 3, 3⟩,
    ⟨106976917, 2175, 0, 6, 3, 2⟩,
    ⟨133626641, 2174, 2, 24, 3, 3⟩,
    ⟨78926831, 2178, 0, 6, 3, 2⟩,
    ⟨97249363, 2179, 0, 6, 3, 2⟩,
    ⟨120823139, 2180, 0, 6, 3, 2⟩,
    ⟨75253853, 2180, 2, 24, 3, 3⟩,
    ⟨88222009, 2181, 2, 24, 3, 3⟩,
    ⟨103033841, 2180, 4, 96, 3, 3⟩,
    ⟨123075397, 2181, 4, 96, 3, 3⟩,
    ⟨75546577, 2183, 4, 96, 3, 3⟩,
    ⟨82118639, 2184, 4, 96, 3, 3⟩,
    ⟨96691213, 2185, 4, 96, 3, 3⟩,
    ⟨109034669, 2190, 0, 6, 3, 2⟩,
    ⟨65969711, 2192, 0, 6, 3, 2⟩,
    ⟨77094733, 2191, 2, 24, 3, 3⟩,
    ⟨79458959, 2190, 4, 96, 3, 3⟩,
    ⟨95602537, 2193, 2, 24, 3, 3⟩,
    ⟨113520821, 2192, 4, 96, 3, 3⟩,
    ⟨69365189, 2198, 0, 6, 3, 2⟩,
    ⟨85156447, 2199, 0, 6, 3, 2⟩,
    ⟨101481311, 2196, 4, 96, 3, 3⟩,
    ⟨125063923, 2199, 2, 24, 3, 3⟩,
    ⟨70163893, 2203, 0, 6, 3, 2⟩,
    ⟨85603979, 2200, 4, 96, 3, 3⟩,
    ⟨104934007, 2201, 4, 96, 3, 3⟩,
    ⟨127291919, 2206, 0, 6, 3, 2⟩,
    ⟨78522071, 2208, 0, 6, 3, 2⟩,
    ⟨91315981, 2207, 2, 24, 3, 3⟩,
    ⟨110439731, 2206, 4, 96, 3, 3⟩,
    ⟨64406231, 2210, 2, 24, 3, 3⟩,
    ⟨78969703, 2211, 2, 24, 3, 3⟩,
    ⟨97534061, 2210, 4, 96, 3, 3⟩,
    ⟨119896519, 2213, 2, 24, 3, 3⟩,
    ⟨73789147, 2213, 4, 96, 3, 3⟩,
    ⟨91365929, 2214, 4, 96, 3, 3⟩,
    ⟨112858939, 2217, 2, 24, 3, 3⟩,
    ⟨62451307, 2221, 0, 6, 3, 2⟩,
    ⟨77667299, 2218, 4, 96, 3, 3⟩,
    ⟨94881253, 2223, 0, 6, 3, 2⟩,
    ⟨115289051, 2224, 0, 6, 3, 2⟩,
    ⟨56649119, 2224, 2, 24, 3, 3⟩,
    ⟨60241087, 2225, 2, 24, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 12282512283357743547184082972052472232871899801761724729897097728447234057054482417041529985835190548416329173907914092601729275248588947883051740038351555601376979400248330609663449090973319330964617678008352565432938066180948716331902925298777254919217282449623348388622830906599212404082504723519637204923647881621139011798736277261197525097681957798909966656711543294783018539950894567751918057134745385634574534860265272419151591034109812864069178604985862149266760289867449827211603545113500203429709538701704745073422383704656992496639851079264996892478782549679833049208017879082276812714643190175500988464687355703496540230 14917400282768037724101041560968701267360400256242255035809474064707246528412288917092516333985090352260728920591046337154370609379528030949121105929822816886696857118760011428854175343085474356238795672322794518348632894664774032659860217332998397533048770384954063046191426862623782138063046100471004704479210742005525655163942090131681951262461054196857026922473670806973126571861995046349333568272765925697859170545194466691078979821699353619497612947435554265872706699419577094759503032664747966982659738982169889708538941767695124927117424970813106256373591672021392966759334881865184644745270574984482739485207249869124123810945159873003785631940699756132103451743470223370 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 12282512283357743547184082972052472232871899801761724729897097728447234057054482417041529985835190548416329173907914092601729275248588947883051740038351555601376979400248330609663449090973319330964617678008352565432938066180948716331902925298777254919217282449623348388622830906599212404082504723519637204923647881621139011798736277261197525097681957798909966656711543294783018539950894567751918057134745385634574534860265272419151591034109812864069178604985862149266760289867449827211603545113500203429709538701704745073422383704656992496639851079264996892478782549679833049208017879082276812714643190175500988464687355703496540230 < f (k - 1))
    (hhi : f (k - 1) ≤ 14917400282768037724101041560968701267360400256242255035809474064707246528412288917092516333985090352260728920591046337154370609379528030949121105929822816886696857118760011428854175343085474356238795672322794518348632894664774032659860217332998397533048770384954063046191426862623782138063046100471004704479210742005525655163942090131681951262461054196857026922473670806973126571861995046349333568272765925697859170545194466691078979821699353619497612947435554265872706699419577094759503032664747966982659738982169889708538941767695124927117424970813106256373591672021392966759334881865184644745270574984482739485207249869124123810945159873003785631940699756132103451743470223370) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

