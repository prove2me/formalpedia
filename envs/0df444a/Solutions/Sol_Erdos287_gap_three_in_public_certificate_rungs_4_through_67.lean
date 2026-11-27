-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_4_through_67
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:50:04.782676+00:00
-- url     : https://prove2.me/submissions/64271809-05b3-4037-a7e1-95b046e4253b

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

/-- Check that this interval extends the interval ending at the given endpoint. -/
def Rung.check (r : Rung) (last : ℕ) : Bool := decide (
  0 < r.oddPart ∧ r.oddPart < 2 ^ (r.exponent + 1) ∧
  powMod r.firstWitness r.p (r.oddPart * 2 ^ r.exponent) = r.p - 1 ∧
  powMod r.secondWitness r.q (r.p * 2 ^ r.shift) = r.q - 1 ∧
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
  letI : Fact (1 < r.q) := ⟨by omega⟩
  letI : NeZero r.q := ⟨by omega⟩
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
  have hp1 : 0 < r.p := Nat.zero_lt_succ _
  have hp : r.p.Prime := Erdos287.proth_prime_certificate r.oddPart r.exponent
    r.firstWitness hodd hbound (half_power_eq_neg_one _ _ _ hp1 hpw)
  have hq : r.q.Prime := second_prime r hp hq4
    (half_power_eq_neg_one _ _ _ (by omega) hqw) hsmall
  exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum r.x r.p r.q r.cofactorCap 2
    hp hq ⟨2 ^ (r.shift + 1), rfl⟩ (dvd_refl _) hfact (by simpa using hq4)
    (by omega) (hupper.trans_lt hhip) (hupper.trans_lt hhiq) (by omega)

def checkChain : List Rung → ℕ → ℕ → Bool
  | [], start, finish => decide (start = finish)
  | r :: tail, start, finish => r.check start && checkChain tail r.upper finish

theorem chain_gap (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ range k, (1 : ℚ) / f i = 1)
    (rungs : List Rung) (start finish : ℕ)
    (hcheck : checkChain rungs start finish = true)
    (hlow : start < f (k - 1)) (hhigh : f (k - 1) ≤ finish) :
    HasGap k f := by
  induction rungs generalizing start with
  | nil =>
      have h : start = finish := of_decide_eq_true hcheck
      omega
  | cons r tail ih =>
      obtain ⟨hr, ht⟩ := Bool.and_eq_true_iff.mp hcheck
      by_cases h : f (k - 1) ≤ r.upper
      · exact rung_gap k hk f hf1 hmono hsum r start hr hlow h
      · exact ih r.upper ht (Nat.lt_of_not_ge h)

end Erdos287.CompactRungs

open Erdos287.CompactRungs

private def certificateRungs : List Rung :=
  [ ⟨111847409, 500, 2, 24, 3, 3⟩,
    ⟨69840311, 504, 0, 6, 3, 2⟩,
    ⟨86874391, 503, 2, 24, 3, 3⟩,
    ⟨108305303, 504, 2, 24, 3, 3⟩,
    ⟨67283729, 508, 0, 6, 3, 2⟩,
    ⟨84059137, 509, 0, 6, 3, 2⟩,
    ⟨104160503, 508, 2, 24, 3, 3⟩,
    ⟨130113433, 511, 0, 6, 3, 2⟩,
    ⟨80895043, 513, 0, 6, 3, 2⟩,
    ⟨100866893, 512, 2, 24, 3, 3⟩,
    ⟨126004369, 513, 2, 24, 3, 3⟩,
    ⟨78404383, 515, 2, 24, 3, 3⟩,
    ⟨97381679, 518, 0, 6, 3, 2⟩,
    ⟨121235743, 519, 0, 6, 3, 2⟩,
    ⟨75364567, 521, 0, 6, 3, 2⟩,
    ⟨93647819, 522, 0, 6, 3, 2⟩,
    ⟨116976187, 523, 0, 6, 3, 2⟩,
    ⟨72918733, 525, 0, 6, 3, 2⟩,
    ⟨91028261, 526, 0, 6, 3, 2⟩,
    ⟨112526593, 527, 0, 6, 3, 2⟩,
    ⟨69991723, 527, 2, 24, 3, 3⟩,
    ⟨87382913, 528, 2, 24, 3, 3⟩,
    ⟨107867017, 529, 2, 24, 3, 3⟩,
    ⟨66356011, 531, 2, 24, 3, 3⟩,
    ⟨82195913, 532, 2, 24, 3, 3⟩,
    ⟨102718639, 533, 2, 24, 3, 3⟩,
    ⟨127963211, 534, 2, 24, 3, 3⟩,
    ⟨79814093, 536, 2, 24, 3, 3⟩,
    ⟨99103483, 539, 0, 6, 3, 2⟩,
    ⟨123650237, 538, 2, 24, 3, 3⟩,
    ⟨77177333, 540, 2, 24, 3, 3⟩,
    ⟨95739277, 541, 2, 24, 3, 3⟩,
    ⟨119585201, 544, 0, 6, 3, 2⟩,
    ⟨73778381, 546, 0, 6, 3, 2⟩,
    ⟨92210317, 547, 0, 6, 3, 2⟩,
    ⟨114723221, 546, 2, 24, 3, 3⟩,
    ⟨69881459, 548, 2, 24, 3, 3⟩,
    ⟨86843947, 551, 0, 6, 3, 2⟩,
    ⟨108017579, 552, 0, 6, 3, 2⟩,
    ⟨67247069, 554, 0, 6, 3, 2⟩,
    ⟨83390113, 555, 0, 6, 3, 2⟩,
    ⟨103608221, 554, 2, 24, 3, 3⟩,
    ⟨128163157, 557, 0, 6, 3, 2⟩,
    ⟨80098099, 557, 2, 24, 3, 3⟩,
    ⟨99650591, 558, 2, 24, 3, 3⟩,
    ⟨124562377, 561, 0, 6, 3, 2⟩,
    ⟨77460457, 563, 0, 6, 3, 2⟩,
    ⟨96730499, 564, 0, 6, 3, 2⟩,
    ⟨120361807, 565, 0, 6, 3, 2⟩,
    ⟨74954557, 565, 2, 24, 3, 3⟩,
    ⟨93570821, 568, 0, 6, 3, 2⟩,
    ⟨116895151, 567, 2, 24, 3, 3⟩,
    ⟨72170107, 571, 0, 6, 3, 2⟩,
    ⟨89962409, 572, 0, 6, 3, 2⟩,
    ⟨112236847, 573, 0, 6, 3, 2⟩,
    ⟨69954277, 573, 2, 24, 3, 3⟩,
    ⟨87163799, 576, 0, 6, 3, 2⟩,
    ⟨108281821, 575, 2, 24, 3, 3⟩,
    ⟨67518877, 577, 2, 24, 3, 3⟩,
    ⟨83647931, 578, 2, 24, 3, 3⟩,
    ⟨103912561, 579, 2, 24, 3, 3⟩,
    ⟨129305003, 580, 2, 24, 3, 3⟩,
    ⟨80500991, 584, 0, 6, 3, 2⟩,
    ⟨100385287, 585, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 5887104692222610115311068713886416666636503914806049781997679266319785399143980188838070510421047673741709770480679026139361407216193271418506778065818374635530 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 5887104692222610115311068713886416666636503914806049781997679266319785399143980188838070510421047673741709770480679026139361407216193271418506778065818374635530 < f (k - 1))
    (hhi : f (k - 1) ≤ 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

