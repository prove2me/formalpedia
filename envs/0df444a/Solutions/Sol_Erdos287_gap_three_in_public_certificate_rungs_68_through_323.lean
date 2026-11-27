-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_68_through_323
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:52:38.307393+00:00
-- url     : https://prove2.me/submissions/838ad7f5-f331-4d60-9b65-34d98401ca45

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
  [ ⟨125079893, 584, 2, 24, 3, 3⟩,
    ⟨77907521, 588, 0, 6, 3, 2⟩,
    ⟨95521171, 587, 2, 24, 3, 3⟩,
    ⟨118753391, 590, 0, 6, 3, 2⟩,
    ⟨73777727, 590, 2, 24, 3, 3⟩,
    ⟨90909193, 593, 0, 6, 3, 2⟩,
    ⟨110570249, 592, 2, 24, 3, 3⟩,
    ⟨68718701, 594, 2, 24, 3, 3⟩,
    ⟨85636063, 595, 2, 24, 3, 3⟩,
    ⟨106626851, 598, 0, 6, 3, 2⟩,
    ⟨133243657, 597, 2, 24, 3, 3⟩,
    ⟨82348141, 599, 2, 24, 3, 3⟩,
    ⟨102719921, 602, 0, 6, 3, 2⟩,
    ⟨128391247, 603, 0, 6, 3, 2⟩,
    ⟨80164627, 605, 0, 6, 3, 2⟩,
    ⟨100116209, 604, 2, 24, 3, 3⟩,
    ⟨123653533, 607, 0, 6, 3, 2⟩,
    ⟨76955653, 609, 0, 6, 3, 2⟩,
    ⟨95586941, 610, 0, 6, 3, 2⟩,
    ⟨119216689, 609, 2, 24, 3, 3⟩,
    ⟨73731013, 613, 0, 6, 3, 2⟩,
    ⟨91824329, 612, 2, 24, 3, 3⟩,
    ⟨114606097, 615, 0, 6, 3, 2⟩,
    ⟨71226691, 615, 2, 24, 3, 3⟩,
    ⟨88451483, 616, 2, 24, 3, 3⟩,
    ⟨110294089, 617, 2, 24, 3, 3⟩,
    ⟨67276273, 619, 2, 24, 3, 3⟩,
    ⟨83770871, 622, 0, 6, 3, 2⟩,
    ⟨104590183, 623, 0, 6, 3, 2⟩,
    ⟨130629797, 622, 2, 24, 3, 3⟩,
    ⟨79882493, 624, 2, 24, 3, 3⟩,
    ⟨97863049, 625, 2, 24, 3, 3⟩,
    ⟨121592321, 626, 2, 24, 3, 3⟩,
    ⟨74876309, 628, 2, 24, 3, 3⟩,
    ⟨92577787, 629, 2, 24, 3, 3⟩,
    ⟨115047839, 632, 0, 6, 3, 2⟩,
    ⟨70411379, 632, 2, 24, 3, 3⟩,
    ⟨87751207, 635, 0, 6, 3, 2⟩,
    ⟨109606151, 636, 0, 6, 3, 2⟩,
    ⟨68318279, 636, 2, 24, 3, 3⟩,
    ⟨85015243, 639, 0, 6, 3, 2⟩,
    ⟨105479369, 640, 0, 6, 3, 2⟩,
    ⟨131067931, 639, 2, 24, 3, 3⟩,
    ⟨81798559, 641, 2, 24, 3, 3⟩,
    ⟨101294009, 644, 0, 6, 3, 2⟩,
    ⟨126324151, 643, 2, 24, 3, 3⟩,
    ⟨77382127, 647, 0, 6, 3, 2⟩,
    ⟨95575397, 646, 2, 24, 3, 3⟩,
    ⟨119450803, 647, 2, 24, 3, 3⟩,
    ⟨74274349, 649, 2, 24, 3, 3⟩,
    ⟨92603141, 650, 2, 24, 3, 3⟩,
    ⟨115520203, 653, 0, 6, 3, 2⟩,
    ⟨71012257, 653, 2, 24, 3, 3⟩,
    ⟨88457909, 656, 0, 6, 3, 2⟩,
    ⟨110480647, 657, 0, 6, 3, 2⟩,
    ⟨67985779, 657, 2, 24, 3, 3⟩,
    ⟨83366681, 658, 2, 24, 3, 3⟩,
    ⟨103826563, 661, 0, 6, 3, 2⟩,
    ⟨129334703, 660, 2, 24, 3, 3⟩,
    ⟨80113391, 664, 0, 6, 3, 2⟩,
    ⟨97090681, 663, 2, 24, 3, 3⟩,
    ⟨120718739, 664, 2, 24, 3, 3⟩,
    ⟨75035657, 666, 2, 24, 3, 3⟩,
    ⟨92951917, 669, 0, 6, 3, 2⟩,
    ⟨115550651, 670, 0, 6, 3, 2⟩,
    ⟨72160607, 670, 2, 24, 3, 3⟩,
    ⟨90147613, 671, 2, 24, 3, 3⟩,
    ⟨112659761, 674, 0, 6, 3, 2⟩,
    ⟨69647321, 674, 2, 24, 3, 3⟩,
    ⟨86870383, 677, 0, 6, 3, 2⟩,
    ⟨108129389, 676, 2, 24, 3, 3⟩,
    ⟨67419971, 680, 0, 6, 3, 2⟩,
    ⟨83931073, 681, 0, 6, 3, 2⟩,
    ⟨104341169, 680, 2, 24, 3, 3⟩,
    ⟨129422749, 681, 2, 24, 3, 3⟩,
    ⟨80308603, 683, 2, 24, 3, 3⟩,
    ⟨100336331, 686, 0, 6, 3, 2⟩,
    ⟨124764847, 687, 0, 6, 3, 2⟩,
    ⟨75128323, 689, 0, 6, 3, 2⟩,
    ⟨93612371, 690, 0, 6, 3, 2⟩,
    ⟨114707947, 689, 2, 24, 3, 3⟩,
    ⟨69577363, 693, 0, 6, 3, 2⟩,
    ⟨85967561, 694, 0, 6, 3, 2⟩,
    ⟨107267527, 695, 0, 6, 3, 2⟩,
    ⟨133689239, 696, 0, 6, 3, 2⟩,
    ⟨83485769, 698, 0, 6, 3, 2⟩,
    ⟨102981139, 697, 2, 24, 3, 3⟩,
    ⟨126966419, 700, 0, 6, 3, 2⟩,
    ⟨79293941, 702, 0, 6, 3, 2⟩,
    ⟨98900587, 703, 0, 6, 3, 2⟩,
    ⟨121538519, 704, 0, 6, 3, 2⟩,
    ⟨73931609, 704, 2, 24, 3, 3⟩,
    ⟨91634629, 705, 2, 24, 3, 3⟩,
    ⟨114178241, 708, 0, 6, 3, 2⟩,
    ⟨71281019, 708, 2, 24, 3, 3⟩,
    ⟨88868047, 709, 2, 24, 3, 3⟩,
    ⟨109758491, 712, 0, 6, 3, 2⟩,
    ⟨68376719, 714, 0, 6, 3, 2⟩,
    ⟨85390369, 713, 2, 24, 3, 3⟩,
    ⟨106403321, 716, 0, 6, 3, 2⟩,
    ⟨132601753, 715, 2, 24, 3, 3⟩,
    ⟨81722023, 719, 0, 6, 3, 2⟩,
    ⟨101771207, 718, 2, 24, 3, 3⟩,
    ⟨126169663, 719, 2, 24, 3, 3⟩,
    ⟨78702829, 721, 2, 24, 3, 3⟩,
    ⟨97552211, 722, 2, 24, 3, 3⟩,
    ⟨119420893, 723, 2, 24, 3, 3⟩,
    ⟨73041607, 725, 2, 24, 3, 3⟩,
    ⟨91214399, 728, 0, 6, 3, 2⟩,
    ⟨113621773, 729, 0, 6, 3, 2⟩,
    ⟨70264267, 731, 0, 6, 3, 2⟩,
    ⟨87400331, 732, 0, 6, 3, 2⟩,
    ⟨107919283, 733, 0, 6, 3, 2⟩,
    ⟨65912167, 735, 0, 6, 3, 2⟩,
    ⟨82155461, 734, 2, 24, 3, 3⟩,
    ⟨102075223, 735, 2, 24, 3, 3⟩,
    ⟨126540983, 736, 2, 24, 3, 3⟩,
    ⟨78220469, 740, 0, 6, 3, 2⟩,
    ⟨96716731, 739, 2, 24, 3, 3⟩,
    ⟨120500153, 740, 2, 24, 3, 3⟩,
    ⟨74486081, 744, 0, 6, 3, 2⟩,
    ⟨93029401, 743, 2, 24, 3, 3⟩,
    ⟨115469021, 746, 0, 6, 3, 2⟩,
    ⟨72129977, 746, 2, 24, 3, 3⟩,
    ⟨88624387, 749, 0, 6, 3, 2⟩,
    ⟨110581181, 750, 0, 6, 3, 2⟩,
    ⟨65974547, 750, 2, 24, 3, 3⟩,
    ⟨82102633, 753, 0, 6, 3, 2⟩,
    ⟨101268239, 754, 0, 6, 3, 2⟩,
    ⟨125171197, 753, 2, 24, 3, 3⟩,
    ⟨77814361, 755, 2, 24, 3, 3⟩,
    ⟨93841613, 756, 2, 24, 3, 3⟩,
    ⟨117137707, 757, 2, 24, 3, 3⟩,
    ⟨73063723, 761, 0, 6, 3, 2⟩,
    ⟨89919521, 762, 0, 6, 3, 2⟩,
    ⟨111742333, 763, 0, 6, 3, 2⟩,
    ⟨69348787, 765, 0, 6, 3, 2⟩,
    ⟨86186339, 766, 0, 6, 3, 2⟩,
    ⟨105437797, 767, 0, 6, 3, 2⟩,
    ⟨131542937, 766, 2, 24, 3, 3⟩,
    ⟨81778943, 768, 2, 24, 3, 3⟩,
    ⟨100961737, 769, 2, 24, 3, 3⟩,
    ⟨125710829, 772, 0, 6, 3, 2⟩,
    ⟨78471479, 772, 2, 24, 3, 3⟩,
    ⟨97547179, 773, 2, 24, 3, 3⟩,
    ⟨121902611, 776, 0, 6, 3, 2⟩,
    ⟨75446909, 778, 0, 6, 3, 2⟩,
    ⟨91836739, 777, 2, 24, 3, 3⟩,
    ⟨113641259, 780, 0, 6, 3, 2⟩,
    ⟨70917179, 780, 2, 24, 3, 3⟩,
    ⟨87935467, 783, 0, 6, 3, 2⟩,
    ⟨108651971, 784, 0, 6, 3, 2⟩,
    ⟨66799301, 786, 0, 6, 3, 2⟩,
    ⟨83130973, 787, 0, 6, 3, 2⟩,
    ⟨103147769, 788, 0, 6, 3, 2⟩,
    ⟨126658933, 789, 0, 6, 3, 2⟩,
    ⟨77874163, 791, 0, 6, 3, 2⟩,
    ⟨97022819, 792, 0, 6, 3, 2⟩,
    ⟨121047103, 793, 0, 6, 3, 2⟩,
    ⟨72590233, 795, 0, 6, 3, 2⟩,
    ⟨90669599, 796, 0, 6, 3, 2⟩,
    ⟨109581271, 795, 2, 24, 3, 3⟩,
    ⟨67815337, 799, 0, 6, 3, 2⟩,
    ⟨83567921, 800, 0, 6, 3, 2⟩,
    ⟨104270527, 801, 0, 6, 3, 2⟩,
    ⟨130151321, 802, 0, 6, 3, 2⟩,
    ⟨80845559, 804, 0, 6, 3, 2⟩,
    ⟨99869797, 805, 0, 6, 3, 2⟩,
    ⟨122289779, 806, 0, 6, 3, 2⟩,
    ⟨76332911, 806, 2, 24, 3, 3⟩,
    ⟨94865557, 809, 0, 6, 3, 2⟩,
    ⟨118187831, 810, 0, 6, 3, 2⟩,
    ⟨72110897, 810, 2, 24, 3, 3⟩,
    ⟨89669761, 811, 2, 24, 3, 3⟩,
    ⟨110462081, 814, 0, 6, 3, 2⟩,
    ⟨66667787, 814, 2, 24, 3, 3⟩,
    ⟨83276203, 815, 2, 24, 3, 3⟩,
    ⟨103895201, 818, 0, 6, 3, 2⟩,
    ⟨126394459, 817, 2, 24, 3, 3⟩,
    ⟨78643597, 821, 0, 6, 3, 2⟩,
    ⟨97101149, 822, 0, 6, 3, 2⟩,
    ⟨121340053, 823, 0, 6, 3, 2⟩,
    ⟨75383701, 823, 2, 24, 3, 3⟩,
    ⟨93562559, 826, 0, 6, 3, 2⟩,
    ⟨116363917, 825, 2, 24, 3, 3⟩,
    ⟨71290411, 827, 2, 24, 3, 3⟩,
    ⟨83247389, 828, 2, 24, 3, 3⟩,
    ⟨102941617, 831, 0, 6, 3, 2⟩,
    ⟨126079799, 832, 0, 6, 3, 2⟩,
    ⟨78539381, 834, 0, 6, 3, 2⟩,
    ⟨97189177, 833, 2, 24, 3, 3⟩,
    ⟨121153091, 836, 0, 6, 3, 2⟩,
    ⟨75272723, 836, 2, 24, 3, 3⟩,
    ⟨93957859, 837, 2, 24, 3, 3⟩,
    ⟨117087809, 840, 0, 6, 3, 2⟩,
    ⟨73051169, 840, 2, 24, 3, 3⟩,
    ⟨90862477, 841, 2, 24, 3, 3⟩,
    ⟨113286659, 844, 0, 6, 3, 2⟩,
    ⟨70668569, 846, 0, 6, 3, 2⟩,
    ⟨87478939, 845, 2, 24, 3, 3⟩,
    ⟨109229807, 846, 2, 24, 3, 3⟩,
    ⟨68262503, 848, 2, 24, 3, 3⟩,
    ⟨83731159, 849, 2, 24, 3, 3⟩,
    ⟨104218871, 850, 2, 24, 3, 3⟩,
    ⟨129412027, 853, 0, 6, 3, 2⟩,
    ⟨77913973, 855, 0, 6, 3, 2⟩,
    ⟨97046981, 854, 2, 24, 3, 3⟩,
    ⟨119824267, 857, 0, 6, 3, 2⟩,
    ⟨74031523, 859, 0, 6, 3, 2⟩,
    ⟨91545161, 858, 2, 24, 3, 3⟩,
    ⟨110673313, 861, 0, 6, 3, 2⟩,
    ⟨64620109, 861, 2, 24, 3, 3⟩,
    ⟨80605781, 862, 2, 24, 3, 3⟩,
    ⟨100618783, 865, 0, 6, 3, 2⟩,
    ⟨124841099, 866, 0, 6, 3, 2⟩,
    ⟨77383511, 868, 0, 6, 3, 2⟩,
    ⟨96159403, 867, 2, 24, 3, 3⟩,
    ⟨119992571, 870, 0, 6, 3, 2⟩,
    ⟨73016057, 870, 2, 24, 3, 3⟩,
    ⟨87435571, 871, 2, 24, 3, 3⟩,
    ⟨109110809, 872, 2, 24, 3, 3⟩,
    ⟨68172581, 874, 2, 24, 3, 3⟩,
    ⟨83548873, 875, 2, 24, 3, 3⟩,
    ⟨103651109, 876, 2, 24, 3, 3⟩,
    ⟨128183707, 877, 2, 24, 3, 3⟩,
    ⟨79185823, 881, 0, 6, 3, 2⟩,
    ⟨97845239, 880, 2, 24, 3, 3⟩,
    ⟨121245589, 881, 2, 24, 3, 3⟩,
    ⟨74165263, 885, 0, 6, 3, 2⟩,
    ⟨90192833, 884, 2, 24, 3, 3⟩,
    ⟨111591673, 887, 0, 6, 3, 2⟩,
    ⟨68246377, 889, 0, 6, 3, 2⟩,
    ⟨85069349, 888, 2, 24, 3, 3⟩,
    ⟨105462433, 891, 0, 6, 3, 2⟩,
    ⟨130140011, 890, 2, 24, 3, 3⟩,
    ⟨80619683, 892, 2, 24, 3, 3⟩,
    ⟨99450553, 895, 0, 6, 3, 2⟩,
    ⟨123952847, 894, 2, 24, 3, 3⟩,
    ⟨76008239, 898, 0, 6, 3, 2⟩,
    ⟨94571689, 897, 2, 24, 3, 3⟩,
    ⟨117462701, 898, 2, 24, 3, 3⟩,
    ⟨72290363, 900, 2, 24, 3, 3⟩,
    ⟨87086497, 901, 2, 24, 3, 3⟩,
    ⟨106997981, 904, 0, 6, 3, 2⟩,
    ⟨131400001, 903, 2, 24, 3, 3⟩,
    ⟨81757069, 905, 2, 24, 3, 3⟩,
    ⟨102180941, 906, 2, 24, 3, 3⟩,
    ⟨127009033, 909, 0, 6, 3, 2⟩,
    ⟨75950869, 909, 2, 24, 3, 3⟩,
    ⟨94797401, 910, 2, 24, 3, 3⟩,
    ⟨115029841, 911, 2, 24, 3, 3⟩,
    ⟨71676343, 915, 0, 6, 3, 2⟩,
    ⟨87945251, 916, 0, 6, 3, 2⟩,
    ⟨109256557, 917, 0, 6, 3, 2⟩,
    ⟨67472539, 917, 2, 24, 3, 3⟩,
    ⟨81325319, 920, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 127121066678798445735243883196317776949351426878578394099564929136550843411572772149955019782860736757937532214437526600769419124790518099200969633104128306711796545988048739553341603835 < f (k - 1))
    (hhi : f (k - 1) ≤ 7208116319200367450407115533588980011400784121272241099449580028658628209152193060371635799711480110024882516743560588651098146444954442114294176237768388665061338446562753736262843608661830460545436394411515307479615712118070190680809270944500958312921705785003119324582869277805117435) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

