-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_580_through_707
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T22:58:14.728446+00:00
-- url     : https://prove2.me/submissions/6854dba0-b459-44e4-853d-593a0e265cab

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
  powMod r.leftWitness r.left (r.oddPart * 2 ^ (r.exponent + 1)) = r.left - 1 ∧
  powMod r.rightWitness r.right (r.oddPart * 2 ^ r.exponent) = r.right - 1 ∧
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
  [ ⟨72875657, 1250, 2, 24, 3, 3⟩,
    ⟨78784333, 1253, 0, 6, 3, 2⟩,
    ⟨95061761, 1254, 0, 6, 3, 2⟩,
    ⟨114775189, 1253, 2, 24, 3, 3⟩,
    ⟨70861081, 1255, 2, 24, 3, 3⟩,
    ⟨85610843, 1256, 2, 24, 3, 3⟩,
    ⟨106119007, 1257, 2, 24, 3, 3⟩,
    ⟨130432331, 1258, 2, 24, 3, 3⟩,
    ⟨79789943, 1260, 2, 24, 3, 3⟩,
    ⟨98612887, 1261, 2, 24, 3, 3⟩,
    ⟨120253559, 1264, 0, 6, 3, 2⟩,
    ⟨70145069, 1262, 4, 96, 3, 3⟩,
    ⟨85152493, 1263, 4, 96, 3, 3⟩,
    ⟨106159451, 1264, 4, 96, 3, 3⟩,
    ⟨132614473, 1265, 4, 96, 3, 3⟩,
    ⟨82799239, 1269, 2, 24, 3, 3⟩,
    ⟨93985301, 1272, 0, 6, 3, 2⟩,
    ⟨116719747, 1269, 4, 96, 3, 3⟩,
    ⟨68642227, 1271, 4, 96, 3, 3⟩,
    ⟨85373801, 1274, 2, 24, 3, 3⟩,
    ⟨105900757, 1273, 4, 96, 3, 3⟩,
    ⟨131711609, 1276, 2, 24, 3, 3⟩,
    ⟨82128041, 1276, 4, 96, 3, 3⟩,
    ⟨101622427, 1281, 0, 6, 3, 2⟩,
    ⟨126451529, 1278, 4, 96, 3, 3⟩,
    ⟨75784799, 1284, 0, 6, 3, 2⟩,
    ⟨93387361, 1283, 2, 24, 3, 3⟩,
    ⟨110825291, 1282, 4, 96, 3, 3⟩,
    ⟨68919467, 1286, 2, 24, 3, 3⟩,
    ⟨84709327, 1285, 4, 96, 3, 3⟩,
    ⟨104179973, 1288, 2, 24, 3, 3⟩,
    ⟨129453739, 1289, 2, 24, 3, 3⟩,
    ⟨80333833, 1293, 0, 6, 3, 2⟩,
    ⟨100059143, 1292, 2, 24, 3, 3⟩,
    ⟨124244839, 1293, 2, 24, 3, 3⟩,
    ⟨77220547, 1293, 4, 96, 3, 3⟩,
    ⟨96324089, 1296, 2, 24, 3, 3⟩,
    ⟨117074323, 1299, 0, 6, 3, 2⟩,
    ⟨71662777, 1297, 4, 96, 3, 3⟩,
    ⟨86942129, 1298, 4, 96, 3, 3⟩,
    ⟨102751717, 1299, 4, 96, 3, 3⟩,
    ⟨127625891, 1304, 0, 6, 3, 2⟩,
    ⟨77235419, 1306, 0, 6, 3, 2⟩,
    ⟨96383719, 1305, 2, 24, 3, 3⟩,
    ⟨118266011, 1304, 4, 96, 3, 3⟩,
    ⟨73737329, 1310, 0, 6, 3, 2⟩,
    ⟨91260397, 1309, 2, 24, 3, 3⟩,
    ⟨113277611, 1308, 4, 96, 3, 3⟩,
    ⟨70678211, 1314, 0, 6, 3, 2⟩,
    ⟨87482737, 1315, 0, 6, 3, 2⟩,
    ⟨105600641, 1312, 4, 96, 3, 3⟩,
    ⟨131891923, 1313, 4, 96, 3, 3⟩,
    ⟨79173439, 1317, 2, 24, 3, 3⟩,
    ⟨98728361, 1320, 0, 6, 3, 2⟩,
    ⟨122711023, 1317, 4, 96, 3, 3⟩,
    ⟨73326133, 1323, 0, 6, 3, 2⟩,
    ⟨90025079, 1320, 4, 96, 3, 3⟩,
    ⟨112492873, 1321, 4, 96, 3, 3⟩,
    ⟨68983237, 1323, 4, 96, 3, 3⟩,
    ⟨83591969, 1324, 4, 96, 3, 3⟩,
    ⟨102218713, 1327, 2, 24, 3, 3⟩,
    ⟨124273271, 1330, 0, 6, 3, 2⟩,
    ⟨72836591, 1328, 4, 96, 3, 3⟩,
    ⟨90380767, 1333, 0, 6, 3, 2⟩,
    ⟨104953613, 1332, 2, 24, 3, 3⟩,
    ⟨129329953, 1335, 0, 6, 3, 2⟩,
    ⟨78641617, 1337, 0, 6, 3, 2⟩,
    ⟨96937541, 1334, 4, 96, 3, 3⟩,
    ⟨119034733, 1335, 4, 96, 3, 3⟩,
    ⟨74136823, 1337, 4, 96, 3, 3⟩,
    ⟨92265731, 1338, 4, 96, 3, 3⟩,
    ⟨113919829, 1341, 2, 24, 3, 3⟩,
    ⟨71185693, 1341, 4, 96, 3, 3⟩,
    ⟨86464619, 1342, 4, 96, 3, 3⟩,
    ⟨107618323, 1343, 4, 96, 3, 3⟩,
    ⟨67123033, 1347, 2, 24, 3, 3⟩,
    ⟨82103369, 1350, 0, 6, 3, 2⟩,
    ⟨100200427, 1347, 4, 96, 3, 3⟩,
    ⟨124907009, 1348, 4, 96, 3, 3⟩,
    ⟨73720919, 1354, 0, 6, 3, 2⟩,
    ⟨91677427, 1353, 2, 24, 3, 3⟩,
    ⟨114354041, 1354, 2, 24, 3, 3⟩,
    ⟨71010371, 1358, 0, 6, 3, 2⟩,
    ⟨87643207, 1355, 4, 96, 3, 3⟩,
    ⟨109205051, 1358, 2, 24, 3, 3⟩,
    ⟨68072969, 1360, 2, 24, 3, 3⟩,
    ⟨80495179, 1361, 2, 24, 3, 3⟩,
    ⟨96930941, 1360, 4, 96, 3, 3⟩,
    ⟨119764963, 1361, 4, 96, 3, 3⟩,
    ⟨74839987, 1367, 0, 6, 3, 2⟩,
    ⟨89871731, 1364, 4, 96, 3, 3⟩,
    ⟨110786413, 1369, 0, 6, 3, 2⟩,
    ⟨69192157, 1369, 2, 24, 3, 3⟩,
    ⟨85846181, 1370, 2, 24, 3, 3⟩,
    ⟨107085103, 1369, 4, 96, 3, 3⟩,
    ⟨128206769, 1370, 4, 96, 3, 3⟩,
    ⟨79233431, 1374, 2, 24, 3, 3⟩,
    ⟨98302027, 1377, 0, 6, 3, 2⟩,
    ⟨121085189, 1374, 4, 96, 3, 3⟩,
    ⟨74706647, 1378, 2, 24, 3, 3⟩,
    ⟨91713211, 1379, 2, 24, 3, 3⟩,
    ⟨113684849, 1382, 0, 6, 3, 2⟩,
    ⟨69317441, 1382, 2, 24, 3, 3⟩,
    ⟨81212293, 1383, 2, 24, 3, 3⟩,
    ⟨100109609, 1386, 0, 6, 3, 2⟩,
    ⟨125130517, 1387, 0, 6, 3, 2⟩,
    ⟨75548623, 1385, 4, 96, 3, 3⟩,
    ⟨91254959, 1386, 4, 96, 3, 3⟩,
    ⟨113711593, 1387, 4, 96, 3, 3⟩,
    ⟨70164673, 1389, 4, 96, 3, 3⟩,
    ⟨86985809, 1392, 2, 24, 3, 3⟩,
    ⟨107938027, 1393, 2, 24, 3, 3⟩,
    ⟨61326103, 1393, 4, 96, 3, 3⟩,
    ⟨75127889, 1398, 0, 6, 3, 2⟩,
    ⟨93451297, 1397, 2, 24, 3, 3⟩,
    ⟨113746079, 1396, 4, 96, 3, 3⟩,
    ⟨70923353, 1400, 2, 24, 3, 3⟩,
    ⟨80979439, 1401, 2, 24, 3, 3⟩,
    ⟨95991041, 1402, 2, 24, 3, 3⟩,
    ⟨116896447, 1405, 0, 6, 3, 2⟩,
    ⟨62252023, 1403, 4, 96, 3, 3⟩,
    ⟨73410767, 1406, 2, 24, 3, 3⟩,
    ⟨90372571, 1407, 2, 24, 3, 3⟩,
    ⟨112857419, 1406, 4, 96, 3, 3⟩,
    ⟨67094141, 1408, 4, 96, 3, 3⟩,
    ⟨80583271, 1411, 2, 24, 3, 3⟩,
    ⟨99780641, 1414, 0, 6, 3, 2⟩,
    ⟨116357953, 1415, 0, 6, 3, 2⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 23805813089741725182015384511104054621492462436169819393247337376348590232433101934819416759323635460150661347734096238203216931254112393534809041441592068475628301049051124656934967823564632980768629149462335397517232454001292587002419225988306705758498861462117908174471405321846075615650603757483916563126131761186680416886434814622774540866409197191052369809358145986408103616184330 1054969579998128804454027271818151521307676020941187320829926552626863692246372373821807093438564019097076004377751497616232485518668074925157713081582174881186241713185561699949790602314567033785617528217260791029814584138367632078695007565513679136095774321065675238064883928760368607578720172502051098479988773620608017545659485684745884790298940635846153902456198655319272838897781971640414867433422520586100071366783895895843799035 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 23805813089741725182015384511104054621492462436169819393247337376348590232433101934819416759323635460150661347734096238203216931254112393534809041441592068475628301049051124656934967823564632980768629149462335397517232454001292587002419225988306705758498861462117908174471405321846075615650603757483916563126131761186680416886434814622774540866409197191052369809358145986408103616184330 < f (k - 1))
    (hhi : f (k - 1) ≤ 1054969579998128804454027271818151521307676020941187320829926552626863692246372373821807093438564019097076004377751497616232485518668074925157713081582174881186241713185561699949790602314567033785617528217260791029814584138367632078695007565513679136095774321065675238064883928760368607578720172502051098479988773620608017545659485684745884790298940635846153902456198655319272838897781971640414867433422520586100071366783895895843799035) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

