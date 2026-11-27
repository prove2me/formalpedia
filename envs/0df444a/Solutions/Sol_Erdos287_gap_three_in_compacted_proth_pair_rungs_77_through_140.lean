-- Prove2me | solution 1 for Erdos287.gap_three_in_compacted_proth_pair_rungs_77_through_140
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:08:24.486836+00:00
-- url     : https://prove2.me/submissions/a65a23ad-5b85-462f-8ce7-973e86422c01

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

private def certificateRungs : List ProthPair :=
  [ ⟨5914809138, 2983, 5, 13⟩,
    ⟨6900191454, 2984, 5, 7⟩,
    ⟨8051124570, 2985, 13, 7⟩,
    ⟨4696089483, 2987, 5, 13⟩,
    ⟨5480414955, 2988, 7, 7⟩,
    ⟨6391828902, 2989, 5, 7⟩,
    ⟨7456595535, 2990, 11, 7⟩,
    ⟨4356167595, 2992, 11, 7⟩,
    ⟨5078088450, 2993, 7, 13⟩,
    ⟨5924270601, 2994, 5, 17⟩,
    ⟨6907158741, 2995, 5, 5⟩,
    ⟨8060673618, 2996, 5, 5⟩,
    ⟨4701543396, 2998, 5, 7⟩,
    ⟨5485757520, 2999, 13, 7⟩,
    ⟨6400897239, 3000, 5, 7⟩,
    ⟨7465929639, 3001, 5, 5⟩,
    ⟨4355107806, 3003, 5, 5⟩,
    ⟨5081533209, 3004, 5, 7⟩,
    ⟨5927179752, 3005, 5, 7⟩,
    ⟨6915429837, 3006, 5, 5⟩,
    ⟨8067324528, 3007, 5, 7⟩,
    ⟨4707152247, 3009, 5, 11⟩,
    ⟨5490583287, 3010, 5, 5⟩,
    ⟨6404989851, 3011, 5, 5⟩,
    ⟨7473276465, 3012, 7, 13⟩,
    ⟨4366092645, 3014, 11, 7⟩,
    ⟨5086325895, 3015, 13, 11⟩,
    ⟨5933567013, 3016, 5, 5⟩,
    ⟨6921836307, 3017, 5, 13⟩,
    ⟨8077714740, 3018, 7, 11⟩,
    ⟨4710869304, 3020, 5, 11⟩,
    ⟨5495950929, 3021, 5, 5⟩,
    ⟨6414885927, 3022, 5, 5⟩,
    ⟨7481881275, 3023, 7, 17⟩,
    ⟨4364973669, 3025, 5, 5⟩,
    ⟨5091322152, 3026, 5, 5⟩,
    ⟨5941545801, 3027, 5, 5⟩,
    ⟨6930820809, 3028, 5, 7⟩,
    ⟨8084034582, 3029, 5, 23⟩,
    ⟨4720331718, 3031, 5, 7⟩,
    ⟨5501739735, 3032, 7, 7⟩,
    ⟨6420391929, 3033, 5, 5⟩,
    ⟨7488677256, 3034, 5, 7⟩,
    ⟨4369147173, 3036, 5, 5⟩,
    ⟨5096555304, 3037, 5, 5⟩,
    ⟨5946781947, 3038, 5, 5⟩,
    ⟨6936711705, 3039, 13, 19⟩,
    ⟨8096538795, 3040, 7, 19⟩,
    ⟨4723837680, 3042, 11, 7⟩,
    ⟨5512525131, 3043, 5, 5⟩,
    ⟨6425917365, 3044, 17, 11⟩,
    ⟨7497369492, 3045, 5, 11⟩,
    ⟨4372910955, 3047, 13, 11⟩,
    ⟨5103425643, 3048, 5, 5⟩,
    ⟨5952436050, 3049, 19, 7⟩,
    ⟨6945426237, 3050, 5, 5⟩,
    ⟨8103699633, 3051, 5, 7⟩,
    ⟨4726396899, 3053, 5, 5⟩,
    ⟨5513775960, 3054, 13, 13⟩,
    ⟨6433868655, 3055, 7, 7⟩,
    ⟨7505049099, 3056, 5, 7⟩,
    ⟨4379641002, 3058, 5, 5⟩,
    ⟨5108316621, 3059, 5, 5⟩,
    ⟨5959335048, 3060, 5, 5⟩ ]

private theorem certificateVerified :
    checkProthChain certificateRungs 237952617733822117836785444486503936290182495276806449612599457700039100028115230384352378913592176876934028153847147527271492443946323848057020754857442167451235018928418454782130294372329914828052571354945056440410039861516367734762707615462996988759646163898794903053141636626387975730138701122898645675419328428402609020156404239568458989159286908809980778558487395163532097741381098688355666769001293538516494442631527317281346623725367476077424923737602104283795077845310536780240107535666658474997239340622463182089324766484814627176578066331432774465437785064152596109807499948991300490654728683354797930546019353210306273948507118291525240424596629340075898313269443975300054271865845043067382734414200687397412463460698153552533195771308066125753703202901064843040617271765243648071610747813450160507011251201339215525489531463169476236039234447076140999071616141334793510225034295176114299029422072 84524874568552531275119190787516448500872644056653766480930295261454586318475202526747310381689212209635657510713946274807490576154354815067620006413772512203569956708865574453339721101704669985976193230108535834485726063789084996743620288466270224317532847052262659137988051969992356104654289953304835910347225996967958357365392728654102038584499952971856935329568245807508991383304124891064757133374419270803286933293128542624979048759028970719066204834830794446484949036303234647690530210777700200889220953901601548593139624400197572784222320267893861617552982382278720272449905700056355088146069900200020206497717672257509591861815974245094149456854149974227309039568841465201297222038146802727066161706631152166223998483022140691146751446528962955899231111903230079989769821048388631388497653392755165095061152946191633131600869567721500482391176761172392606478364324041545490507266703420287419055937532184020907157967318548472 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 237952617733822117836785444486503936290182495276806449612599457700039100028115230384352378913592176876934028153847147527271492443946323848057020754857442167451235018928418454782130294372329914828052571354945056440410039861516367734762707615462996988759646163898794903053141636626387975730138701122898645675419328428402609020156404239568458989159286908809980778558487395163532097741381098688355666769001293538516494442631527317281346623725367476077424923737602104283795077845310536780240107535666658474997239340622463182089324766484814627176578066331432774465437785064152596109807499948991300490654728683354797930546019353210306273948507118291525240424596629340075898313269443975300054271865845043067382734414200687397412463460698153552533195771308066125753703202901064843040617271765243648071610747813450160507011251201339215525489531463169476236039234447076140999071616141334793510225034295176114299029422072 < f (k - 1))
    (hhi : f (k - 1) ≤ 84524874568552531275119190787516448500872644056653766480930295261454586318475202526747310381689212209635657510713946274807490576154354815067620006413772512203569956708865574453339721101704669985976193230108535834485726063789084996743620288466270224317532847052262659137988051969992356104654289953304835910347225996967958357365392728654102038584499952971856935329568245807508991383304124891064757133374419270803286933293128542624979048759028970719066204834830794446484949036303234647690530210777700200889220953901601548593139624400197572784222320267893861617552982382278720272449905700056355088146069900200020206497717672257509591861815974245094149456854149974227309039568841465201297222038146802727066161706631152166223998483022140691146751446528962955899231111903230079989769821048388631388497653392755165095061152946191633131600869567721500482391176761172392606478364324041545490507266703420287419055937532184020907157967318548472) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact proth_chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

