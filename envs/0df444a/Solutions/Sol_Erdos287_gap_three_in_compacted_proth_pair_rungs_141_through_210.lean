-- Prove2me | solution 1 for Erdos287.gap_three_in_compacted_proth_pair_rungs_141_through_210
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:13:33.062588+00:00
-- url     : https://prove2.me/submissions/b605ea4e-dac9-4f4f-a1f1-18455eacc1b4

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
  [ ⟨6952435149, 3061, 5, 5⟩,
    ⟨8112205245, 3062, 11, 7⟩,
    ⟨4733362698, 3064, 5, 5⟩,
    ⟨5523696834, 3065, 5, 5⟩,
    ⟨6440298981, 3066, 5, 11⟩,
    ⟨7514273406, 3067, 5, 5⟩,
    ⟨4383119400, 3069, 13, 7⟩,
    ⟨5112832740, 3070, 11, 7⟩,
    ⟨5964559140, 3071, 7, 13⟩,
    ⟨6962305263, 3072, 5, 5⟩,
    ⟨8120416605, 3073, 11, 11⟩,
    ⟨4735875771, 3075, 5, 5⟩,
    ⟨5529753618, 3076, 5, 5⟩,
    ⟨6447052329, 3077, 5, 5⟩,
    ⟨7521048366, 3078, 5, 7⟩,
    ⟨4389608784, 3080, 5, 13⟩,
    ⟨5118925632, 3081, 5, 7⟩,
    ⟨5971154856, 3082, 5, 11⟩,
    ⟨6969582708, 3083, 5, 7⟩,
    ⟨8129148390, 3084, 17, 7⟩,
    ⟨4745657991, 3086, 5, 7⟩,
    ⟨5530972185, 3087, 7, 11⟩,
    ⟨6453249114, 3088, 5, 7⟩,
    ⟨7528506414, 3089, 5, 5⟩,
    ⟨4395910548, 3091, 5, 7⟩,
    ⟨5123593734, 3092, 5, 17⟩,
    ⟨5978422365, 3093, 23, 7⟩,
    ⟨6973719147, 3094, 5, 5⟩,
    ⟨8135887533, 3095, 5, 7⟩,
    ⟨4746009009, 3097, 5, 5⟩,
    ⟨5537557446, 3098, 5, 11⟩,
    ⟨6460892928, 3099, 5, 11⟩,
    ⟨7538773398, 3100, 5, 5⟩,
    ⟨4398634566, 3102, 5, 11⟩,
    ⟨5129710716, 3103, 5, 5⟩,
    ⟨5983950624, 3104, 5, 13⟩,
    ⟨6982980435, 3105, 7, 11⟩,
    ⟨8144524740, 3106, 7, 13⟩,
    ⟨4751494815, 3108, 7, 11⟩,
    ⟨5543300709, 3109, 5, 5⟩,
    ⟨6470753532, 3110, 5, 5⟩,
    ⟨7545116733, 3111, 5, 13⟩,
    ⟨4401093222, 3113, 5, 11⟩,
    ⟨5135019012, 3114, 5, 5⟩,
    ⟨5992320330, 3115, 11, 7⟩,
    ⟨6992547144, 3116, 5, 7⟩,
    ⟨8153661594, 3117, 5, 5⟩,
    ⟨4759787841, 3119, 5, 5⟩,
    ⟨5548608255, 3120, 7, 7⟩,
    ⟨6476011599, 3121, 5, 5⟩,
    ⟨7553744940, 3122, 17, 11⟩,
    ⟨4405536879, 3124, 5, 13⟩,
    ⟨5140338777, 3125, 5, 11⟩,
    ⟨5996870112, 3126, 5, 5⟩,
    ⟨6996203610, 3127, 7, 7⟩,
    ⟨4083461760, 3129, 13, 13⟩,
    ⟨4761420717, 3130, 5, 5⟩,
    ⟨5554532250, 3131, 7, 11⟩,
    ⟨6481297425, 3132, 7, 7⟩,
    ⟨7560983955, 3133, 13, 11⟩,
    ⟨4411098078, 3135, 5, 7⟩,
    ⟨5147881173, 3136, 5, 5⟩,
    ⟨6002680500, 3137, 11, 7⟩,
    ⟨7003597626, 3138, 5, 11⟩,
    ⟨4085571393, 3140, 5, 5⟩,
    ⟨4766377335, 3141, 11, 7⟩,
    ⟨5561355405, 3142, 7, 7⟩,
    ⟨6489518250, 3143, 11, 7⟩,
    ⟨7569408153, 3144, 5, 5⟩,
    ⟨4415820516, 3146, 5, 7⟩ ]

private theorem certificateVerified :
    checkProthChain certificateRungs 84524874568552531275119190787516448500872644056653766480930295261454586318475202526747310381689212209635657510713946274807490576154354815067620006413772512203569956708865574453339721101704669985976193230108535834485726063789084996743620288466270224317532847052262659137988051969992356104654289953304835910347225996967958357365392728654102038584499952971856935329568245807508991383304124891064757133374419270803286933293128542624979048759028970719066204834830794446484949036303234647690530210777700200889220953901601548593139624400197572784222320267893861617552982382278720272449905700056355088146069900200020206497717672257509591861815974245094149456854149974227309039568841465201297222038146802727066161706631152166223998483022140691146751446528962955899231111903230079989769821048388631388497653392755165095061152946191633131600869567721500482391176761172392606478364324041545490507266703420287419055937532184020907157967318548472 4845937089439660777324251863055270114111534644426658071721476411828638550153525959580540351005891701150188927638672695875717623157002375397002441437388186713462027920489844182456177012959523679408037125986542341642667792228532921383742672999072944446365011225984293364983782945821328684240186716202441653035607163901751883369902943881459006817217780525155286960767120041454961893903974799902754521774901207617757221435903450565204091947818120252392001854502299993418348252527549857793306985733778921676135164874112205339045422527947983525367824183314057712470857249415711383867367476910652286816712015223429167145891907442382026500598613032805857573593720015450524750925480052589571902938391084284984158761513088063126657517273956025430820039677276681059421708414142356784059524743288551173809665739191579827972309622105756428071464649737380683603672233500670491037977007485945054674269142949435969278600137134195567294797111726618770394270925857780651786232 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 84524874568552531275119190787516448500872644056653766480930295261454586318475202526747310381689212209635657510713946274807490576154354815067620006413772512203569956708865574453339721101704669985976193230108535834485726063789084996743620288466270224317532847052262659137988051969992356104654289953304835910347225996967958357365392728654102038584499952971856935329568245807508991383304124891064757133374419270803286933293128542624979048759028970719066204834830794446484949036303234647690530210777700200889220953901601548593139624400197572784222320267893861617552982382278720272449905700056355088146069900200020206497717672257509591861815974245094149456854149974227309039568841465201297222038146802727066161706631152166223998483022140691146751446528962955899231111903230079989769821048388631388497653392755165095061152946191633131600869567721500482391176761172392606478364324041545490507266703420287419055937532184020907157967318548472 < f (k - 1))
    (hhi : f (k - 1) ≤ 4845937089439660777324251863055270114111534644426658071721476411828638550153525959580540351005891701150188927638672695875717623157002375397002441437388186713462027920489844182456177012959523679408037125986542341642667792228532921383742672999072944446365011225984293364983782945821328684240186716202441653035607163901751883369902943881459006817217780525155286960767120041454961893903974799902754521774901207617757221435903450565204091947818120252392001854502299993418348252527549857793306985733778921676135164874112205339045422527947983525367824183314057712470857249415711383867367476910652286816712015223429167145891907442382026500598613032805857573593720015450524750925480052589571902938391084284984158761513088063126657517273956025430820039677276681059421708414142356784059524743288551173809665739191579827972309622105756428071464649737380683603672233500670491037977007485945054674269142949435969278600137134195567294797111726618770394270925857780651786232) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact proth_chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

