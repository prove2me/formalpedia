-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_964_through_1027
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:11:25.694251+00:00
-- url     : https://prove2.me/submissions/409e2659-37ff-48bd-9cbe-487e0fa67b81

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
  [ ⟨76186087, 1745, 0, 6, 3, 2⟩,
    ⟨94217051, 1742, 4, 96, 3, 3⟩,
    ⟨110769343, 1747, 0, 6, 3, 2⟩,
    ⟨65528167, 1745, 4, 96, 3, 3⟩,
    ⟨74006099, 1746, 4, 96, 3, 3⟩,
    ⟨90990157, 1747, 4, 96, 3, 3⟩,
    ⟨109224551, 1748, 4, 96, 3, 3⟩,
    ⟨68025413, 1752, 2, 24, 3, 3⟩,
    ⟨81791527, 1755, 0, 6, 3, 2⟩,
    ⟨101501291, 1756, 0, 6, 3, 2⟩,
    ⟨124928647, 1753, 4, 96, 3, 3⟩,
    ⟨71911969, 1757, 2, 24, 3, 3⟩,
    ⟨89265797, 1758, 2, 24, 3, 3⟩,
    ⟨111226747, 1757, 4, 96, 3, 3⟩,
    ⟨67195327, 1763, 0, 6, 3, 2⟩,
    ⟨81759401, 1760, 4, 96, 3, 3⟩,
    ⟨100547383, 1765, 0, 6, 3, 2⟩,
    ⟨116518229, 1762, 4, 96, 3, 3⟩,
    ⟨71454917, 1766, 2, 24, 3, 3⟩,
    ⟨80844697, 1765, 4, 96, 3, 3⟩,
    ⟨98880461, 1766, 4, 96, 3, 3⟩,
    ⟨115648957, 1767, 4, 96, 3, 3⟩,
    ⟨72208033, 1771, 2, 24, 3, 3⟩,
    ⟨88751393, 1772, 2, 24, 3, 3⟩,
    ⟨110024923, 1775, 0, 6, 3, 2⟩,
    ⟨68550343, 1777, 0, 6, 3, 2⟩,
    ⟨85459061, 1774, 4, 96, 3, 3⟩,
    ⟨105489547, 1779, 0, 6, 3, 2⟩,
    ⟨131778419, 1780, 0, 6, 3, 2⟩,
    ⟨81766151, 1782, 0, 6, 3, 2⟩,
    ⟨100670893, 1783, 0, 6, 3, 2⟩,
    ⟨125121131, 1782, 2, 24, 3, 3⟩,
    ⟨75891929, 1784, 2, 24, 3, 3⟩,
    ⟨94407343, 1783, 4, 96, 3, 3⟩,
    ⟨117879941, 1788, 0, 6, 3, 2⟩,
    ⟨71556479, 1788, 2, 24, 3, 3⟩,
    ⟨87318667, 1791, 0, 6, 3, 2⟩,
    ⟨108987449, 1788, 4, 96, 3, 3⟩,
    ⟨58867253, 1792, 2, 24, 3, 3⟩,
    ⟨71445553, 1791, 4, 96, 3, 3⟩,
    ⟨88889117, 1794, 2, 24, 3, 3⟩,
    ⟨108427321, 1795, 2, 24, 3, 3⟩,
    ⟨66584047, 1797, 2, 24, 3, 3⟩,
    ⟨82183091, 1798, 2, 24, 3, 3⟩,
    ⟨102710497, 1801, 0, 6, 3, 2⟩,
    ⟨125357783, 1800, 2, 24, 3, 3⟩,
    ⟨71547527, 1802, 2, 24, 3, 3⟩,
    ⟨87700183, 1803, 2, 24, 3, 3⟩,
    ⟨108282509, 1806, 0, 6, 3, 2⟩,
    ⟨56460659, 1804, 4, 96, 3, 3⟩,
    ⟨66111943, 1809, 0, 6, 3, 2⟩,
    ⟨71122223, 1808, 2, 24, 3, 3⟩,
    ⟨82607827, 1809, 2, 24, 3, 3⟩,
    ⟨98688167, 1810, 2, 24, 3, 3⟩,
    ⟨120491233, 1813, 0, 6, 3, 2⟩,
    ⟨69723463, 1811, 4, 96, 3, 3⟩,
    ⟨85683761, 1816, 0, 6, 3, 2⟩,
    ⟨99816193, 1817, 0, 6, 3, 2⟩,
    ⟨120922181, 1818, 0, 6, 3, 2⟩,
    ⟨70068731, 1818, 2, 24, 3, 3⟩,
    ⟨86272987, 1817, 4, 96, 3, 3⟩,
    ⟨104787479, 1822, 0, 6, 3, 2⟩,
    ⟨126887653, 1819, 4, 96, 3, 3⟩,
    ⟨62014243, 1821, 4, 96, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 636836264107884224170981213922020606776871637335787800494260876707575901779301126473150287798281603227628312525625618385353763358302881457937963895588641442433332672557746265798686262058801146826205970685315315997755021351141406643135235290580248208125204643829947256311797521244895290596637340576105551317024592076326205647751850947191424061251762297349475663145357548008768858945602327989878966238401172184816403513211553384277179564271866716409652435035837230493238762860996136287867681823837449237363416857214095383222103666851835 1486734890303526180481761943026768374671808207861422190529131525411094304559094449003721366084506815786640371832274922004490824607862741082257204240904753771534694709312199702185010374078418730481668233466619018932187187553298973578485000194291948689776320087518253212707586914726855761147028209863796629322931347003653902711227276402517761010526150605452815283366520039954457205253239613872432590571724894334516288214606230278582046376838101522636261661588924398098942332998081447529443066029421875754058467633800395696784127017004942605189477185709943029830 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 636836264107884224170981213922020606776871637335787800494260876707575901779301126473150287798281603227628312525625618385353763358302881457937963895588641442433332672557746265798686262058801146826205970685315315997755021351141406643135235290580248208125204643829947256311797521244895290596637340576105551317024592076326205647751850947191424061251762297349475663145357548008768858945602327989878966238401172184816403513211553384277179564271866716409652435035837230493238762860996136287867681823837449237363416857214095383222103666851835 < f (k - 1))
    (hhi : f (k - 1) ≤ 1486734890303526180481761943026768374671808207861422190529131525411094304559094449003721366084506815786640371832274922004490824607862741082257204240904753771534694709312199702185010374078418730481668233466619018932187187553298973578485000194291948689776320087518253212707586914726855761147028209863796629322931347003653902711227276402517761010526150605452815283366520039954457205253239613872432590571724894334516288214606230278582046376838101522636261661588924398098942332998081447529443066029421875754058467633800395696784127017004942605189477185709943029830) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

