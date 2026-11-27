-- Prove2me | solution 1 for Erdos287.gap_three_in_public_certificate_rungs_1028_through_1091
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T23:11:38.495246+00:00
-- url     : https://prove2.me/submissions/82b166fb-9043-4356-a43c-ad57a7ee6a93

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
  [ ⟨73947899, 1822, 4, 96, 3, 3⟩,
    ⟨85768093, 1827, 0, 6, 3, 2⟩,
    ⟨103304381, 1824, 4, 96, 3, 3⟩,
    ⟨123188311, 1827, 2, 24, 3, 3⟩,
    ⟨69420313, 1827, 4, 96, 3, 3⟩,
    ⟨85666457, 1830, 2, 24, 3, 3⟩,
    ⟨103136881, 1831, 2, 24, 3, 3⟩,
    ⟨123995999, 1832, 2, 24, 3, 3⟩,
    ⟨68681849, 1836, 0, 6, 3, 2⟩,
    ⟨82076707, 1833, 4, 96, 3, 3⟩,
    ⟨99279119, 1836, 2, 24, 3, 3⟩,
    ⟨118910173, 1839, 0, 6, 3, 2⟩,
    ⟨72788257, 1837, 4, 96, 3, 3⟩,
    ⟨88717229, 1842, 0, 6, 3, 2⟩,
    ⟨106234867, 1839, 4, 96, 3, 3⟩,
    ⟨131334107, 1842, 2, 24, 3, 3⟩,
    ⟨81784121, 1846, 0, 6, 3, 2⟩,
    ⟨100451887, 1847, 0, 6, 3, 2⟩,
    ⟨125488289, 1844, 4, 96, 3, 3⟩,
    ⟨78402971, 1846, 4, 96, 3, 3⟩,
    ⟨92049847, 1847, 4, 96, 3, 3⟩,
    ⟨110092919, 1852, 0, 6, 3, 2⟩,
    ⟨68727881, 1854, 0, 6, 3, 2⟩,
    ⟨83972167, 1851, 4, 96, 3, 3⟩,
    ⟨95122421, 1854, 2, 24, 3, 3⟩,
    ⟨116925841, 1855, 2, 24, 3, 3⟩,
    ⟨61248553, 1855, 4, 96, 3, 3⟩,
    ⟨73338809, 1856, 4, 96, 3, 3⟩,
    ⟨87157537, 1857, 4, 96, 3, 3⟩,
    ⟨104745401, 1862, 0, 6, 3, 2⟩,
    ⟨124298077, 1859, 4, 96, 3, 3⟩,
    ⟨76813993, 1863, 2, 24, 3, 3⟩,
    ⟨95928179, 1866, 0, 6, 3, 2⟩,
    ⟨114068503, 1867, 0, 6, 3, 2⟩,
    ⟨69255073, 1867, 2, 24, 3, 3⟩,
    ⟨86271299, 1868, 2, 24, 3, 3⟩,
    ⟨107315557, 1867, 4, 96, 3, 3⟩,
    ⟨129764501, 1870, 2, 24, 3, 3⟩,
    ⟨79673129, 1874, 0, 6, 3, 2⟩,
    ⟨94140457, 1875, 0, 6, 3, 2⟩,
    ⟨116688917, 1874, 2, 24, 3, 3⟩,
    ⟨70081301, 1874, 4, 96, 3, 3⟩,
    ⟨87345607, 1875, 4, 96, 3, 3⟩,
    ⟨107567171, 1878, 2, 24, 3, 3⟩,
    ⟨66356501, 1882, 0, 6, 3, 2⟩,
    ⟨81544327, 1879, 4, 96, 3, 3⟩,
    ⟨100024157, 1882, 2, 24, 3, 3⟩,
    ⟨120779821, 1883, 2, 24, 3, 3⟩,
    ⟨71728777, 1883, 4, 96, 3, 3⟩,
    ⟨86629541, 1884, 4, 96, 3, 3⟩,
    ⟨108141337, 1889, 0, 6, 3, 2⟩,
    ⟨67413373, 1887, 4, 96, 3, 3⟩,
    ⟨82133339, 1892, 0, 6, 3, 2⟩,
    ⟨102059053, 1889, 4, 96, 3, 3⟩,
    ⟨125881169, 1890, 4, 96, 3, 3⟩,
    ⟨77410391, 1892, 4, 96, 3, 3⟩,
    ⟨95617597, 1893, 4, 96, 3, 3⟩,
    ⟨118702271, 1894, 4, 96, 3, 3⟩,
    ⟨72397571, 1900, 0, 6, 3, 2⟩,
    ⟨89192743, 1901, 0, 6, 3, 2⟩,
    ⟨111007199, 1898, 4, 96, 3, 3⟩,
    ⟨68279039, 1904, 0, 6, 3, 2⟩,
    ⟨75170467, 1901, 4, 96, 3, 3⟩,
    ⟨90222131, 1902, 4, 96, 3, 3⟩ ]

private theorem certificateVerified :
    checkChain certificateRungs 1486734890303526180481761943026768374671808207861422190529131525411094304559094449003721366084506815786640371832274922004490824607862741082257204240904753771534694709312199702185010374078418730481668233466619018932187187553298973578485000194291948689776320087518253212707586914726855761147028209863796629322931347003653902711227276402517761010526150605452815283366520039954457205253239613872432590571724894334516288214606230278582046376838101522636261661588924398098942332998081447529443066029421875754058467633800395696784127017004942605189477185709943029830 5229796815015366576697891942701585646625564493601204679272022210072835802841231155676411126960264420674995672397192054020585027037987476541775427460915385088890504721076128437851519612114221735394044911772864201981931237321532742253617620712830918235635064805112193002968844062891883874451913594946850478871365471806464497512559518594740887259894500929767260944463177689296121337325998486983670360254940566338521659617566878525575362961002025973880212453622665521631965327089854577722635496218486746517055162242150483296130317847580249985582203920737495618973775952965946201436323910 = true := by
  decide +kernel

theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : 1486734890303526180481761943026768374671808207861422190529131525411094304559094449003721366084506815786640371832274922004490824607862741082257204240904753771534694709312199702185010374078418730481668233466619018932187187553298973578485000194291948689776320087518253212707586914726855761147028209863796629322931347003653902711227276402517761010526150605452815283366520039954457205253239613872432590571724894334516288214606230278582046376838101522636261661588924398098942332998081447529443066029421875754058467633800395696784127017004942605189477185709943029830 < f (k - 1))
    (hhi : f (k - 1) ≤ 5229796815015366576697891942701585646625564493601204679272022210072835802841231155676411126960264420674995672397192054020585027037987476541775427460915385088890504721076128437851519612114221735394044911772864201981931237321532742253617620712830918235635064805112193002968844062891883874451913594946850478871365471806464497512559518594740887259894500929767260944463177689296121337325998486983670360254940566338521659617566878525575362961002025973880212453622665521631965327089854577722635496218486746517055162242150483296130317847580249985582203920737495618973775952965946201436323910) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  exact chain_gap k hk f hf1 hmono hsum _ _ _ certificateVerified hlo hhi

