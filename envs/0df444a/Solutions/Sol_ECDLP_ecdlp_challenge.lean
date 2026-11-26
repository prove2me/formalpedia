-- Prove2me | solution 1 for ECDLP.ecdlp_challenge
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-26T21:03:22.706615+00:00
-- url     : https://prove2.me/submissions/4e0073a8-b6f6-4972-9ae8-e8ef977978bb

import Mathlib
import Definitions.Def_ECDLPChallengeData

set_option autoImplicit false
set_option maxRecDepth 100000

open ECDLP

/-! # The challenge curve has exactly `5 n` points

Certificate proof, checked by the kernel:
* `n • P = 0` and `5 • R = 0` for an explicit point `R ≠ 0`, by an executable affine double-and-add
  (`smulC`) shown to agree with Mathlib's group law (`smul_rel`), inverses by Fermat (`invC`);
* `n` is prime, by a Pratt certificate (`lucas_primality`, eleven nodes);
* so `addOrderOf P = n`, `addOrderOf R = 5`, hence `5 n ∣ #E`;
* `1 ≤ #E ≤ 2p + 1` (at most two `y` for each `x`), and `2p + 1 < 10 n`, so `#E = 5 n`. -/

/-! ## Square-and-multiply -/

/-- Square-and-multiply with fuel `f` (exact when `e < 2 ^ f`). -/
private def fpow {M : Type*} [Monoid M] (x : M) : ℕ → ℕ → M
  | 0, _ => 1
  | f + 1, e =>
    if e = 0 then 1 else
      let r := fpow x f (e / 2)
      if e % 2 = 0 then r * r else r * r * x

private lemma fpow_eq {M : Type*} [Monoid M] (x : M) :
    ∀ f e, e < 2 ^ f → fpow x f e = x ^ e
  | 0, e, h => by
    have : e = 0 := by simpa using h
    subst this; simp [fpow]
  | f + 1, e, h => by
    have h' : e / 2 < 2 ^ f := by rw [pow_succ] at h; omega
    simp only [fpow]
    split_ifs with h0 h2
    · subst h0; simp
    · rw [fpow_eq x f (e / 2) h', ← pow_add]; congr 1; omega
    · rw [fpow_eq x f (e / 2) h', ← pow_add, ← pow_succ]; congr 1; omega

/-! ## Primality by a Pratt certificate -/

private lemma prime_of_cert (q a : ℕ) (L : List ℕ) (hL : ∀ r ∈ L, r.Prime)
    (hprod : L.prod = q - 1) (hq : q - 1 < 2 ^ 300)
    (h1 : fpow (a : ZMod q) 300 (q - 1) = 1)
    (h2 : ∀ r ∈ L, fpow (a : ZMod q) 300 ((q - 1) / r) ≠ 1) : q.Prime := by
  refine lucas_primality q a ?_ ?_
  · rwa [← fpow_eq _ 300 _ hq]
  · intro r hr hdvd
    rw [← hprod] at hdvd
    obtain ⟨r', hr', hrr'⟩ := (Prime.dvd_prod_iff hr.prime).1 hdvd
    obtain rfl : r = r' := (Nat.prime_dvd_prime_iff_eq hr (hL r' hr')).1 hrr'
    rw [← fpow_eq _ 300 _ (lt_of_le_of_lt (Nat.div_le_self _ _) hq)]
    exact h2 r hr'

private lemma pr_8031641 : Nat.Prime 8031641 := by
  refine prime_of_cert 8031641 3 [2, 2, 2, 5, 199, 1009] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> norm_num

private lemma pr_48189847 : Nat.Prime 48189847 := by
  refine prime_of_cert 48189847 47 [2, 3, 8031641] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_8031641 | norm_num

private lemma pr_14090612407 : Nat.Prime 14090612407 := by
  refine prime_of_cert 14090612407 5 [2, 3, 13, 23, 61, 331, 389] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> norm_num

private lemma pr_1874947822879 : Nat.Prime 1874947822879 := by
  refine prime_of_cert 1874947822879 3 [2, 3, 13, 19, 13399, 94421] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> norm_num

private lemma pr_51107327756035783 : Nat.Prime 51107327756035783 := by
  refine prime_of_cert 51107327756035783 5 [2, 3, 7, 11, 59, 1874947822879] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_1874947822879 | norm_num

private lemma pr_2217595152162583667 : Nat.Prime 2217595152162583667 := by
  refine prime_of_cert 2217595152162583667 2 [2, 11, 4003, 24659, 28687, 35597] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> norm_num

private lemma pr_66527854564877510011 : Nat.Prime 66527854564877510011 := by
  refine prime_of_cert 66527854564877510011 2 [2, 3, 5, 2217595152162583667] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_2217595152162583667 | norm_num

private lemma pr_942356930322483209823491 : Nat.Prime 942356930322483209823491 := by
  refine prime_of_cert 942356930322483209823491 2 [2, 5, 137, 1013, 48189847, 14090612407] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_48189847 | exact pr_14090612407 | norm_num

private lemma pr_58426129679993959009056443 : Nat.Prime 58426129679993959009056443 := by
  refine prime_of_cert 58426129679993959009056443 2 [2, 31, 942356930322483209823491] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_942356930322483209823491 | norm_num

private lemma pr_64467157784386614394756842980429 : Nat.Prime 64467157784386614394756842980429 := by
  refine prime_of_cert 64467157784386614394756842980429 2 [2, 2, 7, 157, 251, 58426129679993959009056443] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_58426129679993959009056443 | norm_num

private lemma prime_n : Nat.Prime n := by
  refine prime_of_cert n 3 [2, 2, 23, 613, 1489, 51107327756035783, 66527854564877510011, 64467157784386614394756842980429] ?_ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  intro r hr
  fin_cases hr <;> first | exact pr_51107327756035783 | exact pr_66527854564877510011 | exact pr_64467157784386614394756842980429 | norm_num

/-! ## Executable affine addition, and its agreement with Mathlib's group law -/

private def slopeC {R : Type*} [CommRing R] [DecidableEq R] (W : WeierstrassCurve R)
    (inv : R → R) (x₁ x₂ y₁ y₂ : R) : R :=
  if x₁ = x₂ then
    if y₁ = W.toAffine.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) * inv (y₁ - W.toAffine.negY x₁ y₁)
  else (y₁ - y₂) * inv (x₁ - x₂)

private def addC {R : Type*} [CommRing R] [DecidableEq R] (W : WeierstrassCurve R)
    (inv : R → R) : Option (R × R) → Option (R × R) → Option (R × R)
  | none, r => r
  | some q, none => some q
  | some (x₁, y₁), some (x₂, y₂) =>
    if x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂ then none
    else
      let l := slopeC W inv x₁ x₂ y₁ y₂
      some (W.toAffine.addX x₁ x₂ l, W.toAffine.addY x₁ x₂ y₁ l)

private def smulC {R : Type*} [CommRing R] [DecidableEq R] (W : WeierstrassCurve R)
    (inv : R → R) : ℕ → ℕ → Option (R × R) → Option (R × R)
  | 0, _, _ => none
  | f + 1, k, r =>
    if k = 0 then none else
      let h := smulC W inv f (k / 2) r
      let d := addC W inv h h
      if k % 2 = 0 then d else addC W inv d r

/-- `r` represents the point `P`. -/
private def RepC {F : Type*} [Field F] (W : WeierstrassCurve F) :
    Option (F × F) → W.toAffine.Point → Prop
  | none, P => P = 0
  | some (x, y), P => ∃ h : W.toAffine.Nonsingular x y, P = .some x y h

section group
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (inv : F → F)

private lemma slopeC_eq (hinv : ∀ z, inv z = z⁻¹) (x₁ x₂ y₁ y₂ : F) :
    slopeC W inv x₁ x₂ y₁ y₂ = W.toAffine.slope x₁ x₂ y₁ y₂ := by
  simp only [slopeC, WeierstrassCurve.Affine.slope, hinv, div_eq_mul_inv]

private lemma add_rel (hinv : ∀ z, inv z = z⁻¹) :
    ∀ (r₁ r₂ : Option (F × F)) (P₁ P₂ : W.toAffine.Point),
      RepC W r₁ P₁ → RepC W r₂ P₂ → RepC W (addC W inv r₁ r₂) (P₁ + P₂)
  | none, r₂, P₁, P₂, h₁, h₂ => by
    simp only [RepC] at h₁; subst h₁; simpa [addC] using h₂
  | some (x, y), none, P₁, P₂, h₁, h₂ => by
    simp only [RepC] at h₂; subst h₂; simpa [addC] using h₁
  | some (x₁, y₁), some (x₂, y₂), P₁, P₂, ⟨h₁, e₁⟩, ⟨h₂, e₂⟩ => by
    subst e₁ e₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · simp only [addC, if_pos hxy, RepC]
      exact WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2
    · simp only [addC, if_neg hxy, RepC, slopeC_eq W inv hinv]
      exact ⟨_, WeierstrassCurve.Affine.Point.add_some hxy⟩

private lemma smul_rel (hinv : ∀ z, inv z = z⁻¹) (r : Option (F × F)) (P : W.toAffine.Point)
    (hr : RepC W r P) : ∀ f k, k < 2 ^ f → RepC W (smulC W inv f k r) (k • P)
  | 0, k, hk => by
    have : k = 0 := by simpa using hk
    subst this; simp [smulC, RepC]
  | f + 1, k, hk => by
    have hk' : k / 2 < 2 ^ f := by rw [pow_succ] at hk; omega
    have ih := smul_rel hinv r P hr f (k / 2) hk'
    have hd := add_rel W inv hinv _ _ _ _ ih ih
    simp only [smulC]
    split_ifs with h0 h2
    · subst h0; simp [RepC]
    · have : k • P = (k / 2) • P + (k / 2) • P := by rw [← add_nsmul]; congr 1; omega
      rw [this]; exact hd
    · have : k • P = ((k / 2) • P + (k / 2) • P) + P := by
        rw [← add_nsmul, ← succ_nsmul]; congr 1; omega
      rw [this]; exact add_rel W inv hinv _ _ _ _ hd hr

end group

/-- Inversion in `ZMod q` by Fermat's little theorem. -/
private def invC (q : ℕ) (z : ZMod q) : ZMod q := if z = 0 then 0 else fpow z 300 (q - 2)

private lemma invC_eq (q : ℕ) [Fact q.Prime] (hq : q - 2 < 2 ^ 300) (z : ZMod q) :
    invC q z = z⁻¹ := by
  unfold invC
  split_ifs with hz
  · subst hz; simp
  · rw [fpow_eq _ _ _ hq]
    have h2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    have : z * z ^ (q - 2) = 1 := by
      rw [← pow_succ', show q - 2 + 1 = q - 1 by omega]
      exact ZMod.pow_card_sub_one_eq_one hz
    exact (inv_eq_of_mul_eq_one_right this).symm

private lemma smul_zero_of_comp {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (inv : F → F) (hinv : ∀ z, inv z = z⁻¹) (x y : F) (h : W.toAffine.Nonsingular x y) (k : ℕ)
    (hk : k < 2 ^ 300) (hc : smulC W inv 300 k (some (x, y)) = none) :
    k • (WeierstrassCurve.Affine.Point.some x y h) = 0 := by
  have := smul_rel W inv hinv (some (x, y)) _ ⟨h, rfl⟩ 300 k hk
  rw [hc] at this
  exact this

/-! ## The concrete computations -/

private def xR : ZMod p :=
  59478933167960706327322975773189757209782373269190575739786012634213120493300
private def yR : ZMod p :=
  11619245355697056842657563206942848512637989390255921718444119326134982764566

private lemma nonsingular_R : E.toAffine.Nonsingular xR yR := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  exact ⟨by decide, Or.inr (by decide)⟩

private lemma comp_nP : smulC E (invC p) 300 n (some (xP, yP)) = none := by decide +kernel

private lemma comp_5R : smulC E (invC p) 300 5 (some (xR, yR)) = none := by decide +kernel

private lemma disc_ne : E.Δ ≠ 0 := by decide +kernel

/-! ## Counting points: `1 ≤ #E ≤ 2q + 1` -/

private def ptEquiv {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.toAffine.Point ≃ Option {xy : F × F // W.toAffine.Equation xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2 ((W.toAffine.equation_iff_nonsingular).1 xy.2)
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | ⟨⟨x, y⟩, h⟩) <;> rfl

private lemma card_point_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    Nat.card W.toAffine.Point = (Finset.univ.filter (fun xy : F × F =>
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card + 1 := by
  classical
  rw [Nat.card_congr (ptEquiv W), Nat.card_eq_fintype_card, Fintype.card_option,
    Fintype.card_subtype]
  congr 2
  ext xy
  simp [WeierstrassCurve.Affine.equation_iff]

private lemma card_filter_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (f : F → F) :
    ((Finset.univ.filter (fun xy : F × F => xy.2 ^ 2 = f xy.1)).card : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (f x) := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  have h : ∀ x : F, (∑ y : F, if y ^ 2 = f x then (1 : ℤ) else 0) =
      quadraticChar F (f x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hF (f x), Set.toFinset_ofPred, Finset.card_filter]
    push_cast; rfl
  rw [Finset.sum_congr rfl (fun x _ => h x), Finset.sum_add_distrib]
  simp [add_comm]

private lemma card_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) [W.IsElliptic] (h₁ : W.a₁ = 0)
    (h₃ : W.a₃ = 0) : Nat.card W.toAffine.Point ≤ 2 * Fintype.card F + 1 := by
  rw [card_point_eq]
  have key := card_filter_sq hF (fun x => x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hsum : ∑ x : F, quadraticChar F (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) ≤
      ∑ _x : F, (1 : ℤ) := by
    apply Finset.sum_le_sum
    intro x _
    rcases quadraticChar_isQuadratic F (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) with h | h | h <;>
      rw [h] <;> norm_num
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have hfilt : (Finset.univ.filter (fun xy : F × F =>
      xy.2 ^ 2 + W.a₁ * xy.1 * xy.2 + W.a₃ * xy.2 =
        xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)) =
      Finset.univ.filter (fun xy : F × F =>
        xy.2 ^ 2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆) := by
    ext xy; simp [h₁, h₃]
  rw [hfilt]
  have : ((Finset.univ.filter (fun xy : F × F =>
      xy.2 ^ 2 = xy.1 ^ 3 + W.a₂ * xy.1 ^ 2 + W.a₄ * xy.1 + W.a₆)).card : ℤ) ≤
      2 * Fintype.card F := by rw [key]; linarith
  omega

private theorem card_aux [Fact (Nat.Prime ECDLP.p)] :
    Nat.card ECDLP.E.toAffine.Point = ECDLP.h * ECDLP.n := by
  have hp2 : p - 2 < 2 ^ 300 := by decide +kernel
  have hinv : ∀ z, invC p z = z⁻¹ := invC_eq p hp2
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.2 disc_ne⟩
  have hnP : n • P = 0 :=
    smul_zero_of_comp E (invC p) hinv xP yP nonsingular_P n (by decide +kernel) comp_nP
  let R : E.toAffine.Point := .some _ _ nonsingular_R
  have h5R : 5 • R = 0 :=
    smul_zero_of_comp E (invC p) hinv xR yR nonsingular_R 5 (by decide +kernel) comp_5R
  have : Fact n.Prime := ⟨prime_n⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hoP : addOrderOf P = n := addOrderOf_eq_prime hnP (fun h => WeierstrassCurve.Affine.Point.some_ne_zero _ h)
  have hoR : addOrderOf R = 5 := addOrderOf_eq_prime h5R (fun h => WeierstrassCurve.Affine.Point.some_ne_zero _ h)
  have d1 : n ∣ Nat.card E.toAffine.Point := hoP ▸ addOrderOf_dvd_natCard P
  have d5 : 5 ∣ Nat.card E.toAffine.Point := hoR ▸ addOrderOf_dvd_natCard R
  have hcop : Nat.Coprime 5 n := (Nat.coprime_primes (by norm_num) prime_n).2 (by decide +kernel)
  obtain ⟨k, hk⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop d5 d1
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; decide +kernel
  have hle := card_le hchar E rfl rfl
  rw [ZMod.card] at hle
  have hpos : 1 ≤ Nat.card E.toAffine.Point := by rw [card_point_eq]; omega
  have hbig : 2 * p + 1 < 10 * n := by decide +kernel
  have hn0 : 0 < n := prime_n.pos
  have hk1 : k = 1 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [hk] at hpos; simp at hpos
      · rfl
    · exfalso
      have : 5 * n * 2 ≤ 5 * n * k := Nat.mul_le_mul_left _ h
      omega
  rw [hk, hk1]
  show 5 * n * 1 = 5 * n
  ring


private lemma comp_nQ : smulC E (invC p) 300 n (some (xQ, yQ)) = none := by decide +kernel

theorem solution [Fact (Nat.Prime ECDLP.p)] :
    ∃ x : ℕ, 1 ≤ x ∧ x < ECDLP.n ∧ ECDLP.Q = x • ECDLP.P := by
  have hp2 : p - 2 < 2 ^ 300 := by decide +kernel
  have hinv : ∀ z, invC p z = z⁻¹ := invC_eq p hp2
  have : E.IsElliptic := ⟨isUnit_iff_ne_zero.2 disc_ne⟩
  have hnQ : n • Q = 0 :=
    smul_zero_of_comp E (invC p) hinv xQ yQ nonsingular_Q n (by decide +kernel) comp_nQ
  have hnP : n • P = 0 :=
    smul_zero_of_comp E (invC p) hinv xP yP nonsingular_P n (by decide +kernel) comp_nP
  have : Fact n.Prime := ⟨prime_n⟩
  have hP0 : P ≠ 0 := fun h => WeierstrassCurve.Affine.Point.some_ne_zero _ h
  have hQ0 : Q ≠ 0 := fun h => WeierstrassCurve.Affine.Point.some_ne_zero _ h
  have hoP : addOrderOf P = n := addOrderOf_eq_prime hnP hP0
  have hcard : Nat.card E.toAffine.Point = 5 * n := card_aux
  -- `Q` lies in the subgroup generated by `P`: its image in the quotient (of order 5) is killed by
  -- both `n` and `5`.
  have hcardZ : Nat.card (E.toAffine.Point ⧸ AddSubgroup.zmultiples P) = 5 := by
    have h1 := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (AddSubgroup.zmultiples P))
    rw [Nat.card_zmultiples, hoP, hcard] at h1
    have hn0 : 0 < n := prime_n.pos
    nlinarith [h1]
  have h5 : (5 : ℕ) • (QuotientAddGroup.mk Q : E.toAffine.Point ⧸ AddSubgroup.zmultiples P) = 0 := by
    rw [← hcardZ]; exact card_nsmul_eq_zero'
  have hn : n • (QuotientAddGroup.mk Q : E.toAffine.Point ⧸ AddSubgroup.zmultiples P) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, hnQ]; rfl
  have hcop : Nat.Coprime 5 n := (Nat.coprime_primes (by norm_num) prime_n).2 (by decide +kernel)
  have hmk : (QuotientAddGroup.mk Q : E.toAffine.Point ⧸ AddSubgroup.zmultiples P) = 0 := by
    have := addOrderOf_dvd_of_nsmul_eq_zero h5
    have := addOrderOf_dvd_of_nsmul_eq_zero hn
    have : addOrderOf (QuotientAddGroup.mk Q : E.toAffine.Point ⧸ AddSubgroup.zmultiples P) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop ‹_› ‹_›
    exact AddMonoid.addOrderOf_eq_one_iff.1 this
  have hmem : Q ∈ AddSubgroup.zmultiples P := (QuotientAddGroup.eq_zero_iff Q).1 hmk
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 hmem
  have hn0 : 0 < n := prime_n.pos
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn0
  have hnn : (0 : ℤ) ≤ k % (n : ℤ) := Int.emod_nonneg _ hnZ.ne'
  have hlt : k % (n : ℤ) < n := Int.emod_lt_of_pos _ hnZ
  have hkP : k • P = (k % (n : ℤ)) • P := by
    have := mod_addOrderOf_zsmul P k
    rw [hoP] at this
    exact this.symm
  have hcast : (((k % (n : ℤ)).toNat : ℕ) : ℤ) = k % (n : ℤ) := Int.toNat_of_nonneg hnn
  have hQx : Q = (k % (n : ℤ)).toNat • P := by
    rw [← hk, hkP, ← natCast_zsmul, hcast]
  refine ⟨(k % (n : ℤ)).toNat, ?_, ?_, hQx⟩
  · by_contra h0
    have : (k % (n : ℤ)).toNat = 0 := by omega
    rw [this, zero_nsmul] at hQx
    exact hQ0 hQx
  · omega
