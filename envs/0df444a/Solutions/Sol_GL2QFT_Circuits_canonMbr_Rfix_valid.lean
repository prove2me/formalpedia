-- Prove2me | solution 1 for GL2QFT.Circuits.canonMbr_Rfix_valid
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T07:02:22.738809+00:00
-- url     : https://prove2.me/submissions/8fb3b05c-efdb-4f81-8b58-831abe7f3e79

import Definitions.Def_GL2QFT_Circuits_Leaves

noncomputable section

open Classical

namespace GL2QFT_CanonMbrRfixValid_Aux

open GL2QFT FieldData Circuits Supplement AGammaGates
open scoped Matrix ComplexConjugate

/-! ### Layer 1: Finite field structure, characters, and Gauss sums -/

private lemma q_pos (D : FieldData) : 0 < D.q := by
  have := D.one_lt_q
  omega

private lemma q_sq_sub_one_ne_zero (D : FieldData) : D.q ^ 2 - 1 ≠ 0 := by
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
  omega

private lemma q_sq_sub_one_eq_mul (D : FieldData) :
    D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
  have hq := D.one_lt_q
  zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]
  ring

private lemma finrank_fq (D : FieldData) : Module.finrank (ZMod D.p) D.Fq = D.r := by
  have h := (AdjoinRoot.powerBasis' D.f_monic).finrank
  rwa [AdjoinRoot.powerBasis'_dim, D.f_deg] at h

private lemma finrank_fq2 (D : FieldData) : Module.finrank D.Fq D.Fq2 = 2 := by
  have h := (AdjoinRoot.powerBasis' D.F_monic).finrank
  rwa [AdjoinRoot.powerBasis'_dim, D.F_deg] at h

private lemma card_fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod D.p) (V := D.Fq),
    Nat.card_zmod, finrank_fq, FieldData.q]

private lemma natCard_fq (D : FieldData) : Nat.card D.Fq = D.q := by
  rw [← Fintype.card_eq_nat_card, card_fq]

private lemma card_fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := D.Fq) (V := D.Fq2),
    natCard_fq, finrank_fq2]

private lemma natCard_fq2 (D : FieldData) : Nat.card D.Fq2 = D.q ^ 2 := by
  rw [← Fintype.card_eq_nat_card, card_fq2]

private lemma charP_fq (D : FieldData) : CharP D.Fq D.p := by
  have : Fact D.p.Prime := ⟨D.hp⟩
  exact (Algebra.charP_iff (ZMod D.p) D.Fq D.p).mp (ZMod.charP D.p)

private lemma charP_fq2 (D : FieldData) : CharP D.Fq2 D.p := by
  have : CharP D.Fq D.p := charP_fq D
  exact (Algebra.charP_iff D.Fq D.Fq2 D.p).mp this

private lemma ringChar_fq (D : FieldData) : ringChar D.Fq = D.p :=
  (@ringChar.eq_iff D.Fq _ D.p).mpr (charP_fq D)

private lemma fq_isDomain (D : FieldData) : IsDomain D.Fq :=
  AdjoinRoot.isDomain_of_prime D.f_irr.prime

private lemma fq2_isDomain (D : FieldData) : IsDomain D.Fq2 :=
  have := fq_isDomain D
  AdjoinRoot.isDomain_of_prime D.F_irr.prime

private lemma fq2_pow_ne_zero (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) (n : ℕ) : z ^ n ≠ 0 := by
  have := fq2_isDomain D
  exact pow_ne_zero n hz

private lemma fq_pow_q (D : FieldData) (x : D.Fq) : x ^ D.q = x := by
  simpa [card_fq D] using FiniteField.pow_card x

private lemma fq2_pow_q_sq (D : FieldData) (z : D.Fq2) : z ^ D.q ^ 2 = z := by
  simpa [card_fq2 D] using FiniteField.pow_card z

private def fq2Frob (D : FieldData) : D.Fq2 →+* D.Fq2 :=
  letI : CharP D.Fq2 D.p := charP_fq2 D
  (frobenius D.Fq2 D.p) ^ D.r

private lemma fq2Frob_apply (D : FieldData) (z : D.Fq2) : fq2Frob D z = z ^ D.q := by
  have : CharP D.Fq2 D.p := charP_fq2 D
  simp [fq2Frob, iterate_frobenius, FieldData.q]

private lemma fq2_sub_pow_q (D : FieldData) (z w : D.Fq2) :
    (z - w) ^ D.q = z ^ D.q - w ^ D.q := by
  simpa [fq2Frob_apply] using (fq2Frob D).map_sub z w

private lemma field_div_zero {K : Type*} [Field K] (a : K) : a / 0 = 0 := div_zero a
private lemma field_zero_pow {K : Type*} [Field K] {n : ℕ} (hn : n ≠ 0) : (0 : K) ^ n = 0 := zero_pow hn
private lemma field_div_pow {K : Type*} [Field K] (a b : K) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n := div_pow a b n
private lemma field_mul_inv {K : Type*} [Field K] (a b : K) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev, mul_comm]
private lemma field_pow_eq_zero {K : Type*} [Field K] {a : K} {n : ℕ} (h : a ^ n = 0) : a = 0 :=
  eq_zero_of_pow_eq_zero h
private lemma field_div_eq_one_iff_eq {K : Type*} [Field K] {a b : K} (hb : b ≠ 0) :
    a / b = 1 ↔ a = b := div_eq_one_iff_eq hb
private lemma field_mul_eq_zero {K : Type*} [Field K] {a b : K} :
    a * b = 0 ↔ a = 0 ∨ b = 0 := mul_eq_zero
private lemma field_div_eq_div_iff {K : Type*} [Field K] {a b c d : K}
    (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b := div_eq_div_iff hb hd
private lemma field_inv_inv {K : Type*} [Field K] (a : K) : a⁻¹⁻¹ = a := inv_inv a

private lemma fq2_div_pow_q (D : FieldData) (z w : D.Fq2) :
    (z / w) ^ D.q = z ^ D.q / w ^ D.q := by
  by_cases hw : w = 0
  · subst hw; rw [field_div_zero, field_zero_pow (q_pos D).ne', field_div_zero]
  · have hwq : w ^ D.q ≠ 0 := fq2_pow_ne_zero D hw D.q
    apply mul_right_cancel₀ hwq
    rw [div_mul_cancel₀ _ hwq, ← fq2Frob_apply, ← fq2Frob_apply, ← fq2Frob_apply,
      ← (fq2Frob D).map_mul, div_mul_cancel₀ _ hw]

private lemma algebraMap_tr (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.tr z) = z + z ^ D.q := by
  have h := FiniteField.algebraMap_trace_eq_sum_pow D.Fq D.Fq2 z
  rw [finrank_fq2, natCard_fq, Finset.sum_range_succ, Finset.sum_range_one] at h
  simpa [FieldData.tr] using h

private lemma algebraMap_nrm (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.nrm z) = z ^ (D.q + 1) := by
  have h := FiniteField.algebraMap_norm_eq_pow_sum D.Fq D.Fq2 z
  rw [finrank_fq2, natCard_fq, Finset.sum_range_succ, Finset.sum_range_one] at h
  simpa [FieldData.nrm, add_comm] using h

private lemma algebraMap_nrm_mul (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.nrm z) = z * z ^ D.q := by
  rw [algebraMap_nrm, pow_succ']

private lemma algebraMap_gen (D : FieldData) :
    algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  simpa [FieldData.gen, FieldData.nrm] using algebraMap_nrm D D.h

private lemma fq2_pow_q_eq_self_iff (D : FieldData) (z : D.Fq2) :
    z ^ D.q = z ↔ z ∈ Set.range (algebraMap D.Fq D.Fq2) := by
  have := fq2_isDomain D
  constructor
  · intro hz
    let P : Polynomial D.Fq2 := Polynomial.X ^ D.q - Polynomial.X
    have hq : 1 < D.q := D.one_lt_q
    have hP_deg : P.natDegree = D.q := by
      have hlt : (Polynomial.X : Polynomial D.Fq2).natDegree <
          (Polynomial.X ^ D.q : Polynomial D.Fq2).natDegree := by simpa using hq
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    have hP_ne : P ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hP_deg; omega
    let S : Finset D.Fq2 := Finset.univ.image (algebraMap D.Fq D.Fq2)
    have hS_sub : S ⊆ P.roots.toFinset := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨x, _, rfl⟩ := hw
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_X_pow, Polynomial.eval_X,
        ← map_pow, fq_pow_q, sub_self]
    have hS_card : S.card = D.q := by
      rw [Finset.card_image_of_injective _ (FaithfulSMul.algebraMap_injective D.Fq D.Fq2),
        Finset.card_univ, card_fq]
    have hroots_card : P.roots.toFinset.card ≤ D.q := by
      calc P.roots.toFinset.card
          ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ = D.q := hP_deg
    have heq : P.roots.toFinset = S :=
      (Finset.eq_of_subset_of_card_le hS_sub (hroots_card.trans hS_card.symm.le)).symm
    have hz_mem : z ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_X_pow, Polynomial.eval_X, hz, sub_self]
    rw [heq, Finset.mem_image] at hz_mem
    obtain ⟨x, _, hx⟩ := hz_mem
    exact ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    rw [← map_pow, fq_pow_q]

private lemma h_ne_zero (D : FieldData) : D.h ≠ 0 := by
  intro hz
  have h1 : orderOf D.h = D.q ^ 2 - 1 := D.h_order
  rw [hz, orderOf_zero] at h1
  have h2 := q_sq_sub_one_ne_zero D
  change (0 : ℕ) = D.q ^ 2 - 1 at h1
  exact h2 h1.symm

private lemma orderOf_gen (D : FieldData) : orderOf D.gen = D.q - 1 := by
  have hinj : Function.Injective (algebraMap D.Fq D.Fq2) :=
    FaithfulSMul.algebraMap_injective D.Fq D.Fq2
  have h1 : orderOf D.gen = orderOf ((algebraMap D.Fq D.Fq2).toMonoidHom D.gen) :=
    (orderOf_injective (algebraMap D.Fq D.Fq2).toMonoidHom hinj D.gen).symm
  rw [h1, RingHom.toMonoidHom_eq_coe, RingHom.coe_monoidHom_mk]
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = D.q - 1
  rw [algebraMap_gen, orderOf_pow' D.h (by omega), D.h_order]
  change (D.q ^ 2 - 1) / Nat.gcd (D.q ^ 2 - 1) (D.q + 1) = D.q - 1
  rw [q_sq_sub_one_eq_mul, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by omega)]

private lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro hz
  have h1 := orderOf_gen D
  rw [hz, orderOf_zero] at h1
  have hq := D.one_lt_q
  omega

private lemma exists_h_pow (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) :
    ∃ n : ℕ, D.h ^ n = z := by
  let hu : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  let zu : D.Fq2ˣ := Units.mk0 z hz
  have hord : orderOf hu = D.q ^ 2 - 1 := by
    rw [← orderOf_units, show (hu : D.Fq2) = D.h from rfl, D.h_order]; rfl
  have hcard : Nat.card D.Fq2ˣ = D.q ^ 2 - 1 := by
    calc Nat.card D.Fq2ˣ = Nat.card D.Fq2 - 1 := by convert Nat.card_units D.Fq2
      _ = D.q ^ 2 - 1 := by rw [natCard_fq2]
  have htop : Subgroup.zpowers hu = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  obtain ⟨k, hk⟩ := htop ▸ Subgroup.mem_top zu
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
  have hpos : (0 : ℤ) < orderOf hu := by rw [hord]; omega
  let m : ℕ := Int.toNat (k % (orderOf hu : ℤ))
  have hm : (m : ℤ) = k % (orderOf hu : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k hpos.ne')
  refine ⟨m, ?_⟩
  have hn : hu ^ m = zu := by
    rw [← zpow_natCast, hm]
    calc hu ^ (k % (orderOf hu : ℤ))
        = hu ^ (k % (orderOf hu : ℤ)) * (hu ^ (orderOf hu : ℤ)) ^ (k / (orderOf hu : ℤ)) := by
            rw [zpow_natCast, pow_orderOf_eq_one hu, one_zpow, mul_one]
      _ = hu ^ (k % (orderOf hu : ℤ) + (orderOf hu : ℤ) * (k / (orderOf hu : ℤ))) := by
            rw [← zpow_mul, ← zpow_add]
      _ = hu ^ k := by rw [Int.emod_add_mul_ediv]
      _ = zu := hk
  exact congrArg Units.val hn

private lemma exists_gen_pow (D : FieldData) {x : D.Fq} (hx : x ≠ 0) :
    ∃ n : ℕ, D.gen ^ n = x := by
  let gu : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  let xu : D.Fqˣ := Units.mk0 x hx
  have hord : orderOf gu = D.q - 1 := by
    rw [← orderOf_units, show (gu : D.Fq) = D.gen from rfl, orderOf_gen]
  have hcard : Nat.card D.Fqˣ = D.q - 1 := by rw [Nat.card_units, natCard_fq]
  have htop : Subgroup.zpowers gu = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  obtain ⟨k, hk⟩ := htop ▸ Subgroup.mem_top xu
  have hq : 1 < D.q := D.one_lt_q
  have hpos : (0 : ℤ) < orderOf gu := by rw [hord]; omega
  let m : ℕ := Int.toNat (k % (orderOf gu : ℤ))
  have hm : (m : ℤ) = k % (orderOf gu : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg k hpos.ne')
  refine ⟨m, ?_⟩
  have hn : gu ^ m = xu := by
    rw [← zpow_natCast, hm]
    calc gu ^ (k % (orderOf gu : ℤ))
        = gu ^ (k % (orderOf gu : ℤ)) * (gu ^ (orderOf gu : ℤ)) ^ (k / (orderOf gu : ℤ)) := by
            rw [zpow_natCast, pow_orderOf_eq_one gu, one_zpow, mul_one]
      _ = gu ^ (k % (orderOf gu : ℤ) + (orderOf gu : ℤ) * (k / (orderOf gu : ℤ))) := by
            rw [← zpow_mul, ← zpow_add]
      _ = gu ^ k := by rw [Int.emod_add_mul_ediv]
      _ = xu := hk
  exact congrArg Units.val hn

private lemma gen_pow_dlog (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  have h := exists_gen_pow D hx
  simpa [FieldData.dlog, dif_pos h] using Nat.find_spec h

private lemma h_pow_dlog2 (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) : D.h ^ D.dlog2 z = z := by
  have h := exists_h_pow D hz
  simpa [FieldData.dlog2, dif_pos h] using Nat.find_spec h

private lemma dlog_modEq_of_pow (D : FieldData) {x : D.Fq} (hx : x ≠ 0) {n : ℕ}
    (hn : D.gen ^ n = x) : D.dlog x ≡ n [MOD (D.q - 1)] := by
  let gu : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hpow : gu ^ D.dlog x = gu ^ n := by ext; simp [gu, gen_pow_dlog D hx, hn]
  have hord : orderOf gu = D.q - 1 := by
    rw [← orderOf_units, show (gu : D.Fq) = D.gen from rfl, orderOf_gen]
  rwa [pow_eq_pow_iff_modEq, hord] at hpow

private lemma dlog2_modEq_of_pow (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) {n : ℕ}
    (hn : D.h ^ n = z) : D.dlog2 z ≡ n [MOD (D.q ^ 2 - 1)] := by
  let hu : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  have hpow : hu ^ D.dlog2 z = hu ^ n := by ext; simp [hu, h_pow_dlog2 D hz, hn]
  have hord : orderOf hu = D.q ^ 2 - 1 := by
    rw [← orderOf_units, show (hu : D.Fq2) = D.h from rfl, D.h_order]; rfl
  rwa [pow_eq_pow_iff_modEq, hord] at hpow

private lemma dlog_one (D : FieldData) : D.dlog 1 = 0 := by
  have h := exists_gen_pow D (one_ne_zero : (1 : D.Fq) ≠ 0)
  simp only [FieldData.dlog, dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h (pow_zero D.gen))

private lemma dlog2_one (D : FieldData) : D.dlog2 1 = 0 := by
  have h := exists_h_pow D (one_ne_zero : (1 : D.Fq2) ≠ 0)
  simp only [FieldData.dlog2, dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h (pow_zero D.h))

private lemma dlog_gen (D : FieldData) (hq : 2 < D.q) : D.dlog D.gen = 1 := by
  have hne := gen_ne_zero D
  have h := exists_gen_pow D hne
  have hle : Nat.find h ≤ 1 := Nat.find_min' h (pow_one D.gen)
  have hne0 : Nat.find h ≠ 0 := by
    intro h0
    have hspec := Nat.find_spec h
    rw [h0, pow_zero] at hspec
    have hord := orderOf_gen D
    rw [← hspec, orderOf_one] at hord
    change 1 = D.p ^ D.r - 1 at hord
    rw [← FieldData.q] at hord
    omega
  simp only [FieldData.dlog, dif_pos h]
  omega

private lemma dlog2_h (D : FieldData) : D.dlog2 D.h = 1 := by
  have hne := h_ne_zero D
  have h := exists_h_pow D hne
  have hle : Nat.find h ≤ 1 := Nat.find_min' h (pow_one D.h)
  have hne0 : Nat.find h ≠ 0 := by
    intro h0
    have hspec := Nat.find_spec h
    rw [h0, pow_zero] at hspec
    have hord := D.h_order
    rw [← hspec, orderOf_one] at hord
    have h2 := q_sq_sub_one_ne_zero D
    change 1 = (D.p ^ D.r) ^ 2 - 1 at hord
    rw [← FieldData.q] at hord
    have hq : 1 < D.q := D.one_lt_q
    have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
    omega
  simp only [FieldData.dlog2, dif_pos h]
  omega

private lemma dlog_lt (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.dlog x < D.q - 1 := by
  have hq : 1 < D.q := D.one_lt_q
  have h := exists_gen_pow D hx
  by_contra hge
  push Not at hge
  have hlt : D.dlog x % (D.q - 1) < D.q - 1 := Nat.mod_lt _ (by omega)
  have hpow : D.gen ^ (D.dlog x % (D.q - 1)) = x := by
    have hmod := Nat.div_add_mod (D.dlog x) (D.q - 1)
    have hgen : D.gen ^ (D.q - 1) = 1 := by
      rw [← orderOf_gen D]; exact pow_orderOf_eq_one D.gen
    calc D.gen ^ (D.dlog x % (D.q - 1))
        = (D.gen ^ (D.q - 1)) ^ (D.dlog x / (D.q - 1)) * D.gen ^ (D.dlog x % (D.q - 1)) := by
            rw [hgen, one_pow, one_mul]
      _ = D.gen ^ ((D.q - 1) * (D.dlog x / (D.q - 1)) + D.dlog x % (D.q - 1)) := by
            rw [pow_add, pow_mul]
      _ = D.gen ^ D.dlog x := by rw [hmod]
      _ = x := gen_pow_dlog D hx
  have hmin : Nat.find h ≤ D.dlog x % (D.q - 1) := Nat.find_min' h hpow
  have hd : D.dlog x = Nat.find h := by simp [FieldData.dlog, dif_pos h]
  omega

private lemma dlog2_lt (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) : D.dlog2 z < D.q ^ 2 - 1 := by
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
  have h := exists_h_pow D hz
  by_contra hge
  push Not at hge
  have hlt : D.dlog2 z % (D.q ^ 2 - 1) < D.q ^ 2 - 1 := Nat.mod_lt _ (by omega)
  have hpow : D.h ^ (D.dlog2 z % (D.q ^ 2 - 1)) = z := by
    have hmod := Nat.div_add_mod (D.dlog2 z) (D.q ^ 2 - 1)
    have hh : D.h ^ (D.q ^ 2 - 1) = 1 := by
      rw [show D.q ^ 2 - 1 = orderOf D.h from D.h_order.symm]; exact pow_orderOf_eq_one D.h
    calc D.h ^ (D.dlog2 z % (D.q ^ 2 - 1))
        = (D.h ^ (D.q ^ 2 - 1)) ^ (D.dlog2 z / (D.q ^ 2 - 1)) * D.h ^ (D.dlog2 z % (D.q ^ 2 - 1)) := by
            rw [hh, one_pow, one_mul]
      _ = D.h ^ ((D.q ^ 2 - 1) * (D.dlog2 z / (D.q ^ 2 - 1)) + D.dlog2 z % (D.q ^ 2 - 1)) := by
            rw [pow_add, pow_mul]
      _ = D.h ^ D.dlog2 z := by rw [hmod]
      _ = z := h_pow_dlog2 D hz
  have hmin : Nat.find h ≤ D.dlog2 z % (D.q ^ 2 - 1) := Nat.find_min' h hpow
  have hd : D.dlog2 z = Nat.find h := by simp [FieldData.dlog2, dif_pos h]
  omega

private lemma exp_two_pi_I_div_eq_of_modEq {n a b : ℕ} (hn : n ≠ 0) (h : a ≡ b [MOD n]) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (n : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp h
  have hbc : (b : ℂ) = (a : ℂ) + (k : ℂ) * (n : ℂ) := by
    have := congrArg (fun t : ℤ => (t : ℂ)) hk
    push_cast at this
    linear_combination this
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-k, ?_⟩
  rw [hbc]
  field_simp
  push_cast
  ring

private lemma chi_zero_right (D : FieldData) (α : D.Lab) : D.chi α 0 = 0 := by simp [FieldData.chi]
private lemma chi_one_right (D : FieldData) (α : D.Lab) : D.chi α 1 = 1 := by simp [FieldData.chi, dlog_one]
private lemma chi_zero_left (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.chi 0 x = 1 := by
  simp [FieldData.chi, hx]

private lemma chi_mul (D : FieldData) (α : D.Lab) (x y : D.Fq) :
    D.chi α (x * y) = D.chi α x * D.chi α y := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  by_cases hy : y = 0
  · subst hy; simp [chi_zero_right]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [FieldData.chi, if_neg hx, if_neg hy, if_neg hxy, ← Complex.exp_add]
  have hmod : D.dlog (x * y) ≡ D.dlog x + D.dlog y [MOD (D.q - 1)] :=
    dlog_modEq_of_pow D hxy (by rw [pow_add, gen_pow_dlog D hx, gen_pow_dlog D hy])
  have hmod' : α.val * D.dlog (x * y) ≡ α.val * D.dlog x + α.val * D.dlog y [MOD (D.q - 1)] := by
    simpa [mul_add] using hmod.mul_left α.val
  have hq : D.q - 1 ≠ 0 := by have := D.one_lt_q; omega
  rw [exp_two_pi_I_div_eq_of_modEq hq hmod']
  congr 1; push_cast; ring

private lemma chi_add_lab (D : FieldData) (α β : D.Lab) (x : D.Fq) :
    D.chi (α + β) x = D.chi α x * D.chi β x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  simp only [FieldData.chi, if_neg hx, ← Complex.exp_add]
  have hmod : (α + β).val ≡ α.val + β.val [MOD (D.q - 1)] := by
    rw [ZMod.val_add]; exact Nat.mod_modEq _ _
  have hmod' : (α + β).val * D.dlog x ≡ α.val * D.dlog x + β.val * D.dlog x [MOD (D.q - 1)] := by
    simpa [add_mul] using hmod.mul_right (D.dlog x)
  have hq : D.q - 1 ≠ 0 := by have := D.one_lt_q; omega
  rw [exp_two_pi_I_div_eq_of_modEq hq hmod']
  congr 1; push_cast; ring

private lemma chi_norm (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) : ‖D.chi α x‖ = 1 := by
  simp only [FieldData.chi, if_neg hx]
  have heq : (2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ)) =
      ((2 * Real.pi * ((α.val * D.dlog x : ℕ) : ℝ) / ((D.q - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq]; exact Complex.norm_exp_ofReal_mul_I _

private lemma chi_ne_zero (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) : D.chi α x ≠ 0 := by
  simp [FieldData.chi, hx, Complex.exp_ne_zero]

private lemma chi_neg_lab (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi (-α) x = star (D.chi α x) := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  have h1 : D.chi (-α) x * D.chi α x = 1 := by rw [← chi_add_lab, neg_add_cancel, chi_zero_left D hx]
  have h2 : star (D.chi α x) * D.chi α x = 1 := by
    rw [RCLike.star_def, Complex.conj_mul', chi_norm D α hx, Complex.ofReal_one, one_pow]
  exact mul_right_cancel₀ (chi_ne_zero D α hx) (h1.trans h2.symm)

private lemma chi_inv_right (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi α x⁻¹ = D.chi (-α) x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  have h1 : D.chi α x⁻¹ * D.chi α x = 1 := by rw [← chi_mul, inv_mul_cancel₀ hx, chi_one_right]
  have h2 : D.chi (-α) x * D.chi α x = 1 := by rw [← chi_add_lab, neg_add_cancel, chi_zero_left D hx]
  exact mul_right_cancel₀ (chi_ne_zero D α hx) (h1.trans h2.symm)

private lemma chi_div (D : FieldData) (α : D.Lab) (x y : D.Fq) :
    D.chi α (x / y) = D.chi α x * D.chi (-α) y := by
  rw [div_eq_mul_inv, chi_mul, chi_inv_right]

private lemma chi_neg_one_sq (D : FieldData) (α : D.Lab) : D.chi α (-1) ^ 2 = 1 := by
  rw [sq, ← chi_mul, neg_mul_neg, one_mul, chi_one_right]

private lemma star_chi_neg_one (D : FieldData) (α : D.Lab) : star (D.chi α (-1)) = D.chi α (-1) := by
  rw [← chi_neg_lab]
  have h1 : D.chi (-α) (-1) * D.chi α (-1) = 1 := by
    rw [← chi_add_lab, neg_add_cancel, chi_zero_left D (neg_ne_zero.mpr one_ne_zero)]
  have h2 : D.chi α (-1) * D.chi α (-1) = 1 := by rw [← sq, chi_neg_one_sq]
  exact mul_right_cancel₀ (chi_ne_zero D α (neg_ne_zero.mpr one_ne_zero)) (h1.trans h2.symm)

private lemma chi_gen_ne_one (D : FieldData) (hq : 2 < D.q) {α : D.Lab} (hα : α ≠ 0) :
    D.chi α D.gen ≠ 1 := by
  have hne := gen_ne_zero D
  simp only [FieldData.chi, if_neg hne, dlog_gen D hq, mul_one]
  intro heq
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by omega)] at heq
  have hlt : α.val < D.q - 1 := ZMod.val_lt α
  have hpos : 0 < α.val := by
    rcases Nat.eq_zero_or_pos α.val with h0 | hp
    · exact False.elim (hα ((ZMod.val_eq_zero α).mp h0))
    · exact hp
  exact (Nat.le_of_dvd hpos heq).not_gt hlt

private lemma sum_chi_fq_units (D : FieldData) (hq : 2 < D.q) (α : D.Lab) :
    ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x =
      if α = 0 then (D.q : ℂ) - 1 else 0 := by
  split_ifs with hα
  · subst hα
    rw [Finset.sum_congr rfl (fun x hx => chi_zero_left D (Finset.mem_filter.mp hx).2),
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ.filter (fun x : D.Fq => x ≠ 0)).card = D.q - 1 := by
      have hfilt : Finset.univ.filter (fun x : D.Fq => x ≠ 0) =
          Finset.univ \ ({0} : Finset D.Fq) := by ext x; simp
      rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_fq,
        Finset.card_singleton]
    rw [hcard, Nat.cast_sub (by omega), Nat.cast_one]
  · set S := ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x
    have hmul : D.chi α D.gen * S = S := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun x _ => D.gen * x) ?_ ?_ ?_ ?_
      · intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, mul_ne_zero (gen_ne_zero D) hx.2⟩
      · intro x₁ _ x₂ _ h; exact mul_left_cancel₀ (gen_ne_zero D) h
      · intro y hy; rw [Finset.mem_filter] at hy
        exact ⟨D.gen⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero (inv_ne_zero (gen_ne_zero D)) hy.2⟩,
          by rw [← mul_assoc, mul_inv_cancel₀ (gen_ne_zero D), one_mul]⟩
      · intro x _; rw [chi_mul]
    have hne : D.chi α D.gen - 1 ≠ 0 := sub_ne_zero.mpr (chi_gen_ne_one D hq hα)
    have h0 : (D.chi α D.gen - 1) * S = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp h0).resolve_left hne

private lemma chi_one_ne_one (D : FieldData) (hq : 2 < D.q) {x : D.Fq} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    D.chi 1 x ≠ 1 := by
  have h1val : (1 : D.Lab).val = 1 := by
    have : Fact (1 < D.q - 1) := ⟨by omega⟩; exact ZMod.val_one (D.q - 1)
  simp only [FieldData.chi, if_neg hx0, h1val, one_mul]
  intro heq
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by omega)] at heq
  have hd_lt : D.dlog x < D.q - 1 := dlog_lt D hx0
  have hd_pos : 0 < D.dlog x := by
    rcases Nat.eq_zero_or_pos (D.dlog x) with h0 | hpos
    · have hpow := gen_pow_dlog D hx0; rw [h0, pow_zero] at hpow; exact False.elim (hx1 hpow.symm)
    · exact hpos
  exact (Nat.le_of_dvd hd_pos heq).not_gt hd_lt

private lemma sum_chi_lab (D : FieldData) (hq : 2 < D.q) {x : D.Fq} (hx : x ≠ 0) :
    ∑ α : D.Lab, D.chi α x = if x = 1 then (D.q : ℂ) - 1 else 0 := by
  split_ifs with hx1
  · subst hx1
    simp only [chi_one_right, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  · set S := ∑ α : D.Lab, D.chi α x
    have hmul : D.chi 1 x * S = S := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun α _ => 1 + α) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => add_left_cancel h) (fun β _ => ⟨β - 1, Finset.mem_univ _, by ring⟩)
        (fun α _ => by rw [chi_add_lab])
    have hne : D.chi 1 x - 1 ≠ 0 := sub_ne_zero.mpr (chi_one_ne_one D hq hx hx1)
    have h0 : (D.chi 1 x - 1) * S = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp h0).resolve_left hne

private lemma theta_zero_right (D : FieldData) (k : D.Lab2) : D.theta k 0 = 0 := by simp [FieldData.theta]
private lemma theta_one_right (D : FieldData) (k : D.Lab2) : D.theta k 1 = 1 := by
  simp [FieldData.theta, dlog2_one]
private lemma theta_zero_left (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) : D.theta 0 z = 1 := by
  simp [FieldData.theta, hz]

private lemma theta_mul (D : FieldData) (k : D.Lab2) (z w : D.Fq2) :
    D.theta k (z * w) = D.theta k z * D.theta k w := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero_right]
  by_cases hw : w = 0
  · subst hw; simp [theta_zero_right]
  have hzw : z * w ≠ 0 := mul_ne_zero hz hw
  simp only [FieldData.theta, if_neg hz, if_neg hw, if_neg hzw, ← Complex.exp_add]
  have hmod : D.dlog2 (z * w) ≡ D.dlog2 z + D.dlog2 w [MOD (D.q ^ 2 - 1)] :=
    dlog2_modEq_of_pow D hzw (by rw [pow_add, h_pow_dlog2 D hz, h_pow_dlog2 D hw])
  have hmod' : k.val * D.dlog2 (z * w) ≡ k.val * D.dlog2 z + k.val * D.dlog2 w [MOD (D.q ^ 2 - 1)] := by
    simpa [mul_add] using hmod.mul_left k.val
  rw [exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) hmod']
  congr 1; push_cast; ring

private lemma theta_add_lab (D : FieldData) (k₁ k₂ : D.Lab2) (z : D.Fq2) :
    D.theta (k₁ + k₂) z = D.theta k₁ z * D.theta k₂ z := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero_right]
  simp only [FieldData.theta, if_neg hz, ← Complex.exp_add]
  have hmod : (k₁ + k₂).val ≡ k₁.val + k₂.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_add]; exact Nat.mod_modEq _ _
  have hmod' : (k₁ + k₂).val * D.dlog2 z ≡
      k₁.val * D.dlog2 z + k₂.val * D.dlog2 z [MOD (D.q ^ 2 - 1)] := by
    simpa [add_mul] using hmod.mul_right (D.dlog2 z)
  rw [exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) hmod']
  congr 1; push_cast; ring

private lemma theta_norm (D : FieldData) (k : D.Lab2) {z : D.Fq2} (hz : z ≠ 0) : ‖D.theta k z‖ = 1 := by
  simp only [FieldData.theta, if_neg hz]
  have heq : (2 * Real.pi * Complex.I * ((k.val * D.dlog2 z : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ)) =
      ((2 * Real.pi * ((k.val * D.dlog2 z : ℕ) : ℝ) / ((D.q ^ 2 - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq]; exact Complex.norm_exp_ofReal_mul_I _

private lemma theta_ne_zero (D : FieldData) (k : D.Lab2) {z : D.Fq2} (hz : z ≠ 0) : D.theta k z ≠ 0 := by
  simp [FieldData.theta, hz, Complex.exp_ne_zero]

private lemma theta_neg_lab (D : FieldData) (k : D.Lab2) (z : D.Fq2) :
    D.theta (-k) z = star (D.theta k z) := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero_right]
  have h1 : D.theta (-k) z * D.theta k z = 1 := by
    rw [← theta_add_lab, neg_add_cancel, theta_zero_left D hz]
  have h2 : star (D.theta k z) * D.theta k z = 1 := by
    rw [RCLike.star_def, Complex.conj_mul', theta_norm D k hz, Complex.ofReal_one, one_pow]
  exact mul_right_cancel₀ (theta_ne_zero D k hz) (h1.trans h2.symm)

private lemma theta_h_ne_one (D : FieldData) (_hq : 2 < D.q) {k : D.Lab2} (hk : k ≠ 0) :
    D.theta k D.h ≠ 1 := by
  have hne := h_ne_zero D
  simp only [FieldData.theta, if_neg hne, dlog2_h, mul_one]
  intro heq
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (q_sq_sub_one_ne_zero D)] at heq
  have hlt : k.val < D.q ^ 2 - 1 := ZMod.val_lt k
  have hpos : 0 < k.val := by
    rcases Nat.eq_zero_or_pos k.val with h0 | hp
    · exact False.elim (hk ((ZMod.val_eq_zero k).mp h0))
    · exact hp
  exact (Nat.le_of_dvd hpos heq).not_gt hlt

private lemma theta_algebraMap (D : FieldData) (k : D.Lab2) (x : D.Fq) :
    D.theta k (algebraMap D.Fq D.Fq2 x) = D.chi (D.restrLab k) x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, theta_zero_right, chi_zero_right]
  have hax : algebraMap D.Fq D.Fq2 x ≠ 0 := by simpa [map_eq_zero] using hx
  simp only [FieldData.theta, FieldData.chi, if_neg hax, if_neg hx]
  have hpow : D.h ^ ((D.q + 1) * D.dlog x) = algebraMap D.Fq D.Fq2 x := by
    rw [pow_mul, ← algebraMap_gen, ← map_pow, gen_pow_dlog D hx]
  have hmod1 : D.dlog2 (algebraMap D.Fq D.Fq2 x) ≡ (D.q + 1) * D.dlog x [MOD (D.q ^ 2 - 1)] :=
    dlog2_modEq_of_pow D hax hpow
  rw [exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) (hmod1.mul_left k.val)]
  have hmod2 : (D.restrLab k).val ≡ k.val [MOD (D.q - 1)] := by
    simp only [FieldData.restrLab, ZMod.val_natCast]; exact Nat.mod_modEq _ _
  have hq1 : D.q - 1 ≠ 0 := by have := D.one_lt_q; omega
  rw [exp_two_pi_I_div_eq_of_modEq hq1 (hmod2.mul_right (D.dlog x))]
  congr 1
  have hfac : ((D.q ^ 2 - 1 : ℕ) : ℂ) = ((D.q + 1 : ℕ) : ℂ) * ((D.q - 1 : ℕ) : ℂ) := by
    exact_mod_cast q_sq_sub_one_eq_mul D
  have hq1' : ((D.q + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq2' : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq1
  rw [hfac]; push_cast; field_simp

private lemma restrLab_add (D : FieldData) (k₁ k₂ : D.Lab2) :
    D.restrLab (k₁ + k₂) = D.restrLab k₁ + D.restrLab k₂ := by
  simp only [FieldData.restrLab]
  have hq : (D.q - 1) ∣ (D.q ^ 2 - 1) := ⟨D.q + 1, by rw [q_sq_sub_one_eq_mul, mul_comm]⟩
  have hmod := Nat.ModEq.of_dvd hq
    (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _ : (k₁ + k₂).val ≡ k₁.val + k₂.val [MOD (D.q ^ 2 - 1)])
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  simpa [Nat.cast_add] using hmod

private lemma restrLab_neg (D : FieldData) (k : D.Lab2) : D.restrLab (-k) = -D.restrLab k := by
  apply eq_neg_of_add_eq_zero_left
  rw [← restrLab_add, neg_add_cancel]; simp [FieldData.restrLab]

private lemma restrLab_sub (D : FieldData) (k₁ k₂ : D.Lab2) :
    D.restrLab (k₁ - k₂) = D.restrLab k₁ - D.restrLab k₂ := by
  rw [sub_eq_add_neg, restrLab_add, restrLab_neg, sub_eq_add_neg]

private lemma restrLab_theta0 (D : FieldData) (γ : D.Lab) : D.restrLab (theta0Lab D γ) = γ := by
  simp only [FieldData.restrLab, theta0Lab]
  have hq : D.q - 1 < D.q ^ 2 - 1 := by
    have hq1 := D.one_lt_q
    have hq2 : D.q < D.q ^ 2 := by nlinarith
    omega
  have hlt : γ.val < D.q ^ 2 - 1 := (ZMod.val_lt γ).trans hq
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.natCast_zmod_val]

private lemma restrLab_q_add_one_mul (D : FieldData) (δ : D.Lab) :
    D.restrLab (((D.q + 1) * δ.val : ℕ) : D.Lab2) = 2 * δ := by
  simp only [FieldData.restrLab]
  have hq : (D.q - 1) ∣ (D.q ^ 2 - 1) := ⟨D.q + 1, by rw [q_sq_sub_one_eq_mul, mul_comm]⟩
  have hmod1 : (((D.q + 1) * δ.val : ℕ) : D.Lab2).val ≡ (D.q + 1) * δ.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_natCast]; exact Nat.mod_modEq _ _
  have hmod2 := Nat.ModEq.of_dvd hq hmod1
  have hqmod : D.q + 1 ≡ 2 [MOD (D.q - 1)] := by
    rw [Nat.modEq_iff_dvd]; exact ⟨-1, by have := D.one_lt_q; omega⟩
  have hmod3 := hmod2.trans (hqmod.mul_right δ.val)
  rw [← ZMod.natCast_eq_natCast_iff] at hmod3
  simpa [Nat.cast_mul, ZMod.natCast_zmod_val] using hmod3

private lemma kerChar_eq_theta (D : FieldData) {m : D.Lab2} (hm : D.restrLab m = 0)
    {w : D.Fq2} (hw : w ≠ 0) :
    kerChar D m (w / w ^ D.q) = D.theta m w := by
  have hex : ∃ w' : D.Fq2, w' ≠ 0 ∧ w' / w' ^ D.q = w / w ^ D.q := ⟨w, hw, rfl⟩
  simp only [kerChar, dif_pos hex]
  set w' := Classical.choose hex
  have hw' : w' ≠ 0 := (Classical.choose_spec hex).1
  have heq : w' / w' ^ D.q = w / w ^ D.q := (Classical.choose_spec hex).2
  have hpow : (w' / w) ^ D.q = w' / w := by
    rw [fq2_div_pow_q]
    have h2 : w' ^ D.q ≠ 0 := fq2_pow_ne_zero D hw' D.q
    have h3 : w ^ D.q ≠ 0 := fq2_pow_ne_zero D hw D.q
    rw [field_div_eq_div_iff h2 h3] at heq
    rw [field_div_eq_div_iff h3 hw]
    linear_combination -heq
  obtain ⟨x, hx⟩ := (fq2_pow_q_eq_self_iff D (w' / w)).mp hpow
  have hw'_eq : w' = algebraMap D.Fq D.Fq2 x * w := by rw [hx, div_mul_cancel₀ _ hw]
  have hx0 : x ≠ 0 := by
    intro hx0; rw [hx0, map_zero, zero_mul] at hw'_eq; exact hw' hw'_eq
  rw [hw'_eq, theta_mul, theta_algebraMap, hm, chi_zero_left D hx0, one_mul]

private lemma exists_ker_quot (D : FieldData) {r : D.Fq2} (hr0 : r ≠ 0) (hr1 : r ^ (D.q + 1) = 1) :
    ∃ w : D.Fq2, w ≠ 0 ∧ w / w ^ D.q = r := by
  have hq : 1 < D.q := D.one_lt_q
  have hpow : D.h ^ ((D.q + 1) * D.dlog2 r) = 1 := by rw [mul_comm, pow_mul, h_pow_dlog2 D hr0, hr1]
  have hdvd : D.q ^ 2 - 1 ∣ (D.q + 1) * D.dlog2 r := by
    rw [show D.q ^ 2 - 1 = orderOf D.h from D.h_order.symm]; exact orderOf_dvd_of_pow_eq_one hpow
  rw [q_sq_sub_one_eq_mul D] at hdvd
  obtain ⟨j, hj⟩ := (Nat.mul_dvd_mul_iff_left (by omega : 0 < D.q + 1)).mp hdvd
  refine ⟨(D.h⁻¹) ^ j, fq2_pow_ne_zero D (inv_ne_zero (h_ne_zero D)) j, ?_⟩
  have hq_sub : 1 ≤ D.q := by omega
  have hhjq : ((D.h⁻¹) ^ j) ^ D.q = ((D.h ^ j) ^ D.q)⁻¹ := by rw [inv_pow, inv_pow]
  calc (D.h⁻¹) ^ j / ((D.h⁻¹) ^ j) ^ D.q
      = (D.h⁻¹) ^ j * (D.h ^ j) ^ D.q := by rw [div_eq_mul_inv, hhjq, field_inv_inv]
    _ = (D.h⁻¹) ^ j * D.h ^ (j * D.q) := by rw [← pow_mul]
    _ = (D.h⁻¹) ^ j * (D.h ^ j * D.h ^ ((D.q - 1) * j)) := by
          rw [← pow_add]; congr 2; zify [hq_sub]; ring
    _ = ((D.h⁻¹) ^ j * D.h ^ j) * D.h ^ ((D.q - 1) * j) := by ring
    _ = D.h ^ D.dlog2 r := by rw [← mul_pow, inv_mul_cancel₀ (h_ne_zero D), one_pow, one_mul, ← hj]
    _ = r := h_pow_dlog2 D hr0

private lemma sum_kerChar_orth (D : FieldData) (hq : 2 < D.q) (γ : D.Lab)
    {r₁ r₂ : D.Fq2} (hr₁0 : r₁ ≠ 0) (hr₁1 : r₁ ^ (D.q + 1) = 1)
    (hr₂0 : r₂ ≠ 0) (hr₂1 : r₂ ^ (D.q + 1) = 1) :
    ∑ θ : {θ : D.Lab2 // D.restrLab θ = γ},
      star (kerChar D (θ.1 - theta0Lab D γ) r₁) * kerChar D (θ.1 - theta0Lab D γ) r₂ =
      if r₁ = r₂ then (D.q : ℂ) + 1 else 0 := by
  obtain ⟨w₁, hw₁0, hw₁⟩ := exists_ker_quot D hr₁0 hr₁1
  obtain ⟨w₂, hw₂0, hw₂⟩ := exists_ker_quot D hr₂0 hr₂1
  let toKer : Fin (D.q + 1) → {θ : D.Lab2 // D.restrLab θ = γ} := fun j =>
    ⟨theta0Lab D γ + (((D.q - 1) * j.1 : ℕ) : D.Lab2), by
      rw [restrLab_add, restrLab_theta0]
      have h0 : D.restrLab (((D.q - 1) * j.1 : ℕ) : D.Lab2) = 0 := by
        simp only [FieldData.restrLab]
        have hq' : (D.q - 1) ∣ (D.q ^ 2 - 1) := ⟨D.q + 1, by rw [q_sq_sub_one_eq_mul, mul_comm]⟩
        have hmod : (((D.q - 1) * j.1 : ℕ) : D.Lab2).val ≡ (D.q - 1) * j.1 [MOD (D.q - 1)] :=
          Nat.ModEq.of_dvd hq' (by rw [ZMod.val_natCast]; exact Nat.mod_modEq _ _)
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr ⟨j.1, rfl⟩))
      rw [h0, add_zero]⟩
  have hbij : Function.Bijective toKer := by
    constructor
    · intro j₁ j₂ heq
      have hval := congrArg (fun x : {θ : D.Lab2 // D.restrLab θ = γ} =>
        (x.1 - theta0Lab D γ).val) heq
      have hqsub : 0 < D.q - 1 := Nat.sub_pos_of_lt D.one_lt_q
      have hlt₁ : (D.q - 1) * j₁.1 < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul, mul_comm (D.q + 1) (D.q - 1)]; exact Nat.mul_lt_mul_of_pos_left j₁.2 hqsub
      have hlt₂ : (D.q - 1) * j₂.1 < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul, mul_comm (D.q + 1) (D.q - 1)]; exact Nat.mul_lt_mul_of_pos_left j₂.2 hqsub
      have hv1 : ((toKer j₁).1 - theta0Lab D γ).val = (D.q - 1) * j₁.1 := by
        dsimp only [toKer]; rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hlt₁]
      have hv2 : ((toKer j₂).1 - theta0Lab D γ).val = (D.q - 1) * j₂.1 := by
        dsimp only [toKer]; rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hlt₂]
      rw [hv1, hv2] at hval
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hqsub hval)
    · intro θ
      set m := θ.1 - theta0Lab D γ
      have hm0 : D.restrLab m = 0 := by rw [restrLab_sub, θ.2, restrLab_theta0, sub_self]
      obtain ⟨j, hj⟩ := (ZMod.natCast_eq_zero_iff m.val (D.q - 1)).mp hm0
      have hjlt : j < D.q + 1 := by
        have hmlt : m.val < (D.q - 1) * (D.q + 1) := by
          rw [mul_comm, ← q_sq_sub_one_eq_mul]; exact ZMod.val_lt m
        rw [hj] at hmlt
        exact Nat.lt_of_mul_lt_mul_left hmlt
      refine ⟨⟨j, hjlt⟩, Subtype.ext ?_⟩
      have h1 : (((D.q - 1) * j : ℕ) : D.Lab2) = θ.1 - theta0Lab D γ := by
        rw [← hj, ZMod.natCast_zmod_val]
      change theta0Lab D γ + (((D.q - 1) * j : ℕ) : D.Lab2) = θ.1
      rw [h1, add_sub_cancel]
  have hterm : ∀ j : Fin (D.q + 1),
      star (kerChar D ((toKer j).1 - theta0Lab D γ) r₁) *
        kerChar D ((toKer j).1 - theta0Lab D γ) r₂ =
      D.theta (((D.q - 1) * j.1 : ℕ) : D.Lab2) (w₂ / w₁) := by
    intro j
    have hm : D.restrLab ((toKer j).1 - theta0Lab D γ) = 0 := by
      rw [restrLab_sub, (toKer j).2, restrLab_theta0, sub_self]
    rw [← hw₁, ← hw₂, kerChar_eq_theta D hm hw₁0, kerChar_eq_theta D hm hw₂0]
    simp only [toKer, add_sub_cancel_left]
    rw [← theta_neg_lab, div_eq_mul_inv, theta_mul]
    have hinv : D.theta (((D.q - 1) * j.1 : ℕ) : D.Lab2) w₁⁻¹ =
        D.theta (-(((D.q - 1) * j.1 : ℕ) : D.Lab2)) w₁ := by
      apply mul_right_cancel₀ (theta_ne_zero D (((D.q - 1) * j.1 : ℕ) : D.Lab2) hw₁0)
      rw [← theta_mul, inv_mul_cancel₀ hw₁0, theta_one_right, ← theta_add_lab, neg_add_cancel,
        theta_zero_left D hw₁0]
    rw [hinv]; ring
  have hbij_sum := Fintype.sum_bijective toKer hbij
    (fun j => D.theta (((D.q - 1) * j.1 : ℕ) : D.Lab2) (w₂ / w₁))
    (fun θ => star (kerChar D (θ.1 - theta0Lab D γ) r₁) * kerChar D (θ.1 - theta0Lab D γ) r₂)
    (fun j => (hterm j).symm)
  rw [← hbij_sum]
  set u := w₂ / w₁
  have hu0 : u ≠ 0 := div_ne_zero hw₂0 hw₁0
  have heq_iff : r₁ = r₂ ↔ u ^ D.q = u := by
    rw [← hw₁, ← hw₂]
    have hw₁q : w₁ ^ D.q ≠ 0 := fq2_pow_ne_zero D hw₁0 D.q
    have hw₂q : w₂ ^ D.q ≠ 0 := fq2_pow_ne_zero D hw₂0 D.q
    calc w₁ / w₁ ^ D.q = w₂ / w₂ ^ D.q
        ↔ w₁ * w₂ ^ D.q = w₂ * w₁ ^ D.q := field_div_eq_div_iff hw₁q hw₂q
      _ ↔ w₂ ^ D.q / w₁ ^ D.q = w₂ / w₁ := by
          rw [field_div_eq_div_iff hw₁q hw₁0]; constructor <;> intro h <;> linear_combination h
      _ ↔ (w₂ / w₁) ^ D.q = w₂ / w₁ := by rw [fq2_div_pow_q]
  split_ifs with h12
  · have huq : u ^ D.q = u := heq_iff.mp h12
    obtain ⟨x, hx⟩ := (fq2_pow_q_eq_self_iff D u).mp huq
    have hx0 : x ≠ 0 := by intro h0; rw [h0, map_zero] at hx; exact hu0 hx.symm
    have h1 : ∀ j : Fin (D.q + 1), D.theta (((D.q - 1) * j.1 : ℕ) : D.Lab2) u = 1 := by
      intro j
      rw [← hx, theta_algebraMap]
      have hr0 : D.restrLab (((D.q - 1) * j.1 : ℕ) : D.Lab2) = 0 := by
        have := (toKer j).2; rw [restrLab_add, restrLab_theta0] at this; simpa [add_eq_left] using this
      rw [hr0, chi_zero_left D hx0]
    simp_rw [h1]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · have huq : u ^ D.q ≠ u := fun h => h12 (heq_iff.mpr h)
    have hmul1 : D.theta (((D.q - 1) : ℕ) : D.Lab2) u ≠ 1 := by
      intro h1
      have hpow : u ^ (D.q - 1) = 1 := by
        have hc : D.theta (((D.q - 1) : ℕ) : D.Lab2) u =
            D.theta (1 : D.Lab2) (u ^ (D.q - 1)) := by
          have h1v : (1 : D.Lab2).val = 1 := by
            have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
            have : Fact (1 < D.q ^ 2 - 1) := ⟨by omega⟩
            exact ZMod.val_one (D.q ^ 2 - 1)
          have hupow : u ^ (D.q - 1) ≠ 0 := fq2_pow_ne_zero D hu0 (D.q - 1)
          simp only [FieldData.theta, if_neg hu0, if_neg hupow, h1v, one_mul]
          have hmod1 : D.dlog2 (u ^ (D.q - 1)) ≡ (D.q - 1) * D.dlog2 u [MOD (D.q ^ 2 - 1)] :=
            dlog2_modEq_of_pow D hupow (by rw [mul_comm, pow_mul, h_pow_dlog2 D hu0])
          have hmod2 : ((D.q - 1 : ℕ) : D.Lab2).val ≡ D.q - 1 [MOD (D.q ^ 2 - 1)] := by
            rw [ZMod.val_natCast]; exact Nat.mod_modEq _ _
          exact exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) ((hmod2.mul_right _).trans hmod1.symm)
        rw [hc] at h1
        by_contra hne1
        have hupow : u ^ (D.q - 1) ≠ 0 := fq2_pow_ne_zero D hu0 (D.q - 1)
        have hd_lt : D.dlog2 (u ^ (D.q - 1)) < D.q ^ 2 - 1 := dlog2_lt D hupow
        have hd_pos : 0 < D.dlog2 (u ^ (D.q - 1)) := by
          rcases Nat.eq_zero_or_pos (D.dlog2 (u ^ (D.q - 1))) with h0 | hp
          · have hs := h_pow_dlog2 D hupow; rw [h0, pow_zero] at hs; exact False.elim (hne1 hs.symm)
          · exact hp
        have h1v : (1 : D.Lab2).val = 1 := by
          have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
          have : Fact (1 < D.q ^ 2 - 1) := ⟨by omega⟩
          exact ZMod.val_one (D.q ^ 2 - 1)
        simp only [FieldData.theta, if_neg hupow, h1v, one_mul] at h1
        rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (q_sq_sub_one_ne_zero D)] at h1
        exact (Nat.le_of_dvd hd_pos h1).not_gt hd_lt
      have hpow' : u ^ D.q = u := by
        calc u ^ D.q = u ^ (D.q - 1 + 1) := by congr 1; omega
          _ = u ^ (D.q - 1) * u := pow_succ _ _
          _ = u := by rw [hpow, one_mul]
      exact huq hpow'
    set S := ∑ j : Fin (D.q + 1), D.theta (((D.q - 1) * j.1 : ℕ) : D.Lab2) u
    have hshift : D.theta (((D.q - 1) : ℕ) : D.Lab2) u * S = S := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun j _ => j + 1) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => add_right_cancel h) (fun k _ => ⟨k - 1, Finset.mem_univ _, sub_add_cancel k 1⟩) ?_
      intro j _
      rw [← theta_add_lab]; congr 1
      have hjlt : j.1 + 1 ≤ D.q + 1 := j.2
      rcases lt_or_eq_of_le hjlt with hlt | heq
      · have hj1 : (j + 1).1 = j.1 + 1 := by simp [Fin.val_add, Nat.mod_eq_of_lt hlt]
        rw [hj1]; push_cast; ring
      · have hj1 : (j + 1).1 = 0 := by simp [Fin.val_add, heq]
        rw [hj1, mul_zero, Nat.cast_zero]
        have hlhs : (((D.q - 1 : ℕ) : D.Lab2) + (((D.q - 1) * j.1 : ℕ) : D.Lab2)) =
            (((D.q ^ 2 - 1 : ℕ) : D.Lab2)) := by
          rw [← Nat.cast_add, show D.q - 1 + (D.q - 1) * j.1 = (D.q - 1) * (j.1 + 1) by ring,
            heq, mul_comm, ← q_sq_sub_one_eq_mul]
        rw [hlhs, ZMod.natCast_self]
    have h0 : (D.theta (((D.q - 1) : ℕ) : D.Lab2) u - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hmul1)

private lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by simp [FieldData.psi]

private lemma psi_add (D : FieldData) (x y : D.Fq) : D.psi (x + y) = D.psi x * D.psi y := by
  simp only [FieldData.psi, map_add, ← Complex.exp_add]
  have hmod : (Algebra.trace (ZMod D.p) D.Fq x + Algebra.trace (ZMod D.p) D.Fq y).val ≡
      (Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val [MOD D.p] := by
    rw [ZMod.val_add]; exact Nat.mod_modEq _ _
  rw [exp_two_pi_I_div_eq_of_modEq D.hp.ne_zero hmod]; congr 1; push_cast; ring

private lemma psi_norm (D : FieldData) (x : D.Fq) : ‖D.psi x‖ = 1 := by
  simp only [FieldData.psi]
  have heq : (2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) / (D.p : ℂ)) =
      ((2 * Real.pi * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℝ) / (D.p : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [heq]; exact Complex.norm_exp_ofReal_mul_I _

private lemma psi_ne_zero (D : FieldData) (x : D.Fq) : D.psi x ≠ 0 := by simp [FieldData.psi, Complex.exp_ne_zero]

private lemma psi_neg (D : FieldData) (x : D.Fq) : D.psi (-x) = star (D.psi x) := by
  have h1 : D.psi (-x) * D.psi x = 1 := by rw [← psi_add, neg_add_cancel, psi_zero]
  have h2 : star (D.psi x) * D.psi x = 1 := by
    rw [RCLike.star_def, Complex.conj_mul', psi_norm D x, Complex.ofReal_one, one_pow]
  exact mul_right_cancel₀ (psi_ne_zero D x) (h1.trans h2.symm)

private lemma psi_nontrivial (D : FieldData) : ∃ c : D.Fq, D.psi c ≠ 1 := by
  have := fq_isDomain D
  let P : Polynomial D.Fq := ∑ i ∈ Finset.range D.r, Polynomial.X ^ (D.p ^ i)
  have hrm1 : D.r - 1 ∈ Finset.range D.r := Finset.mem_range.mpr (by have := D.hr; omega)
  have hP_ne : P ≠ 0 := by
    intro h0
    have hc := congrArg (fun q : Polynomial D.Fq => q.coeff (D.p ^ (D.r - 1))) h0
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single (D.r - 1)] at hc
    · simp at hc
    · intro i hi hne; rw [Finset.mem_range] at hi
      have hne_pow : D.p ^ (D.r - 1) ≠ D.p ^ i :=
        fun h => hne (Nat.pow_right_injective D.hp.one_lt h).symm
      simp [hne_pow]
    · intro habs; exact False.elim (habs hrm1)
  have hdeg : P.natDegree < D.q := by
    have hle : P.natDegree ≤ D.p ^ (D.r - 1) := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi; rw [Finset.mem_range] at hi; rw [Polynomial.natDegree_X_pow]
      exact Nat.pow_le_pow_right D.hp.pos (by omega)
    have hlt : D.p ^ (D.r - 1) < D.p ^ D.r :=
      Nat.pow_lt_pow_right D.hp.one_lt (by have := D.hr; omega)
    exact lt_of_le_of_lt hle hlt
  have hcard : P.roots.toFinset.card < Fintype.card D.Fq := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ < D.q := hdeg
      _ = Fintype.card D.Fq := (card_fq D).symm
  obtain ⟨c, hc_mem⟩ : ∃ c : D.Fq, c ∉ P.roots.toFinset := by
    by_contra h; push Not at h
    exact (Finset.card_le_card (fun x _ => h x)).not_gt hcard
  have htr_ne : Algebra.trace (ZMod D.p) D.Fq c ≠ 0 := by
    intro h0
    have hmap := FiniteField.algebraMap_trace_eq_sum_pow (ZMod D.p) D.Fq c
    rw [finrank_fq, Nat.card_zmod, h0, map_zero] at hmap
    have heval : P.eval c = 0 := by
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_X_pow]; exact hmap.symm
    exact hc_mem (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP_ne).mpr heval))
  refine ⟨c, ?_⟩
  simp only [FieldData.psi]
  intro heq
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff D.hp.ne_zero] at heq
  have : NeZero D.p := ⟨D.hp.ne_zero⟩
  have hval_lt : (Algebra.trace (ZMod D.p) D.Fq c).val < D.p := ZMod.val_lt _
  have hval_pos : 0 < (Algebra.trace (ZMod D.p) D.Fq c).val := by
    rcases Nat.eq_zero_or_pos (Algebra.trace (ZMod D.p) D.Fq c).val with h0 | hp
    · exact False.elim (htr_ne ((ZMod.val_eq_zero _).mp h0))
    · exact hp
  exact (Nat.le_of_dvd hval_pos heq).not_gt hval_lt

private lemma sum_psi_mul (D : FieldData) (b : D.Fq) :
    ∑ x : D.Fq, D.psi (b * x) = if b = 0 then (D.q : ℂ) else 0 := by
  split_ifs with hb
  · subst hb; simp [psi_zero, Finset.sum_const, Finset.card_univ, card_fq]
  · have hbij : ∑ x : D.Fq, D.psi (b * x) = ∑ y : D.Fq, D.psi y :=
      Finset.sum_bij (fun x _ => b * x) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => mul_left_cancel₀ hb h)
        (fun y _ => ⟨b⁻¹ * y, Finset.mem_univ _, by rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]⟩)
        (fun _ _ => rfl)
    rw [hbij]
    obtain ⟨c, hc⟩ := psi_nontrivial D
    set S := ∑ y : D.Fq, D.psi y
    have hshift : D.psi c * S = S := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun y _ => c + y) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => add_left_cancel h) (fun z _ => ⟨z - c, Finset.mem_univ _, add_sub_cancel c z⟩)
        (fun y _ => by rw [psi_add])
    have h0 : (D.psi c - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

private lemma gauss_zero (D : FieldData) : D.gauss 0 = -1 := by
  simp only [FieldData.gauss, FieldData.gaussG, one_mul]
  rw [Finset.sum_congr rfl (fun x hx => by rw [chi_zero_left D (Finset.mem_filter.mp hx).2, one_mul])]
  have hsum : ∑ x : D.Fq, D.psi x = 0 := by simpa using sum_psi_mul D 1
  have hsplit : ∑ x : D.Fq, D.psi x =
      D.psi 0 + ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.psi x := by
    rw [← Finset.add_sum_erase Finset.univ D.psi (Finset.mem_univ 0)]
    congr 1; apply Finset.sum_congr; · ext x; simp [Finset.mem_erase]
    · intro _ _; rfl
  rw [hsplit, psi_zero] at hsum
  linear_combination hsum

private lemma jacobi_neg (D : FieldData) (hq : 2 < D.q) (α : D.Lab) :
    D.jacobi α (-α) = if α = 0 then (D.q : ℂ) - 2 else -D.chi α (-1) := by
  simp only [FieldData.jacobi]
  split_ifs with hα
  · subst hα
    rw [Finset.sum_congr rfl (fun x hx => by
      have hx' := (Finset.mem_filter.mp hx).2
      rw [chi_zero_left D hx'.1, neg_zero, chi_zero_left D (sub_ne_zero.mpr hx'.2.symm), mul_one])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hfilt : Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1) =
        Finset.univ \ ({0, 1} : Finset D.Fq) := by ext x; simp
    rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_fq,
      Finset.card_pair (zero_ne_one : (0 : D.Fq) ≠ 1), Nat.cast_sub (by omega), Nat.cast_ofNat]
  · have hsum : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1),
        D.chi α x * D.chi (-α) (1 - x) =
        ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0 ∧ u ≠ -1), D.chi α u := by
      refine Finset.sum_bij (fun x _ => x / (1 - x)) ?_ ?_ ?_ ?_
      · intro x hx; rw [Finset.mem_filter] at hx ⊢
        have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.2.symm
        refine ⟨Finset.mem_univ _, div_ne_zero hx.2.1 h1x, ?_⟩
        intro heq; rw [div_eq_iff h1x] at heq
        exact one_ne_zero (by linear_combination heq : (1 : D.Fq) = 0)
      · intro x₁ hx₁ x₂ hx₂ heq; rw [Finset.mem_filter] at hx₁ hx₂
        rw [field_div_eq_div_iff (sub_ne_zero.mpr hx₁.2.2.symm) (sub_ne_zero.mpr hx₂.2.2.symm)] at heq
        linear_combination heq
      · intro u hu; rw [Finset.mem_filter] at hu
        have h1u : 1 + u ≠ 0 := fun h => hu.2.2 (by linear_combination h)
        refine ⟨u / (1 + u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_ne_zero hu.2.1 h1u, ?_⟩, ?_⟩
        · intro heq; rw [field_div_eq_one_iff_eq h1u] at heq
          exact one_ne_zero (by linear_combination -heq : (1 : D.Fq) = 0)
        · have hsub : 1 - u / (1 + u) = 1 / (1 + u) := by
            calc 1 - u / (1 + u) = (1 + u) / (1 + u) - u / (1 + u) := by rw [div_self h1u]
              _ = (1 + u - u) / (1 + u) := (sub_div _ _ _).symm
              _ = 1 / (1 + u) := by rw [add_sub_cancel_right]
          rw [hsub, div_div_div_cancel_right₀ h1u, div_one]
      · intro x _; rw [chi_div]
    rw [hsum]
    have hsplit : ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0), D.chi α u =
        D.chi α (-1) + ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0 ∧ u ≠ -1), D.chi α u := by
      have hm1 : (-1 : D.Fq) ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, neg_ne_zero.mpr one_ne_zero⟩
      rw [← Finset.add_sum_erase _ _ hm1]
      congr 1; apply Finset.sum_congr; · ext u; simp [Finset.mem_erase, and_comm]
      · intro _ _; rfl
    rw [sum_chi_fq_units D hq α, if_neg hα] at hsplit
    linear_combination -hsplit

private lemma gauss_mul_gauss_split (D : FieldData) (α β : D.Lab) :
    D.gauss α * D.gauss β =
      D.chi β (-1) * ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi (α + β) x +
      D.jacobi α β * D.gauss (α + β) := by
  simp only [FieldData.gauss, FieldData.gaussG, one_mul, FieldData.jacobi]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  let S0 := Finset.univ.filter (fun p : D.Fq × D.Fq => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 = 0)
  let S1 := Finset.univ.filter (fun p : D.Fq × D.Fq => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 + p.2 ≠ 0)
  have hprod : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0),
      ∑ y ∈ Finset.univ.filter (fun y : D.Fq => y ≠ 0),
        D.chi α x * D.psi x * (D.chi β y * D.psi y) =
      (∑ p ∈ S0, D.chi α p.1 * D.chi β p.2 * D.psi (p.1 + p.2)) +
      (∑ p ∈ S1, D.chi α p.1 * D.chi β p.2 * D.psi (p.1 + p.2)) := by
    rw [← Finset.sum_product']
    have hdisj : Disjoint S0 S1 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2.2.2 h1.2.2)
    have hunion : S0 ∪ S1 = Finset.univ.filter (fun x : D.Fq => x ≠ 0) ×ˢ
        Finset.univ.filter (fun y : D.Fq => y ≠ 0) := by
      ext ⟨x, y⟩; simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product]; tauto
    rw [← hunion, Finset.sum_union hdisj]
    have hterm : ∀ p : D.Fq × D.Fq,
        D.chi α p.1 * D.psi p.1 * (D.chi β p.2 * D.psi p.2) =
          D.chi α p.1 * D.chi β p.2 * D.psi (p.1 + p.2) := by
      intro p; rw [psi_add]; ring
    simp_rw [hterm]
  rw [hprod]
  congr 1
  · refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
    · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩
    · intro p₁ hp₁ p₂ hp₂ heq
      have h1 := (Finset.mem_filter.mp hp₁).2.2.2
      have h2 := (Finset.mem_filter.mp hp₂).2.2.2
      ext; · exact heq
      · linear_combination h1 - h2 - heq
    · intro x hx; rw [Finset.mem_filter] at hx
      exact ⟨(x, -x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2, neg_ne_zero.mpr hx.2, add_neg_cancel x⟩, rfl⟩
    · intro p hp
      have hadd : p.1 + p.2 = 0 := (Finset.mem_filter.mp hp).2.2.2
      have hp2 : p.2 = (-1) * p.1 := by linear_combination hadd
      rw [hadd, psi_zero, mul_one, hp2, chi_mul, chi_add_lab]; ring
  · simp_rw [Finset.sum_mul]; rw [← Finset.sum_product']
    refine Finset.sum_bij (fun p _ => (p.1 + p.2, p.1 / (p.1 + p.2))) ?_ ?_ ?_ ?_
    · intro p hp; rw [Finset.mem_filter] at hp
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, hp.2.2.2⟩, Finset.mem_univ _, div_ne_zero hp.2.1 hp.2.2.2, ?_⟩
      intro hdiv; rw [field_div_eq_one_iff_eq hp.2.2.2] at hdiv
      exact hp.2.2.1 (by linear_combination -hdiv)
    · intro p₁ hp₁ p₂ hp₂ heq; rw [Finset.mem_filter] at hp₁ hp₂
      have hs : p₁.1 + p₁.2 = p₂.1 + p₂.2 := congrArg Prod.fst heq
      have hd : p₁.1 / (p₁.1 + p₁.2) = p₂.1 / (p₂.1 + p₂.2) := congrArg Prod.snd heq
      rw [hs, div_left_inj' hp₂.2.2.2] at hd
      ext; · exact hd
      · linear_combination hs - hd
    · intro q hq; rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hq
      refine ⟨(q.1 * q.2, q.1 * (1 - q.2)), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mul_ne_zero hq.1.2 hq.2.2.1, mul_ne_zero hq.1.2 (sub_ne_zero.mpr hq.2.2.2.symm),
        by rw [show q.1 * q.2 + q.1 * (1 - q.2) = q.1 by ring]; exact hq.1.2⟩, ?_⟩
      ext; · ring
      · have hsum : q.1 * q.2 + q.1 * (1 - q.2) = q.1 := by ring
        rw [hsum, mul_div_cancel_left₀ _ hq.1.2]
    · intro p hp; rw [Finset.mem_filter] at hp
      have hz : p.1 + p.2 ≠ 0 := hp.2.2.2
      have hp1 : p.1 = (p.1 + p.2) * (p.1 / (p.1 + p.2)) := (mul_div_cancel₀ _ hz).symm
      have hp2 : p.2 = (p.1 + p.2) * (1 - p.1 / (p.1 + p.2)) := by rw [mul_sub, mul_one, ← hp1]; ring
      calc D.chi α p.1 * D.chi β p.2 * D.psi (p.1 + p.2)
          = D.chi α ((p.1 + p.2) * (p.1 / (p.1 + p.2))) *
              D.chi β ((p.1 + p.2) * (1 - p.1 / (p.1 + p.2))) * D.psi (p.1 + p.2) := by
                conv_lhs => arg 1; arg 1; rw [hp1]
                conv_lhs => arg 1; arg 2; rw [hp2]
        _ = D.chi α (p.1 / (p.1 + p.2)) * D.chi β (1 - p.1 / (p.1 + p.2)) *
              (D.chi (α + β) (p.1 + p.2) * D.psi (p.1 + p.2)) := by
                rw [chi_mul, chi_mul, chi_add_lab]; ring

private lemma gauss_mul_gauss_neg (D : FieldData) (hq : 2 < D.q) (α : D.Lab) :
    D.gauss α * D.gauss (-α) = if α = 0 then 1 else D.chi α (-1) * (D.q : ℂ) := by
  split_ifs with hα
  · subst hα; rw [neg_zero, gauss_zero]; ring
  · rw [gauss_mul_gauss_split, add_neg_cancel, sum_chi_fq_units D hq 0, if_pos rfl,
      jacobi_neg D hq α, if_neg hα, gauss_zero]
    have hneg : D.chi (-α) (-1) = D.chi α (-1) := by rw [chi_neg_lab, star_chi_neg_one]
    rw [hneg]; ring

private lemma star_gauss (D : FieldData) (α : D.Lab) :
    star (D.gauss α) = D.chi α (-1) * D.gauss (-α) := by
  simp only [FieldData.gauss, FieldData.gaussG, one_mul, star_sum, star_mul']
  have hbij : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0),
        star (D.psi x) * star (D.chi α x) =
      ∑ y ∈ Finset.univ.filter (fun y : D.Fq => y ≠ 0),
        D.chi α (-1) * (D.chi (-α) y * D.psi y) := by
    refine Finset.sum_bij (fun x _ => -x) ?_ ?_ ?_ ?_
    · intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, neg_ne_zero.mpr hx.2⟩
    · intro x₁ _ x₂ _ h; exact neg_inj.mp h
    · intro y hy; rw [Finset.mem_filter] at hy
      exact ⟨-y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, neg_ne_zero.mpr hy.2⟩, neg_neg y⟩
    · intro x _
      rw [← psi_neg, ← chi_neg_lab]
      have hmx : -x = (-1 : D.Fq) * x := by ring
      rw [hmx, chi_mul, chi_neg_lab D α (-1), star_chi_neg_one]
      have hsq : D.chi α (-1) * D.chi α (-1) = 1 := by rw [← sq, chi_neg_one_sq]
      calc D.psi ((-1 : D.Fq) * x) * D.chi (-α) x
          = (D.chi α (-1) * D.chi α (-1)) * (D.psi ((-1 : D.Fq) * x) * D.chi (-α) x) := by
              rw [hsq, one_mul]
        _ = D.chi α (-1) * (D.chi α (-1) * D.chi (-α) x * D.psi ((-1 : D.Fq) * x)) := by ring
  have hcomm : (∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0),
      star (D.psi x) * star (D.chi α x)) =
      ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), star (D.chi α x) * star (D.psi x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [← hcomm, hbij, ← Finset.mul_sum]

/-! ### Layer 2: `Bgate`, `canonMbr`, `FxDag`, `Dgate` orthogonality -/

private lemma isqrt_conj (x : ℝ) : star (isqrt x) = isqrt x := by simp [isqrt]

private lemma isqrt_mul_self {x : ℝ} (hx : 0 ≤ x) : isqrt x * isqrt x = (x : ℂ)⁻¹ := by
  simp only [isqrt]; rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hx, Complex.ofReal_inv]

private lemma isqrt_q_sub_one_sq (D : FieldData) :
    isqrt (D.q - 1) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := by
  have h1 : (D.q : ℝ) - 1 = ((D.q - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub D.one_lt_q.le, Nat.cast_one]
  rw [h1, isqrt_mul_self (Nat.cast_nonneg _), Nat.cast_sub D.one_lt_q.le, Nat.cast_one,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]

private lemma fq_two_eq_zero_iff (D : FieldData) : (2 : D.Fq) = 0 ↔ ringChar D.Fq = 2 := by
  have : CharP D.Fq D.p := charP_fq D
  rw [ringChar_fq D]
  have hcast : (2 : D.Fq) = ((2 : ℕ) : D.Fq) := by norm_cast
  rw [hcast, CharP.cast_eq_zero_iff D.Fq D.p 2, Nat.Prime.dvd_iff_eq (by norm_num) D.hp.ne_one, eq_comm]

private lemma fq_four_eq_zero_iff (D : FieldData) : (4 : D.Fq) = 0 ↔ ringChar D.Fq = 2 := by
  have := fq_isDomain D
  have h4 : (4 : D.Fq) = (2 : D.Fq) * (2 : D.Fq) := by norm_num
  rw [h4, mul_eq_zero, or_self, fq_two_eq_zero_iff]

private lemma fq2_two_ne_zero (D : FieldData) (h : ringChar D.Fq ≠ 2) : (2 : D.Fq2) ≠ 0 := by
  have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp h
  intro h0; apply h2; apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2; rw [map_ofNat, map_zero]; exact h0

private lemma algebraMap_two_inv (D : FieldData) (h : ringChar D.Fq ≠ 2) :
    algebraMap D.Fq D.Fq2 (2 : D.Fq)⁻¹ = (2 : D.Fq2)⁻¹ := by
  have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp h
  have h2' : (2 : D.Fq2) ≠ 0 := fq2_two_ne_zero D h
  apply mul_right_cancel₀ h2'
  rw [← show algebraMap D.Fq D.Fq2 2 = 2 from map_ofNat _ 2, ← map_mul,
    inv_mul_cancel₀ h2, map_one, inv_mul_cancel₀ h2']

private lemma algebraMap_four_inv (D : FieldData) (h : ringChar D.Fq ≠ 2) :
    algebraMap D.Fq D.Fq2 (4 : D.Fq)⁻¹ = (4 : D.Fq2)⁻¹ := by
  have h4 : (4 : D.Fq) ≠ 0 := mt (fq_four_eq_zero_iff D).mp h
  have h4' : (4 : D.Fq2) ≠ 0 := by
    have h4eq : (4 : D.Fq2) = 2 * 2 := by norm_num
    rw [h4eq]; exact mul_ne_zero (fq2_two_ne_zero D h) (fq2_two_ne_zero D h)
  apply mul_right_cancel₀ h4'
  rw [← show algebraMap D.Fq D.Fq2 4 = 4 from map_ofNat _ 4, ← map_mul,
    inv_mul_cancel₀ h4, map_one, inv_mul_cancel₀ h4']

private lemma quad_factor {K : Type*} [CommRing K] (t w₀ w : K) (hw₀ : w₀ ^ 2 - w₀ + t = 0) :
    w ^ 2 - w + t = (w - w₀) * (w - (1 - w₀)) := by linear_combination hw₀

private lemma quad_roots_eq_pair {K : Type*} [Field K] (t w₀ w : K) (hw₀ : w₀ ^ 2 - w₀ + t = 0) :
    w ^ 2 - w + t = 0 ↔ w = w₀ ∨ w = 1 - w₀ := by
  rw [quad_factor t w₀ w hw₀, mul_eq_zero, sub_eq_zero, sub_eq_zero]

private lemma quad_symm_root {K : Type*} [CommRing K] (t w : K) (hw : w ^ 2 - w + t = 0) :
    (1 - w) ^ 2 - (1 - w) + t = 0 := by linear_combination hw

private lemma quad_root_eq_sub_self_iff (D : FieldData) (x : D.Fq) :
    x = 1 - x ↔ ringChar D.Fq ≠ 2 ∧ x = (2 : D.Fq)⁻¹ := by
  constructor
  · intro hx
    have h2x : (2 : D.Fq) * x = 1 := by linear_combination hx
    have h2 : (2 : D.Fq) ≠ 0 := by intro h0; rw [h0, zero_mul] at h2x; exact zero_ne_one h2x
    refine ⟨mt (fq_two_eq_zero_iff D).mpr h2, ?_⟩
    apply mul_left_cancel₀ h2; rw [h2x, mul_inv_cancel₀ h2]
  · rintro ⟨hc, rfl⟩
    have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
    apply mul_left_cancel₀ h2; rw [mul_sub, mul_one, mul_inv_cancel₀ h2]; ring

private lemma quad_exists_root_fq2 (D : FieldData) (t : D.Fq)
    (hno : ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0) :
    ∃ z : D.Fq2, z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0 := by
  have := fq_isDomain D
  let P : Polynomial D.Fq := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C t
  have hdeg : P.natDegree = 2 := by
    have hP : P = Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C t) := by simp only [P]; ring
    have hlt : (-Polynomial.X + Polynomial.C t).natDegree < (Polynomial.X ^ 2 : Polynomial D.Fq).natDegree := by
      calc (-Polynomial.X + Polynomial.C t).natDegree
          ≤ max (-Polynomial.X : Polynomial D.Fq).natDegree (Polynomial.C t : Polynomial D.Fq).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ 1 := by simp [Polynomial.natDegree_neg, Polynomial.natDegree_X, Polynomial.natDegree_C]
        _ < 2 := by norm_num
        _ = (Polynomial.X ^ 2 : Polynomial D.Fq).natDegree := by rw [Polynomial.natDegree_X_pow]
    rw [hP, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hP_ne : P ≠ 0 := by intro h0; rw [h0, Polynomial.natDegree_zero] at hdeg; norm_num at hdeg
  have hirr : Irreducible P := by
    refine ⟨fun hu => by have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega, ?_⟩
    intro a b hab
    by_cases ha0 : a = 0
    · subst ha0; simp at hab; exact absurd hab hP_ne
    by_cases hb0 : b = 0
    · subst hb0; simp at hab; exact absurd hab hP_ne
    have hsum : 2 = a.natDegree + b.natDegree := by rw [← hdeg, hab, Polynomial.natDegree_mul ha0 hb0]
    rcases Nat.lt_trichotomy a.natDegree 1 with ha | ha | ha
    · left
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree ha0, show a.natDegree = 0 by omega, Nat.cast_zero])
    · exfalso
      have ha1 : a.natDegree = 1 := ha
      have hlc : a.coeff 1 ≠ 0 := by rw [← ha1]; exact Polynomial.leadingCoeff_ne_zero.mpr ha0
      have ha_eq : a = Polynomial.C (a.coeff 1) * Polynomial.X + Polynomial.C (a.coeff 0) :=
        Polynomial.eq_X_add_C_of_natDegree_le_one ha1.le
      let r : D.Fq := -(a.coeff 0) / a.coeff 1
      have har : a.eval r = 0 := by
        rw [ha_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          Polynomial.eval_C]
        dsimp only [r]; rw [mul_div_cancel₀ _ hlc, neg_add_cancel]
      have hPr : P.eval r = 0 := by rw [hab, Polynomial.eval_mul, har, zero_mul]
      exact hno ⟨r, by simpa [P] using hPr⟩
    · right
      exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by
        rw [Polynomial.degree_eq_natDegree hb0, show b.natDegree = 0 by omega, Nat.cast_zero])
  haveI : Fact (Irreducible P) := ⟨hirr⟩
  haveI : CharP D.Fq D.p := charP_fq D
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  have hP_monic : P.Monic := by
    have hP : P = Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C t) := by simp [P]; ring
    rw [hP]
    refine Polynomial.Monic.add_of_left (Polynomial.monic_X_pow 2) ?_
    have hdeg1 : (-Polynomial.X + Polynomial.C t).natDegree ≤ 1 := by
      calc (-Polynomial.X + Polynomial.C t).natDegree
          ≤ max (-Polynomial.X : Polynomial D.Fq).natDegree (Polynomial.C t : Polynomial D.Fq).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ 1 := by simp [Polynomial.natDegree_neg, Polynomial.natDegree_X, Polynomial.natDegree_C]
    calc (-Polynomial.X + Polynomial.C t).degree
        ≤ ((-Polynomial.X + Polynomial.C t).natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
      _ ≤ (1 : WithBot ℕ) := Nat.cast_le.mpr hdeg1
      _ < (2 : WithBot ℕ) := WithBot.coe_lt_coe.mpr (by norm_num)
      _ = (Polynomial.X ^ 2 : Polynomial D.Fq).degree := by simp [Polynomial.degree_X_pow]
  have hfin1 : Module.finrank D.Fq (AdjoinRoot P) = 2 := by
    have h := (AdjoinRoot.powerBasis' hP_monic).finrank; rwa [AdjoinRoot.powerBasis'_dim, hdeg] at h
  let e1 := FiniteField.algEquivExtension D.Fq D.p 2 (AdjoinRoot P) hfin1
  let e2 := FiniteField.algEquivExtension D.Fq D.p 2 D.Fq2 (finrank_fq2 D)
  let e : AdjoinRoot P ≃ₐ[D.Fq] D.Fq2 := e1.trans e2.symm
  refine ⟨e (AdjoinRoot.root P), ?_⟩
  have hroot : Polynomial.aeval (e (AdjoinRoot.root P)) P = 0 := AdjoinRoot.aeval_algHom_eq_zero P e.toAlgHom
  simp only [P, map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hroot
  exact hroot

private def B_T2 (D : FieldData) (t : D.Fq) : Prop := ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹
private def B_T3 (D : FieldData) (t : D.Fq) : Prop :=
  t ≠ 0 ∧ ¬ B_T2 D t ∧ ∃ x : D.Fq, x ^ 2 - x + t = 0
private def B_T4 (D : FieldData) (t : D.Fq) : Prop :=
  t ≠ 0 ∧ ¬ B_T2 D t ∧ ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0
private def Z_nb (D : FieldData) : Finset D.Fq2 :=
  Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ z ^ D.q ≠ z)

private lemma B_T4_root_iff (D : FieldData) {t : D.Fq} (ht : B_T4 D t) (z : D.Fq2) :
    z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0 ↔ z ∈ Z_nb D ∧ D.nrm z = t := by
  constructor
  · intro hz
    have hzq_ne : z ^ D.q ≠ z := by
      intro heq
      obtain ⟨x, rfl⟩ := (fq2_pow_q_eq_self_iff D z).mp heq
      apply ht.2.2
      refine ⟨x, ?_⟩
      apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
      simpa only [map_add, map_sub, map_pow, map_zero] using hz
    have hzq_root : (z ^ D.q) ^ 2 - z ^ D.q + algebraMap D.Fq D.Fq2 t = 0 := by
      have hmap := congrArg (fq2Frob D) hz
      rw [map_zero, map_add, map_sub, map_pow, fq2Frob_apply, fq2Frob_apply,
        ← map_pow, fq_pow_q] at hmap
      exact hmap
    rw [quad_roots_eq_pair _ z _ hz] at hzq_root
    have hzq : z ^ D.q = 1 - z := hzq_root.resolve_left hzq_ne
    have htr : D.tr z = 1 := by
      apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
      rw [algebraMap_tr, hzq, map_one]; ring
    have hnrm : D.nrm z = t := by
      apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
      rw [algebraMap_nrm_mul, hzq]; linear_combination -hz
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, htr, hzq_ne⟩, hnrm⟩
  · rintro ⟨hz, rfl⟩
    simp only [Z_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hzq : z ^ D.q = 1 - z := by
      have h := algebraMap_tr D z; rw [hz.1, map_one] at h; linear_combination -h
    rw [algebraMap_nrm_mul, hzq]; ring

private def InBranchDom (D : FieldData) (br : Bool × D.Fq2) : Prop :=
  if br.1 then br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1
  else ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r

private lemma inBranchDom_iff_mem_branchSrc (D : FieldData) (br : Bool × D.Fq2) :
    InBranchDom D br ↔
      (br.1 = false ∧ ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r) ∨
      (br.1 = true ∧ br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1) := by
  cases h : br.1 <;> simp [InBranchDom, h]

private lemma Bgate_mem_InBranchDom (D : FieldData) (γ : D.Lab) (br : Bool × D.Fq2) (t : D.Fq)
    (hne : Bgate D γ br t ≠ 0) : InBranchDom D br := by
  simp only [Bgate, Matrix.of_apply] at hne
  by_cases ht0 : t = 0
  · subst ht0; simp only [if_pos rfl] at hne
    have hbr2 : br.2 = 1 := by by_contra h; simp [h] at hne
    rw [InBranchDom]; cases h1 : br.1
    · exact ⟨1, one_ne_zero, by rw [hbr2, map_one]⟩
    · exact ⟨by rw [hbr2]; exact one_ne_zero, by rw [hbr2, one_pow]⟩
  · by_cases ht2 : ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹
    · simp only [if_neg ht0, if_pos ht2] at hne
      have hbr2 : br.2 = 1 := by by_contra h; simp [h] at hne
      rw [InBranchDom]; cases h1 : br.1
      · exact ⟨1, one_ne_zero, by rw [hbr2, map_one]⟩
      · exact ⟨by rw [hbr2]; exact one_ne_zero, by rw [hbr2, one_pow]⟩
    · by_cases hex : ∃ x : D.Fq, x ^ 2 - x + t = 0
      · simp only [if_neg ht0, if_neg ht2, if_pos hex] at hne
        have hbr1 : br.1 = false := by
          cases h1 : br.1; · rfl
          · exfalso; apply hne; simp [h1]
        rw [hbr1] at hne
        have hsum_ne : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0),
            (if br.2 = algebraMap D.Fq D.Fq2 (x / (1 - x)) then D.chi γ (1 - x) else 0) ≠ 0 := by
          intro h0; apply hne; rw [if_neg Bool.false_ne_true, h0, mul_zero]
        obtain ⟨x, hx, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
        rw [Finset.mem_filter] at hx
        have hbr2 : br.2 = algebraMap D.Fq D.Fq2 (x / (1 - x)) := by
          by_contra h; rw [if_neg h] at hterm; exact hterm rfl
        have hx0 : x ≠ 0 := fun h => ht0 (by simpa [h] using hx.2)
        have hx1 : 1 - x ≠ 0 := fun h => by
          have hx1' : x = 1 := by linear_combination -h
          exact ht0 (by simpa [hx1'] using hx.2)
        rw [InBranchDom, hbr1]; exact ⟨x / (1 - x), div_ne_zero hx0 hx1, hbr2⟩
      · simp only [if_neg ht0, if_neg ht2, if_neg hex] at hne
        have hbr1 : br.1 = true := by
          cases h1 : br.1; · exfalso; apply hne; simp [h1]
          · rfl
        rw [hbr1] at hne
        have hsum_ne : ∑ z ∈ Finset.univ.filter
            (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0),
            (if br.2 = z / z ^ D.q then D.theta (theta0Lab D γ) z else 0) ≠ 0 := by
          intro h0; apply hne; rw [if_pos rfl, h0, mul_zero, neg_zero]
        obtain ⟨z, hz, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
        rw [Finset.mem_filter] at hz
        have hbr2 : br.2 = z / z ^ D.q := by
          by_contra h; rw [if_neg h] at hterm; exact hterm rfl
        have hz0 : z ≠ 0 := by
          intro h0; rw [h0, zero_pow two_ne_zero, sub_zero, zero_add] at hz
          exact ht0 (FaithfulSMul.algebraMap_injective D.Fq D.Fq2 (by rw [hz.2, map_zero]))
        have hzq0 : z ^ D.q ≠ 0 := fq2_pow_ne_zero D hz0 D.q
        rw [InBranchDom, hbr1]
        refine ⟨by rw [hbr2]; exact div_ne_zero hz0 hzq0, ?_⟩
        rw [hbr2, fq2_div_pow_q_add_one D hz0]
  where
    fq2_div_pow_q_add_one (D : FieldData) {z : D.Fq2} (hz0 : z ≠ 0) :
        (z / z ^ D.q) ^ (D.q + 1) = 1 := by
      have hzq : z ^ D.q ≠ 0 := fq2_pow_ne_zero D hz0 D.q
      rw [field_div_pow, field_div_eq_one_iff_eq (fq2_pow_ne_zero D hzq (D.q + 1))]
      calc z ^ (D.q + 1) = z * z ^ D.q := pow_succ' z D.q
        _ = z ^ (D.q ^ 2) * z ^ D.q := by rw [fq2_pow_q_sq]
        _ = z ^ (D.q ^ 2 + D.q) := (pow_add z _ _).symm
        _ = (z ^ D.q) ^ (D.q + 1) := by rw [← pow_mul, show D.q * (D.q + 1) = D.q ^ 2 + D.q from by ring]

private lemma Bgate_orth (D : FieldData) (γ : D.Lab) (t₁ t₂ : D.Fq) :
    ∑ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₂ =
      if t₁ = t₂ then 1 else 0 := by
  have hchi_sq : ∀ (α : D.Lab) {x : D.Fq}, x ≠ 0 → star (D.chi α x) * D.chi α x = 1 := by
    intro α x hx; rw [← chi_neg_lab, ← chi_add_lab, neg_add_cancel, chi_zero_left D hx]
  have htheta_sq : ∀ (k : D.Lab2) {z : D.Fq2}, z ≠ 0 → star (D.theta k z) * D.theta k z = 1 := by
    intro k z hz; rw [← theta_neg_lab, ← theta_add_lab, neg_add_cancel, theta_zero_left D hz]
  have hisqrt2 : star (isqrt 2) * isqrt 2 = (2 : ℂ)⁻¹ := by
    rw [isqrt_conj, isqrt_mul_self (by norm_num)]; norm_num
  have hB3_char : ∀ t (ht : B_T3 D t), ∃ x₀ : D.Fq,
      x₀ ^ 2 - x₀ + t = 0 ∧ x₀ ≠ 0 ∧ x₀ ≠ 1 ∧ x₀ ≠ 1 - x₀ ∧
      x₀ / (1 - x₀) ≠ 1 ∧ x₀ / (1 - x₀) ≠ (1 - x₀) / x₀ ∧
      Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) = {x₀, 1 - x₀} := by
    intro t ht; obtain ⟨x₀, hx₀⟩ := ht.2.2
    have hx₀_0 : x₀ ≠ 0 := fun h => ht.1 (by simpa [h] using hx₀)
    have hx₀_1 : x₀ ≠ 1 := fun h => ht.1 (by rw [h] at hx₀; simpa using hx₀)
    have h1x₀ : 1 - x₀ ≠ 0 := sub_ne_zero.mpr hx₀_1.symm
    have hne : x₀ ≠ 1 - x₀ := by
      intro h; apply ht.2.1; obtain ⟨hc, hx2⟩ := (quad_root_eq_sub_self_iff D x₀).mp h
      refine ⟨hc, ?_⟩; rw [hx2] at hx₀
      have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
      have h4 : (4 : D.Fq) = 2 * 2 := by norm_num
      have h4inv : (4 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by rw [h4, field_mul_inv]
      calc t = (2 : D.Fq)⁻¹ - (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by linear_combination hx₀
        _ = (2 * (2 : D.Fq)⁻¹) * (2 : D.Fq)⁻¹ - (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by rw [mul_inv_cancel₀ h2, one_mul]
        _ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by ring
        _ = (4 : D.Fq)⁻¹ := h4inv.symm
    have hdiv1 : x₀ / (1 - x₀) ≠ 1 := fun h => hne ((field_div_eq_one_iff_eq h1x₀).mp h)
    have hdiv2 : x₀ / (1 - x₀) ≠ (1 - x₀) / x₀ := by
      intro h; rw [field_div_eq_div_iff h1x₀ hx₀_0] at h
      exact hne (by linear_combination (by linear_combination h : (2 : D.Fq) * x₀ = 1))
    have hfilt : Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) = {x₀, 1 - x₀} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]; exact quad_roots_eq_pair t x₀ x hx₀
    exact ⟨x₀, hx₀, hx₀_0, hx₀_1, hne, hdiv1, hdiv2, hfilt⟩
  have hB4_char : ∀ t (ht : B_T4 D t), ∃ z₀ : D.Fq2,
      z₀ ^ 2 - z₀ + algebraMap D.Fq D.Fq2 t = 0 ∧ z₀ ≠ 0 ∧ 1 - z₀ ≠ 0 ∧
      z₀ ^ D.q = 1 - z₀ ∧ z₀ ≠ 1 - z₀ ∧
      z₀ / (1 - z₀) ≠ 1 ∧ z₀ / (1 - z₀) ≠ (1 - z₀) / z₀ ∧
      Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) = {z₀, 1 - z₀} := by
    intro t ht; obtain ⟨z₀, hz₀⟩ := quad_exists_root_fq2 D t ht.2.2
    have hmem := (B_T4_root_iff D ht z₀).mp hz₀
    have hnb := hmem.1; simp only [Z_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hnb
    have hz₀q : z₀ ^ D.q = 1 - z₀ := by
      have h := algebraMap_tr D z₀; rw [hnb.1, map_one] at h; linear_combination -h
    have hz₀_0 : z₀ ≠ 0 := fun h => hnb.2 (by rw [h, zero_pow (q_pos D).ne'])
    have h1z₀ : 1 - z₀ ≠ 0 := by rw [← hz₀q]; exact fq2_pow_ne_zero D hz₀_0 D.q
    have hne : z₀ ≠ 1 - z₀ := by rw [← hz₀q]; exact hnb.2.symm
    have hdiv1 : z₀ / (1 - z₀) ≠ 1 := fun h => hne ((field_div_eq_one_iff_eq h1z₀).mp h)
    have hdiv2 : z₀ / (1 - z₀) ≠ (1 - z₀) / z₀ := by
      intro h; rw [field_div_eq_div_iff h1z₀ hz₀_0] at h
      exact hne (by linear_combination (by linear_combination h : (2 : D.Fq2) * z₀ = 1))
    have hfilt : Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) =
        {z₀, 1 - z₀} := by
      ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]; exact quad_roots_eq_pair _ z₀ z hz₀
    exact ⟨z₀, hz₀, hz₀_0, h1z₀, hz₀q, hne, hdiv1, hdiv2, hfilt⟩
  have hB3_val : ∀ t (ht : B_T3 D t) x₀ (_hx₀ : x₀ ^ 2 - x₀ + t = 0)
      (hne : x₀ ≠ 1 - x₀) (hfilt : Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) = {x₀, 1 - x₀})
      (br : Bool × D.Fq2),
      Bgate D γ br t = if br.1 then 0 else
        isqrt 2 * ((if br.2 = algebraMap D.Fq D.Fq2 (x₀ / (1 - x₀)) then D.chi γ (1 - x₀) else 0) +
          (if br.2 = algebraMap D.Fq D.Fq2 ((1 - x₀) / x₀) then D.chi γ x₀ else 0)) := by
    intro t ht x₀ _ hne hfilt br
    have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht.2.1
    simp only [Bgate, Matrix.of_apply]
    rw [if_neg ht.1, if_neg ht2, if_pos ht.2.2, hfilt]
    cases br.1 <;> simp [Finset.sum_pair hne]
  have hB4_val : ∀ t (ht : B_T4 D t) z₀ (hz₀q : z₀ ^ D.q = 1 - z₀) (hne : z₀ ≠ 1 - z₀)
      (hfilt : Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) = {z₀, 1 - z₀})
      (br : Bool × D.Fq2),
      Bgate D γ br t = if br.1 then
        -(isqrt 2 * ((if br.2 = z₀ / (1 - z₀) then D.theta (theta0Lab D γ) z₀ else 0) +
          (if br.2 = (1 - z₀) / z₀ then D.theta (theta0Lab D γ) (1 - z₀) else 0)))
        else 0 := by
    intro t ht z₀ hz₀q hne hfilt br
    have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht.2.1
    simp only [Bgate, Matrix.of_apply]
    rw [if_neg ht.1, if_neg ht2, if_neg ht.2.2, hfilt]
    have h1zq : (1 - z₀) ^ D.q = z₀ := by rw [fq2_sub_pow_q, one_pow, hz₀q]; ring
    cases br.1
    · simp
    · simp only [↓reduceIte, Finset.sum_pair hne, hz₀q, h1zq]
  have hsplit_inj : ∀ x₁ x₂ : D.Fq, x₁ ≠ 1 → x₂ ≠ 1 →
      x₁ / (1 - x₁) = x₂ / (1 - x₂) → x₁ = x₂ := by
    intro x₁ x₂ h1 h2 heq
    rw [field_div_eq_div_iff (sub_ne_zero.mpr h1.symm) (sub_ne_zero.mpr h2.symm)] at heq
    linear_combination heq
  have hns_inj : ∀ z₁ z₂ : D.Fq2, z₁ ≠ 1 → z₂ ≠ 1 →
      z₁ / (1 - z₁) = z₂ / (1 - z₂) → z₁ = z₂ := by
    intro z₁ z₂ h1 h2 heq
    rw [field_div_eq_div_iff (sub_ne_zero.mpr h1.symm) (sub_ne_zero.mpr h2.symm)] at heq
    linear_combination heq
  have hT3_supp : ∀ t (ht : B_T3 D t) (br : Bool × D.Fq2), Bgate D γ br t ≠ 0 →
      br.1 = false ∧ br.2 ≠ 1 := by
    intro t ht br hne
    obtain ⟨x₀, hx₀, hx₀0, _, hne_x, hdiv1, _, hfilt⟩ := hB3_char t ht
    rw [hB3_val t ht x₀ hx₀ hne_x hfilt br] at hne
    cases h1 : br.1
    · refine ⟨rfl, fun hbr2 => ?_⟩
      rw [hbr2] at hne
      have ha1 : (1 : D.Fq2) ≠ algebraMap D.Fq D.Fq2 (x₀ / (1 - x₀)) := by
        intro h; apply hdiv1; apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2; rw [map_one]; exact h.symm
      have ha2 : (1 : D.Fq2) ≠ algebraMap D.Fq D.Fq2 ((1 - x₀) / x₀) := by
        intro h; apply hdiv1; apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
        rw [← map_one (algebraMap D.Fq D.Fq2)] at h
        have hx' := FaithfulSMul.algebraMap_injective D.Fq D.Fq2 h
        rw [eq_comm, field_div_eq_one_iff_eq hx₀0] at hx'; exact absurd hx'.symm hne_x
      rw [if_neg ha1, if_neg ha2] at hne; simp at hne
    · simp [h1] at hne
  have hT4_supp : ∀ t (ht : B_T4 D t) (br : Bool × D.Fq2), Bgate D γ br t ≠ 0 →
      br.1 = true ∧ br.2 ≠ 1 := by
    intro t ht br hne
    obtain ⟨z₀, _, hz₀0, _, hz₀q, hne_z, hdiv1, _, hfilt⟩ := hB4_char t ht
    rw [hB4_val t ht z₀ hz₀q hne_z hfilt br] at hne
    cases h1 : br.1
    · simp [h1] at hne
    · refine ⟨rfl, fun hbr2 => ?_⟩
      rw [hbr2] at hne
      have ha2 : (1 : D.Fq2) ≠ (1 - z₀) / z₀ := fun h => hne_z ((field_div_eq_one_iff_eq hz₀0).mp h.symm).symm
      rw [if_neg hdiv1.symm, if_neg ha2] at hne; simp at hne
  have h02_supp : ∀ t, (t = 0 ∨ B_T2 D t) → ∀ br : Bool × D.Fq2, Bgate D γ br t ≠ 0 → br.2 = 1 := by
    rintro t (rfl | ht2) br hne
    · simp only [Bgate, Matrix.of_apply, if_pos rfl] at hne; by_contra h; simp [h] at hne
    · have ht0 : t ≠ 0 := by rcases ht2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
      have ht2' : ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹ := ht2
      simp only [Bgate, Matrix.of_apply, if_neg ht0, if_pos ht2'] at hne; by_contra h; simp [h] at hne
  by_cases h1_02 : t₁ = 0 ∨ B_T2 D t₁
  · by_cases h2_02 : t₂ = 0 ∨ B_T2 D t₂
    · rcases h1_02 with rfl | h1_2 <;> rcases h2_02 with rfl | h2_2
      · rw [if_pos rfl]
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br 0) * Bgate D γ br 0 =
            if br.2 = 1 then (2 : ℂ)⁻¹ else 0 := by
          intro br; simp only [Bgate, Matrix.of_apply, if_pos rfl]
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl]; cases br.1 <;> simp only [↓reduceIte, mul_one] <;> exact hisqrt2
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]; norm_num
      · have ht20 : t₂ ≠ 0 := by rcases h2_2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        have h2_2' : ringChar D.Fq ≠ 2 ∧ t₂ = (4 : D.Fq)⁻¹ := h2_2
        rw [if_neg (Ne.symm ht20)]
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br 0) * Bgate D γ br t₂ =
            if br.2 = 1 then (2 : ℂ)⁻¹ * D.chi γ (2 : D.Fq)⁻¹ * (if br.1 then -1 else 1) else 0 := by
          intro br; simp only [Bgate, Matrix.of_apply, if_pos rfl, if_neg ht20, if_pos h2_2']
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl, if_pos rfl]
            cases br.1
            · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]; rw [← mul_assoc, hisqrt2]
            · simp only [↓reduceIte, mul_one, mul_neg]; rw [← mul_assoc, hisqrt2]
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]; simp [Fintype.sum_bool]
      · have ht10 : t₁ ≠ 0 := by rcases h1_2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        have h1_2' : ringChar D.Fq ≠ 2 ∧ t₁ = (4 : D.Fq)⁻¹ := h1_2
        rw [if_neg ht10]
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br 0 =
            if br.2 = 1 then (2 : ℂ)⁻¹ * star (D.chi γ (2 : D.Fq)⁻¹) * (if br.1 then -1 else 1) else 0 := by
          intro br; simp only [Bgate, Matrix.of_apply, if_pos rfl, if_neg ht10, if_pos h1_2']
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl, if_pos rfl]
            cases br.1
            · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, star_mul']
              calc star (isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) * isqrt 2
                  = (star (isqrt 2) * isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) := by ring
                _ = (2 : ℂ)⁻¹ * star (D.chi γ (2 : D.Fq)⁻¹) := by rw [hisqrt2]
            · simp only [↓reduceIte, star_mul', star_neg, star_one, mul_neg, mul_one, neg_mul]
              calc -(star (isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) * isqrt 2)
                  = -((star (isqrt 2) * isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹)) := by ring
                _ = -(2⁻¹ * star (D.chi γ 2⁻¹)) := by rw [hisqrt2]
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]; simp [Fintype.sum_bool]
      · have ht10 : t₁ ≠ 0 := by rcases h1_2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        have ht12 : t₁ = t₂ := by rcases h1_2 with ⟨_, rfl⟩; rcases h2_2 with ⟨_, rfl⟩; rfl
        subst ht12; have h1_2' : ringChar D.Fq ≠ 2 ∧ t₁ = (4 : D.Fq)⁻¹ := h1_2
        rw [if_pos rfl]
        have h2 : (2 : D.Fq)⁻¹ ≠ 0 := inv_ne_zero (mt (fq_two_eq_zero_iff D).mp h1_2.1)
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₁ =
            if br.2 = 1 then (2 : ℂ)⁻¹ else 0 := by
          intro br; simp only [Bgate, Matrix.of_apply, if_neg ht10, if_pos h1_2']
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl]
            cases br.1 <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one, star_mul',
              star_neg, star_one, mul_neg, neg_mul, neg_neg]
            · calc star (isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) * (isqrt 2 * D.chi γ (2 : D.Fq)⁻¹)
                  = (star (isqrt 2) * isqrt 2) * (star (D.chi γ (2 : D.Fq)⁻¹) * D.chi γ (2 : D.Fq)⁻¹) := by ring
                _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ h2, mul_one]
            · calc star (isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) * (isqrt 2 * D.chi γ (2 : D.Fq)⁻¹)
                  = (star (isqrt 2) * isqrt 2) * (star (D.chi γ (2 : D.Fq)⁻¹) * D.chi γ (2 : D.Fq)⁻¹) := by ring
                _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ h2, mul_one]
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]; norm_num
    · have ht20 : t₂ ≠ 0 := fun h => h2_02 (Or.inl h)
      have ht22 : ¬ B_T2 D t₂ := fun h => h2_02 (Or.inr h)
      have hne12 : t₁ ≠ t₂ := fun h => h2_02 (h ▸ h1_02)
      rw [if_neg hne12]
      apply Finset.sum_eq_zero; intro br _
      by_cases h1z : Bgate D γ br t₁ = 0; · simp [h1z]
      by_cases h2z : Bgate D γ br t₂ = 0; · simp [h2z]
      exfalso; have hbr2 := h02_supp t₁ h1_02 br h1z
      by_cases hex2 : ∃ x : D.Fq, x ^ 2 - x + t₂ = 0
      · exact (hT3_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).2 hbr2
      · exact (hT4_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).2 hbr2
  · have ht10 : t₁ ≠ 0 := fun h => h1_02 (Or.inl h)
    have ht12 : ¬ B_T2 D t₁ := fun h => h1_02 (Or.inr h)
    by_cases h2_02 : t₂ = 0 ∨ B_T2 D t₂
    · have hne12 : t₁ ≠ t₂ := fun h => h1_02 (h ▸ h2_02)
      rw [if_neg hne12]
      apply Finset.sum_eq_zero; intro br _
      by_cases h1z : Bgate D γ br t₁ = 0; · simp [h1z]
      by_cases h2z : Bgate D γ br t₂ = 0; · simp [h2z]
      exfalso; have hbr2 := h02_supp t₂ h2_02 br h2z
      by_cases hex1 : ∃ x : D.Fq, x ^ 2 - x + t₁ = 0
      · exact (hT3_supp t₁ ⟨ht10, ht12, hex1⟩ br h1z).2 hbr2
      · exact (hT4_supp t₁ ⟨ht10, ht12, hex1⟩ br h1z).2 hbr2
    · have ht20 : t₂ ≠ 0 := fun h => h2_02 (Or.inl h)
      have ht22 : ¬ B_T2 D t₂ := fun h => h2_02 (Or.inr h)
      by_cases hex1 : ∃ x : D.Fq, x ^ 2 - x + t₁ = 0 <;>
        by_cases hex2 : ∃ x : D.Fq, x ^ 2 - x + t₂ = 0
      · have hB1 : B_T3 D t₁ := ⟨ht10, ht12, hex1⟩
        have hB2 : B_T3 D t₂ := ⟨ht20, ht22, hex2⟩
        obtain ⟨x₁, hx₁, hx₁0, hx₁1, hne₁, _, hdiv₁, hfilt₁⟩ := hB3_char t₁ hB1
        obtain ⟨x₂, hx₂, hx₂0, hx₂1, hne₂, _, _, hfilt₂⟩ := hB3_char t₂ hB2
        have hinj : ∀ a b : D.Fq, a ≠ 1 → b ≠ 1 →
            algebraMap D.Fq D.Fq2 (a / (1 - a)) = algebraMap D.Fq D.Fq2 (b / (1 - b)) → a = b :=
          fun a b ha hb h => hsplit_inj a b ha hb (FaithfulSMul.algebraMap_injective D.Fq D.Fq2 h)
        by_cases ht12_eq : t₁ = t₂
        · subst ht12_eq; rw [if_pos rfl]
          have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₁ =
              if br.1 then 0 else (2 : ℂ)⁻¹ *
                ((if br.2 = algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁)) then 1 else 0) +
                 (if br.2 = algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁) then 1 else 0)) := by
            intro br; rw [hB3_val t₁ hB1 x₁ hx₁ hne₁ hfilt₁ br]
            cases br.1
            · simp only [Bool.false_eq_true, ↓reduceIte, star_mul']
              have hadj : algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁)) ≠
                  algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁) :=
                fun h => hdiv₁ (FaithfulSMul.algebraMap_injective D.Fq D.Fq2 h)
              by_cases h1 : br.2 = algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁))
              · rw [h1]; simp only [↓reduceIte, hadj, add_zero, mul_one]
                calc star (isqrt 2) * star (D.chi γ (1 - x₁)) * (isqrt 2 * D.chi γ (1 - x₁))
                    = (star (isqrt 2) * isqrt 2) * (star (D.chi γ (1 - x₁)) * D.chi γ (1 - x₁)) := by ring
                  _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ (sub_ne_zero.mpr hx₁1.symm), mul_one]
              · by_cases h2 : br.2 = algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁)
                · rw [h2]; simp only [↓reduceIte, hadj.symm, zero_add, mul_one]
                  calc star (isqrt 2) * star (D.chi γ x₁) * (isqrt 2 * D.chi γ x₁)
                      = (star (isqrt 2) * isqrt 2) * (star (D.chi γ x₁) * D.chi γ x₁) := by ring
                    _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ hx₁0, mul_one]
                · simp only [h1, h2, ↓reduceIte, add_zero, mul_zero, star_zero, zero_mul]
            · simp
          simp_rw [hterm, Fintype.sum_prod_type]
          simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, zero_add]
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]; norm_num
        · rw [if_neg ht12_eq]; apply Finset.sum_eq_zero; intro br _
          rw [hB3_val t₁ hB1 x₁ hx₁ hne₁ hfilt₁ br, hB3_val t₂ hB2 x₂ hx₂ hne₂ hfilt₂ br]
          cases br.1
          · simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases h1a : br.2 = algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁))
            · have h2a : br.2 ≠ algebraMap D.Fq D.Fq2 (x₂ / (1 - x₂)) := by
                intro h; have heq := hinj x₁ x₂ hx₁1 hx₂1 (h1a.symm.trans h)
                apply ht12_eq; subst heq; linear_combination hx₁ - hx₂
              have h2b : br.2 ≠ algebraMap D.Fq D.Fq2 ((1 - x₂) / x₂) := by
                intro h; have h2x : (1 - x₂) / (1 - (1 - x₂)) = (1 - x₂) / x₂ := by ring
                have heq := hinj x₁ (1 - x₂) hx₁1 (fun h0 => hx₂0 (by linear_combination -h0))
                  (h1a.symm.trans (h.trans (by rw [h2x])))
                apply ht12_eq; have hsym := quad_symm_root t₂ x₂ hx₂; rw [← heq] at hsym
                linear_combination hx₁ - hsym
              rw [if_pos h1a, if_neg h2a, if_neg h2b]; simp
            · by_cases h1b : br.2 = algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁)
              · have h1x : (1 - x₁) / (1 - (1 - x₁)) = (1 - x₁) / x₁ := by ring
                have h2a : br.2 ≠ algebraMap D.Fq D.Fq2 (x₂ / (1 - x₂)) := by
                  intro h; have heq := hinj (1 - x₁) x₂ (fun h0 => hx₁0 (by linear_combination -h0)) hx₂1
                    (by rw [h1x]; exact h1b.symm.trans h)
                  apply ht12_eq; have hsym := quad_symm_root t₁ x₁ hx₁; rw [heq] at hsym
                  linear_combination hsym - hx₂
                have h2b : br.2 ≠ algebraMap D.Fq D.Fq2 ((1 - x₂) / x₂) := by
                  intro h; have h2x : (1 - x₂) / (1 - (1 - x₂)) = (1 - x₂) / x₂ := by ring
                  have heq := hinj (1 - x₁) (1 - x₂) (fun h0 => hx₁0 (by linear_combination -h0))
                    (fun h0 => hx₂0 (by linear_combination -h0)) (by rw [h1x, h2x]; exact h1b.symm.trans h)
                  apply ht12_eq; have hx12 : x₁ = x₂ := by linear_combination -heq
                  subst hx12; linear_combination hx₁ - hx₂
                rw [if_neg h1a, if_pos h1b, if_neg h2a, if_neg h2b]; simp
              · rw [if_neg h1a, if_neg h1b]; simp
          · simp
      · have hne12 : t₁ ≠ t₂ := fun h => hex2 (h ▸ hex1)
        rw [if_neg hne12]; apply Finset.sum_eq_zero; intro br _
        by_cases h1z : Bgate D γ br t₁ = 0; · simp [h1z]
        by_cases h2z : Bgate D γ br t₂ = 0; · simp [h2z]
        exfalso; have h1f := (hT3_supp t₁ ⟨ht10, ht12, hex1⟩ br h1z).1
        have h2t := (hT4_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).1; rw [h1f] at h2t; cases h2t
      · have hne12 : t₁ ≠ t₂ := fun h => hex1 (h ▸ hex2)
        rw [if_neg hne12]; apply Finset.sum_eq_zero; intro br _
        by_cases h1z : Bgate D γ br t₁ = 0; · simp [h1z]
        by_cases h2z : Bgate D γ br t₂ = 0; · simp [h2z]
        exfalso; have h1t := (hT4_supp t₁ ⟨ht10, ht12, hex1⟩ br h1z).1
        have h2f := (hT3_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).1; rw [h1t] at h2f; cases h2f
      · have hB1 : B_T4 D t₁ := ⟨ht10, ht12, hex1⟩
        have hB2 : B_T4 D t₂ := ⟨ht20, ht22, hex2⟩
        obtain ⟨z₁, hz₁, hz₁0, h1z₁, hz₁q, hne₁, _, hdiv₁, hfilt₁⟩ := hB4_char t₁ hB1
        obtain ⟨z₂, hz₂, hz₂0, h1z₂, hz₂q, hne₂, _, _, hfilt₂⟩ := hB4_char t₂ hB2
        have hz₁_nrm : D.nrm z₁ = t₁ := ((B_T4_root_iff D hB1 z₁).mp hz₁).2
        have hz₂_nrm : D.nrm z₂ = t₂ := ((B_T4_root_iff D hB2 z₂).mp hz₂).2
        have h1z₁_nrm : D.nrm (1 - z₁) = t₁ := by
          apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
          rw [algebraMap_nrm_mul, ← hz₁q, ← pow_mul, ← sq, fq2_pow_q_sq]
          rw [← hz₁_nrm, algebraMap_nrm_mul, hz₁q]; ring
        have h1z₂_nrm : D.nrm (1 - z₂) = t₂ := by
          apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
          rw [algebraMap_nrm_mul, ← hz₂q, ← pow_mul, ← sq, fq2_pow_q_sq]
          rw [← hz₂_nrm, algebraMap_nrm_mul, hz₂q]; ring
        have hz₁_ne1 : z₁ ≠ 1 := fun h => h1z₁ (by rw [h, sub_self])
        have hz₂_ne1 : z₂ ≠ 1 := fun h => h1z₂ (by rw [h, sub_self])
        by_cases ht12_eq : t₁ = t₂
        · subst ht12_eq; rw [if_pos rfl]
          have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₁ =
              if br.1 then (2 : ℂ)⁻¹ *
                ((if br.2 = z₁ / (1 - z₁) then 1 else 0) +
                 (if br.2 = (1 - z₁) / z₁ then 1 else 0)) else 0 := by
            intro br; rw [hB4_val t₁ hB1 z₁ hz₁q hne₁ hfilt₁ br]
            cases br.1
            · simp
            · simp only [↓reduceIte, star_neg, neg_mul, mul_neg, neg_neg, star_mul']
              by_cases h1 : br.2 = z₁ / (1 - z₁)
              · rw [h1]; simp only [↓reduceIte, hdiv₁, add_zero, mul_one]
                calc star (isqrt 2) * star (D.theta (theta0Lab D γ) z₁) *
                      (isqrt 2 * D.theta (theta0Lab D γ) z₁)
                    = (star (isqrt 2) * isqrt 2) *
                        (star (D.theta (theta0Lab D γ) z₁) * D.theta (theta0Lab D γ) z₁) := by ring
                  _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, htheta_sq _ hz₁0, mul_one]
              · by_cases h2 : br.2 = (1 - z₁) / z₁
                · rw [h2]; simp only [↓reduceIte, hdiv₁.symm, zero_add, mul_one]
                  calc star (isqrt 2) * star (D.theta (theta0Lab D γ) (1 - z₁)) *
                        (isqrt 2 * D.theta (theta0Lab D γ) (1 - z₁))
                      = (star (isqrt 2) * isqrt 2) *
                          (star (D.theta (theta0Lab D γ) (1 - z₁)) * D.theta (theta0Lab D γ) (1 - z₁)) := by ring
                    _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, htheta_sq _ h1z₁, mul_one]
                · simp only [h1, h2, ↓reduceIte, add_zero, mul_zero, star_zero, zero_mul]
          simp_rw [hterm, Fintype.sum_prod_type]
          simp only [Fintype.sum_bool, ↓reduceIte, add_zero]
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]; norm_num
        · rw [if_neg ht12_eq]; apply Finset.sum_eq_zero; intro br _
          rw [hB4_val t₁ hB1 z₁ hz₁q hne₁ hfilt₁ br, hB4_val t₂ hB2 z₂ hz₂q hne₂ hfilt₂ br]
          cases br.1
          · simp
          · simp only [↓reduceIte]
            by_cases h1a : br.2 = z₁ / (1 - z₁)
            · have h2a : br.2 ≠ z₂ / (1 - z₂) := by
                intro h; have heq := hns_inj z₁ z₂ hz₁_ne1 hz₂_ne1 (h1a.symm.trans h)
                apply ht12_eq; rw [← hz₁_nrm, ← hz₂_nrm, heq]
              have h2b : br.2 ≠ (1 - z₂) / z₂ := by
                intro h; have h2z : (1 - z₂) / (1 - (1 - z₂)) = (1 - z₂) / z₂ := by ring
                have heq := hns_inj z₁ (1 - z₂) hz₁_ne1 (fun h0 => hz₂0 (by linear_combination -h0))
                  (h1a.symm.trans (h.trans (by rw [h2z])))
                apply ht12_eq; rw [← hz₁_nrm, ← h1z₂_nrm, heq]
              rw [if_pos h1a, if_neg h2a, if_neg h2b]; simp
            · by_cases h1b : br.2 = (1 - z₁) / z₁
              · have h1z : (1 - z₁) / (1 - (1 - z₁)) = (1 - z₁) / z₁ := by ring
                have h2a : br.2 ≠ z₂ / (1 - z₂) := by
                  intro h; have heq := hns_inj (1 - z₁) z₂ (fun h0 => hz₁0 (by linear_combination -h0)) hz₂_ne1
                    (by rw [h1z]; exact h1b.symm.trans h)
                  apply ht12_eq; rw [← h1z₁_nrm, ← hz₂_nrm, heq]
                have h2b : br.2 ≠ (1 - z₂) / z₂ := by
                  intro h; have h2z : (1 - z₂) / (1 - (1 - z₂)) = (1 - z₂) / z₂ := by ring
                  have heq := hns_inj (1 - z₁) (1 - z₂) (fun h0 => hz₁0 (by linear_combination -h0))
                    (fun h0 => hz₂0 (by linear_combination -h0)) (by rw [h1z, h2z]; exact h1b.symm.trans h)
                  apply ht12_eq; rw [← h1z₁_nrm, ← h1z₂_nrm, heq]
                rw [if_neg h1a, if_pos h1b, if_neg h2a, if_neg h2b]; simp
              · rw [if_neg h1a, if_neg h1b]; simp

private lemma Mbr_orth_on_dom (D : FieldData) (hq : 2 < D.q) (γ : D.Lab)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    {br₁ br₂ : Bool × D.Fq2} (h1 : InBranchDom D br₁) (h2 : InBranchDom D br₂) :
    ∑ o : BranchOut D γ, star (Mbr o br₁) * Mbr o br₂ = if br₁ = br₂ then 1 else 0 := by
  rcases br₁ with ⟨b1, w1⟩
  rcases br₂ with ⟨b2, w2⟩
  cases b1 <;> cases b2
  · simp only [InBranchDom, Bool.false_eq_true, ↓reduceIte] at h1 h2
    obtain ⟨r₁, hr₁, rfl⟩ := h1; obtain ⟨r₂, hr₂, rfl⟩ := h2
    simp only [Fintype.sum_sum_type, hMbr.1 r₁ hr₁, hMbr.1 r₂ hr₂, mul_zero, star_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    have hterm : ∀ δ : D.Lab, star (isqrt (D.q - 1) * D.chi δ r₁) * (isqrt (D.q - 1) * D.chi δ r₂) =
        ((D.q : ℂ) - 1)⁻¹ * D.chi δ (r₂ / r₁) := by
      intro δ
      rw [star_mul', isqrt_conj, ← chi_neg_lab, chi_div, mul_comm (D.chi δ r₂) (D.chi (-δ) r₁)]
      have hisq : isqrt (D.q - 1) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := isqrt_q_sub_one_sq D
      calc isqrt (D.q - 1) * D.chi (-δ) r₁ * (isqrt (D.q - 1) * D.chi δ r₂)
          = (isqrt (D.q - 1) * isqrt (D.q - 1)) * (D.chi (-δ) r₁ * D.chi δ r₂) := by ring
        _ = ((D.q : ℂ) - 1)⁻¹ * (D.chi (-δ) r₁ * D.chi δ r₂) := by rw [hisq]
    simp_rw [hterm, ← Finset.mul_sum, sum_chi_lab D hq (div_ne_zero hr₂ hr₁)]
    have heq_iff : (false, algebraMap D.Fq D.Fq2 r₁) = (false, algebraMap D.Fq D.Fq2 r₂) ↔
        r₂ / r₁ = 1 := by
      rw [Prod.mk.injEq, eq_self, true_and, (FaithfulSMul.algebraMap_injective D.Fq D.Fq2).eq_iff,
        eq_comm, field_div_eq_one_iff_eq hr₁]
    simp only [← heq_iff]
    split_ifs with h
    · have hq1 : ((D.q : ℂ) - 1) ≠ 0 := by
        have hqr : (2 : ℝ) < D.q := by exact_mod_cast hq
        intro h0; have hr := congrArg Complex.re h0
        simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hr; linarith
      exact inv_mul_cancel₀ hq1
    · rw [mul_zero]
  · simp only [InBranchDom, Bool.false_eq_true, ↓reduceIte] at h1 h2
    obtain ⟨r₁, hr₁, rfl⟩ := h1
    simp only [Fintype.sum_sum_type, hMbr.1 r₁ hr₁, hMbr.2 w2 h2.1 h2.2,
      mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero]; simp
  · simp only [InBranchDom, Bool.false_eq_true, ↓reduceIte] at h1 h2
    obtain ⟨r₂, hr₂, rfl⟩ := h2
    simp only [Fintype.sum_sum_type, hMbr.2 w1 h1.1 h1.2, hMbr.1 r₂ hr₂,
      mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero]; simp
  · simp only [InBranchDom, ↓reduceIte] at h1 h2
    simp only [Fintype.sum_sum_type, hMbr.2 w1 h1.1 h1.2, hMbr.2 w2 h2.1 h2.2,
      mul_zero, star_zero, zero_mul, Finset.sum_const_zero, zero_add]
    have hterm : ∀ θ : {θ : D.Lab2 // D.restrLab θ = γ},
        star (isqrt (D.q + 1) * kerChar D (θ.1 - theta0Lab D γ) w1) *
          (isqrt (D.q + 1) * kerChar D (θ.1 - theta0Lab D γ) w2) =
        ((D.q : ℂ) + 1)⁻¹ *
          (star (kerChar D (θ.1 - theta0Lab D γ) w1) * kerChar D (θ.1 - theta0Lab D γ) w2) := by
      intro θ
      rw [star_mul', isqrt_conj]
      have hisq : isqrt (D.q + 1) * isqrt (D.q + 1) = ((D.q : ℂ) + 1)⁻¹ := by
        rw [isqrt_mul_self (by positivity)]; push_cast; rfl
      calc isqrt (D.q + 1) * star (kerChar D (θ.1 - theta0Lab D γ) w1) *
            (isqrt (D.q + 1) * kerChar D (θ.1 - theta0Lab D γ) w2)
          = (isqrt (D.q + 1) * isqrt (D.q + 1)) *
              (star (kerChar D (θ.1 - theta0Lab D γ) w1) * kerChar D (θ.1 - theta0Lab D γ) w2) := by ring
        _ = ((D.q : ℂ) + 1)⁻¹ * _ := by rw [hisq]
    simp_rw [hterm, ← Finset.mul_sum, sum_kerChar_orth D hq γ h1.1 h1.2 h2.1 h2.2]
    have heq_iff : (true, w1) = (true, w2) ↔ w1 = w2 := by simp
    simp only [← heq_iff]
    split_ifs with h
    · exact inv_mul_cancel₀ (by exact_mod_cast Nat.succ_ne_zero D.q)
    · rw [mul_zero]

private lemma FxDag_iso (D : FieldData) (hq : 2 < D.q) :
    (FxDag D).conjTranspose * FxDag D = 1 := by
  ext c₁ c₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Matrix.conjTranspose_apply]
  cases c₁ <;> cases c₂
  · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
    simp only [FxDag, Matrix.of_apply, ↓reduceIte, star_one, mul_one]
    rw [Finset.sum_eq_zero, add_zero]
    intro t ht; simp [Finset.ne_of_mem_erase ht]
  · rw [if_neg (by simp)]; refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t = 0 <;> simp [FxDag, ht]
  · rw [if_neg (by simp)]; refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t = 0 <;> simp [FxDag, ht]
  · rename_i α β
    have hsplit : ∑ t : D.Fq, star (FxDag D t (some α)) * FxDag D t (some β) =
        ((D.q : ℂ) - 1)⁻¹ * ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0),
          D.chi (α - β) t := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
      have h0 : star (FxDag D 0 (some α)) * FxDag D 0 (some β) = 0 := by simp [FxDag]
      rw [h0, zero_add, Finset.mul_sum]
      have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun t : D.Fq => t ≠ 0) := by
        ext t; simp [Finset.mem_erase]
      rw [hfilt]; apply Finset.sum_congr rfl; intro t ht
      have ht0 : t ≠ 0 := (Finset.mem_filter.mp ht).2
      simp only [FxDag, Matrix.of_apply, if_neg ht0, star_mul', isqrt_conj]
      rw [← RCLike.star_def, star_star, ← chi_neg_lab D β t]
      have hisq : isqrt (D.q - 1) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := isqrt_q_sub_one_sq D
      calc isqrt (D.q - 1) * D.chi α t * (isqrt (D.q - 1) * D.chi (-β) t)
          = (isqrt (D.q - 1) * isqrt (D.q - 1)) * (D.chi α t * D.chi (-β) t) := by ring
        _ = ((D.q : ℂ) - 1)⁻¹ * D.chi (α - β) t := by rw [hisq, ← chi_add_lab, ← sub_eq_add_neg α β]
    rw [hsplit, sum_chi_fq_units D hq (α - β)]
    have heq : (some α = some β) ↔ α - β = 0 := by simp [sub_eq_zero]
    simp only [← heq]
    split_ifs with h
    · have hq1 : ((D.q : ℂ) - 1) ≠ 0 := by
        have hqr : (2 : ℝ) < D.q := by exact_mod_cast hq
        intro h0; have hr := congrArg Complex.re h0
        simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hr; linarith
      exact inv_mul_cancel₀ hq1
    · rw [mul_zero]

private lemma Dgate_iso (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) :
    (Dgate D γ).conjTranspose * Dgate D γ = 1 := by
  ext c₁ c₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Matrix.conjTranspose_apply, Dgate, Matrix.diagonal_apply]
  by_cases h12 : c₁ = c₂
  · subst h12
    rw [if_pos rfl, Finset.sum_eq_single c₁]
    · simp only [↓reduceIte]
      cases c₁ with
      | none => simp
      | some α =>
          dsimp only
          by_cases hne : α ≠ γ - α
          · rw [if_pos hne]
            have hba : (γ - α) - α ≠ 0 := fun h => hne (by linear_combination -h)
            have hq_pos : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
            have hqc : (D.q : ℂ) ≠ 0 := by exact_mod_cast (q_pos D).ne'
            have hsq_sq : (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ) = (D.q : ℂ) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt hq_pos.le, Complex.ofReal_natCast]
            have hg_sq : star (D.gauss ((γ - α) - α)) * D.gauss ((γ - α) - α) = (D.q : ℂ) := by
              rw [star_gauss, mul_assoc, mul_comm (D.gauss (-((γ - α) - α))),
                gauss_mul_gauss_neg D hq ((γ - α) - α), if_neg hba]
              have hsq1 : D.chi ((γ - α) - α) (-1) * (D.chi ((γ - α) - α) (-1) * (D.q : ℂ)) =
                  D.chi ((γ - α) - α) (-1) ^ 2 * (D.q : ℂ) := by ring
              rw [hsq1, chi_neg_one_sq, one_mul]
            have hchi_sq : star (D.chi (γ - α) (-1)) * D.chi (γ - α) (-1) = 1 := by
              rw [star_chi_neg_one, ← sq, chi_neg_one_sq]
            simp only [zeta]
            rw [star_div₀, star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
            calc (star (D.chi (γ - α) (-1)) * star (D.gauss ((γ - α) - α))) / (Real.sqrt D.q : ℂ) *
                  (D.chi (γ - α) (-1) * D.gauss ((γ - α) - α) / (Real.sqrt D.q : ℂ))
                = (star (D.chi (γ - α) (-1)) * D.chi (γ - α) (-1)) *
                    (star (D.gauss ((γ - α) - α)) * D.gauss ((γ - α) - α)) /
                    ((Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ)) := by ring
              _ = 1 * (D.q : ℂ) / (D.q : ℂ) := by rw [hchi_sq, hg_sq, hsq_sq]
              _ = 1 := by rw [one_mul, div_self hqc]
          · rw [if_neg hne]; simp
    · intro c _ hc
      by_cases hcc : c = c₁
      · exact absurd hcc hc
      · simp [hcc]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · rw [if_neg h12]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h1 : c = c₁
    · subst h1; simp [h12]
    · simp [h1]

private lemma canonMbr_valid (D : FieldData) (γ : D.Lab) :
    IsBranchTransform D γ (canonMbr D γ) := by
  constructor
  · intro r hr o
    cases o with
    | inl δ =>
        have hex : ∃ x : D.Fq, x ≠ 0 ∧ algebraMap D.Fq D.Fq2 x = algebraMap D.Fq D.Fq2 r :=
          ⟨r, hr, rfl⟩
        simp only [canonMbr, Matrix.of_apply, dif_pos hex]
        have hch := FaithfulSMul.algebraMap_injective D.Fq D.Fq2 (Classical.choose_spec hex).2
        rw [hch]
    | inr θ => rfl
  · intro r hr0 hr1 o
    cases o with
    | inl δ => rfl
    | inr θ => simp [canonMbr, hr0, hr1]

private lemma canonMbr_nonzero_mem (D : FieldData) (γ : D.Lab) (o : BranchOut D γ)
    (br : Bool × D.Fq2) (hne : canonMbr D γ o br ≠ 0) : InBranchDom D br := by
  rcases br with ⟨b, r⟩
  cases b
  · cases o with
    | inl δ =>
        simp only [canonMbr, Matrix.of_apply] at hne
        split_ifs at hne with h
        · rcases h with ⟨x, hx0, hxeq⟩
          exact ⟨x, hx0, hxeq.symm⟩
        · exact absurd rfl hne
    | inr θ => simp [canonMbr] at hne
  · cases o with
    | inl δ => simp [canonMbr] at hne
    | inr θ =>
        simp only [canonMbr, Matrix.of_apply] at hne
        split_ifs at hne with h
        · simpa [InBranchDom] using h
        · exact absurd rfl hne

private lemma canonMbr_mul_Bgate_eq (D : FieldData) (γ : D.Lab) :
    canonMbr D γ * Bgate D γ = canonMbrCore D γ * BgateSub D γ := by
  ext o t
  simp only [Matrix.mul_apply, canonMbrCore, BgateSub, Matrix.submatrix_apply, id_eq]
  let S := Finset.univ.filter (fun br : Bool × D.Fq2 =>
    (br.1 = false ∧ ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r) ∨
    (br.1 = true ∧ br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1))
  have mem_S : ∀ br : Bool × D.Fq2,
      ((br.1 = false ∧ ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r) ∨
       (br.1 = true ∧ br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1)) ↔ br ∈ S := fun br => by
    dsimp only [S]
    rw [Finset.mem_filter]
    exact (and_iff_right (Finset.mem_univ br)).symm
  have hsub : ∑ br : Bool × D.Fq2, canonMbr D γ o br * Bgate D γ br t =
      ∑ br ∈ S, canonMbr D γ o br * Bgate D γ br t := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun br _ hnot => ?_
    have hzero : canonMbr D γ o br = 0 := by
      by_contra hne
      have hdom := canonMbr_nonzero_mem D γ o br hne
      rw [inBranchDom_iff_mem_branchSrc] at hdom
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdom⟩)
    rw [hzero, zero_mul]
  rw [hsub, ← Finset.sum_coe_sort S]
  symm
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight mem_S) _ _ fun _ => rfl

private lemma BgateSub_iso (D : FieldData) (γ : D.Lab) :
    (BgateSub D γ).conjTranspose * BgateSub D γ = 1 := by
  ext t₁ t₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Matrix.conjTranspose_apply, BgateSub, Matrix.submatrix_apply, id_eq]
  let S := Finset.univ.filter (fun br : Bool × D.Fq2 =>
    (br.1 = false ∧ ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r) ∨
    (br.1 = true ∧ br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1))
  have mem_S : ∀ br : Bool × D.Fq2,
      ((br.1 = false ∧ ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r) ∨
       (br.1 = true ∧ br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1)) ↔ br ∈ S := fun br => by
    dsimp only [S]
    rw [Finset.mem_filter]
    exact (and_iff_right (Finset.mem_univ br)).symm
  have hS : (∑ br : BranchSrc D, star (Bgate D γ br.1 t₁) * Bgate D γ br.1 t₂) =
      ∑ br ∈ S, star (Bgate D γ br t₁) * Bgate D γ br t₂ := by
    rw [← Finset.sum_coe_sort S]
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight mem_S) _ _ fun _ => rfl
  have heq : ∑ br ∈ S, star (Bgate D γ br t₁) * Bgate D γ br t₂ =
      ∑ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₂ := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun br _ hnot => ?_
    have hzero : Bgate D γ br t₁ = 0 := by
      by_contra hne
      have hdom := Bgate_mem_InBranchDom D γ br t₁ hne
      rw [inBranchDom_iff_mem_branchSrc] at hdom
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdom⟩)
    rw [hzero, star_zero, zero_mul]
  rw [hS, heq, Bgate_orth D γ t₁ t₂]

private lemma canonMbrCore_iso (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) :
    (canonMbrCore D γ).conjTranspose * canonMbrCore D γ = 1 := by
  ext br₁ br₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Matrix.conjTranspose_apply, canonMbrCore, Matrix.submatrix_apply, id_eq]
  have h1 : InBranchDom D br₁.1 := (inBranchDom_iff_mem_branchSrc D br₁.1).mpr br₁.2
  have h2 : InBranchDom D br₂.1 := (inBranchDom_iff_mem_branchSrc D br₂.1).mpr br₂.2
  rw [Mbr_orth_on_dom D hq γ (canonMbr D γ) (canonMbr_valid D γ) h1 h2]
  simp [Subtype.ext_iff]

/-! ### Layer 3: `canonRfix` validity and isometry -/

private lemma lab2_mul_q_sq (D : FieldData) (k : D.Lab2) :
    (D.q : D.Lab2) * ((D.q : D.Lab2) * k) = k := by
  have hq2 : (D.q : D.Lab2) * (D.q : D.Lab2) = 1 := by
    have hmod : D.q * D.q ≡ 1 [MOD (D.q ^ 2 - 1)] := by
      rw [Nat.modEq_iff_dvd]; refine ⟨-1, ?_⟩
      have hq : 1 < D.q := D.one_lt_q; have hq2' : 1 ≤ D.q ^ 2 := by nlinarith
      zify [hq2']; ring
    rw [← Nat.cast_mul, ← Nat.cast_one (R := D.Lab2)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [← mul_assoc, hq2, one_mul]

private lemma lab2_fixed_iff_dvd (D : FieldData) (hq : 2 < D.q) (k : D.Lab2) :
    (D.q : D.Lab2) * k = k ↔ D.q + 1 ∣ k.val := by
  have hq1 : 1 ≤ D.q := by omega
  have hsub : ((D.q - 1 : ℕ) : D.Lab2) * k = (D.q : D.Lab2) * k - k := by
    rw [Nat.cast_sub hq1, Nat.cast_one, sub_mul, one_mul]
  constructor
  · intro heq
    have h0 : ((D.q - 1 : ℕ) : D.Lab2) * k = 0 := by rw [hsub, heq, sub_self]
    rw [← ZMod.natCast_zmod_val k, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at h0
    conv_lhs at h0 => rw [q_sq_sub_one_eq_mul, mul_comm]
    exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < D.q - 1)).mp h0
  · rintro ⟨m, hm⟩
    rw [← sub_eq_zero, ← hsub, ← ZMod.natCast_zmod_val k, hm, ← Nat.cast_mul,
      show (D.q - 1) * ((D.q + 1) * m) = (D.q ^ 2 - 1) * m by rw [q_sq_sub_one_eq_mul]; ring,
      ZMod.natCast_eq_zero_iff]
    exact ⟨m, rfl⟩

private lemma cusp_snd_not_cusp (D : FieldData) (hq : 2 < D.q) (k : {k : D.Lab2 // D.IsCuspLabel k}) :
    ¬ (D.q + 1 ∣ ((D.q : D.Lab2) * k.1).val) ∧ ¬ D.IsCuspLabel ((D.q : D.Lab2) * k.1) ∧
      D.IsCuspLabel ((D.q : D.Lab2) * ((D.q : D.Lab2) * k.1)) := by
  have hndvd : ¬ (D.q + 1 ∣ ((D.q : D.Lab2) * k.1).val) := by
    intro hdvd
    have hfix := (lab2_fixed_iff_dvd D hq _).mpr hdvd
    rw [lab2_mul_q_sq] at hfix
    exact k.2.1 ((lab2_fixed_iff_dvd D hq k.1).mp hfix.symm)
  have hnot_cusp : ¬ D.IsCuspLabel ((D.q : D.Lab2) * k.1) := by
    intro hcusp
    unfold FieldData.IsCuspLabel at hcusp
    rw [lab2_mul_q_sq] at hcusp
    have heqv : ((D.q : D.Lab2) * k.1).val = k.1.val := le_antisymm hcusp.2 k.2.2
    have hfix : (D.q : D.Lab2) * k.1 = k.1 := ZMod.val_injective _ heqv
    exact k.2.1 ((lab2_fixed_iff_dvd D hq k.1).mp hfix)
  have hcusp2 : D.IsCuspLabel ((D.q : D.Lab2) * ((D.q : D.Lab2) * k.1)) := by
    rw [lab2_mul_q_sq]; exact k.2
  exact ⟨hndvd, hnot_cusp, hcusp2⟩

private def pairVec {T : Type} (x y : T) (vx vy : ℂ) (o : T) : ℂ :=
  (if o = x then vx else 0) + (if o = y then vy else 0)

private lemma mulVec_eB (D : FieldData) (γ : D.Lab) (R : Matrix (D.Irr ⊕ D.Irr) (BranchOut D γ) ℂ)
    (i : BranchOut D γ) (o : D.Irr ⊕ D.Irr) :
    R.mulVec (eB D γ i) o = R o i := by
  simp [Matrix.mulVec, dotProduct, eB]

private lemma eO_eq_pairVec (D : FieldData) (x y : D.Irr ⊕ D.Irr) (hx : x ≠ y) :
    eO D x = pairVec x y 1 0 := by
  ext o; simp only [eO, pairVec]; split_ifs with h1 h2 <;> simp_all

private lemma isqrt_two_mul_two : isqrt 2 * (isqrt 2 + isqrt 2) = 1 := by
  have h : isqrt 2 * isqrt 2 = (2 : ℂ)⁻¹ := isqrt_mul_self (by norm_num)
  calc isqrt 2 * (isqrt 2 + isqrt 2) = isqrt 2 * isqrt 2 + isqrt 2 * isqrt 2 := by ring
    _ = (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ := by rw [h]
    _ = 1 := by norm_num

private abbrev RFixBlock (D : FieldData) :=
  D.Lab ⊕ {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} ⊕ {k : D.Lab2 // D.IsCuspLabel k}

private def blockLeft {D : FieldData} : RFixBlock D → D.Irr ⊕ D.Irr
  | .inl δ => .inl (.inr (.inl δ))
  | .inr (.inl ab) => .inl (.inr (.inr (.inl ab)))
  | .inr (.inr k) => .inl (.inr (.inr (.inr k)))

private def blockRight {D : FieldData} : RFixBlock D → D.Irr ⊕ D.Irr
  | .inl δ => .inl (.inl δ)
  | .inr (.inl ab) => .inr (.inr (.inr (.inl ab)))
  | .inr (.inr k) => .inr (.inr (.inr (.inr k)))

private lemma blockLeft_injective {D : FieldData} : Function.Injective (@blockLeft D) := by
  rintro (δ₁ | ab₁ | k₁) (δ₂ | ab₂ | k₂) h <;> simp [blockLeft] at h ⊢ <;> exact h

private lemma blockRight_injective {D : FieldData} : Function.Injective (@blockRight D) := by
  rintro (δ₁ | ab₁ | k₁) (δ₂ | ab₂ | k₂) h <;> simp [blockRight] at h ⊢ <;> exact h

private lemma blockLeft_ne_blockRight {D : FieldData} (b₁ b₂ : RFixBlock D) :
    @blockLeft D b₁ ≠ @blockRight D b₂ := by
  rcases b₁ with δ₁ | ab₁ | k₁ <;> rcases b₂ with δ₂ | ab₂ | k₂ <;> simp [blockLeft, blockRight]

private lemma pairVec_dot {D : FieldData} (b₁ b₂ : RFixBlock D) (u₁ v₁ u₂ v₂ : ℂ) :
    ∑ o : D.Irr ⊕ D.Irr,
      star (pairVec (blockLeft b₁) (blockRight b₁) u₁ v₁ o) *
        pairVec (blockLeft b₂) (blockRight b₂) u₂ v₂ o =
      if b₁ = b₂ then star u₁ * u₂ + star v₁ * v₂ else 0 := by
  by_cases hb : b₁ = b₂
  · subst hb
    rw [if_pos rfl]
    have hne : blockLeft b₁ ≠ blockRight b₁ := blockLeft_ne_blockRight b₁ b₁
    have hterm : ∀ o : D.Irr ⊕ D.Irr,
        star (pairVec (blockLeft b₁) (blockRight b₁) u₁ v₁ o) *
          pairVec (blockLeft b₁) (blockRight b₁) u₂ v₂ o =
        (if o = blockLeft b₁ then star u₁ * u₂ else 0) +
        (if o = blockRight b₁ then star v₁ * v₂ else 0) := by
      intro o
      simp only [pairVec]
      by_cases hL : o = blockLeft b₁
      · have hR : o ≠ blockRight b₁ := hL ▸ hne
        simp [hL, hR, hne]
      · by_cases hR : o = blockRight b₁
        · simp [hL, hR, hne.symm]
        · simp [hL, hR]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun o _ => ?_
    have hLL : blockLeft b₁ ≠ blockLeft b₂ := fun h => hb (blockLeft_injective h)
    have hRR : blockRight b₁ ≠ blockRight b₂ := fun h => hb (blockRight_injective h)
    have hLR : blockLeft b₁ ≠ blockRight b₂ := blockLeft_ne_blockRight b₁ b₂
    have hRL : blockRight b₁ ≠ blockLeft b₂ := (blockLeft_ne_blockRight b₂ b₁).symm
    have h11 : blockLeft b₁ ≠ blockRight b₁ := blockLeft_ne_blockRight b₁ b₁
    by_cases h1 : o = blockLeft b₁
    · subst h1; simp [pairVec, h11, hLL, hLR]
    · by_cases h2 : o = blockRight b₁
      · subst h2; simp [pairVec, h11.symm, hRL, hRR]
      · simp [pairVec, h1, h2]

private def coeffL (D : FieldData) : RFixBlock D → Bool → ℂ
  | .inl _, false => (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ)
  | .inl _, true => (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ)
  | .inr _, _ => FieldData.isqrt 2

private def coeffR (D : FieldData) : RFixBlock D → Bool → ℂ
  | .inl _, false => (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ)
  | .inl _, true => -(Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ)
  | .inr _, false => FieldData.isqrt 2
  | .inr _, true => -FieldData.isqrt 2

private lemma coeff_orth (D : FieldData) (hq : 2 < D.q) (b : RFixBlock D) (p₁ p₂ : Bool) :
    star (coeffL D b p₁) * coeffL D b p₂ + star (coeffR D b p₁) * coeffR D b p₂ =
      if p₁ = p₂ then 1 else 0 := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hqc : (D.q : ℂ) ≠ 0 := by exact_mod_cast (q_pos D).ne'
  have hq1 : (0 : ℝ) ≤ (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) ≤ (D.q : ℝ) + 1 := by linarith
  have hsq_plus : (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) *
      (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) =
      ((((D.q : ℝ) + 1) / (2 * D.q) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hq2 (by linarith))]
  have hsq_minus : (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) *
      (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) =
      ((((D.q : ℝ) - 1) / (2 * D.q) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg hq1 (by linarith))]
  have hisq2 : star (FieldData.isqrt 2) * FieldData.isqrt 2 = (2 : ℂ)⁻¹ := by
    rw [isqrt_conj, isqrt_mul_self (by norm_num)]; norm_num
  rcases b with δ | ab | k
  · cases p₁ <;> cases p₂ <;> simp only [coeffL, coeffR]
    · rw [if_true]; simp only [Complex.star_def, Complex.conj_ofReal, hsq_plus, hsq_minus]
      push_cast; field_simp [hqc]; ring
    · rw [if_neg (by decide)]; simp only [Complex.star_def, Complex.conj_ofReal]; ring
    · rw [if_neg (by decide)]; simp only [Complex.star_def, map_neg, Complex.conj_ofReal]; ring
    · rw [if_true]; simp only [star_neg, Complex.star_def, Complex.conj_ofReal, mul_neg, neg_mul,
        neg_neg, hsq_minus, hsq_plus]
      push_cast; field_simp [hqc]; ring
  · cases p₁ <;> cases p₂ <;> simp only [coeffL, coeffR, star_neg]
    · rw [if_true]; rw [hisq2]; norm_num
    · rw [if_neg (by decide)]; ring
    · rw [if_neg (by decide)]; ring
    · rw [if_true]; rw [mul_neg, neg_mul, neg_neg, hisq2]; norm_num
  · cases p₁ <;> cases p₂ <;> simp only [coeffL, coeffR, star_neg]
    · rw [if_true]; rw [hisq2]; norm_num
    · rw [if_neg (by decide)]; ring
    · rw [if_neg (by decide)]; ring
    · rw [if_true]; rw [mul_neg, neg_mul, neg_neg, hisq2]; norm_num

private def rfixTag (D : FieldData) (γ : D.Lab) (i : BranchOut D γ) : RFixBlock D × Bool :=
  match i with
  | .inl δ =>
      if δ = γ - δ then (.inl δ, false)
      else if hlt : δ.val < (γ - δ).val then (.inr (.inl ⟨(δ, γ - δ), hlt⟩), false)
      else if hgt : (γ - δ).val < δ.val then (.inr (.inl ⟨(γ - δ, δ), hgt⟩), true)
      else (.inl δ, false)
  | .inr θ =>
      if D.q + 1 ∣ θ.1.val then (.inl ((θ.1.val / (D.q + 1) : ℕ) : D.Lab), true)
      else if hcusp1 : D.IsCuspLabel θ.1 then (.inr (.inr ⟨θ.1, hcusp1⟩), false)
      else if hcusp2 : D.IsCuspLabel ((D.q : D.Lab2) * θ.1) then (.inr (.inr ⟨_, hcusp2⟩), true)
      else (.inl 0, true)

private lemma rfix_inl_spec (D : FieldData) (γ : D.Lab) (δ : D.Lab) (o : D.Irr ⊕ D.Irr) :
    canonRfix D γ o (.inl δ) =
      let bp := rfixTag D γ (.inl δ)
      pairVec (blockLeft bp.1) (blockRight bp.1) (coeffL D bp.1 bp.2) (coeffR D bp.1 bp.2) o := by
  by_cases heq : δ = γ - δ
  · simp only [canonRfix, Matrix.of_apply, rfixTag, if_pos heq, blockLeft, blockRight, coeffL, coeffR]
    rfl
  · by_cases hlt : δ.val < (γ - δ).val
    · simp only [canonRfix, Matrix.of_apply, rfixTag, if_neg heq, dif_pos hlt,
        blockLeft, blockRight, coeffL, coeffR]
      rfl
    · have hgt : (γ - δ).val < δ.val := by
        have hne : δ.val ≠ (γ - δ).val := fun h => heq (ZMod.val_injective _ h)
        omega
      simp only [canonRfix, Matrix.of_apply, rfixTag, if_neg heq, dif_neg hlt, dif_pos hgt,
        blockLeft, blockRight, coeffL, coeffR]
      rfl

private lemma rfix_inr_spec (D : FieldData) (hq : 2 < D.q) (γ : D.Lab)
    (θ : {θ : D.Lab2 // D.restrLab θ = γ}) (o : D.Irr ⊕ D.Irr) :
    canonRfix D γ o (.inr θ) =
      let bp := rfixTag D γ (.inr θ)
      pairVec (blockLeft bp.1) (blockRight bp.1) (coeffL D bp.1 bp.2) (coeffR D bp.1 bp.2) o := by
  by_cases hdvd : D.q + 1 ∣ θ.1.val
  · simp only [canonRfix, Matrix.of_apply, rfixTag, if_pos hdvd, blockLeft, blockRight, coeffL, coeffR]
    rfl
  · by_cases hcusp1 : D.IsCuspLabel θ.1
    · simp only [canonRfix, Matrix.of_apply, rfixTag, if_neg hdvd, dif_pos hcusp1,
        blockLeft, blockRight, coeffL, coeffR]
      rfl
    · have hle : ((D.q : D.Lab2) * θ.1).val ≤ θ.1.val := by
        by_contra hgt
        push Not at hgt
        exact hcusp1 ⟨hdvd, hgt.le⟩
      have hndvd2 : ¬ (D.q + 1 ∣ ((D.q : D.Lab2) * θ.1).val) := by
        intro h2
        have hfix := (lab2_fixed_iff_dvd D hq _).mpr h2
        rw [lab2_mul_q_sq] at hfix
        exact hdvd ((lab2_fixed_iff_dvd D hq θ.1).mp hfix.symm)
      have hle2 : ((D.q : D.Lab2) * θ.1).val ≤ ((D.q : D.Lab2) * ((D.q : D.Lab2) * θ.1)).val := by
        rw [lab2_mul_q_sq]; exact hle
      have hcusp2 : D.IsCuspLabel ((D.q : D.Lab2) * θ.1) := ⟨hndvd2, hle2⟩
      simp only [canonRfix, Matrix.of_apply, rfixTag, if_neg hdvd, dif_neg hcusp1, dif_pos hcusp2,
        blockLeft, blockRight, coeffL, coeffR]
      rfl

private lemma rfixTag_inr_dvd_eq (D : FieldData) (γ : D.Lab)
    {θ : {θ : D.Lab2 // D.restrLab θ = γ}} (hd : D.q + 1 ∣ θ.1.val) :
    (((D.q + 1) * (((θ.1.val / (D.q + 1) : ℕ) : D.Lab)).val : ℕ) : D.Lab2) = θ.1 := by
  have hlt : θ.1.val / (D.q + 1) < D.q - 1 := by
    have hθlt : θ.1.val < (D.q + 1) * (D.q - 1) := by rw [← q_sq_sub_one_eq_mul]; exact ZMod.val_lt θ.1
    exact Nat.div_lt_of_lt_mul hθlt
  have hval : (((θ.1.val / (D.q + 1) : ℕ) : D.Lab)).val = θ.1.val / (D.q + 1) := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [hval, Nat.mul_div_cancel' hd, ZMod.natCast_zmod_val]

private lemma rfixTag_inr_cusp (D : FieldData) (hq : 2 < D.q) (γ : D.Lab)
    (θ : {θ : D.Lab2 // D.restrLab θ = γ}) (hd : ¬ D.q + 1 ∣ θ.1.val) :
    (∃ hc1 : D.IsCuspLabel θ.1, rfixTag D γ (.inr θ) = (.inr (.inr ⟨θ.1, hc1⟩), false)) ∨
    (∃ hc2 : D.IsCuspLabel ((D.q : D.Lab2) * θ.1),
      rfixTag D γ (.inr θ) = (.inr (.inr ⟨(D.q : D.Lab2) * θ.1, hc2⟩), true)) := by
  by_cases hc1 : D.IsCuspLabel θ.1
  · left; exact ⟨hc1, by simp [rfixTag, hd, hc1]⟩
  · right
    have hle : ((D.q : D.Lab2) * θ.1).val ≤ θ.1.val := by
      by_contra hgt; push Not at hgt; exact hc1 ⟨hd, hgt.le⟩
    have hndvd2 : ¬ (D.q + 1 ∣ ((D.q : D.Lab2) * θ.1).val) := by
      intro h2; have hfix := (lab2_fixed_iff_dvd D hq _).mpr h2
      rw [lab2_mul_q_sq] at hfix; exact hd ((lab2_fixed_iff_dvd D hq θ.1).mp hfix.symm)
    have hc2 : D.IsCuspLabel ((D.q : D.Lab2) * θ.1) := ⟨hndvd2, by rw [lab2_mul_q_sq]; exact hle⟩
    exact ⟨hc2, by simp [rfixTag, hd, hc1, hc2]⟩

private lemma rfixTag_injective (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) :
    Function.Injective (rfixTag D γ) := by
  intro i₁ i₂ h
  rcases i₁ with δ₁ | θ₁ <;> rcases i₂ with δ₂ | θ₂
  · by_cases heq1 : δ₁ = γ - δ₁ <;> by_cases heq2 : δ₂ = γ - δ₂
    · simp only [rfixTag, if_pos heq1, if_pos heq2, Prod.mk.injEq, Sum.inl.injEq, and_true] at h
      rw [h]
    · exfalso
      simp only [rfixTag, if_pos heq1, if_neg heq2] at h
      split_ifs at h with hlt2 hgt2
      · simp at h
      · simp at h
      · have hne : δ₂.val ≠ (γ - δ₂).val := fun hv => heq2 (ZMod.val_injective _ hv)
        omega
    · exfalso
      simp only [rfixTag, if_neg heq1, if_pos heq2] at h
      split_ifs at h with hlt1 hgt1
      · simp at h
      · simp at h
      · have hne : δ₁.val ≠ (γ - δ₁).val := fun hv => heq1 (ZMod.val_injective _ hv)
        omega
    · simp only [rfixTag, if_neg heq1, if_neg heq2] at h
      by_cases hlt1 : δ₁.val < (γ - δ₁).val <;> by_cases hlt2 : δ₂.val < (γ - δ₂).val
      · simp only [dif_pos hlt1, dif_pos hlt2, Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq,
          Subtype.mk.injEq, Prod.mk.injEq, and_true] at h
        rw [h.1]
      · have hgt2 : (γ - δ₂).val < δ₂.val := by
          have hne : δ₂.val ≠ (γ - δ₂).val := fun hv => heq2 (ZMod.val_injective _ hv)
          omega
        simp [dif_pos hlt1, dif_neg hlt2, dif_pos hgt2] at h
      · have hgt1 : (γ - δ₁).val < δ₁.val := by
          have hne : δ₁.val ≠ (γ - δ₁).val := fun hv => heq1 (ZMod.val_injective _ hv)
          omega
        simp [dif_neg hlt1, dif_pos hgt1, dif_pos hlt2] at h
      · have hgt1 : (γ - δ₁).val < δ₁.val := by
          have hne : δ₁.val ≠ (γ - δ₁).val := fun hv => heq1 (ZMod.val_injective _ hv)
          omega
        have hgt2 : (γ - δ₂).val < δ₂.val := by
          have hne : δ₂.val ≠ (γ - δ₂).val := fun hv => heq2 (ZMod.val_injective _ hv)
          omega
        simp only [dif_neg hlt1, dif_pos hgt1, dif_neg hlt2, dif_pos hgt2, Prod.mk.injEq,
          Sum.inr.injEq, Sum.inl.injEq, Subtype.mk.injEq, Prod.mk.injEq, and_true] at h
        rw [h.2]
  · exfalso
    have hsnd : (rfixTag D γ (.inl δ₁)).2 = (rfixTag D γ (.inr θ₂)).2 := congrArg Prod.snd h
    have hfst : (rfixTag D γ (.inl δ₁)).1 = (rfixTag D γ (.inr θ₂)).1 := congrArg Prod.fst h
    by_cases hd2 : D.q + 1 ∣ θ₂.1.val
    · have h2 : (rfixTag D γ (.inr θ₂)).2 = true := by simp [rfixTag, hd2]
      rw [h2] at hsnd
      simp only [rfixTag] at hsnd hfst
      split_ifs at hsnd hfst <;> simp at hsnd hfst
    · rcases rfixTag_inr_cusp D hq γ θ₂ hd2 with ⟨hc2, ht2⟩ | ⟨hc2, ht2⟩ <;>
        rw [ht2] at hfst hsnd <;> simp only [rfixTag] at hfst hsnd <;>
        split_ifs at hfst hsnd <;> simp at hfst hsnd
  · exfalso
    have hsnd : (rfixTag D γ (.inr θ₁)).2 = (rfixTag D γ (.inl δ₂)).2 := congrArg Prod.snd h
    have hfst : (rfixTag D γ (.inr θ₁)).1 = (rfixTag D γ (.inl δ₂)).1 := congrArg Prod.fst h
    by_cases hd1 : D.q + 1 ∣ θ₁.1.val
    · have h1 : (rfixTag D γ (.inr θ₁)).2 = true := by simp [rfixTag, hd1]
      rw [h1] at hsnd
      simp only [rfixTag] at hsnd hfst
      split_ifs at hsnd hfst <;> simp at hsnd hfst
    · rcases rfixTag_inr_cusp D hq γ θ₁ hd1 with ⟨hc1, ht1⟩ | ⟨hc1, ht1⟩ <;>
        rw [ht1] at hfst hsnd <;> simp only [rfixTag] at hfst hsnd <;>
        split_ifs at hfst hsnd <;> simp at hfst hsnd
  · by_cases hd1 : D.q + 1 ∣ θ₁.1.val <;> by_cases hd2 : D.q + 1 ∣ θ₂.1.val
    · have hp1 := rfixTag_inr_dvd_eq D γ hd1
      have hp2 := rfixTag_inr_dvd_eq D γ hd2
      simp only [rfixTag, if_pos hd1, if_pos hd2, Prod.mk.injEq, Sum.inl.injEq, and_true] at h
      congr 1; apply Subtype.ext
      rw [← hp1, ← hp2, h]
    · exfalso
      have h1 : rfixTag D γ (.inr θ₁) = (.inl ((θ₁.1.val / (D.q + 1) : ℕ) : D.Lab), true) := by
        simp [rfixTag, hd1]
      rw [h1] at h
      rcases rfixTag_inr_cusp D hq γ θ₂ hd2 with ⟨hc2, ht2⟩ | ⟨hc2, ht2⟩ <;>
        rw [ht2] at h <;> simp at h
    · exfalso
      have h2 : rfixTag D γ (.inr θ₂) = (.inl ((θ₂.1.val / (D.q + 1) : ℕ) : D.Lab), true) := by
        simp [rfixTag, hd2]
      rw [h2] at h
      rcases rfixTag_inr_cusp D hq γ θ₁ hd1 with ⟨hc1, ht1⟩ | ⟨hc1, ht1⟩ <;>
        rw [ht1] at h <;> simp at h
    · rcases rfixTag_inr_cusp D hq γ θ₁ hd1 with ⟨hc1, ht1⟩ | ⟨hc1, ht1⟩ <;>
        rcases rfixTag_inr_cusp D hq γ θ₂ hd2 with ⟨hc2, ht2⟩ | ⟨hc2, ht2⟩
      · rw [ht1, ht2] at h
        simp only [Prod.mk.injEq, Sum.inr.injEq, Subtype.mk.injEq, and_true] at h
        exact congrArg Sum.inr (Subtype.ext h)
      · rw [ht1, ht2] at h; simp at h
      · rw [ht1, ht2] at h; simp at h
      · rw [ht1, ht2] at h
        simp only [Prod.mk.injEq, Sum.inr.injEq, Subtype.mk.injEq, and_true] at h
        have hqmul := congrArg (fun x : D.Lab2 => (D.q : D.Lab2) * x) h
        rw [lab2_mul_q_sq, lab2_mul_q_sq] at hqmul
        exact congrArg Sum.inr (Subtype.ext hqmul)

private lemma canonRfix_iso (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) :
    (canonRfix D γ).conjTranspose * canonRfix D γ = 1 := by
  ext i₁ i₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Matrix.conjTranspose_apply]
  have hspec : ∀ i : BranchOut D γ, ∀ o : D.Irr ⊕ D.Irr,
      canonRfix D γ o i =
        pairVec (blockLeft (rfixTag D γ i).1) (blockRight (rfixTag D γ i).1)
          (coeffL D (rfixTag D γ i).1 (rfixTag D γ i).2)
          (coeffR D (rfixTag D γ i).1 (rfixTag D γ i).2) o := by
    intro i o
    cases i with
    | inl δ => exact rfix_inl_spec D γ δ o
    | inr θ => exact rfix_inr_spec D hq γ θ o
  simp_rw [hspec]
  rw [pairVec_dot]
  by_cases hb : (rfixTag D γ i₁).1 = (rfixTag D γ i₂).1
  · rw [if_pos hb, hb, coeff_orth D hq _ (rfixTag D γ i₁).2 (rfixTag D γ i₂).2]
    have hiff : (rfixTag D γ i₁).2 = (rfixTag D γ i₂).2 ↔ i₁ = i₂ := by
      constructor
      · intro hp; exact rfixTag_injective D hq γ (Prod.ext hb hp)
      · intro hi; subst hi; rfl
    simp [hiff]
  · rw [if_neg hb]
    have hne : i₁ ≠ i₂ := fun h => hb (congrArg (fun x => (rfixTag D γ x).1) h)
    rw [if_neg hne]

private lemma canonRfix_valid (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) :
    IsFixingGate D γ (canonRfix D γ) := by
  refine ⟨?_, ?_, ?_, canonRfix_iso D hq γ⟩
  · -- Clause 1: split pairs ab.1.1 < ab.1.2 with ab.1.1 + ab.1.2 = γ
    intro ab hab
    let α := ab.1.1
    let β := ab.1.2
    have hαβ : α.val < β.val := ab.2
    have hγα : γ - α = β := (eq_sub_of_add_eq' hab).symm
    have hγβ : γ - β = α := (eq_sub_of_add_eq hab).symm
    have hα_ne : α ≠ γ - α := by
      intro h; rw [hγα] at h
      have hαβ_eq : α.val = β.val := congrArg ZMod.val h
      omega
    have hβ_ne : β ≠ γ - β := by
      intro h; rw [hγβ] at h
      have hβα_eq : β.val = α.val := congrArg ZMod.val h
      omega
    have hα_lt : α.val < (γ - α).val := by rw [hγα]; exact hαβ
    have hβ_nlt : ¬ (β.val < (γ - β).val) := by rw [hγβ]; omega
    have hβ_gt : (γ - β).val < β.val := by rw [hγβ]; exact hαβ
    have hcolα : ∀ o : D.Irr ⊕ D.Irr,
        (canonRfix D γ).mulVec (eB D γ (.inl α)) o =
          pairVec (.inl (.inr (.inr (.inl ab)))) (.inr (.inr (.inr (.inl ab))))
            (isqrt 2) (isqrt 2) o := by
      intro o
      rw [mulVec_eB]
      simp only [canonRfix, Matrix.of_apply, if_neg hα_ne, dif_pos hα_lt]
      have hab1 : (⟨(α, γ - α), hα_lt⟩ : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}) = ab :=
        Subtype.ext (Prod.ext rfl hγα)
      rw [hab1]; rfl
    have hcolβ : ∀ o : D.Irr ⊕ D.Irr,
        (canonRfix D γ).mulVec (eB D γ (.inl β)) o =
          pairVec (.inl (.inr (.inr (.inl ab)))) (.inr (.inr (.inr (.inl ab))))
            (isqrt 2) (-isqrt 2) o := by
      intro o
      rw [mulVec_eB]
      simp only [canonRfix, Matrix.of_apply, if_neg hβ_ne, dif_neg hβ_nlt, dif_pos hβ_gt]
      have hab2 : (⟨(γ - β, β), hβ_gt⟩ : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}) = ab :=
        Subtype.ext (Prod.ext hγβ rfl)
      rw [hab2]; rfl
    constructor
    · ext o
      rw [Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        hcolα o, hcolβ o]
      simp only [pairVec, eO]
      have hneq : (Sum.inl (Sum.inr (Sum.inr (Sum.inl ab))) : D.Irr ⊕ D.Irr) ≠
          Sum.inr (Sum.inr (Sum.inr (Sum.inl ab))) := by simp
      by_cases hL : o = Sum.inl (Sum.inr (Sum.inr (Sum.inl ab)))
      · have hR : o ≠ Sum.inr (Sum.inr (Sum.inr (Sum.inl ab))) := hL ▸ hneq
        simp [hL, hR, isqrt_two_mul_two]
      · by_cases hR : o = Sum.inr (Sum.inr (Sum.inr (Sum.inl ab)))
        · simp [hL, hR]
        · simp [hL, hR]
    · intro o
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        hcolα (.inl o), hcolβ (.inl o)]
      simp [pairVec]
  · -- Clause 2: cuspidal pairs k
    intro k h₁ h₂
    have hk_cusp : D.IsCuspLabel k.1 := k.2
    have hk1_ndvd : ¬ (D.q + 1 ∣ k.1.val) := hk_cusp.1
    obtain ⟨hk2_ndvd, hk2_not_cusp, hk2_cusp2⟩ := cusp_snd_not_cusp D hq k
    have hcol1 : ∀ o : D.Irr ⊕ D.Irr,
        (canonRfix D γ).mulVec (eB D γ (.inr ⟨k.1, h₁⟩)) o =
          pairVec (.inl (.inr (.inr (.inr k)))) (.inr (.inr (.inr (.inr k))))
            (isqrt 2) (isqrt 2) o := by
      intro o
      rw [mulVec_eB]
      simp only [canonRfix, Matrix.of_apply, if_neg hk1_ndvd, dif_pos hk_cusp]
      have hk_eq : (⟨k.1, hk_cusp⟩ : {k : D.Lab2 // D.IsCuspLabel k}) = k := Subtype.ext rfl
      rw [hk_eq]; rfl
    have hcol2 : ∀ o : D.Irr ⊕ D.Irr,
        (canonRfix D γ).mulVec (eB D γ (.inr ⟨(D.q : D.Lab2) * k.1, h₂⟩)) o =
          pairVec (.inl (.inr (.inr (.inr k)))) (.inr (.inr (.inr (.inr k))))
            (isqrt 2) (-isqrt 2) o := by
      intro o
      rw [mulVec_eB]
      simp only [canonRfix, Matrix.of_apply, if_neg hk2_ndvd, dif_neg hk2_not_cusp, dif_pos hk2_cusp2]
      have hk_eq : (⟨(D.q : D.Lab2) * ((D.q : D.Lab2) * k.1), hk2_cusp2⟩ :
          {k : D.Lab2 // D.IsCuspLabel k}) = k := Subtype.ext (lab2_mul_q_sq D k.1)
      rw [hk_eq]; rfl
    constructor
    · ext o
      rw [Matrix.mulVec_smul, Matrix.mulVec_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
        hcol1 o, hcol2 o]
      simp only [pairVec, eO]
      have hneq : (Sum.inl (Sum.inr (Sum.inr (Sum.inr k))) : D.Irr ⊕ D.Irr) ≠
          Sum.inr (Sum.inr (Sum.inr (Sum.inr k))) := by simp
      by_cases hL : o = Sum.inl (Sum.inr (Sum.inr (Sum.inr k)))
      · have hR : o ≠ Sum.inr (Sum.inr (Sum.inr (Sum.inr k))) := hL ▸ hneq
        simp [hL, hR, isqrt_two_mul_two]
      · by_cases hR : o = Sum.inr (Sum.inr (Sum.inr (Sum.inr k)))
        · simp [hL, hR]
        · simp [hL, hR]
    · intro o
      rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        hcol1 (.inl o), hcol2 (.inl o)]
      simp [pairVec]
  · -- Clause 3: fixed point 2 * δ = γ
    intro δ hδ
    have hδeq : δ = γ - δ := by linear_combination hδ
    have hcolL : ∀ o : D.Irr ⊕ D.Irr,
        (canonRfix D γ).mulVec (eB D γ (.inl δ)) o =
          pairVec (.inl (.inr (.inl δ))) (.inl (.inl δ))
            (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)))
            (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q))) o := by
      intro o
      rw [mulVec_eB]
      simp only [canonRfix, Matrix.of_apply, if_pos hδeq]
      rfl
    have hneq : (Sum.inl (Sum.inr (Sum.inl δ)) : D.Irr ⊕ D.Irr) ≠ Sum.inl (Sum.inl δ) := by simp
    constructor
    · ext o
      rw [hcolL o]
      simp only [pairVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eO]
      by_cases hL : o = Sum.inl (Sum.inr (Sum.inl δ))
      · have hR : o ≠ Sum.inl (Sum.inl δ) := hL ▸ hneq
        simp [hL, hR]
      · by_cases hR : o = Sum.inl (Sum.inl δ)
        · simp [hL, hR]
        · simp [hL, hR]
    · intro θ hθ
      have hlt : (D.q + 1) * δ.val < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt δ) (by omega)
      have hval : θ.1.val = (D.q + 1) * δ.val := by
        rw [hθ, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      have hdvd : D.q + 1 ∣ θ.1.val := ⟨δ.val, hval⟩
      have hdiv : ((θ.1.val / (D.q + 1) : ℕ) : D.Lab) = δ := by
        rw [hval, Nat.mul_div_cancel_left _ (by omega), ZMod.natCast_zmod_val]
      have hcolR : ∀ o : D.Irr ⊕ D.Irr,
          (canonRfix D γ).mulVec (eB D γ (.inr θ)) o =
            pairVec (.inl (.inr (.inl δ))) (.inl (.inl δ))
              (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)))
              (-(Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)))) o := by
        intro o
        rw [mulVec_eB]
        simp only [canonRfix, Matrix.of_apply, if_pos hdvd, hdiv]
        rfl
      ext o
      rw [hcolR o]
      simp only [pairVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, eO]
      by_cases hL : o = Sum.inl (Sum.inr (Sum.inl δ))
      · have hR : o ≠ Sum.inl (Sum.inl δ) := hL ▸ hneq
        simp [hL, hR]
      · by_cases hR : o = Sum.inl (Sum.inl δ)
        · simp [hL, hR]
        · simp [hL, hR]

end GL2QFT_CanonMbrRfixValid_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates QAlgorithms QAlgorithms.Complexity

theorem solution (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) :
    IsBranchTransform D γ (canonMbr D γ) ∧
    IsFixingGate D γ (canonRfix D γ) ∧
    canonMbr D γ * Bgate D γ = canonMbrCore D γ * BgateSub D γ ∧
    (Dgate D γ).conjTranspose * Dgate D γ = 1 ∧
    (FxDag D).conjTranspose * FxDag D = 1 ∧
    (BgateSub D γ).conjTranspose * BgateSub D γ = 1 ∧
    (canonMbrCore D γ).conjTranspose * canonMbrCore D γ = 1 ∧
    (canonRfix D γ).conjTranspose * canonRfix D γ = 1 :=
  ⟨GL2QFT_CanonMbrRfixValid_Aux.canonMbr_valid D γ,
   GL2QFT_CanonMbrRfixValid_Aux.canonRfix_valid D hq γ,
   GL2QFT_CanonMbrRfixValid_Aux.canonMbr_mul_Bgate_eq D γ,
   GL2QFT_CanonMbrRfixValid_Aux.Dgate_iso D hq γ,
   GL2QFT_CanonMbrRfixValid_Aux.FxDag_iso D hq,
   GL2QFT_CanonMbrRfixValid_Aux.BgateSub_iso D γ,
   GL2QFT_CanonMbrRfixValid_Aux.canonMbrCore_iso D hq γ,
   GL2QFT_CanonMbrRfixValid_Aux.canonRfix_iso D hq γ⟩
