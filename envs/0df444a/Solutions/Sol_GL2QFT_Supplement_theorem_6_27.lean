-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_6_27
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T04:47:27.004832+00:00
-- url     : https://prove2.me/submissions/d34bbb3c-0ffc-45a9-bf9a-122a13a770dc

import Definitions.Def_GL2QFT_Supplement_AGammaGates

noncomputable section

open Classical

namespace GL2QFT.Supplement.Thm627Helpers

open FieldData AGammaGates
open scoped Matrix ComplexConjugate

/-! ### Layer 1: Finite field structure, Frobenius, trace/norm, discrete log, and characters -/

private lemma q_pos (D : FieldData) : 0 < D.q := by
  have := D.one_lt_q
  omega

private lemma q_sub_one_pos (D : FieldData) (hq : 2 < D.q) : 0 < D.q - 1 := by omega

private lemma q_sq_sub_one_pos (D : FieldData) (hq : 2 < D.q) : 0 < D.q ^ 2 - 1 := by
  have : 4 < D.q ^ 2 := by nlinarith
  omega

private lemma q_sq_sub_one_ne_zero (D : FieldData) : D.q ^ 2 - 1 ≠ 0 := by
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 4 ≤ D.q ^ 2 := by nlinarith
  omega

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

private lemma fq2_add_pow_q (D : FieldData) (z w : D.Fq2) :
    (z + w) ^ D.q = z ^ D.q + w ^ D.q := by
  simpa [fq2Frob_apply] using (fq2Frob D).map_add z w

private lemma fq2_sub_pow_q (D : FieldData) (z w : D.Fq2) :
    (z - w) ^ D.q = z ^ D.q - w ^ D.q := by
  simpa [fq2Frob_apply] using (fq2Frob D).map_sub z w

private lemma field_div_zero {K : Type*} [Field K] (a : K) : a / 0 = 0 := div_zero a

private lemma field_zero_pow {K : Type*} [Field K] {n : ℕ} (hn : n ≠ 0) : (0 : K) ^ n = 0 :=
  zero_pow hn

private lemma field_div_pow {K : Type*} [Field K] (a b : K) (n : ℕ) : (a / b) ^ n = a ^ n / b ^ n :=
  div_pow a b n

private lemma field_mul_inv {K : Type*} [Field K] (a b : K) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  rw [mul_inv_rev, mul_comm]

private lemma field_pow_eq_zero {K : Type*} [Field K] {a : K} {n : ℕ} (h : a ^ n = 0) : a = 0 :=
  eq_zero_of_pow_eq_zero h

private lemma field_div_eq_one_iff_eq {K : Type*} [Field K] {a b : K} (hb : b ≠ 0) :
    a / b = 1 ↔ a = b :=
  div_eq_one_iff_eq hb

private lemma field_mul_eq_zero {K : Type*} [Field K] {a b : K} :
    a * b = 0 ↔ a = 0 ∨ b = 0 :=
  mul_eq_zero

private lemma fq2_div_pow_q (D : FieldData) (z w : D.Fq2) :
    (z / w) ^ D.q = z ^ D.q / w ^ D.q := by
  by_cases hw : w = 0
  · subst hw; rw [field_div_zero, field_zero_pow (q_pos D).ne', field_div_zero]
  · have hwq : w ^ D.q ≠ 0 := fq2_pow_ne_zero D hw D.q
    apply mul_right_cancel₀ hwq
    rw [div_mul_cancel₀ _ hwq, ← fq2Frob_apply, ← fq2Frob_apply, ← fq2Frob_apply,
      ← (fq2Frob D).map_mul, div_mul_cancel₀ _ hw]

private lemma field_div_eq_div_iff {K : Type*} [Field K] {a b c d : K}
    (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  div_eq_div_iff hb hd

private lemma field_eq_div_iff {K : Type*} [Field K] {a b c : K} (hc : c ≠ 0) :
    a = b / c ↔ a * c = b :=
  eq_div_iff hc

private lemma field_div_mul_eq_mul_div {K : Type*} [Field K] (a b c : K) :
    (a / b) * c = (a * c) / b :=
  div_mul_eq_mul_div a b c

private lemma field_inv_inv {K : Type*} [Field K] (a : K) : a⁻¹⁻¹ = a := inv_inv a

private lemma field_neg_div_neg {K : Type*} [Field K] (a b : K) : -a / -b = a / b :=
  neg_div_neg_eq a b

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
          (Polynomial.X ^ D.q : Polynomial D.Fq2).natDegree := by
        simpa using hq
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    have hP_ne : P ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hP_deg
      omega
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
  have hfac : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
    have hq := D.one_lt_q
    zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]
    ring
  rw [hfac, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by omega)]

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
    rw [← orderOf_units, show (hu : D.Fq2) = D.h from rfl, D.h_order]
    rfl
  have hcard : Nat.card D.Fq2ˣ = D.q ^ 2 - 1 := by
    calc Nat.card D.Fq2ˣ = Nat.card D.Fq2 - 1 := by convert Nat.card_units D.Fq2
      _ = D.q ^ 2 - 1 := by rw [natCard_fq2]
  have htop : Subgroup.zpowers hu = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  have hmem : zu ∈ Subgroup.zpowers hu := htop ▸ Subgroup.mem_top zu
  obtain ⟨k, hk⟩ := hmem
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
  have hcard : Nat.card D.Fqˣ = D.q - 1 := by
    rw [Nat.card_units, natCard_fq]
  have htop : Subgroup.zpowers gu = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hcard])
  have hmem : xu ∈ Subgroup.zpowers gu := htop ▸ Subgroup.mem_top xu
  obtain ⟨k, hk⟩ := hmem
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

private lemma gen_pow_dlog (D : FieldData) {x : D.Fq} (hx : x ≠ 0) :
    D.gen ^ D.dlog x = x := by
  have h := exists_gen_pow D hx
  simpa [FieldData.dlog, dif_pos h] using Nat.find_spec h

private lemma h_pow_dlog2 (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) :
    D.h ^ D.dlog2 z = z := by
  have h := exists_h_pow D hz
  simpa [FieldData.dlog2, dif_pos h] using Nat.find_spec h

private lemma dlog_modEq_of_pow (D : FieldData) {x : D.Fq} (hx : x ≠ 0) {n : ℕ}
    (hn : D.gen ^ n = x) : D.dlog x ≡ n [MOD (D.q - 1)] := by
  let gu : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hpow : gu ^ D.dlog x = gu ^ n := by
    ext; simp [gu, gen_pow_dlog D hx, hn]
  have hord : orderOf gu = D.q - 1 := by
    rw [← orderOf_units, show (gu : D.Fq) = D.gen from rfl, orderOf_gen]
  rwa [pow_eq_pow_iff_modEq, hord] at hpow

private lemma dlog2_modEq_of_pow (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) {n : ℕ}
    (hn : D.h ^ n = z) : D.dlog2 z ≡ n [MOD (D.q ^ 2 - 1)] := by
  let hu : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  have hpow : hu ^ D.dlog2 z = hu ^ n := by
    ext; simp [hu, h_pow_dlog2 D hz, hn]
  have hord : orderOf hu = D.q ^ 2 - 1 := by
    rw [← orderOf_units, show (hu : D.Fq2) = D.h from rfl, D.h_order]
    rfl
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
      rw [← orderOf_gen D]
      exact pow_orderOf_eq_one D.gen
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
      have ho : orderOf D.h = D.q ^ 2 - 1 := D.h_order
      rw [← ho]
      exact pow_orderOf_eq_one D.h
    calc D.h ^ (D.dlog2 z % (D.q ^ 2 - 1))
        = (D.h ^ (D.q ^ 2 - 1)) ^ (D.dlog2 z / (D.q ^ 2 - 1)) *
            D.h ^ (D.dlog2 z % (D.q ^ 2 - 1)) := by
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

private lemma chi_zero_right (D : FieldData) (α : D.Lab) : D.chi α 0 = 0 := by
  simp [FieldData.chi]

private lemma chi_one_right (D : FieldData) (α : D.Lab) : D.chi α 1 = 1 := by
  simp [FieldData.chi, dlog_one]

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
  congr 1
  push_cast
  ring

private lemma chi_add_lab (D : FieldData) (α β : D.Lab) (x : D.Fq) :
    D.chi (α + β) x = D.chi α x * D.chi β x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  simp only [FieldData.chi, if_neg hx, ← Complex.exp_add]
  have hmod : (α + β).val ≡ α.val + β.val [MOD (D.q - 1)] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hmod' : (α + β).val * D.dlog x ≡ α.val * D.dlog x + β.val * D.dlog x [MOD (D.q - 1)] := by
    simpa [add_mul] using hmod.mul_right (D.dlog x)
  have hq : D.q - 1 ≠ 0 := by have := D.one_lt_q; omega
  rw [exp_two_pi_I_div_eq_of_modEq hq hmod']
  congr 1
  push_cast
  ring

private lemma chi_norm (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    ‖D.chi α x‖ = 1 := by
  simp only [FieldData.chi, if_neg hx]
  have heq : (2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ)) =
      ((2 * Real.pi * ((α.val * D.dlog x : ℕ) : ℝ) / ((D.q - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma chi_ne_zero (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    D.chi α x ≠ 0 := by
  simp [FieldData.chi, hx, Complex.exp_ne_zero]

private lemma chi_neg_lab (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi (-α) x = star (D.chi α x) := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  have h1 : D.chi (-α) x * D.chi α x = 1 := by
    rw [← chi_add_lab, neg_add_cancel, chi_zero_left D hx]
  have h2 : star (D.chi α x) * D.chi α x = 1 := by
    rw [RCLike.star_def, Complex.conj_mul', chi_norm D α hx, Complex.ofReal_one, one_pow]
  exact mul_right_cancel₀ (chi_ne_zero D α hx) (h1.trans h2.symm)

private lemma chi_inv_right (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi α x⁻¹ = D.chi (-α) x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero_right]
  have h1 : D.chi α x⁻¹ * D.chi α x = 1 := by
    rw [← chi_mul, inv_mul_cancel₀ hx, chi_one_right]
  have h2 : D.chi (-α) x * D.chi α x = 1 := by
    rw [← chi_add_lab, neg_add_cancel, chi_zero_left D hx]
  exact mul_right_cancel₀ (chi_ne_zero D α hx) (h1.trans h2.symm)

private lemma chi_div (D : FieldData) (α : D.Lab) (x y : D.Fq) :
    D.chi α (x / y) = D.chi α x * D.chi (-α) y := by
  rw [div_eq_mul_inv, chi_mul, chi_inv_right]

private lemma chi_neg_one_sq (D : FieldData) (α : D.Lab) :
    D.chi α (-1) ^ 2 = 1 := by
  rw [sq, ← chi_mul, neg_mul_neg, one_mul, chi_one_right]

private lemma star_chi_neg_one (D : FieldData) (α : D.Lab) :
    star (D.chi α (-1)) = D.chi α (-1) := by
  rw [← chi_neg_lab]
  have h1 : D.chi (-α) (-1) * D.chi α (-1) = 1 := by
    rw [← chi_add_lab, neg_add_cancel, chi_zero_left D (neg_ne_zero.mpr one_ne_zero)]
  have h2 : D.chi α (-1) * D.chi α (-1) = 1 := by
    rw [← sq, chi_neg_one_sq]
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
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _, mul_ne_zero (gen_ne_zero D) hx.2⟩
      · intro x₁ _ x₂ _ h
        exact mul_left_cancel₀ (gen_ne_zero D) h
      · intro y hy
        rw [Finset.mem_filter] at hy
        exact ⟨D.gen⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          mul_ne_zero (inv_ne_zero (gen_ne_zero D)) hy.2⟩,
          by rw [← mul_assoc, mul_inv_cancel₀ (gen_ne_zero D), one_mul]⟩
      · intro x _
        rw [chi_mul]
    have hne : D.chi α D.gen - 1 ≠ 0 := sub_ne_zero.mpr (chi_gen_ne_one D hq hα)
    have h0 : (D.chi α D.gen - 1) * S = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp h0).resolve_left hne

private lemma chi_one_ne_one (D : FieldData) (hq : 2 < D.q) {x : D.Fq} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    D.chi 1 x ≠ 1 := by
  have h1val : (1 : D.Lab).val = 1 := by
    have : Fact (1 < D.q - 1) := ⟨by omega⟩
    exact ZMod.val_one (D.q - 1)
  simp only [FieldData.chi, if_neg hx0, h1val, one_mul]
  intro heq
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by omega)] at heq
  have hd_lt : D.dlog x < D.q - 1 := dlog_lt D hx0
  have hd_pos : 0 < D.dlog x := by
    rcases Nat.eq_zero_or_pos (D.dlog x) with h0 | hpos
    · have hpow := gen_pow_dlog D hx0
      rw [h0, pow_zero] at hpow
      exact False.elim (hx1 hpow.symm)
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

/-! ### Layer 1b: `theta`, `restrLab`, `theta0Lab`, `kerChar`, and `psi` -/

private lemma theta_zero_right (D : FieldData) (k : D.Lab2) : D.theta k 0 = 0 := by
  simp [FieldData.theta]

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
  congr 1
  push_cast
  ring

private lemma theta_add_lab (D : FieldData) (k₁ k₂ : D.Lab2) (z : D.Fq2) :
    D.theta (k₁ + k₂) z = D.theta k₁ z * D.theta k₂ z := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero_right]
  simp only [FieldData.theta, if_neg hz, ← Complex.exp_add]
  have hmod : (k₁ + k₂).val ≡ k₁.val + k₂.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hmod' : (k₁ + k₂).val * D.dlog2 z ≡
      k₁.val * D.dlog2 z + k₂.val * D.dlog2 z [MOD (D.q ^ 2 - 1)] := by
    simpa [add_mul] using hmod.mul_right (D.dlog2 z)
  rw [exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) hmod']
  congr 1
  push_cast
  ring

private lemma theta_norm (D : FieldData) (k : D.Lab2) {z : D.Fq2} (hz : z ≠ 0) :
    ‖D.theta k z‖ = 1 := by
  simp only [FieldData.theta, if_neg hz]
  have heq : (2 * Real.pi * Complex.I * ((k.val * D.dlog2 z : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ)) =
      ((2 * Real.pi * ((k.val * D.dlog2 z : ℕ) : ℝ) / ((D.q ^ 2 - 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma theta_ne_zero (D : FieldData) (k : D.Lab2) {z : D.Fq2} (hz : z ≠ 0) :
    D.theta k z ≠ 0 := by
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

private lemma theta_pow_q (D : FieldData) (k : D.Lab2) (z : D.Fq2) :
    D.theta k (z ^ D.q) = D.theta ((D.q : D.Lab2) * k) z := by
  by_cases hz : z = 0
  · subst hz; rw [zero_pow (q_pos D).ne', theta_zero_right, theta_zero_right]
  have hzq : z ^ D.q ≠ 0 := fq2_pow_ne_zero D hz D.q
  simp only [FieldData.theta, if_neg hzq, if_neg hz]
  have hpow : D.h ^ (D.q * D.dlog2 z) = z ^ D.q := by
    rw [mul_comm, pow_mul, h_pow_dlog2 D hz]
  have hmod1 : D.dlog2 (z ^ D.q) ≡ D.q * D.dlog2 z [MOD (D.q ^ 2 - 1)] :=
    dlog2_modEq_of_pow D hzq hpow
  have hmod2 : ((D.q : D.Lab2) * k).val ≡ D.q * k.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_mul, ZMod.val_natCast]
    exact (Nat.mod_modEq (D.q % (D.q ^ 2 - 1) * k.val) (D.q ^ 2 - 1)).trans
      ((Nat.mod_modEq D.q (D.q ^ 2 - 1)).mul_right k.val)
  have hmod : k.val * D.dlog2 (z ^ D.q) ≡ ((D.q : D.Lab2) * k).val * D.dlog2 z [MOD (D.q ^ 2 - 1)] := by
    have a := hmod1.mul_left k.val
    have b := hmod2.mul_right (D.dlog2 z)
    have b' : D.q * k.val * D.dlog2 z ≡ ((D.q : D.Lab2) * k).val * D.dlog2 z [MOD (D.q ^ 2 - 1)] :=
      b.symm
    exact a.trans (by simpa [mul_assoc, mul_left_comm] using b')
  exact exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) hmod

private lemma q_sq_sub_one_eq_mul (D : FieldData) :
    D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
  have hq := D.one_lt_q
  zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]
  ring

private lemma theta_algebraMap (D : FieldData) (k : D.Lab2) (x : D.Fq) :
    D.theta k (algebraMap D.Fq D.Fq2 x) = D.chi (D.restrLab k) x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, theta_zero_right, chi_zero_right]
  have hax : algebraMap D.Fq D.Fq2 x ≠ 0 := by
    simpa [map_eq_zero] using hx
  simp only [FieldData.theta, FieldData.chi, if_neg hax, if_neg hx]
  have hpow : D.h ^ ((D.q + 1) * D.dlog x) = algebraMap D.Fq D.Fq2 x := by
    rw [pow_mul, ← algebraMap_gen, ← map_pow, gen_pow_dlog D hx]
  have hmod1 : D.dlog2 (algebraMap D.Fq D.Fq2 x) ≡ (D.q + 1) * D.dlog x [MOD (D.q ^ 2 - 1)] :=
    dlog2_modEq_of_pow D hax hpow
  rw [exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) (hmod1.mul_left k.val)]
  have hmod2 : (D.restrLab k).val ≡ k.val [MOD (D.q - 1)] := by
    simp only [FieldData.restrLab, ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  have hq1 : D.q - 1 ≠ 0 := by have := D.one_lt_q; omega
  rw [exp_two_pi_I_div_eq_of_modEq hq1 (hmod2.mul_right (D.dlog x))]
  congr 1
  have hfac : ((D.q ^ 2 - 1 : ℕ) : ℂ) = ((D.q + 1 : ℕ) : ℂ) * ((D.q - 1 : ℕ) : ℂ) := by
    exact_mod_cast q_sq_sub_one_eq_mul D
  have hq1' : ((D.q + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq2' : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq1
  rw [hfac]
  push_cast
  field_simp

private lemma theta_mul_q_add_one (D : FieldData) (δ : D.Lab) (z : D.Fq2) :
    D.theta (((D.q + 1) * δ.val : ℕ) : D.Lab2) z = D.chi δ (D.nrm z) := by
  by_cases hz : z = 0
  · subst hz; simp [FieldData.nrm, theta_zero_right, chi_zero_right]
  have hnz : D.nrm z ≠ 0 := by
    intro h0
    have h1 := algebraMap_nrm D z
    rw [h0, map_zero] at h1
    exact fq2_pow_ne_zero D hz (D.q + 1) h1.symm
  simp only [FieldData.theta, FieldData.chi, if_neg hz, if_neg hnz]
  have hpow : D.gen ^ D.dlog2 z = D.nrm z := by
    apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
    rw [map_pow, algebraMap_gen, algebraMap_nrm, ← pow_mul, mul_comm, pow_mul, h_pow_dlog2 D hz]
  have hmod1 : D.dlog (D.nrm z) ≡ D.dlog2 z [MOD (D.q - 1)] :=
    dlog_modEq_of_pow D hnz hpow
  have hq1 : D.q - 1 ≠ 0 := by have := D.one_lt_q; omega
  rw [exp_two_pi_I_div_eq_of_modEq hq1 (hmod1.mul_left δ.val)]
  have hmod2 : (((D.q + 1) * δ.val : ℕ) : D.Lab2).val ≡ (D.q + 1) * δ.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_natCast]
    exact Nat.mod_modEq _ _
  rw [exp_two_pi_I_div_eq_of_modEq (q_sq_sub_one_ne_zero D) (hmod2.mul_right (D.dlog2 z))]
  congr 1
  have hfac : ((D.q ^ 2 - 1 : ℕ) : ℂ) = ((D.q + 1 : ℕ) : ℂ) * ((D.q - 1 : ℕ) : ℂ) := by
    exact_mod_cast q_sq_sub_one_eq_mul D
  have hq1' : ((D.q + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq2' : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq1
  rw [hfac]
  push_cast
  field_simp

private lemma restrLab_add (D : FieldData) (k₁ k₂ : D.Lab2) :
    D.restrLab (k₁ + k₂) = D.restrLab k₁ + D.restrLab k₂ := by
  simp only [FieldData.restrLab]
  have hq : (D.q - 1) ∣ (D.q ^ 2 - 1) := ⟨D.q + 1, by rw [q_sq_sub_one_eq_mul, mul_comm]⟩
  have hmod := Nat.ModEq.of_dvd hq
    (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _ : (k₁ + k₂).val ≡ k₁.val + k₂.val [MOD (D.q ^ 2 - 1)])
  rw [← ZMod.natCast_eq_natCast_iff] at hmod
  simpa [Nat.cast_add] using hmod

private lemma restrLab_neg (D : FieldData) (k : D.Lab2) :
    D.restrLab (-k) = -D.restrLab k := by
  apply eq_neg_of_add_eq_zero_left
  rw [← restrLab_add, neg_add_cancel]
  simp [FieldData.restrLab]

private lemma restrLab_sub (D : FieldData) (k₁ k₂ : D.Lab2) :
    D.restrLab (k₁ - k₂) = D.restrLab k₁ - D.restrLab k₂ := by
  rw [sub_eq_add_neg, restrLab_add, restrLab_neg, sub_eq_add_neg]

private lemma restrLab_theta0 (D : FieldData) (γ : D.Lab) :
    D.restrLab (theta0Lab D γ) = γ := by
  simp only [FieldData.restrLab, theta0Lab]
  have hq : D.q - 1 < D.q ^ 2 - 1 := by
    have := D.one_lt_q
    have : D.q < D.q ^ 2 := by nlinarith
    omega
  have hlt : γ.val < D.q ^ 2 - 1 := (ZMod.val_lt γ).trans hq
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.natCast_zmod_val]

private lemma restrLab_mul_q (D : FieldData) (k : D.Lab2) :
    D.restrLab ((D.q : D.Lab2) * k) = D.restrLab k := by
  simp only [FieldData.restrLab]
  have hq : (D.q - 1) ∣ (D.q ^ 2 - 1) := ⟨D.q + 1, by rw [q_sq_sub_one_eq_mul, mul_comm]⟩
  have hmod1 : ((D.q : D.Lab2) * k).val ≡ D.q * k.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_mul, ZMod.val_natCast]
    exact (Nat.mod_modEq _ _).trans ((Nat.mod_modEq _ _).mul_right _)
  have hmod2 : ((D.q : D.Lab2) * k).val ≡ D.q * k.val [MOD (D.q - 1)] :=
    Nat.ModEq.of_dvd hq hmod1
  have hqmod : D.q ≡ 1 [MOD (D.q - 1)] := by
    rw [Nat.modEq_iff_dvd]
    exact ⟨-1, by have := D.one_lt_q; omega⟩
  have hmod3 : ((D.q : D.Lab2) * k).val ≡ k.val [MOD (D.q - 1)] :=
    hmod2.trans (by simpa using hqmod.mul_right k.val)
  rw [← ZMod.natCast_eq_natCast_iff] at hmod3
  exact hmod3

private lemma restrLab_q_add_one_mul (D : FieldData) (δ : D.Lab) :
    D.restrLab (((D.q + 1) * δ.val : ℕ) : D.Lab2) = 2 * δ := by
  simp only [FieldData.restrLab]
  have hq : (D.q - 1) ∣ (D.q ^ 2 - 1) := ⟨D.q + 1, by rw [q_sq_sub_one_eq_mul, mul_comm]⟩
  have hmod1 : (((D.q + 1) * δ.val : ℕ) : D.Lab2).val ≡ (D.q + 1) * δ.val [MOD (D.q ^ 2 - 1)] := by
    rw [ZMod.val_natCast]; exact Nat.mod_modEq _ _
  have hmod2 := Nat.ModEq.of_dvd hq hmod1
  have hqmod : D.q + 1 ≡ 2 [MOD (D.q - 1)] := by
    rw [Nat.modEq_iff_dvd]
    exact ⟨-1, by have := D.one_lt_q; omega⟩
  have hmod3 := hmod2.trans (hqmod.mul_right δ.val)
  rw [← ZMod.natCast_eq_natCast_iff] at hmod3
  simpa [Nat.cast_mul, ZMod.natCast_zmod_val] using hmod3

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

private lemma sum_theta_fq2_units (D : FieldData) (hq : 2 < D.q) (k : D.Lab2) :
    ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z =
      if k = 0 then (D.q : ℂ) ^ 2 - 1 else 0 := by
  split_ifs with hk
  · subst hk
    rw [Finset.sum_congr rfl (fun z hz => theta_zero_left D (Finset.mem_filter.mp hz).2),
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : (Finset.univ.filter (fun z : D.Fq2 => z ≠ 0)).card = D.q ^ 2 - 1 := by
      have hfilt : Finset.univ.filter (fun z : D.Fq2 => z ≠ 0) =
          Finset.univ \ ({0} : Finset D.Fq2) := by ext z; simp
      rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_fq2,
        Finset.card_singleton]
    rw [hcard, Nat.cast_sub (by have := D.one_lt_q; nlinarith), Nat.cast_pow, Nat.cast_one]
  · set S := ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z
    have hmul : D.theta k D.h * S = S := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun z _ => D.h * z) ?_ ?_ ?_ ?_
      · intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨Finset.mem_univ _, mul_ne_zero (h_ne_zero D) hz.2⟩
      · intro z₁ _ z₂ _ h
        exact mul_left_cancel₀ (h_ne_zero D) h
      · intro w hw
        rw [Finset.mem_filter] at hw
        exact ⟨D.h⁻¹ * w, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          mul_ne_zero (inv_ne_zero (h_ne_zero D)) hw.2⟩,
          by rw [← mul_assoc, mul_inv_cancel₀ (h_ne_zero D), one_mul]⟩
      · intro z _
        rw [theta_mul]
    have hne : D.theta k D.h - 1 ≠ 0 := sub_ne_zero.mpr (theta_h_ne_one D hq hk)
    have h0 : (D.theta k D.h - 1) * S = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp h0).resolve_left hne

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
  have hax : algebraMap D.Fq D.Fq2 x = w' / w := hx
  have hw'_eq : w' = algebraMap D.Fq D.Fq2 x * w := by
    rw [hax, div_mul_cancel₀ _ hw]
  have hx0 : x ≠ 0 := by
    intro hx0
    rw [hx0, map_zero, zero_mul] at hw'_eq
    exact hw' hw'_eq
  rw [hw'_eq, theta_mul, theta_algebraMap, hm, chi_zero_left D hx0, one_mul]

private lemma kerChar_one (D : FieldData) {m : D.Lab2} (hm : D.restrLab m = 0) :
    kerChar D m 1 = 1 := by
  have h := kerChar_eq_theta D hm (w := 1) one_ne_zero
  simpa [one_pow, div_one, theta_one_right] using h

private lemma exists_ker_quot (D : FieldData) {r : D.Fq2} (hr0 : r ≠ 0) (hr1 : r ^ (D.q + 1) = 1) :
    ∃ w : D.Fq2, w ≠ 0 ∧ w / w ^ D.q = r := by
  have hq : 1 < D.q := D.one_lt_q
  have hpow : D.h ^ ((D.q + 1) * D.dlog2 r) = 1 := by
    rw [mul_comm, pow_mul, h_pow_dlog2 D hr0, hr1]
  have hdvd : D.q ^ 2 - 1 ∣ (D.q + 1) * D.dlog2 r := by
    rw [show D.q ^ 2 - 1 = orderOf D.h from D.h_order.symm]
    exact orderOf_dvd_of_pow_eq_one hpow
  rw [q_sq_sub_one_eq_mul D] at hdvd
  have hdvd' : D.q - 1 ∣ D.dlog2 r :=
    (Nat.mul_dvd_mul_iff_left (by omega : 0 < D.q + 1)).mp hdvd
  obtain ⟨j, hj⟩ := hdvd'
  refine ⟨(D.h⁻¹) ^ j, fq2_pow_ne_zero D (inv_ne_zero (h_ne_zero D)) j, ?_⟩
  have hq_sub : 1 ≤ D.q := by omega
  have hhjq : ((D.h⁻¹) ^ j) ^ D.q = ((D.h ^ j) ^ D.q)⁻¹ := by
    rw [inv_pow, inv_pow]
  calc (D.h⁻¹) ^ j / ((D.h⁻¹) ^ j) ^ D.q
      = (D.h⁻¹) ^ j * (D.h ^ j) ^ D.q := by
          rw [div_eq_mul_inv, hhjq, field_inv_inv]
    _ = (D.h⁻¹) ^ j * D.h ^ (j * D.q) := by rw [← pow_mul]
    _ = (D.h⁻¹) ^ j * (D.h ^ j * D.h ^ ((D.q - 1) * j)) := by
          rw [← pow_add]
          congr 2
          zify [hq_sub]
          ring
    _ = ((D.h⁻¹) ^ j * D.h ^ j) * D.h ^ ((D.q - 1) * j) := by ring
    _ = D.h ^ D.dlog2 r := by
          rw [← mul_pow, inv_mul_cancel₀ (h_ne_zero D), one_pow, one_mul, ← hj]
    _ = r := h_pow_dlog2 D hr0

private lemma kerChar_mul_theta0 (D : FieldData) (γ : D.Lab)
    (θ : {θ : D.Lab2 // D.restrLab θ = γ}) {z : D.Fq2} (hz : z ≠ 0) :
    D.theta (theta0Lab D γ) z * kerChar D (θ.1 - theta0Lab D γ) (z / z ^ D.q) = D.theta θ.1 z := by
  have hm : D.restrLab (θ.1 - theta0Lab D γ) = 0 := by
    rw [restrLab_sub, θ.2, restrLab_theta0, sub_self]
  rw [kerChar_eq_theta D hm hz, ← theta_add_lab, add_sub_cancel]

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
        rw [q_sq_sub_one_eq_mul, mul_comm (D.q + 1) (D.q - 1)]
        exact Nat.mul_lt_mul_of_pos_left j₁.2 hqsub
      have hlt₂ : (D.q - 1) * j₂.1 < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul, mul_comm (D.q + 1) (D.q - 1)]
        exact Nat.mul_lt_mul_of_pos_left j₂.2 hqsub
      have hv1 : ((toKer j₁).1 - theta0Lab D γ).val = (D.q - 1) * j₁.1 := by
        dsimp only [toKer]
        rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hlt₁]
      have hv2 : ((toKer j₂).1 - theta0Lab D γ).val = (D.q - 1) * j₂.1 := by
        dsimp only [toKer]
        rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hlt₂]
      rw [hv1, hv2] at hval
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hqsub hval)
    · intro θ
      set m := θ.1 - theta0Lab D γ
      have hm0 : D.restrLab m = 0 := by rw [restrLab_sub, θ.2, restrLab_theta0, sub_self]
      have hdvd : D.q - 1 ∣ m.val := (ZMod.natCast_eq_zero_iff m.val (D.q - 1)).mp hm0
      obtain ⟨j, hj⟩ := hdvd
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
    rw [hinv]
    ring
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
          rw [field_div_eq_div_iff hw₁q hw₁0]
          constructor <;> intro h <;> linear_combination h
      _ ↔ (w₂ / w₁) ^ D.q = w₂ / w₁ := by rw [fq2_div_pow_q]
  split_ifs with h12
  · have huq : u ^ D.q = u := heq_iff.mp h12
    obtain ⟨x, hx⟩ := (fq2_pow_q_eq_self_iff D u).mp huq
    have hx0 : x ≠ 0 := by intro h0; rw [h0, map_zero] at hx; exact hu0 hx.symm
    have h1 : ∀ j : Fin (D.q + 1), D.theta (((D.q - 1) * j.1 : ℕ) : D.Lab2) u = 1 := by
      intro j
      rw [← hx, theta_algebraMap]
      have hr0 : D.restrLab (((D.q - 1) * j.1 : ℕ) : D.Lab2) = 0 := by
        have := (toKer j).2
        rw [restrLab_add, restrLab_theta0] at this
        simpa [add_eq_left] using this
      rw [hr0, chi_zero_left D hx0]
    simp_rw [h1]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · have huq : u ^ D.q ≠ u := fun h => h12 (heq_iff.mpr h)
    have hmul1 : D.theta (((D.q - 1) : ℕ) : D.Lab2) u ≠ 1 := by
      intro h1
      have hpow : (u ^ (D.q - 1)) = 1 := by
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
          · have hs := h_pow_dlog2 D hupow
            rw [h0, pow_zero] at hs
            exact False.elim (hne1 hs.symm)
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
      rw [← theta_add_lab]
      congr 1
      have hjlt : j.1 + 1 ≤ D.q + 1 := j.2
      rcases lt_or_eq_of_le hjlt with hlt | heq
      · have hj1 : (j + 1).1 = j.1 + 1 := by
          simp [Fin.val_add, Nat.mod_eq_of_lt hlt]
        rw [hj1]
        push_cast
        ring
      · have hj1 : (j + 1).1 = 0 := by
          simp [Fin.val_add, heq]
        rw [hj1, mul_zero, Nat.cast_zero]
        have hlhs : (((D.q - 1 : ℕ) : D.Lab2) + (((D.q - 1) * j.1 : ℕ) : D.Lab2)) =
            (((D.q ^ 2 - 1 : ℕ) : D.Lab2)) := by
          rw [← Nat.cast_add, show D.q - 1 + (D.q - 1) * j.1 = (D.q - 1) * (j.1 + 1) by ring,
            heq, mul_comm, ← q_sq_sub_one_eq_mul]
        rw [hlhs, ZMod.natCast_self]
    have h0 : (D.theta (((D.q - 1) : ℕ) : D.Lab2) u - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hmul1)

private lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by
  simp [FieldData.psi]

private lemma psi_add (D : FieldData) (x y : D.Fq) :
    D.psi (x + y) = D.psi x * D.psi y := by
  simp only [FieldData.psi, map_add, ← Complex.exp_add]
  have hmod : (Algebra.trace (ZMod D.p) D.Fq x + Algebra.trace (ZMod D.p) D.Fq y).val ≡
      (Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val [MOD D.p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  rw [exp_two_pi_I_div_eq_of_modEq D.hp.ne_zero hmod]
  congr 1
  push_cast
  ring

private lemma psi_norm (D : FieldData) (x : D.Fq) : ‖D.psi x‖ = 1 := by
  simp only [FieldData.psi]
  have heq : (2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) /
      (D.p : ℂ)) =
      ((2 * Real.pi * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℝ) / (D.p : ℝ) : ℝ) : ℂ) *
        Complex.I := by
    push_cast; ring
  rw [heq]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma psi_ne_zero (D : FieldData) (x : D.Fq) : D.psi x ≠ 0 := by
  simp [FieldData.psi, Complex.exp_ne_zero]

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
    · intro i hi hne
      rw [Finset.mem_range] at hi
      have hne_pow : D.p ^ (D.r - 1) ≠ D.p ^ i :=
        fun h => hne (Nat.pow_right_injective D.hp.one_lt h).symm
      simp [hne_pow]
    · intro habs; exact False.elim (habs hrm1)
  have hdeg : P.natDegree < D.q := by
    have hle : P.natDegree ≤ D.p ^ (D.r - 1) := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Polynomial.natDegree_X_pow]
      exact Nat.pow_le_pow_right D.hp.pos (by omega)
    have hlt : D.p ^ (D.r - 1) < D.p ^ D.r :=
      Nat.pow_lt_pow_right D.hp.one_lt (by have := D.hr; omega)
    exact lt_of_le_of_lt hle hlt
  have hcard : P.roots.toFinset.card < Fintype.card D.Fq := by
    calc P.roots.toFinset.card
        ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ < D.q := hdeg
      _ = Fintype.card D.Fq := (card_fq D).symm
  obtain ⟨c, hc_mem⟩ : ∃ c : D.Fq, c ∉ P.roots.toFinset := by
    by_contra h
    push Not at h
    have hsub : Finset.univ ⊆ P.roots.toFinset := fun x _ => h x
    exact (Finset.card_le_card hsub).not_gt hcard
  have htr_ne : Algebra.trace (ZMod D.p) D.Fq c ≠ 0 := by
    intro h0
    have hmap := FiniteField.algebraMap_trace_eq_sum_pow (ZMod D.p) D.Fq c
    rw [finrank_fq, Nat.card_zmod, h0, map_zero] at hmap
    have heval : P.eval c = 0 := by
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_X_pow]
      exact hmap.symm
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
  · subst hb
    simp [psi_zero, Finset.sum_const, Finset.card_univ, card_fq]
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
        (fun _ _ _ _ h => add_left_cancel h)
        (fun z _ => ⟨z - c, Finset.mem_univ _, add_sub_cancel c z⟩)
        (fun y _ => by rw [psi_add])
    have h0 : (D.psi c - 1) * S = 0 := by linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

/-! ### Layer 2: Gauss sums, Jacobi sums, and Lemma A.5 -/

private lemma gauss_zero (D : FieldData) : D.gauss 0 = -1 := by
  simp only [FieldData.gauss, FieldData.gaussG, one_mul]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [chi_zero_left D (Finset.mem_filter.mp hx).2, one_mul])]
  have hsum : ∑ x : D.Fq, D.psi x = 0 := by
    simpa using sum_psi_mul D 1
  have hsplit : ∑ x : D.Fq, D.psi x =
      D.psi 0 + ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.psi x := by
    rw [← Finset.add_sum_erase Finset.univ D.psi (Finset.mem_univ 0)]
    congr 1
    apply Finset.sum_congr
    · ext x; simp [Finset.mem_erase]
    · intro _ _; rfl
  rw [hsplit, psi_zero] at hsum
  linear_combination hsum

private lemma gaussG_eq (D : FieldData) (α : D.Lab) {b : D.Fq} (hb : b ≠ 0) :
    D.gaussG α b = D.chi (-α) b * D.gauss α := by
  simp only [FieldData.gauss, FieldData.gaussG, one_mul, Finset.mul_sum]
  refine Finset.sum_bij (fun x _ => b * x) ?_ ?_ ?_ ?_
  · intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_univ _, mul_ne_zero hb hx.2⟩
  · intro _ _ _ _ h; exact mul_left_cancel₀ hb h
  · intro y hy
    rw [Finset.mem_filter] at hy
    exact ⟨b⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero (inv_ne_zero hb) hy.2⟩,
      by rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]⟩
  · intro x _
    rw [chi_mul, ← chi_inv_right]
    have hinv : D.chi α b⁻¹ * D.chi α b = 1 := by
      rw [← chi_mul, inv_mul_cancel₀ hb, chi_one_right]
    calc D.chi α x * D.psi (b * x)
        = (D.chi α b⁻¹ * D.chi α b) * D.chi α x * D.psi (b * x) := by rw [hinv, one_mul]
      _ = D.chi α b⁻¹ * (D.chi α b * D.chi α x * D.psi (b * x)) := by ring

private lemma jacobi_symm (D : FieldData) (α β : D.Lab) :
    D.jacobi α β = D.jacobi β α := by
  simp only [FieldData.jacobi]
  refine Finset.sum_bij (fun x _ => 1 - x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    refine ⟨Finset.mem_univ _, sub_ne_zero.mpr hx.2.2.symm, ?_⟩
    intro h; exact hx.2.1 (by linear_combination -h)
  · intro x₁ _ x₂ _ h; linear_combination -h
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨1 - y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub_ne_zero.mpr hy.2.2.symm, ?_⟩, by ring⟩
    intro h; exact hy.2.1 (by linear_combination -h)
  · intro x _; rw [sub_sub_cancel, mul_comm]

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
        Finset.univ \ ({0, 1} : Finset D.Fq) := by
      ext x; simp
    rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_fq,
      Finset.card_pair (zero_ne_one : (0 : D.Fq) ≠ 1), Nat.cast_sub (by omega), Nat.cast_ofNat]
  · have hsum : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1),
        D.chi α x * D.chi (-α) (1 - x) =
        ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0 ∧ u ≠ -1), D.chi α u := by
      refine Finset.sum_bij (fun x _ => x / (1 - x)) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        have h1x : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.2.symm
        refine ⟨Finset.mem_univ _, div_ne_zero hx.2.1 h1x, ?_⟩
        intro heq
        rw [div_eq_iff h1x] at heq
        have : (1 : D.Fq) = 0 := by linear_combination heq
        exact one_ne_zero this
      · intro x₁ hx₁ x₂ hx₂ heq
        rw [Finset.mem_filter] at hx₁ hx₂
        have h1 : 1 - x₁ ≠ 0 := sub_ne_zero.mpr hx₁.2.2.symm
        have h2 : 1 - x₂ ≠ 0 := sub_ne_zero.mpr hx₂.2.2.symm
        rw [field_div_eq_div_iff h1 h2] at heq
        linear_combination heq
      · intro u hu
        rw [Finset.mem_filter] at hu
        have h1u : 1 + u ≠ 0 := fun h => hu.2.2 (by linear_combination h)
        refine ⟨u / (1 + u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_ne_zero hu.2.1 h1u, ?_⟩, ?_⟩
        · intro heq
          rw [field_div_eq_one_iff_eq h1u] at heq
          exact one_ne_zero (by linear_combination -heq : (1 : D.Fq) = 0)
        · have hsub : 1 - u / (1 + u) = 1 / (1 + u) := by
            calc 1 - u / (1 + u) = (1 + u) / (1 + u) - u / (1 + u) := by rw [div_self h1u]
              _ = (1 + u - u) / (1 + u) := (sub_div _ _ _).symm
              _ = 1 / (1 + u) := by rw [add_sub_cancel_right]
          rw [hsub, div_div_div_cancel_right₀ h1u, div_one]
      · intro x _
        rw [chi_div]
    rw [hsum]
    have hsplit : ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0), D.chi α u =
        D.chi α (-1) + ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0 ∧ u ≠ -1), D.chi α u := by
      have hm1 : (-1 : D.Fq) ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, neg_ne_zero.mpr one_ne_zero⟩
      rw [← Finset.add_sum_erase _ _ hm1]
      congr 1
      apply Finset.sum_congr
      · ext u; simp [Finset.mem_erase, and_comm]
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
      ext ⟨x, y⟩
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product]
      tauto
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
      ext
      · exact heq
      · linear_combination h1 - h2 - heq
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact ⟨(x, -x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2, neg_ne_zero.mpr hx.2,
        add_neg_cancel x⟩, rfl⟩
    · intro p hp
      have hadd : p.1 + p.2 = 0 := (Finset.mem_filter.mp hp).2.2.2
      have hp2 : p.2 = (-1) * p.1 := by linear_combination hadd
      rw [hadd, psi_zero, mul_one, hp2, chi_mul, chi_add_lab]
      ring
  · simp_rw [Finset.sum_mul]
    rw [← Finset.sum_product']
    refine Finset.sum_bij (fun p _ => (p.1 + p.2, p.1 / (p.1 + p.2))) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, hp.2.2.2⟩, Finset.mem_univ _, div_ne_zero hp.2.1 hp.2.2.2, ?_⟩
      intro hdiv
      rw [field_div_eq_one_iff_eq hp.2.2.2] at hdiv
      exact hp.2.2.1 (by linear_combination -hdiv)
    · intro p₁ hp₁ p₂ hp₂ heq
      rw [Finset.mem_filter] at hp₁ hp₂
      have hs : p₁.1 + p₁.2 = p₂.1 + p₂.2 := congrArg Prod.fst heq
      have hd : p₁.1 / (p₁.1 + p₁.2) = p₂.1 / (p₂.1 + p₂.2) := congrArg Prod.snd heq
      rw [hs, div_left_inj' hp₂.2.2.2] at hd
      ext
      · exact hd
      · linear_combination hs - hd
    · intro q hq
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hq
      refine ⟨(q.1 * q.2, q.1 * (1 - q.2)), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mul_ne_zero hq.1.2 hq.2.2.1, mul_ne_zero hq.1.2 (sub_ne_zero.mpr hq.2.2.2.symm),
        by rw [show q.1 * q.2 + q.1 * (1 - q.2) = q.1 by ring]; exact hq.1.2⟩, ?_⟩
      ext
      · ring
      · have hsum : q.1 * q.2 + q.1 * (1 - q.2) = q.1 := by ring
        rw [hsum, mul_div_cancel_left₀ _ hq.1.2]
    · intro p hp
      rw [Finset.mem_filter] at hp
      have hz : p.1 + p.2 ≠ 0 := hp.2.2.2
      have hp1 : p.1 = (p.1 + p.2) * (p.1 / (p.1 + p.2)) := (mul_div_cancel₀ _ hz).symm
      have hp2 : p.2 = (p.1 + p.2) * (1 - p.1 / (p.1 + p.2)) := by
        rw [mul_sub, mul_one, ← hp1]; ring
      calc D.chi α p.1 * D.chi β p.2 * D.psi (p.1 + p.2)
          = D.chi α ((p.1 + p.2) * (p.1 / (p.1 + p.2))) *
              D.chi β ((p.1 + p.2) * (1 - p.1 / (p.1 + p.2))) * D.psi (p.1 + p.2) := by
                conv_lhs =>
                  arg 1
                  arg 1
                  rw [hp1]
                conv_lhs =>
                  arg 1
                  arg 2
                  rw [hp2]
        _ = D.chi α (p.1 / (p.1 + p.2)) * D.chi β (1 - p.1 / (p.1 + p.2)) *
              (D.chi (α + β) (p.1 + p.2) * D.psi (p.1 + p.2)) := by
                rw [chi_mul, chi_mul, chi_add_lab]; ring

private lemma gauss_mul_gauss (D : FieldData) (hq : 2 < D.q) {α β : D.Lab} (h : α + β ≠ 0) :
    D.gauss α * D.gauss β = D.jacobi α β * D.gauss (α + β) := by
  rw [gauss_mul_gauss_split, sum_chi_fq_units D hq (α + β), if_neg h, mul_zero, zero_add]

private lemma gauss_mul_gauss_neg (D : FieldData) (hq : 2 < D.q) (α : D.Lab) :
    D.gauss α * D.gauss (-α) = if α = 0 then 1 else D.chi α (-1) * (D.q : ℂ) := by
  split_ifs with hα
  · subst hα; rw [neg_zero, gauss_zero]; ring
  · rw [gauss_mul_gauss_split, add_neg_cancel, sum_chi_fq_units D hq 0, if_pos rfl,
      jacobi_neg D hq α, if_neg hα, gauss_zero]
    have hneg : D.chi (-α) (-1) = D.chi α (-1) := by
      rw [chi_neg_lab, star_chi_neg_one]
    rw [hneg]
    ring

private lemma exists_tr_eq_zero (D : FieldData) :
    ∃ ζ : D.Fq2, ζ ≠ 0 ∧ D.tr ζ = 0 := by
  have h1 : D.h ^ D.q ≠ D.h := by
    intro heq
    have hpow : D.h ^ (D.q - 1) = 1 := by
      apply mul_right_cancel₀ (h_ne_zero D)
      rw [← pow_succ, show D.q - 1 + 1 = D.q from by have := D.one_lt_q; omega, heq, one_mul]
    have hdvd : D.q ^ 2 - 1 ∣ D.q - 1 := by
      rw [show D.q ^ 2 - 1 = orderOf D.h from D.h_order.symm]
      exact orderOf_dvd_of_pow_eq_one hpow
    have hle := Nat.le_of_dvd (by have := D.one_lt_q; omega) hdvd
    have hq := D.one_lt_q
    have hq2 : D.q < D.q ^ 2 := by nlinarith
    omega
  refine ⟨D.h - D.h ^ D.q, sub_ne_zero.mpr h1.symm, ?_⟩
  apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
  rw [map_zero, algebraMap_tr, fq2_sub_pow_q, ← pow_mul, ← sq, fq2_pow_q_sq]
  ring

private lemma exists_tr_eq_one (D : FieldData) :
    ∃ w₀ : D.Fq2, D.tr w₀ = 1 := by
  have := fq2_isDomain D
  have hex : ∃ w : D.Fq2, D.tr w ≠ 0 := by
    by_contra h
    push Not at h
    let P : Polynomial D.Fq2 := Polynomial.X ^ D.q + Polynomial.X
    have hq : 1 < D.q := D.one_lt_q
    have hP_deg : P.natDegree = D.q := by
      have hlt : (Polynomial.X : Polynomial D.Fq2).natDegree <
          (Polynomial.X ^ D.q : Polynomial D.Fq2).natDegree := by simpa using hq
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    have hP_ne : P ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hP_deg; omega
    have hcard : P.roots.toFinset.card < Fintype.card D.Fq2 := by
      calc P.roots.toFinset.card
          ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ = D.q := hP_deg
        _ < D.q ^ 2 := by nlinarith
        _ = Fintype.card D.Fq2 := (card_fq2 D).symm
    have hsub : Finset.univ ⊆ P.roots.toFinset := by
      intro z _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP_ne, Polynomial.IsRoot,
        Polynomial.eval_add, Polynomial.eval_X_pow, Polynomial.eval_X,
        add_comm, ← algebraMap_tr, h z, map_zero]
    exact (Finset.card_le_card hsub).not_gt hcard
  obtain ⟨w, hw⟩ := hex
  refine ⟨algebraMap D.Fq D.Fq2 (D.tr w)⁻¹ * w, ?_⟩
  have hsmul : algebraMap D.Fq D.Fq2 (D.tr w)⁻¹ * w = (D.tr w)⁻¹ • w := (Algebra.smul_def _ _).symm
  rw [FieldData.tr, hsmul, map_smul, show Algebra.trace D.Fq D.Fq2 w = D.tr w from rfl,
    smul_eq_mul, inv_mul_cancel₀ hw]

private lemma tr_eq_zero_iff (D : FieldData) {ζ : D.Fq2} (hζ0 : ζ ≠ 0) (hζtr : D.tr ζ = 0)
    (z : D.Fq2) : z ≠ 0 ∧ D.tr z = 0 ↔ ∃ t : D.Fq, t ≠ 0 ∧ z = algebraMap D.Fq D.Fq2 t * ζ := by
  constructor
  · rintro ⟨hz0, hztr⟩
    have hζq : ζ ^ D.q = -ζ := by
      have h := algebraMap_tr D ζ
      rw [hζtr, map_zero] at h
      linear_combination -h
    have hzq : z ^ D.q = -z := by
      have h := algebraMap_tr D z
      rw [hztr, map_zero] at h
      linear_combination -h
    have hpow : (z / ζ) ^ D.q = z / ζ := by
      rw [fq2_div_pow_q, hzq, hζq, field_neg_div_neg]
    obtain ⟨t, ht⟩ := (fq2_pow_q_eq_self_iff D (z / ζ)).mp hpow
    have ht0 : t ≠ 0 := by
      intro h0; rw [h0, map_zero] at ht; exact div_ne_zero hz0 hζ0 ht.symm
    exact ⟨t, ht0, by rw [ht, div_mul_cancel₀ _ hζ0]⟩
  · rintro ⟨t, ht0, rfl⟩
    refine ⟨mul_ne_zero (by simpa [map_eq_zero] using ht0) hζ0, ?_⟩
    have hsmul : algebraMap D.Fq D.Fq2 t * ζ = t • ζ := (Algebra.smul_def t ζ).symm
    rw [FieldData.tr, hsmul, map_smul, show Algebra.trace D.Fq D.Fq2 ζ = D.tr ζ from rfl,
      hζtr, smul_zero]

private lemma card_tr_eq_one (D : FieldData) :
    (Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1)).card = D.q := by
  obtain ⟨ζ, hζ0, hζtr⟩ := exists_tr_eq_zero D
  obtain ⟨w₀, hw₀⟩ := exists_tr_eq_one D
  have hbij : (Finset.univ : Finset D.Fq).card =
      (Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1)).card := by
    refine Finset.card_bij (fun t _ => w₀ + algebraMap D.Fq D.Fq2 t * ζ) ?_ ?_ ?_
    · intro t _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hmul : algebraMap D.Fq D.Fq2 t * ζ = t • ζ := (Algebra.smul_def t ζ).symm
      rw [FieldData.tr, map_add, hmul, map_smul,
        show Algebra.trace D.Fq D.Fq2 w₀ = D.tr w₀ from rfl,
        show Algebra.trace D.Fq D.Fq2 ζ = D.tr ζ from rfl, hw₀, hζtr, smul_zero, add_zero]
    · intro t₁ _ t₂ _ heq
      have heq' : algebraMap D.Fq D.Fq2 t₁ * ζ = algebraMap D.Fq D.Fq2 t₂ * ζ :=
        add_left_cancel heq
      exact FaithfulSMul.algebraMap_injective D.Fq D.Fq2 (mul_right_cancel₀ hζ0 heq')
    · intro z hz
      rw [Finset.mem_filter] at hz
      by_cases h0 : z - w₀ = 0
      · refine ⟨0, Finset.mem_univ _, ?_⟩
        rw [map_zero, zero_mul, add_zero]
        linear_combination -h0
      · have htr : D.tr (z - w₀) = 0 := by
          rw [FieldData.tr, map_sub]
          change D.tr z - D.tr w₀ = 0
          rw [hz.2, hw₀, sub_self]
        obtain ⟨t, _, ht⟩ := (tr_eq_zero_iff D hζ0 hζtr (z - w₀)).mp ⟨h0, htr⟩
        refine ⟨t, Finset.mem_univ _, ?_⟩
        linear_combination -ht
  rw [← hbij, Finset.card_univ, card_fq]

private lemma gaussQ2_theta_eq (D : FieldData) (hq : 2 < D.q) {k : D.Lab2} (hk : k ≠ 0) :
    D.gaussQ2 (D.theta k) =
      (if D.restrLab k = 0 then -(D.q : ℂ) else D.gauss (D.restrLab k)) *
        ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1), D.theta k z := by
  set β := D.restrLab k
  set S : D.Fq → ℂ := fun t =>
    ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t), D.theta k z
  have hS1_eq : S 1 = ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1), D.theta k z := by
    apply Finset.sum_congr
    · ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
      intro htr hz0
      subst hz0
      have h0 : D.tr 0 = 0 := by simp [FieldData.tr]
      rw [h0] at htr
      exact zero_ne_one htr
    · intro _ _; rfl
  rw [← hS1_eq]
  have hSt : ∀ t : D.Fq, t ≠ 0 → S t = D.chi β t * S 1 := by
    intro t ht
    simp only [S, Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun z _ => algebraMap D.Fq D.Fq2 t * z) ?_ ?_ ?_ ?_
    · intro z hz
      rw [Finset.mem_filter] at hz ⊢
      have htr : D.tr (algebraMap D.Fq D.Fq2 t * z) = t := by
        have hmul : algebraMap D.Fq D.Fq2 t * z = t • z := (Algebra.smul_def t z).symm
        rw [FieldData.tr, hmul, map_smul, show Algebra.trace D.Fq D.Fq2 z = D.tr z from rfl,
          hz.2.2, smul_eq_mul, mul_one]
      exact ⟨Finset.mem_univ _, mul_ne_zero (by simpa [map_eq_zero] using ht) hz.2.1, htr⟩
    · intro z₁ _ z₂ _ heq
      exact mul_left_cancel₀ (by simpa [map_eq_zero] using ht) heq
    · intro w hw
      rw [Finset.mem_filter] at hw
      refine ⟨algebraMap D.Fq D.Fq2 t⁻¹ * w, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mul_ne_zero (by simpa [map_eq_zero] using inv_ne_zero ht) hw.2.1, ?_⟩, ?_⟩
      · have hmul : algebraMap D.Fq D.Fq2 t⁻¹ * w = t⁻¹ • w := (Algebra.smul_def t⁻¹ w).symm
        rw [FieldData.tr, hmul, map_smul, show Algebra.trace D.Fq D.Fq2 w = D.tr w from rfl,
          hw.2.2, smul_eq_mul, inv_mul_cancel₀ ht]
      · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
    · intro z _
      rw [theta_mul, theta_algebraMap]
  obtain ⟨ζ, hζ0, hζtr⟩ := exists_tr_eq_zero D
  have hS0 : S 0 = if β = 0 then ((D.q : ℂ) - 1) * D.theta k ζ else 0 := by
    have hbij : S 0 = ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0),
        D.theta k (algebraMap D.Fq D.Fq2 t * ζ) := by
      simp only [S]
      symm
      refine Finset.sum_bij (fun t _ => algebraMap D.Fq D.Fq2 t * ζ) ?_ ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_filter] at ht ⊢
        obtain ⟨hz0, htr⟩ := (tr_eq_zero_iff D hζ0 hζtr (algebraMap D.Fq D.Fq2 t * ζ)).mpr
          ⟨t, ht.2, rfl⟩
        exact ⟨Finset.mem_univ _, hz0, htr⟩
      · intro t₁ _ t₂ _ heq
        exact FaithfulSMul.algebraMap_injective D.Fq D.Fq2 (mul_right_cancel₀ hζ0 heq)
      · intro z hz
        rw [Finset.mem_filter] at hz
        obtain ⟨t, ht0, rfl⟩ := (tr_eq_zero_iff D hζ0 hζtr z).mp hz.2
        exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0⟩, rfl⟩
      · intro _ _; rfl
    rw [hbij]
    have hterm : ∀ t : D.Fq, D.theta k (algebraMap D.Fq D.Fq2 t * ζ) = D.theta k ζ * D.chi β t := by
      intro t; rw [theta_mul, theta_algebraMap, mul_comm]
    simp_rw [hterm, ← Finset.mul_sum, sum_chi_fq_units D hq β]
    split_ifs <;> ring
  have hg : D.gaussQ2 (D.theta k) = S 0 + D.gauss β * S 1 := by
    simp only [FieldData.gaussQ2, FieldData.gauss, FieldData.gaussG, one_mul]
    have hpart : ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z * D.psi (D.tr z) =
        ∑ t : D.Fq, ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t),
          D.theta k z * D.psi (D.tr z) := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (fun z : D.Fq2 => z ≠ 0)) D.tr]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr
      · ext z; simp [and_comm]
      · intro _ _; rfl
    rw [hpart]
    have hsplit : ∑ t : D.Fq, ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t),
          D.theta k z * D.psi (D.tr z) =
        (∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = 0),
          D.theta k z * D.psi (D.tr z)) +
        ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0),
          ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t),
            D.theta k z * D.psi (D.tr z) := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
      congr 1
      apply Finset.sum_congr
      · ext t; simp [Finset.mem_erase]
      · intro _ _; rfl
    rw [hsplit]
    have h0' : ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = 0),
        D.theta k z * D.psi (D.tr z) = S 0 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2.2, psi_zero, mul_one]
    have ht' : ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0),
          ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t),
            D.theta k z * D.psi (D.tr z) =
        ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), S t * D.psi t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2.2]),
        ← Finset.sum_mul]
    rw [h0', ht']
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hSt t (Finset.mem_filter.mp ht).2]
    ring
  rw [hg, hS0]
  split_ifs with hβ
  · have htot : ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z = 0 := by
      rw [sum_theta_fq2_units D hq k, if_neg hk]
    have hpart : ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z =
        S 0 + ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), S t := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (fun z : D.Fq2 => z ≠ 0)) D.tr]
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
      congr 1
      · apply Finset.sum_congr
        · ext z; simp [and_comm]
        · intro _ _; rfl
      · apply Finset.sum_congr
        · ext t; simp [Finset.mem_erase]
        · intro t _
          apply Finset.sum_congr
          · ext z; simp [and_comm]
          · intro _ _; rfl
    rw [hpart, hS0, if_pos hβ] at htot
    have hsum_t : ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), S t =
        ((D.q : ℂ) - 1) * S 1 := by
      have ht_eq : ∀ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), S t = S 1 := by
        intro t ht
        rw [hSt t (Finset.mem_filter.mp ht).2, hβ, chi_zero_left D (Finset.mem_filter.mp ht).2,
          one_mul]
      rw [Finset.sum_congr rfl ht_eq, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter (fun t : D.Fq => t ≠ 0)).card = D.q - 1 := by
        have hfilt : Finset.univ.filter (fun t : D.Fq => t ≠ 0) =
            Finset.univ \ ({0} : Finset D.Fq) := by ext t; simp
        rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_fq,
          Finset.card_singleton]
      rw [hcard, Nat.cast_sub (by omega), Nat.cast_one]
    rw [hsum_t] at htot
    have hq1 : ((D.q : ℂ) - 1) ≠ 0 := by
      have hqr : (2 : ℝ) < D.q := by exact_mod_cast hq
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
      linarith
    have hrel : ((D.q : ℂ) - 1) * (D.theta k ζ + S 1) = 0 := by linear_combination htot
    have hzeta : D.theta k ζ = -S 1 := eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp hrel).resolve_left hq1)
    rw [hzeta, hβ, gauss_zero]
    ring
  · rw [zero_add]

/-! ### Layer 3: Quadratic roots in `Fq` / `Fq2`, partition of `Fq`, and `Tᴴ * T = 1` -/

private lemma isqrt_conj (x : ℝ) : star (isqrt x) = isqrt x := by
  simp [isqrt]

private lemma isqrt_mul_self {x : ℝ} (hx : 0 ≤ x) : isqrt x * isqrt x = (x : ℂ)⁻¹ := by
  simp only [isqrt]
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt hx, Complex.ofReal_inv]

private lemma isqrt_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    isqrt (x * y) = isqrt x * isqrt y := by
  simp only [isqrt, Real.sqrt_mul hx, mul_inv, Complex.ofReal_mul]

private lemma isqrt_ne_zero {x : ℝ} (hx : 0 < x) : isqrt x ≠ 0 := by
  simp [isqrt, (Real.sqrt_pos.mpr hx).ne']

private lemma fq_two_eq_zero_iff (D : FieldData) : (2 : D.Fq) = 0 ↔ ringChar D.Fq = 2 := by
  have : CharP D.Fq D.p := charP_fq D
  rw [ringChar_fq D]
  have hcast : (2 : D.Fq) = ((2 : ℕ) : D.Fq) := by norm_cast
  rw [hcast, CharP.cast_eq_zero_iff D.Fq D.p 2,
    Nat.Prime.dvd_iff_eq (by norm_num) D.hp.ne_one, eq_comm]

private lemma fq_four_eq_zero_iff (D : FieldData) : (4 : D.Fq) = 0 ↔ ringChar D.Fq = 2 := by
  have := fq_isDomain D
  have h4 : (4 : D.Fq) = (2 : D.Fq) * (2 : D.Fq) := by norm_num
  rw [h4, mul_eq_zero, or_self, fq_two_eq_zero_iff]

private lemma fq2_two_ne_zero (D : FieldData) (h : ringChar D.Fq ≠ 2) : (2 : D.Fq2) ≠ 0 := by
  have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp h
  intro h0
  apply h2
  apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
  rw [map_ofNat, map_zero]
  exact h0

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
    w ^ 2 - w + t = (w - w₀) * (w - (1 - w₀)) := by
  linear_combination hw₀

private lemma quad_roots_eq_pair {K : Type*} [Field K] (t w₀ w : K) (hw₀ : w₀ ^ 2 - w₀ + t = 0) :
    w ^ 2 - w + t = 0 ↔ w = w₀ ∨ w = 1 - w₀ := by
  rw [quad_factor t w₀ w hw₀, mul_eq_zero, sub_eq_zero, sub_eq_zero]

private lemma quad_symm_root {K : Type*} [CommRing K] (t w : K) (hw : w ^ 2 - w + t = 0) :
    (1 - w) ^ 2 - (1 - w) + t = 0 := by
  linear_combination hw

private lemma quad_root_eq_sub_self_iff (D : FieldData) (x : D.Fq) :
    x = 1 - x ↔ ringChar D.Fq ≠ 2 ∧ x = (2 : D.Fq)⁻¹ := by
  constructor
  · intro hx
    have h2x : (2 : D.Fq) * x = 1 := by linear_combination hx
    have h2 : (2 : D.Fq) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h2x; exact zero_ne_one h2x
    refine ⟨mt (fq_two_eq_zero_iff D).mpr h2, ?_⟩
    apply mul_left_cancel₀ h2
    rw [h2x, mul_inv_cancel₀ h2]
  · rintro ⟨hc, rfl⟩
    have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
    apply mul_left_cancel₀ h2
    rw [mul_sub, mul_one, mul_inv_cancel₀ h2]
    ring

private lemma quad_exists_root_fq2 (D : FieldData) (t : D.Fq)
    (hno : ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0) :
    ∃ z : D.Fq2, z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0 := by
  have := fq_isDomain D
  let P : Polynomial D.Fq := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C t
  have hdeg : P.natDegree = 2 := by
    have hP : P = Polynomial.X ^ 2 + (-Polynomial.X + Polynomial.C t) := by
      simp only [P]; ring
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
    refine ⟨?_, ?_⟩
    · intro hu
      have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro a b hab
      by_cases ha0 : a = 0
      · subst ha0; simp at hab; exact absurd hab hP_ne
      by_cases hb0 : b = 0
      · subst hb0; simp at hab; exact absurd hab hP_ne
      have hsum : 2 = a.natDegree + b.natDegree := by
        rw [← hdeg, hab, Polynomial.natDegree_mul ha0 hb0]
      rcases Nat.lt_trichotomy a.natDegree 1 with ha | ha | ha
      · left
        have ha' : a.natDegree = 0 := by omega
        exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree ha0, ha', Nat.cast_zero])
      · exfalso
        have ha1 : a.natDegree = 1 := ha
        have hlc : a.coeff 1 ≠ 0 := by
          rw [← ha1]; exact Polynomial.leadingCoeff_ne_zero.mpr ha0
        have ha_eq : a = Polynomial.C (a.coeff 1) * Polynomial.X + Polynomial.C (a.coeff 0) :=
          Polynomial.eq_X_add_C_of_natDegree_le_one ha1.le
        let r : D.Fq := -(a.coeff 0) / a.coeff 1
        have har : a.eval r = 0 := by
          rw [ha_eq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
            Polynomial.eval_C]
          dsimp only [r]
          rw [mul_div_cancel₀ _ hlc, neg_add_cancel]
        have hPr : P.eval r = 0 := by rw [hab, Polynomial.eval_mul, har, zero_mul]
        apply hno
        refine ⟨r, ?_⟩
        simpa [P] using hPr
      · right
        have hb' : b.natDegree = 0 := by omega
        exact Polynomial.isUnit_iff_degree_eq_zero.mpr (by
          rw [Polynomial.degree_eq_natDegree hb0, hb', Nat.cast_zero])
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
    have h := (AdjoinRoot.powerBasis' hP_monic).finrank
    rwa [AdjoinRoot.powerBasis'_dim, hdeg] at h
  let e1 := FiniteField.algEquivExtension D.Fq D.p 2 (AdjoinRoot P) hfin1
  let e2 := FiniteField.algEquivExtension D.Fq D.p 2 D.Fq2 (finrank_fq2 D)
  let e : AdjoinRoot P ≃ₐ[D.Fq] D.Fq2 := e1.trans e2.symm
  refine ⟨e (AdjoinRoot.root P), ?_⟩
  have hroot : Polynomial.aeval (e (AdjoinRoot.root P)) P = 0 :=
    AdjoinRoot.aeval_algHom_eq_zero P e.toAlgHom
  simp only [P, map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at hroot
  exact hroot

private def B_T2 (D : FieldData) (t : D.Fq) : Prop := ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹
private def B_T3 (D : FieldData) (t : D.Fq) : Prop :=
  t ≠ 0 ∧ ¬ B_T2 D t ∧ ∃ x : D.Fq, x ^ 2 - x + t = 0
private def B_T4 (D : FieldData) (t : D.Fq) : Prop :=
  t ≠ 0 ∧ ¬ B_T2 D t ∧ ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0

private def S_nb (D : FieldData) : Finset D.Fq :=
  Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1 ∧ ¬ (ringChar D.Fq ≠ 2 ∧ x = (2 : D.Fq)⁻¹))

private def X_all (D : FieldData) : Finset D.Fq :=
  Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1)

private def Z_nb (D : FieldData) : Finset D.Fq2 :=
  Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ z ^ D.q ≠ z)

private def Z_all (D : FieldData) : Finset D.Fq2 :=
  Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1)

private lemma mem_S_nb_iff (D : FieldData) (x : D.Fq) :
    x ∈ S_nb D ↔ B_T3 D (x * (1 - x)) := by
  simp only [S_nb, Finset.mem_filter, Finset.mem_univ, true_and, B_T3, B_T2]
  constructor
  · rintro ⟨hx0, hx1, hnx⟩
    refine ⟨mul_ne_zero hx0 (sub_ne_zero.mpr hx1.symm), ?_, x, by ring⟩
    rintro ⟨hc, ht⟩
    apply hnx ⟨hc, ?_⟩
    have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
    have hsq : (x - (2 : D.Fq)⁻¹) ^ 2 = 0 := by
      have h4 : (4 : D.Fq) = 2 * 2 := by norm_num
      have hinv4 : (4 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by
        rw [h4, field_mul_inv]
      calc (x - (2 : D.Fq)⁻¹) ^ 2
          = x ^ 2 - 2 * (2 : D.Fq)⁻¹ * x + (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by ring
        _ = x ^ 2 - x + (4 : D.Fq)⁻¹ := by rw [mul_inv_cancel₀ h2, one_mul, hinv4]
        _ = (4 : D.Fq)⁻¹ - x * (1 - x) := by rw [← ht]; ring
        _ = 0 := by rw [ht, sub_self]
    exact sub_eq_zero.mp (field_pow_eq_zero hsq)
  · rintro ⟨ht0, hnt2, x₀, hx₀⟩
    have hfac : x * (1 - x) = x₀ * (1 - x₀) := by linear_combination hx₀
    have hx_ne0 : x ≠ 0 := fun h => ht0 (by rw [h, zero_mul])
    have hx_ne1 : x ≠ 1 := fun h => ht0 (by rw [h, sub_self, mul_zero])
    refine ⟨hx_ne0, hx_ne1, ?_⟩
    rintro ⟨hc, rfl⟩
    apply hnt2 ⟨hc, ?_⟩
    have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
    have h4 : (4 : D.Fq) = 2 * 2 := by norm_num
    rw [h4, field_mul_inv]
    have h12 : 1 - (2 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ := by
      apply mul_left_cancel₀ h2
      rw [mul_sub, mul_one, mul_inv_cancel₀ h2]
      ring
    rw [h12]

private lemma B_T3_root_iff (D : FieldData) {t : D.Fq} (ht : B_T3 D t) (x : D.Fq) :
    x ^ 2 - x + t = 0 ↔ x ∈ S_nb D ∧ x * (1 - x) = t := by
  constructor
  · intro hx
    have heq : x * (1 - x) = t := by linear_combination -hx
    exact ⟨(mem_S_nb_iff D x).mpr (heq.symm ▸ ht), heq⟩
  · rintro ⟨_, heq⟩
    linear_combination -heq

private lemma sum_T3_roots (D : FieldData) (g : D.Fq → D.Fq → ℂ) :
    ∑ t ∈ Finset.univ.filter (B_T3 D),
      ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0), g t x =
    ∑ x ∈ S_nb D, g (x * (1 - x)) x := by
  have hmaps : ∀ x ∈ S_nb D, x * (1 - x) ∈ Finset.univ.filter (B_T3 D) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_S_nb_iff D x).mp hx⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => g (x * (1 - x)) x)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_filter] at ht
  have hfilt : (S_nb D).filter (fun x => x * (1 - x) = t) =
      Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (B_T3_root_iff D ht.2 x).symm
  rw [hfilt]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_filter] at hx
  have heq : x * (1 - x) = t := by linear_combination -hx.2
  rw [heq]

private lemma Z_nb_nrm_mem_T4 (D : FieldData) {z : D.Fq2} (hz : z ∈ Z_nb D) :
    B_T4 D (D.nrm z) := by
  simp only [Z_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  have hzq : z ^ D.q = 1 - z := by
    have h := algebraMap_tr D z
    rw [hz.1, map_one] at h
    linear_combination -h
  have hquad : z ^ 2 - z + algebraMap D.Fq D.Fq2 (D.nrm z) = 0 := by
    rw [algebraMap_nrm_mul, hzq]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hquad
    have hz01 : z * (1 - z) = 0 := by linear_combination -hquad
    rcases field_mul_eq_zero.mp hz01 with h | h
    · exact hz.2 (by rw [h, zero_pow (q_pos D).ne'])
    · have hz1 : z = 1 := by linear_combination -h
      exact hz.2 (by rw [hz1, one_pow])
  · rintro ⟨hc, ht⟩
    rw [ht, algebraMap_four_inv D hc] at hquad
    have h2 : (2 : D.Fq2) ≠ 0 := fq2_two_ne_zero D hc
    have h4 : (4 : D.Fq2)⁻¹ = (2 : D.Fq2)⁻¹ * (2 : D.Fq2)⁻¹ := by
      have h4eq : (4 : D.Fq2) = 2 * 2 := by norm_num
      rw [h4eq, field_mul_inv]
    have hsq : (z - (2 : D.Fq2)⁻¹) ^ 2 = 0 := by
      calc (z - (2 : D.Fq2)⁻¹) ^ 2
          = z ^ 2 - 2 * (2 : D.Fq2)⁻¹ * z + (2 : D.Fq2)⁻¹ * (2 : D.Fq2)⁻¹ := by ring
        _ = z ^ 2 - z + (4 : D.Fq2)⁻¹ := by rw [mul_inv_cancel₀ h2, one_mul, h4]
        _ = 0 := hquad
    have hz2 : z = (2 : D.Fq2)⁻¹ := sub_eq_zero.mp (field_pow_eq_zero hsq)
    rw [← algebraMap_two_inv D hc] at hz2
    exact hz.2 ((fq2_pow_q_eq_self_iff D z).mpr ⟨(2 : D.Fq)⁻¹, hz2.symm⟩)
  · rintro ⟨x, hx⟩
    have hax : (algebraMap D.Fq D.Fq2 x) ^ 2 - algebraMap D.Fq D.Fq2 x +
        algebraMap D.Fq D.Fq2 (D.nrm z) = 0 := by
      simpa only [map_add, map_sub, map_pow, map_zero] using congrArg (algebraMap D.Fq D.Fq2) hx
    rw [quad_roots_eq_pair _ z _ hquad] at hax
    rcases hax with h | h
    · exact hz.2 ((fq2_pow_q_eq_self_iff D z).mpr ⟨x, h⟩)
    · rw [← hzq] at h
      have hz' : z = z ^ (D.q ^ 2) := (fq2_pow_q_sq D z).symm
      rw [sq, pow_mul, ← h, ← map_pow, fq_pow_q, h] at hz'
      exact hz.2 hz'.symm

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
      rw [algebraMap_tr, hzq, map_one]
      ring
    have hnrm : D.nrm z = t := by
      apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
      rw [algebraMap_nrm_mul, hzq]
      linear_combination -hz
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, htr, hzq_ne⟩, hnrm⟩
  · rintro ⟨hz, rfl⟩
    simp only [Z_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hzq : z ^ D.q = 1 - z := by
      have h := algebraMap_tr D z
      rw [hz.1, map_one] at h
      linear_combination -h
    rw [algebraMap_nrm_mul, hzq]
    ring

private lemma sum_T4_roots (D : FieldData) (g : D.Fq → D.Fq2 → ℂ) :
    ∑ t ∈ Finset.univ.filter (B_T4 D),
      ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0), g t z =
    ∑ z ∈ Z_nb D, g (D.nrm z) z := by
  have hmaps : ∀ z ∈ Z_nb D, D.nrm z ∈ Finset.univ.filter (B_T4 D) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Z_nb_nrm_mem_T4 D hz⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun z => g (D.nrm z) z)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_filter] at ht
  have hfilt : (Z_nb D).filter (fun z => D.nrm z = t) =
      Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (B_T4_root_iff D ht.2 z).symm
  rw [hfilt]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.mem_filter] at hz
  rw [((B_T4_root_iff D ht.2 z).mp hz.2).2]

private lemma X_all_eq_split (D : FieldData) :
    (if ringChar D.Fq ≠ 2 then
      insert (2 : D.Fq)⁻¹ (S_nb D) = X_all D ∧ (2 : D.Fq)⁻¹ ∉ S_nb D
    else S_nb D = X_all D) := by
  split_ifs with hc
  · refine ⟨?_, ?_⟩
    · ext x
      simp only [Finset.mem_insert, S_nb, X_all, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | ⟨hx0, hx1, _⟩)
        · have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
          refine ⟨inv_ne_zero h2, ?_⟩
          intro h1
          have : (2 : D.Fq) = 1 := by
            calc (2 : D.Fq) = 2 * 1 := (mul_one 2).symm
              _ = 2 * (2 : D.Fq)⁻¹ := by rw [h1]
              _ = 1 := mul_inv_cancel₀ h2
          have : (1 : D.Fq) = 0 := by linear_combination this
          exact one_ne_zero this
        · exact ⟨hx0, hx1⟩
      · rintro ⟨hx0, hx1⟩
        by_cases hx2 : x = (2 : D.Fq)⁻¹
        · left; exact hx2
        · right; exact ⟨hx0, hx1, fun h => hx2 h.2⟩
    · simp [S_nb, hc]
  · ext x
    simp [S_nb, X_all, hc]

private lemma Z_all_eq_split (D : FieldData) :
    (if ringChar D.Fq ≠ 2 then
      insert (2 : D.Fq2)⁻¹ (Z_nb D) = Z_all D ∧ (2 : D.Fq2)⁻¹ ∉ Z_nb D
    else Z_nb D = Z_all D) := by
  split_ifs with hc
  · have h2 : (2 : D.Fq2) ≠ 0 := fq2_two_ne_zero D hc
    have htr2 : D.tr (2 : D.Fq2)⁻¹ = 1 := by
      apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
      rw [algebraMap_tr, ← algebraMap_two_inv D hc, ← map_pow, fq_pow_q, algebraMap_two_inv D hc,
        map_one]
      apply mul_left_cancel₀ h2
      rw [mul_add, mul_inv_cancel₀ h2, mul_one]
      norm_num
    have hpow2 : ((2 : D.Fq2)⁻¹) ^ D.q = (2 : D.Fq2)⁻¹ :=
      (fq2_pow_q_eq_self_iff D _).mpr ⟨(2 : D.Fq)⁻¹, algebraMap_two_inv D hc⟩
    refine ⟨?_, ?_⟩
    · ext z
      simp only [Finset.mem_insert, Z_nb, Z_all, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | ⟨htr, _⟩)
        · exact htr2
        · exact htr
      · intro htr
        by_cases hzq : z ^ D.q = z
        · left
          have h := algebraMap_tr D z
          rw [htr, map_one, hzq] at h
          have h2z : (2 : D.Fq2) * z = 1 := by linear_combination -h
          apply mul_left_cancel₀ h2
          rw [h2z, mul_inv_cancel₀ h2]
        · right; exact ⟨htr, hzq⟩
    · simp [Z_nb, hpow2]
  · ext z
    simp only [Z_nb, Z_all, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.1
    · intro htr
      refine ⟨htr, ?_⟩
      intro hzq
      have h := algebraMap_tr D z
      rw [htr, map_one, hzq] at h
      have h2_0 : (2 : D.Fq2) = 0 := by
        rw [← show algebraMap D.Fq D.Fq2 2 = 2 from map_ofNat _ 2,
          (fq_two_eq_zero_iff D).mpr (not_not.mp hc), map_zero]
      have h01 : (0 : D.Fq2) = 1 := by
        calc (0 : D.Fq2) = 2 * z := by rw [h2_0, zero_mul]
          _ = z + z := by ring
          _ = 1 := h.symm
      exact zero_ne_one h01

private lemma card_split_plus_ns_eq_two (D : FieldData) (t : D.Fq) :
    (Finset.univ.filter (fun x : D.Fq => x * (1 - x) = t)).card +
    (Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = t)).card = 2 := by
  by_cases ht0 : t = 0
  · subst ht0
    have hs : Finset.univ.filter (fun x : D.Fq => x * (1 - x) = 0) = {0, 1} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, mul_eq_zero, sub_eq_zero]
      constructor
      · rintro (rfl | h) <;> [left; right] <;> [rfl; exact h.symm]
      · rintro (rfl | rfl) <;> [left; right] <;> rfl
    have hn : Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = 0) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨htr, hnrm⟩
      have h0 : z ^ (D.q + 1) = 0 := by rw [← algebraMap_nrm, hnrm, map_zero]
      have hz0 : z = 0 := field_pow_eq_zero h0
      rw [hz0, show D.tr 0 = 0 from by simp [FieldData.tr]] at htr
      exact zero_ne_one htr
    rw [hs, hn, Finset.card_pair (zero_ne_one : (0 : D.Fq) ≠ 1), Finset.card_empty]
  · by_cases ht2 : B_T2 D t
    · rcases ht2 with ⟨hc, rfl⟩
      have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
      have h4 : (4 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by
        have : (4 : D.Fq) = 2 * 2 := by norm_num
        rw [this, field_mul_inv]
      have hs : Finset.univ.filter (fun x : D.Fq => x * (1 - x) = (4 : D.Fq)⁻¹) = {(2 : D.Fq)⁻¹} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hx
          have hsq : (x - (2 : D.Fq)⁻¹) ^ 2 = 0 := by
            calc (x - (2 : D.Fq)⁻¹) ^ 2
                = x ^ 2 - 2 * (2 : D.Fq)⁻¹ * x + (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by ring
              _ = x ^ 2 - x + (4 : D.Fq)⁻¹ := by rw [mul_inv_cancel₀ h2, one_mul, h4]
              _ = (4 : D.Fq)⁻¹ - x * (1 - x) := by ring
              _ = 0 := by rw [hx, sub_self]
          exact sub_eq_zero.mp (field_pow_eq_zero hsq)
        · rintro rfl
          have h12 : 1 - (2 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ := by
            apply mul_left_cancel₀ h2; rw [mul_sub, mul_one, mul_inv_cancel₀ h2]; ring
          rw [h12, h4]
      have h2' : (2 : D.Fq2) ≠ 0 := fq2_two_ne_zero D hc
      have h4' : (4 : D.Fq2)⁻¹ = (2 : D.Fq2)⁻¹ * (2 : D.Fq2)⁻¹ := by
        have : (4 : D.Fq2) = 2 * 2 := by norm_num
        rw [this, field_mul_inv]
      have hn : Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = (4 : D.Fq)⁻¹) =
          {(2 : D.Fq2)⁻¹} := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨htr, hnrm⟩
          have hzq : z ^ D.q = 1 - z := by
            have h := algebraMap_tr D z; rw [htr, map_one] at h; linear_combination -h
          have hquad : z * (1 - z) = (4 : D.Fq2)⁻¹ := by
            rw [← hzq, ← algebraMap_nrm_mul, hnrm, algebraMap_four_inv D hc]
          have hsq : (z - (2 : D.Fq2)⁻¹) ^ 2 = 0 := by
            calc (z - (2 : D.Fq2)⁻¹) ^ 2
                = z ^ 2 - 2 * (2 : D.Fq2)⁻¹ * z + (2 : D.Fq2)⁻¹ * (2 : D.Fq2)⁻¹ := by ring
              _ = z ^ 2 - z + (4 : D.Fq2)⁻¹ := by rw [mul_inv_cancel₀ h2', one_mul, h4']
              _ = (4 : D.Fq2)⁻¹ - z * (1 - z) := by ring
              _ = 0 := by rw [hquad, sub_self]
          exact sub_eq_zero.mp (field_pow_eq_zero hsq)
        · rintro rfl
          have htr2 : D.tr (2 : D.Fq2)⁻¹ = 1 := by
            apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
            rw [algebraMap_tr, ← algebraMap_two_inv D hc, ← map_pow, fq_pow_q,
              algebraMap_two_inv D hc, map_one]
            apply mul_left_cancel₀ h2'
            rw [mul_add, mul_inv_cancel₀ h2', mul_one]
            norm_num
          have hpow2 : ((2 : D.Fq2)⁻¹) ^ D.q = (2 : D.Fq2)⁻¹ :=
            (fq2_pow_q_eq_self_iff D _).mpr ⟨(2 : D.Fq)⁻¹, algebraMap_two_inv D hc⟩
          refine ⟨htr2, ?_⟩
          apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
          rw [algebraMap_nrm_mul, hpow2, algebraMap_four_inv D hc, h4']
      rw [hs, hn, Finset.card_singleton, Finset.card_singleton]
    · by_cases hex : ∃ x : D.Fq, x ^ 2 - x + t = 0
      · have ht3 : B_T3 D t := ⟨ht0, ht2, hex⟩
        obtain ⟨x₀, hx₀⟩ := hex
        have hne : x₀ ≠ 1 - x₀ := by
          intro h
          apply ht2
          exact ⟨((quad_root_eq_sub_self_iff D x₀).mp h).1, by
            have hx2 := ((quad_root_eq_sub_self_iff D x₀).mp h).2
            rw [hx2] at hx₀
            have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp ((quad_root_eq_sub_self_iff D x₀).mp h).1
            have h4 : (4 : D.Fq) = 2 * 2 := by norm_num
            have h4inv : (4 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by rw [h4, field_mul_inv]
            calc t = (2 : D.Fq)⁻¹ - (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by linear_combination hx₀
              _ = (2 * (2 : D.Fq)⁻¹) * (2 : D.Fq)⁻¹ - (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by
                    rw [mul_inv_cancel₀ h2, one_mul]
              _ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by ring
              _ = (4 : D.Fq)⁻¹ := h4inv.symm⟩
        have hs : Finset.univ.filter (fun x : D.Fq => x * (1 - x) = t) = {x₀, 1 - x₀} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          rw [show x * (1 - x) = t ↔ x ^ 2 - x + t = 0 from ⟨fun h => by linear_combination -h,
            fun h => by linear_combination -h⟩, quad_roots_eq_pair t x₀ x hx₀]
        have hn : Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = t) = ∅ := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨htr, hnrm⟩
          have hzq : z ^ D.q = 1 - z := by
            have h := algebraMap_tr D z; rw [htr, map_one] at h; linear_combination -h
          have hquad : z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0 := by
            rw [← hnrm, algebraMap_nrm_mul, hzq]; ring
          have hax₀ : (algebraMap D.Fq D.Fq2 x₀) ^ 2 - algebraMap D.Fq D.Fq2 x₀ +
              algebraMap D.Fq D.Fq2 t = 0 := by
            simpa only [map_add, map_sub, map_pow, map_zero] using
              congrArg (algebraMap D.Fq D.Fq2) hx₀
          rw [quad_roots_eq_pair _ (algebraMap D.Fq D.Fq2 x₀) z hax₀] at hquad
          have hz_self : z ^ D.q = z := by
            rcases hquad with h | h
            · exact (fq2_pow_q_eq_self_iff D z).mpr ⟨x₀, h.symm⟩
            · exact (fq2_pow_q_eq_self_iff D z).mpr ⟨1 - x₀, by rw [map_sub, map_one, h]⟩
          have h2z : (2 : D.Fq2) * z = 1 := by
            have h := algebraMap_tr D z
            rw [htr, map_one, hz_self] at h
            linear_combination -h
          have hc : ringChar D.Fq ≠ 2 := by
            intro hc2
            have h20 : (2 : D.Fq2) = 0 := by
              rw [← show algebraMap D.Fq D.Fq2 2 = 2 from map_ofNat _ 2,
                (fq_two_eq_zero_iff D).mpr hc2, map_zero]
            rw [h20, zero_mul] at h2z
            exact zero_ne_one h2z
          have h2 : (2 : D.Fq2) ≠ 0 := fq2_two_ne_zero D hc
          have hz2 : z = (2 : D.Fq2)⁻¹ := by
            apply mul_left_cancel₀ h2; rw [h2z, mul_inv_cancel₀ h2]
          apply ht2 ⟨hc, ?_⟩
          apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
          rw [← hnrm, algebraMap_nrm_mul, hz_self, hz2, algebraMap_four_inv D hc]
          have h4 : (4 : D.Fq2) = 2 * 2 := by norm_num
          rw [h4, field_mul_inv]
        rw [hs, hn, Finset.card_pair hne, Finset.card_empty]
      · have ht4 : B_T4 D t := ⟨ht0, ht2, hex⟩
        have hs : Finset.univ.filter (fun x : D.Fq => x * (1 - x) = t) = ∅ := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro hx; exact hex ⟨x, by linear_combination -hx⟩
        obtain ⟨z₀, hz₀⟩ := quad_exists_root_fq2 D t hex
        have hz₀_mem := (B_T4_root_iff D ht4 z₀).mp hz₀
        have hz₀_nb := hz₀_mem.1
        simp only [Z_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hz₀_nb
        have hz₀q : z₀ ^ D.q = 1 - z₀ := by
          have h := algebraMap_tr D z₀; rw [hz₀_nb.1, map_one] at h; linear_combination -h
        have hne : z₀ ≠ 1 - z₀ := by rw [← hz₀q]; exact hz₀_nb.2.symm
        have hn : Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = t) = {z₀, 1 - z₀} := by
          ext z
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          constructor
          · rintro ⟨htr, hnrm⟩
            have hzq : z ^ D.q = 1 - z := by
              have h := algebraMap_tr D z; rw [htr, map_one] at h; linear_combination -h
            have hquad : z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0 := by
              rw [← hnrm, algebraMap_nrm_mul, hzq]; ring
            exact (quad_roots_eq_pair _ z₀ z hz₀).mp hquad
          · intro h
            have hquad : z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0 :=
              (quad_roots_eq_pair _ z₀ z hz₀).mpr h
            have hm := (B_T4_root_iff D ht4 z).mp hquad
            exact ⟨(Finset.mem_filter.mp hm.1).2.1, hm.2⟩
        rw [hs, hn, Finset.card_empty, Finset.card_pair hne]

private lemma sum_tr1_chi_nrm_eq_neg_jacobi (D : FieldData) (hq : 2 < D.q) {ξ : D.Lab} (hξ : ξ ≠ 0) :
    ∑ z ∈ Z_all D, D.chi ξ (D.nrm z) = -D.jacobi ξ ξ := by
  have hjac : D.jacobi ξ ξ = ∑ x : D.Fq, D.chi ξ (x * (1 - x)) := by
    simp only [FieldData.jacobi]
    have hsplit : ∑ x : D.Fq, D.chi ξ (x * (1 - x)) =
        ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1), D.chi ξ (x * (1 - x)) := by
      have hsub : Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1) ⊆ Finset.univ :=
        Finset.subset_univ _
      rw [← Finset.sum_subset hsub]
      intro x _ hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hx
      by_cases hx0 : x = 0
      · subst hx0; simp [chi_zero_right]
      · rw [hx hx0, sub_self, mul_zero, chi_zero_right]
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro x _
    rw [chi_mul]
  rw [hjac]
  have h1 : ∑ x : D.Fq, D.chi ξ (x * (1 - x)) =
      ∑ t : D.Fq, ((Finset.univ.filter (fun x : D.Fq => x * (1 - x) = t)).card : ℂ) * D.chi ξ t := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : D.Fq => x * (1 - x)) (fun x => D.chi ξ (x * (1 - x)))]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
      Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ z ∈ Z_all D, D.chi ξ (D.nrm z) =
      ∑ t : D.Fq, ((Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = t)).card : ℂ) *
        D.chi ξ t := by
    have hmaps : ∀ z ∈ Z_all D, D.nrm z ∈ (Finset.univ : Finset D.Fq) := fun _ _ => Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun z => D.chi ξ (D.nrm z))]
    apply Finset.sum_congr rfl
    intro t _
    have hfilt : (Z_all D).filter (fun z => D.nrm z = t) =
        Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = t) := by
      ext z; simp [Z_all]
    rw [hfilt, Finset.sum_congr rfl (fun z hz => by rw [(Finset.mem_filter.mp hz).2.2]),
      Finset.sum_const, nsmul_eq_mul]
  rw [eq_neg_iff_add_eq_zero, h2, h1, add_comm, ← Finset.sum_add_distrib]
  have hsum_t : ∑ t : D.Fq,
      (((Finset.univ.filter (fun x : D.Fq => x * (1 - x) = t)).card : ℂ) * D.chi ξ t +
       ((Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1 ∧ D.nrm z = t)).card : ℂ) * D.chi ξ t) =
      2 * ∑ t : D.Fq, D.chi ξ t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    have hc := congrArg (fun n : ℕ => (n : ℂ)) (card_split_plus_ns_eq_two D t)
    push_cast at hc
    linear_combination (D.chi ξ t) * hc
  rw [hsum_t]
  have hzero : ∑ t : D.Fq, D.chi ξ t = 0 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq)), chi_zero_right, zero_add]
    have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun t : D.Fq => t ≠ 0) := by
      ext t; simp [Finset.mem_erase]
    rw [hfilt, sum_chi_fq_units D hq ξ, if_neg hξ]
  rw [hzero, mul_zero]

private def InBranchDom (D : FieldData) (br : Bool × D.Fq2) : Prop :=
  if br.1 then br.2 ≠ 0 ∧ br.2 ^ (D.q + 1) = 1
  else ∃ r : D.Fq, r ≠ 0 ∧ br.2 = algebraMap D.Fq D.Fq2 r

private lemma Bgate_mem_InBranchDom (D : FieldData) (γ : D.Lab) (br : Bool × D.Fq2) (t : D.Fq)
    (hne : Bgate D γ br t ≠ 0) : InBranchDom D br := by
  simp only [Bgate, Matrix.of_apply] at hne
  by_cases ht0 : t = 0
  · subst ht0
    simp only [if_pos rfl] at hne
    have hbr2 : br.2 = 1 := by by_contra h; simp [h] at hne
    rw [InBranchDom]
    cases h1 : br.1
    · exact ⟨1, one_ne_zero, by rw [hbr2, map_one]⟩
    · exact ⟨by rw [hbr2]; exact one_ne_zero, by rw [hbr2, one_pow]⟩
  · by_cases ht2 : ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹
    · simp only [if_neg ht0, if_pos ht2] at hne
      have hbr2 : br.2 = 1 := by by_contra h; simp [h] at hne
      rw [InBranchDom]
      cases h1 : br.1
      · exact ⟨1, one_ne_zero, by rw [hbr2, map_one]⟩
      · exact ⟨by rw [hbr2]; exact one_ne_zero, by rw [hbr2, one_pow]⟩
    · by_cases hex : ∃ x : D.Fq, x ^ 2 - x + t = 0
      · simp only [if_neg ht0, if_neg ht2, if_pos hex] at hne
        have hbr1 : br.1 = false := by
          cases h1 : br.1
          · rfl
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
        have hx1 : 1 - x ≠ 0 := fun h => ht0 (by
          have : x = 1 := by linear_combination -h
          simpa [this] using hx.2)
        rw [InBranchDom, hbr1]
        exact ⟨x / (1 - x), div_ne_zero hx0 hx1, hbr2⟩
      · simp only [if_neg ht0, if_neg ht2, if_neg hex] at hne
        have hbr1 : br.1 = true := by
          cases h1 : br.1
          · exfalso; apply hne; simp [h1]
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
          intro h0
          rw [h0, zero_pow two_ne_zero, sub_zero, zero_add] at hz
          have ht' : t = 0 := FaithfulSMul.algebraMap_injective D.Fq D.Fq2 (by rw [hz.2, map_zero])
          exact ht0 ht'
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
  -- Helper: norm squared of chi is 1 and theta is 1
  have hchi_sq : ∀ (α : D.Lab) {x : D.Fq}, x ≠ 0 → star (D.chi α x) * D.chi α x = 1 := by
    intro α x hx; rw [← chi_neg_lab, ← chi_add_lab, neg_add_cancel, chi_zero_left D hx]
  have htheta_sq : ∀ (k : D.Lab2) {z : D.Fq2}, z ≠ 0 → star (D.theta k z) * D.theta k z = 1 := by
    intro k z hz; rw [← theta_neg_lab, ← theta_add_lab, neg_add_cancel, theta_zero_left D hz]
  have hisqrt2 : star (isqrt 2) * isqrt 2 = (2 : ℂ)⁻¹ := by
    rw [isqrt_conj, isqrt_mul_self (by norm_num)]; norm_num
  -- Split by whether t = 0, B_T2, B_T3, B_T4
  -- Wait: if br has nonzero entry in both t₁ and t₂, let's check case by case!
  have hB3_char : ∀ t (ht : B_T3 D t), ∃ x₀ : D.Fq,
      x₀ ^ 2 - x₀ + t = 0 ∧ x₀ ≠ 0 ∧ x₀ ≠ 1 ∧ x₀ ≠ 1 - x₀ ∧
      x₀ / (1 - x₀) ≠ 1 ∧ x₀ / (1 - x₀) ≠ (1 - x₀) / x₀ ∧
      Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) = {x₀, 1 - x₀} := by
    intro t ht
    obtain ⟨x₀, hx₀⟩ := ht.2.2
    have hx₀_0 : x₀ ≠ 0 := fun h => ht.1 (by simpa [h] using hx₀)
    have hx₀_1 : x₀ ≠ 1 := fun h => ht.1 (by rw [h] at hx₀; simpa using hx₀)
    have h1x₀ : 1 - x₀ ≠ 0 := sub_ne_zero.mpr hx₀_1.symm
    have hne : x₀ ≠ 1 - x₀ := by
      intro h; apply ht.2.1
      obtain ⟨hc, hx2⟩ := (quad_root_eq_sub_self_iff D x₀).mp h
      refine ⟨hc, ?_⟩
      rw [hx2] at hx₀
      have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
      have h4 : (4 : D.Fq) = 2 * 2 := by norm_num
      have h4inv : (4 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by rw [h4, field_mul_inv]
      calc t = (2 : D.Fq)⁻¹ - (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by linear_combination hx₀
        _ = (2 * (2 : D.Fq)⁻¹) * (2 : D.Fq)⁻¹ - (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by
              rw [mul_inv_cancel₀ h2, one_mul]
        _ = (2 : D.Fq)⁻¹ * (2 : D.Fq)⁻¹ := by ring
        _ = (4 : D.Fq)⁻¹ := h4inv.symm
    have hdiv1 : x₀ / (1 - x₀) ≠ 1 := by
      intro h; rw [field_div_eq_one_iff_eq h1x₀] at h; exact hne h
    have hdiv2 : x₀ / (1 - x₀) ≠ (1 - x₀) / x₀ := by
      intro h
      rw [field_div_eq_div_iff h1x₀ hx₀_0] at h
      have h2x : (2 : D.Fq) * x₀ = 1 := by linear_combination h
      exact hne (by linear_combination h2x)
    have hfilt : Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) = {x₀, 1 - x₀} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact quad_roots_eq_pair t x₀ x hx₀
    exact ⟨x₀, hx₀, hx₀_0, hx₀_1, hne, hdiv1, hdiv2, hfilt⟩
  have hB4_char : ∀ t (ht : B_T4 D t), ∃ z₀ : D.Fq2,
      z₀ ^ 2 - z₀ + algebraMap D.Fq D.Fq2 t = 0 ∧ z₀ ≠ 0 ∧ 1 - z₀ ≠ 0 ∧
      z₀ ^ D.q = 1 - z₀ ∧ z₀ ≠ 1 - z₀ ∧
      z₀ / (1 - z₀) ≠ 1 ∧ z₀ / (1 - z₀) ≠ (1 - z₀) / z₀ ∧
      Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) = {z₀, 1 - z₀} := by
    intro t ht
    obtain ⟨z₀, hz₀⟩ := quad_exists_root_fq2 D t ht.2.2
    have hmem := (B_T4_root_iff D ht z₀).mp hz₀
    have hnb := hmem.1
    simp only [Z_nb, Finset.mem_filter, Finset.mem_univ, true_and] at hnb
    have hz₀q : z₀ ^ D.q = 1 - z₀ := by
      have h := algebraMap_tr D z₀; rw [hnb.1, map_one] at h; linear_combination -h
    have hz₀_0 : z₀ ≠ 0 := fun h => hnb.2 (by rw [h, zero_pow (q_pos D).ne'])
    have h1z₀ : 1 - z₀ ≠ 0 := by rw [← hz₀q]; exact fq2_pow_ne_zero D hz₀_0 D.q
    have hne : z₀ ≠ 1 - z₀ := by rw [← hz₀q]; exact hnb.2.symm
    have hdiv1 : z₀ / (1 - z₀) ≠ 1 := by
      intro h; rw [field_div_eq_one_iff_eq h1z₀] at h; exact hne h
    have hdiv2 : z₀ / (1 - z₀) ≠ (1 - z₀) / z₀ := by
      intro h
      rw [field_div_eq_div_iff h1z₀ hz₀_0] at h
      have h2z : (2 : D.Fq2) * z₀ = 1 := by linear_combination h
      have hz_eq : z₀ = 1 - z₀ := by linear_combination h2z
      exact hne hz_eq
    have hfilt : Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) =
        {z₀, 1 - z₀} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact quad_roots_eq_pair _ z₀ z hz₀
    exact ⟨z₀, hz₀, hz₀_0, h1z₀, hz₀q, hne, hdiv1, hdiv2, hfilt⟩
  -- For any t, Bgate at t simplified
  have hB3_val : ∀ t (ht : B_T3 D t) x₀ (hx₀ : x₀ ^ 2 - x₀ + t = 0)
      (hne : x₀ ≠ 1 - x₀) (hfilt : Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0) = {x₀, 1 - x₀})
      (br : Bool × D.Fq2),
      Bgate D γ br t = if br.1 then 0 else
        isqrt 2 * ((if br.2 = algebraMap D.Fq D.Fq2 (x₀ / (1 - x₀)) then D.chi γ (1 - x₀) else 0) +
          (if br.2 = algebraMap D.Fq D.Fq2 ((1 - x₀) / x₀) then D.chi γ x₀ else 0)) := by
    intro t ht x₀ _ hne hfilt br
    have ht1 : t ≠ 0 := ht.1
    have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht.2.1
    have ht3 : ∃ x : D.Fq, x ^ 2 - x + t = 0 := ht.2.2
    simp only [Bgate, Matrix.of_apply]
    rw [if_neg ht1, if_neg ht2, if_pos ht3, hfilt]
    cases br.1 <;> simp [Finset.sum_pair hne]
  have hB4_val : ∀ t (ht : B_T4 D t) z₀
      (hz₀q : z₀ ^ D.q = 1 - z₀) (hne : z₀ ≠ 1 - z₀)
      (hfilt : Finset.univ.filter (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0) = {z₀, 1 - z₀})
      (br : Bool × D.Fq2),
      Bgate D γ br t = if br.1 then
        -(isqrt 2 * ((if br.2 = z₀ / (1 - z₀) then D.theta (theta0Lab D γ) z₀ else 0) +
          (if br.2 = (1 - z₀) / z₀ then D.theta (theta0Lab D γ) (1 - z₀) else 0)))
        else 0 := by
    intro t ht z₀ hz₀q hne hfilt br
    have ht1 : t ≠ 0 := ht.1
    have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht.2.1
    have ht3 : ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0 := ht.2.2
    simp only [Bgate, Matrix.of_apply]
    rw [if_neg ht1, if_neg ht2, if_neg ht3, hfilt]
    have h1zq : (1 - z₀) ^ D.q = z₀ := by
      rw [fq2_sub_pow_q, one_pow, hz₀q]; ring
    cases br.1
    · simp
    · simp only [↓reduceIte, Finset.sum_pair hne, hz₀q, h1zq]
  -- Helper: injectivity of x ↦ x / (1 - x) on {0, 1}ᶜ and z ↦ z / (1 - z) on Z_nb
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
    · refine ⟨rfl, ?_⟩
      intro hbr2
      rw [hbr2] at hne
      have ha1 : (1 : D.Fq2) ≠ algebraMap D.Fq D.Fq2 (x₀ / (1 - x₀)) := by
        intro h; apply hdiv1; apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
        rw [map_one]; exact h.symm
      have ha2 : (1 : D.Fq2) ≠ algebraMap D.Fq D.Fq2 ((1 - x₀) / x₀) := by
        intro h; apply hdiv1; apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
        rw [← map_one (algebraMap D.Fq D.Fq2)] at h
        have hx' := FaithfulSMul.algebraMap_injective D.Fq D.Fq2 h
        rw [eq_comm, field_div_eq_one_iff_eq hx₀0] at hx'
        exact absurd hx'.symm hne_x
      rw [if_neg ha1, if_neg ha2] at hne
      simp at hne
    · simp [h1] at hne
  have hT4_supp : ∀ t (ht : B_T4 D t) (br : Bool × D.Fq2), Bgate D γ br t ≠ 0 →
      br.1 = true ∧ br.2 ≠ 1 := by
    intro t ht br hne
    obtain ⟨z₀, _, hz₀0, _, hz₀q, hne_z, hdiv1, _, hfilt⟩ := hB4_char t ht
    rw [hB4_val t ht z₀ hz₀q hne_z hfilt br] at hne
    cases h1 : br.1
    · simp [h1] at hne
    · refine ⟨rfl, ?_⟩
      intro hbr2
      rw [hbr2] at hne
      have ha2 : (1 : D.Fq2) ≠ (1 - z₀) / z₀ := by
        intro h; rw [eq_comm, field_div_eq_one_iff_eq hz₀0] at h; exact hne_z h.symm
      rw [if_neg hdiv1.symm, if_neg ha2] at hne
      simp at hne
  have h02_supp : ∀ t, (t = 0 ∨ B_T2 D t) → ∀ br : Bool × D.Fq2, Bgate D γ br t ≠ 0 → br.2 = 1 := by
    rintro t (rfl | ht2) br hne
    · simp only [Bgate, Matrix.of_apply, if_pos rfl] at hne
      by_contra h; simp [h] at hne
    · have ht0 : t ≠ 0 := by rcases ht2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
      have ht2' : ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹ := ht2
      simp only [Bgate, Matrix.of_apply, if_neg ht0, if_pos ht2'] at hne
      by_contra h; simp [h] at hne
  by_cases h1_02 : t₁ = 0 ∨ B_T2 D t₁
  · by_cases h2_02 : t₂ = 0 ∨ B_T2 D t₂
    · rcases h1_02 with rfl | h1_2 <;> rcases h2_02 with rfl | h2_2
      · rw [if_pos rfl]
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br 0) * Bgate D γ br 0 =
            if br.2 = 1 then (2 : ℂ)⁻¹ else 0 := by
          intro br
          simp only [Bgate, Matrix.of_apply, if_pos rfl]
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl]; cases br.1 <;> simp only [↓reduceIte, mul_one] <;> exact hisqrt2
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        norm_num
      · have ht20 : t₂ ≠ 0 := by rcases h2_2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        have h2_2' : ringChar D.Fq ≠ 2 ∧ t₂ = (4 : D.Fq)⁻¹ := h2_2
        rw [if_neg (Ne.symm ht20)]
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br 0) * Bgate D γ br t₂ =
            if br.2 = 1 then (2 : ℂ)⁻¹ * D.chi γ (2 : D.Fq)⁻¹ * (if br.1 then -1 else 1) else 0 := by
          intro br
          simp only [Bgate, Matrix.of_apply, if_pos rfl, if_neg ht20, if_pos h2_2']
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl, if_pos rfl]
            cases br.1
            · simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
              rw [← mul_assoc, hisqrt2]
            · simp only [↓reduceIte, mul_one, mul_neg]
              rw [← mul_assoc, hisqrt2]
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]
        simp [Fintype.sum_bool]
      · have ht10 : t₁ ≠ 0 := by rcases h1_2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        have h1_2' : ringChar D.Fq ≠ 2 ∧ t₁ = (4 : D.Fq)⁻¹ := h1_2
        rw [if_neg ht10]
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br 0 =
            if br.2 = 1 then (2 : ℂ)⁻¹ * star (D.chi γ (2 : D.Fq)⁻¹) * (if br.1 then -1 else 1) else 0 := by
          intro br
          simp only [Bgate, Matrix.of_apply, if_pos rfl, if_neg ht10, if_pos h1_2']
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
        simp_rw [hterm, Fintype.sum_prod_type]
        simp [Fintype.sum_bool]
      · have ht10 : t₁ ≠ 0 := by rcases h1_2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        have ht12 : t₁ = t₂ := by rcases h1_2 with ⟨_, rfl⟩; rcases h2_2 with ⟨_, rfl⟩; rfl
        subst ht12
        have h1_2' : ringChar D.Fq ≠ 2 ∧ t₁ = (4 : D.Fq)⁻¹ := h1_2
        rw [if_pos rfl]
        have h2 : (2 : D.Fq)⁻¹ ≠ 0 := inv_ne_zero (mt (fq_two_eq_zero_iff D).mp h1_2.1)
        have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₁ =
            if br.2 = 1 then (2 : ℂ)⁻¹ else 0 := by
          intro br
          simp only [Bgate, Matrix.of_apply, if_neg ht10, if_pos h1_2']
          by_cases hbr2 : br.2 = 1
          · rw [hbr2, if_pos rfl]
            cases br.1
            · simp only [Bool.false_eq_true, ↓reduceIte, mul_one, star_mul']
              calc star (isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) * (isqrt 2 * D.chi γ (2 : D.Fq)⁻¹)
                  = (star (isqrt 2) * isqrt 2) * (star (D.chi γ (2 : D.Fq)⁻¹) * D.chi γ (2 : D.Fq)⁻¹) := by ring
                _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ h2, mul_one]
            · simp only [↓reduceIte, star_mul', star_neg, star_one, mul_neg, mul_one, neg_mul, neg_neg]
              calc star (isqrt 2) * star (D.chi γ (2 : D.Fq)⁻¹) * (isqrt 2 * D.chi γ (2 : D.Fq)⁻¹)
                  = (star (isqrt 2) * isqrt 2) * (star (D.chi γ (2 : D.Fq)⁻¹) * D.chi γ (2 : D.Fq)⁻¹) := by ring
                _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ h2, mul_one]
          · simp [hbr2]
        simp_rw [hterm, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        norm_num
    · have ht20 : t₂ ≠ 0 := fun h => h2_02 (Or.inl h)
      have ht22 : ¬ B_T2 D t₂ := fun h => h2_02 (Or.inr h)
      have hne12 : t₁ ≠ t₂ := fun h => h2_02 (h ▸ h1_02)
      rw [if_neg hne12]
      apply Finset.sum_eq_zero
      intro br _
      by_cases h1z : Bgate D γ br t₁ = 0
      · simp [h1z]
      · by_cases h2z : Bgate D γ br t₂ = 0
        · simp [h2z]
        · exfalso
          have hbr2 : br.2 = 1 := h02_supp t₁ h1_02 br h1z
          by_cases hex2 : ∃ x : D.Fq, x ^ 2 - x + t₂ = 0
          · exact (hT3_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).2 hbr2
          · exact (hT4_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).2 hbr2
  · have ht10 : t₁ ≠ 0 := fun h => h1_02 (Or.inl h)
    have ht12 : ¬ B_T2 D t₁ := fun h => h1_02 (Or.inr h)
    by_cases h2_02 : t₂ = 0 ∨ B_T2 D t₂
    · have hne12 : t₁ ≠ t₂ := fun h => h1_02 (h ▸ h2_02)
      rw [if_neg hne12]
      apply Finset.sum_eq_zero
      intro br _
      by_cases h1z : Bgate D γ br t₁ = 0
      · simp [h1z]
      · by_cases h2z : Bgate D γ br t₂ = 0
        · simp [h2z]
        · exfalso
          have hbr2 : br.2 = 1 := h02_supp t₂ h2_02 br h2z
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
            algebraMap D.Fq D.Fq2 (a / (1 - a)) = algebraMap D.Fq D.Fq2 (b / (1 - b)) → a = b := by
          intro a b ha hb h
          exact hsplit_inj a b ha hb (FaithfulSMul.algebraMap_injective D.Fq D.Fq2 h)
        by_cases ht12_eq : t₁ = t₂
        · subst ht12_eq
          rw [if_pos rfl]
          have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₁ =
              if br.1 then 0 else (2 : ℂ)⁻¹ *
                ((if br.2 = algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁)) then 1 else 0) +
                 (if br.2 = algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁) then 1 else 0)) := by
            intro br
            rw [hB3_val t₁ hB1 x₁ hx₁ hne₁ hfilt₁ br]
            cases br.1
            · simp only [Bool.false_eq_true, ↓reduceIte, star_mul']
              have hadj : algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁)) ≠
                  algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁) := by
                intro h; exact hdiv₁ (FaithfulSMul.algebraMap_injective D.Fq D.Fq2 h)
              by_cases h1 : br.2 = algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁))
              · rw [h1]
                simp only [↓reduceIte, hadj, add_zero, mul_one]
                calc star (isqrt 2) * star (D.chi γ (1 - x₁)) * (isqrt 2 * D.chi γ (1 - x₁))
                    = (star (isqrt 2) * isqrt 2) * (star (D.chi γ (1 - x₁)) * D.chi γ (1 - x₁)) := by ring
                  _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ (sub_ne_zero.mpr hx₁1.symm), mul_one]
              · by_cases h2 : br.2 = algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁)
                · rw [h2]
                  simp only [↓reduceIte, hadj.symm, zero_add, mul_one]
                  calc star (isqrt 2) * star (D.chi γ x₁) * (isqrt 2 * D.chi γ x₁)
                      = (star (isqrt 2) * isqrt 2) * (star (D.chi γ x₁) * D.chi γ x₁) := by ring
                    _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, hchi_sq γ hx₁0, mul_one]
                · simp only [h1, h2, ↓reduceIte, add_zero, mul_zero, star_zero, zero_mul]
            · simp
          simp_rw [hterm, Fintype.sum_prod_type]
          simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, zero_add]
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          norm_num
        · rw [if_neg ht12_eq]
          apply Finset.sum_eq_zero
          intro br _
          rw [hB3_val t₁ hB1 x₁ hx₁ hne₁ hfilt₁ br, hB3_val t₂ hB2 x₂ hx₂ hne₂ hfilt₂ br]
          cases br.1
          · simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases h1a : br.2 = algebraMap D.Fq D.Fq2 (x₁ / (1 - x₁))
            · have h2a : br.2 ≠ algebraMap D.Fq D.Fq2 (x₂ / (1 - x₂)) := by
                intro h
                have heq := hinj x₁ x₂ hx₁1 hx₂1 (h1a.symm.trans h)
                apply ht12_eq; subst heq; linear_combination hx₁ - hx₂
              have h2b : br.2 ≠ algebraMap D.Fq D.Fq2 ((1 - x₂) / x₂) := by
                intro h
                have h2x : (1 - x₂) / (1 - (1 - x₂)) = (1 - x₂) / x₂ := by ring
                have heq := hinj x₁ (1 - x₂) hx₁1 (fun h0 => hx₂0 (by linear_combination -h0))
                  (h1a.symm.trans (h.trans (by rw [h2x])))
                apply ht12_eq
                have hsym := quad_symm_root t₂ x₂ hx₂
                rw [← heq] at hsym
                linear_combination hx₁ - hsym
              rw [if_pos h1a, if_neg h2a, if_neg h2b]; simp
            · by_cases h1b : br.2 = algebraMap D.Fq D.Fq2 ((1 - x₁) / x₁)
              · have h1x : (1 - x₁) / (1 - (1 - x₁)) = (1 - x₁) / x₁ := by ring
                have h2a : br.2 ≠ algebraMap D.Fq D.Fq2 (x₂ / (1 - x₂)) := by
                  intro h
                  have heq := hinj (1 - x₁) x₂ (fun h0 => hx₁0 (by linear_combination -h0)) hx₂1
                    (by rw [h1x]; exact h1b.symm.trans h)
                  apply ht12_eq
                  have hsym := quad_symm_root t₁ x₁ hx₁
                  rw [heq] at hsym
                  linear_combination hsym - hx₂
                have h2b : br.2 ≠ algebraMap D.Fq D.Fq2 ((1 - x₂) / x₂) := by
                  intro h
                  have h2x : (1 - x₂) / (1 - (1 - x₂)) = (1 - x₂) / x₂ := by ring
                  have heq := hinj (1 - x₁) (1 - x₂) (fun h0 => hx₁0 (by linear_combination -h0))
                    (fun h0 => hx₂0 (by linear_combination -h0)) (by rw [h1x, h2x]; exact h1b.symm.trans h)
                  apply ht12_eq
                  have hx12 : x₁ = x₂ := by linear_combination -heq
                  subst hx12; linear_combination hx₁ - hx₂
                rw [if_neg h1a, if_pos h1b, if_neg h2a, if_neg h2b]; simp
              · rw [if_neg h1a, if_neg h1b]; simp
          · simp
      · have hne12 : t₁ ≠ t₂ := fun h => hex2 (h ▸ hex1)
        rw [if_neg hne12]
        apply Finset.sum_eq_zero
        intro br _
        by_cases h1z : Bgate D γ br t₁ = 0
        · simp [h1z]
        · by_cases h2z : Bgate D γ br t₂ = 0
          · simp [h2z]
          · exfalso
            have h1f := (hT3_supp t₁ ⟨ht10, ht12, hex1⟩ br h1z).1
            have h2t := (hT4_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).1
            rw [h1f] at h2t; cases h2t
      · have hne12 : t₁ ≠ t₂ := fun h => hex1 (h ▸ hex2)
        rw [if_neg hne12]
        apply Finset.sum_eq_zero
        intro br _
        by_cases h1z : Bgate D γ br t₁ = 0
        · simp [h1z]
        · by_cases h2z : Bgate D γ br t₂ = 0
          · simp [h2z]
          · exfalso
            have h1t := (hT4_supp t₁ ⟨ht10, ht12, hex1⟩ br h1z).1
            have h2f := (hT3_supp t₂ ⟨ht20, ht22, hex2⟩ br h2z).1
            rw [h1t] at h2f; cases h2f
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
        · subst ht12_eq
          rw [if_pos rfl]
          have hterm : ∀ br : Bool × D.Fq2, star (Bgate D γ br t₁) * Bgate D γ br t₁ =
              if br.1 then (2 : ℂ)⁻¹ *
                ((if br.2 = z₁ / (1 - z₁) then 1 else 0) +
                 (if br.2 = (1 - z₁) / z₁ then 1 else 0)) else 0 := by
            intro br
            rw [hB4_val t₁ hB1 z₁ hz₁q hne₁ hfilt₁ br]
            cases br.1
            · simp
            · simp only [↓reduceIte, star_neg, neg_mul, mul_neg, neg_neg, star_mul']
              by_cases h1 : br.2 = z₁ / (1 - z₁)
              · rw [h1]
                simp only [↓reduceIte, hdiv₁, add_zero, mul_one]
                calc star (isqrt 2) * star (D.theta (theta0Lab D γ) z₁) *
                      (isqrt 2 * D.theta (theta0Lab D γ) z₁)
                    = (star (isqrt 2) * isqrt 2) *
                        (star (D.theta (theta0Lab D γ) z₁) * D.theta (theta0Lab D γ) z₁) := by ring
                  _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, htheta_sq _ hz₁0, mul_one]
              · by_cases h2 : br.2 = (1 - z₁) / z₁
                · rw [h2]
                  simp only [↓reduceIte, hdiv₁.symm, zero_add, mul_one]
                  calc star (isqrt 2) * star (D.theta (theta0Lab D γ) (1 - z₁)) *
                        (isqrt 2 * D.theta (theta0Lab D γ) (1 - z₁))
                      = (star (isqrt 2) * isqrt 2) *
                          (star (D.theta (theta0Lab D γ) (1 - z₁)) * D.theta (theta0Lab D γ) (1 - z₁)) := by ring
                    _ = (2 : ℂ)⁻¹ := by rw [hisqrt2, htheta_sq _ h1z₁, mul_one]
                · simp only [h1, h2, ↓reduceIte, add_zero, mul_zero, star_zero, zero_mul]
          simp_rw [hterm, Fintype.sum_prod_type]
          simp only [Fintype.sum_bool, ↓reduceIte, add_zero]
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          norm_num
        · rw [if_neg ht12_eq]
          apply Finset.sum_eq_zero
          intro br _
          rw [hB4_val t₁ hB1 z₁ hz₁q hne₁ hfilt₁ br, hB4_val t₂ hB2 z₂ hz₂q hne₂ hfilt₂ br]
          cases br.1
          · simp
          · simp only [↓reduceIte]
            by_cases h1a : br.2 = z₁ / (1 - z₁)
            · have h2a : br.2 ≠ z₂ / (1 - z₂) := by
                intro h
                have heq := hns_inj z₁ z₂ hz₁_ne1 hz₂_ne1 (h1a.symm.trans h)
                apply ht12_eq; rw [← hz₁_nrm, ← hz₂_nrm, heq]
              have h2b : br.2 ≠ (1 - z₂) / z₂ := by
                intro h
                have h2z : (1 - z₂) / (1 - (1 - z₂)) = (1 - z₂) / z₂ := by ring
                have heq := hns_inj z₁ (1 - z₂) hz₁_ne1 (fun h0 => hz₂0 (by linear_combination -h0))
                  (h1a.symm.trans (h.trans (by rw [h2z])))
                apply ht12_eq; rw [← hz₁_nrm, ← h1z₂_nrm, heq]
              rw [if_pos h1a, if_neg h2a, if_neg h2b]; simp
            · by_cases h1b : br.2 = (1 - z₁) / z₁
              · have h1z : (1 - z₁) / (1 - (1 - z₁)) = (1 - z₁) / z₁ := by ring
                have h2a : br.2 ≠ z₂ / (1 - z₂) := by
                  intro h
                  have heq := hns_inj (1 - z₁) z₂ (fun h0 => hz₁0 (by linear_combination -h0)) hz₂_ne1
                    (by rw [h1z]; exact h1b.symm.trans h)
                  apply ht12_eq; rw [← h1z₁_nrm, ← hz₂_nrm, heq]
                have h2b : br.2 ≠ (1 - z₂) / z₂ := by
                  intro h
                  have h2z : (1 - z₂) / (1 - (1 - z₂)) = (1 - z₂) / z₂ := by ring
                  have heq := hns_inj (1 - z₁) (1 - z₂) (fun h0 => hz₁0 (by linear_combination -h0))
                    (fun h0 => hz₂0 (by linear_combination -h0)) (by rw [h1z, h2z]; exact h1b.symm.trans h)
                  apply ht12_eq; rw [← h1z₁_nrm, ← h1z₂_nrm, heq]
                rw [if_neg h1a, if_pos h1b, if_neg h2a, if_neg h2b]; simp
              · rw [if_neg h1a, if_neg h1b]; simp

private lemma isqrt_q_sub_one_sq (D : FieldData) :
    isqrt (D.q - 1) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := by
  have h1 : (D.q : ℝ) - 1 = ((D.q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub D.one_lt_q.le, Nat.cast_one]
  rw [h1, isqrt_mul_self (Nat.cast_nonneg _), Nat.cast_sub D.one_lt_q.le, Nat.cast_one,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one]

private lemma Mbr_orth_on_dom (D : FieldData) (hq : 2 < D.q) (γ : D.Lab)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    {br₁ br₂ : Bool × D.Fq2} (h1 : InBranchDom D br₁) (h2 : InBranchDom D br₂) :
    ∑ o : BranchOut D γ, star (Mbr o br₁) * Mbr o br₂ = if br₁ = br₂ then 1 else 0 := by
  rcases br₁ with ⟨b1, w1⟩
  rcases br₂ with ⟨b2, w2⟩
  cases b1 <;> cases b2
  · simp only [InBranchDom, Bool.false_eq_true, ↓reduceIte] at h1 h2
    obtain ⟨r₁, hr₁, rfl⟩ := h1
    obtain ⟨r₂, hr₂, rfl⟩ := h2
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
        intro h0
        have hr := congrArg Complex.re h0
        simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hr
        linarith
      exact inv_mul_cancel₀ hq1
    · rw [mul_zero]
  · simp only [InBranchDom, Bool.false_eq_true, ↓reduceIte] at h1 h2
    obtain ⟨r₁, hr₁, rfl⟩ := h1
    simp only [Fintype.sum_sum_type, hMbr.1 r₁ hr₁, hMbr.2 w2 h2.1 h2.2,
      mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp
  · simp only [InBranchDom, Bool.false_eq_true, ↓reduceIte] at h1 h2
    obtain ⟨r₂, hr₂, rfl⟩ := h2
    simp only [Fintype.sum_sum_type, hMbr.2 w1 h1.1 h1.2, hMbr.1 r₂ hr₂,
      mul_zero, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    simp
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
        rw [isqrt_mul_self (by positivity)]
        push_cast; rfl
      calc isqrt (D.q + 1) * star (kerChar D (θ.1 - theta0Lab D γ) w1) *
            (isqrt (D.q + 1) * kerChar D (θ.1 - theta0Lab D γ) w2)
          = (isqrt (D.q + 1) * isqrt (D.q + 1)) *
              (star (kerChar D (θ.1 - theta0Lab D γ) w1) * kerChar D (θ.1 - theta0Lab D γ) w2) := by ring
        _ = ((D.q : ℂ) + 1)⁻¹ * _ := by rw [hisq]
    simp_rw [hterm, ← Finset.mul_sum, sum_kerChar_orth D hq γ h1.1 h1.2 h2.1 h2.2]
    have heq_iff : (true, w1) = (true, w2) ↔ w1 = w2 := by simp
    simp only [← heq_iff]
    split_ifs with h
    · have hq1 : ((D.q : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero D.q
      exact inv_mul_cancel₀ hq1
    · rw [mul_zero]

private lemma FxDag_orth (D : FieldData) (hq : 2 < D.q) (c₁ c₂ : Option D.Lab) :
    ∑ t : D.Fq, star (FxDag D t c₁) * FxDag D t c₂ = if c₁ = c₂ then 1 else 0 := by
  cases c₁ <;> cases c₂
  · rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
    simp only [FxDag, Matrix.of_apply, ↓reduceIte, star_one, mul_one]
    rw [Finset.sum_eq_zero, add_zero]
    intro t ht
    simp [Finset.ne_of_mem_erase ht]
  · rw [if_neg (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t = 0 <;> simp only [FxDag, Matrix.of_apply, ht, ↓reduceIte, star_zero, zero_mul,
      mul_zero]
  · rw [if_neg (by simp)]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : t = 0 <;> simp only [FxDag, Matrix.of_apply, ht, ↓reduceIte, star_zero, zero_mul,
      mul_zero]
  · rename_i α β
    have hsplit : ∑ t : D.Fq, star (FxDag D t (some α)) * FxDag D t (some β) =
        ((D.q : ℂ) - 1)⁻¹ * ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0),
          D.chi (α - β) t := by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
      have h0 : star (FxDag D 0 (some α)) * FxDag D 0 (some β) = 0 := by
        simp [FxDag]
      rw [h0, zero_add, Finset.mul_sum]
      have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun t : D.Fq => t ≠ 0) := by
        ext t; simp [Finset.mem_erase]
      rw [hfilt]
      apply Finset.sum_congr rfl
      intro t ht
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
        intro h0
        have hr := congrArg Complex.re h0
        simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hr
        linarith
      exact inv_mul_cancel₀ hq1
    · rw [mul_zero]

private lemma sum_isometry_inner {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : ι → κ → ℂ) (x y : κ → ℂ)
    (hA : ∀ a b, x a ≠ 0 → y b ≠ 0 → ∑ i, star (A i a) * A i b = if a = b then 1 else 0) :
    ∑ i, star (∑ a, A i a * x a) * (∑ b, A i b * y b) = ∑ a, star (x a) * y a := by
  simp_rw [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have h2 : ∑ b, ∑ i, star (A i a) * star (x a) * (A i b * y b) =
      ∑ b, star (x a) * (if a = b then 1 else 0) * y b := by
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hxa : x a = 0
    · simp [hxa]
    · by_cases hyb : y b = 0
      · simp [hyb]
      · calc ∑ i, star (A i a) * star (x a) * (A i b * y b)
            = star (x a) * (∑ i, star (A i a) * A i b) * y b := by
                rw [Finset.mul_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun i _ => ?_
                ring
          _ = star (x a) * (if a = b then 1 else 0) * y b := by rw [hA a b hxa hyb]
  rw [h2]
  simp [mul_ite]

private lemma T_isometry (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (c₁ c₂ : Option D.Lab) :
    ∑ o : D.Irr ⊕ U,
      star ((Rfix * Mbr * Bgate D γ * FxDag D) o c₁) *
        (Rfix * Mbr * Bgate D γ * FxDag D) o c₂ =
      if c₁ = c₂ then 1 else 0 := by
  let T := Rfix * Mbr * Bgate D γ * FxDag D
  change ∑ o, star (T o c₁) * T o c₂ = _
  have hT_eq : T = Rfix * (Mbr * (Bgate D γ * FxDag D)) := by
    simp only [T, Matrix.mul_assoc]
  set BF := Bgate D γ * FxDag D
  set MBF := Mbr * BF
  have hR : ∑ i : D.Irr ⊕ U, star ((Rfix * MBF) i c₁) * (Rfix * MBF) i c₂ =
      ∑ o : BranchOut D γ, star (MBF o c₁) * MBF o c₂ := by
    simp only [Matrix.mul_apply]
    refine sum_isometry_inner Rfix (fun o => MBF o c₁) (fun o => MBF o c₂) ?_
    intro o₁ o₂ _ _
    have hhr : (Rfixᴴ * Rfix) o₁ o₂ = (1 : Matrix (BranchOut D γ) (BranchOut D γ) ℂ) o₁ o₂ :=
      congrFun (congrFun hRfix.2.2.2 o₁) o₂
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
      Matrix.one_apply] using hhr
  have hBF_dom : ∀ br c, BF br c ≠ 0 → InBranchDom D br := by
    intro br c hne
    simp only [BF, Matrix.mul_apply] at hne
    obtain ⟨t, _, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact Bgate_mem_InBranchDom D γ br t (left_ne_zero_of_mul ht)
  have hM : ∑ o : BranchOut D γ, star (MBF o c₁) * MBF o c₂ =
      ∑ br : Bool × D.Fq2, star (BF br c₁) * BF br c₂ := by
    simp only [MBF, Matrix.mul_apply]
    exact sum_isometry_inner Mbr (fun br => BF br c₁) (fun br => BF br c₂)
      (fun br₁ br₂ h1 h2 => Mbr_orth_on_dom D hq γ Mbr hMbr (hBF_dom br₁ c₁ h1) (hBF_dom br₂ c₂ h2))
  have hB : ∑ br : Bool × D.Fq2, star (BF br c₁) * BF br c₂ =
      ∑ t : D.Fq, star (FxDag D t c₁) * FxDag D t c₂ := by
    simp only [BF, Matrix.mul_apply]
    exact sum_isometry_inner (Bgate D γ) (fun t => FxDag D t c₁) (fun t => FxDag D t c₂)
      (fun t₁ t₂ _ _ => Bgate_orth D γ t₁ t₂)
  rw [hT_eq, hR, hM, hB, FxDag_orth D hq c₁ c₂]

/-! ### Partition lemmas for `BranchOut D γ` -/

private lemma sum_lab_split {M : Type*} [AddCommMonoid M] (D : FieldData) (γ : D.Lab)
    (f : D.Lab → M) :
    ∑ κ : D.Lab, f κ =
      (∑ δ : D.Lab, if 2 * δ = γ then f δ else 0) +
      ∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
        if ab.1.1 + ab.1.2 = γ then f ab.1.1 + f ab.1.2 else 0 := by
  let A := Finset.univ.filter (fun κ : D.Lab => 2 * κ = γ)
  let B := Finset.univ.filter (fun κ : D.Lab => κ.val < (γ - κ).val)
  let C := Finset.univ.filter (fun κ : D.Lab => (γ - κ).val < κ.val)
  have h2eq : ∀ κ : D.Lab, 2 * κ = γ ↔ κ.val = (γ - κ).val := by
    intro κ
    rw [show 2 * κ = γ ↔ κ = γ - κ from
      ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩,
      (ZMod.val_injective (D.q - 1)).eq_iff]
  have hAB : Disjoint A B := Finset.disjoint_filter.mpr (fun κ _ hA hB => ((h2eq κ).mp hA).not_lt hB)
  have hAC : Disjoint A C := Finset.disjoint_filter.mpr (fun κ _ hA hC => ((h2eq κ).mp hA).symm.not_lt hC)
  have hBC : Disjoint B C := Finset.disjoint_filter.mpr (fun _ _ hB hC => hB.not_gt hC)
  have huniv : Finset.univ = (A ∪ B) ∪ C := by
    ext κ
    simp only [Finset.mem_univ, Finset.mem_union, A, B, C, Finset.mem_filter, true_and, h2eq]
    rw [true_iff]
    rcases lt_trichotomy κ.val (γ - κ).val with h | h | h
    · left; right; exact h
    · left; left; exact h
    · right; exact h
  have hsum : ∑ κ : D.Lab, f κ = (∑ κ ∈ A, f κ) + (∑ κ ∈ B, f κ) + (∑ κ ∈ C, f κ) := by
    calc ∑ κ : D.Lab, f κ = ∑ κ ∈ (A ∪ B) ∪ C, f κ := by rw [← huniv]
      _ = ∑ κ ∈ A ∪ B, f κ + ∑ κ ∈ C, f κ :=
          Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)
      _ = (∑ κ ∈ A, f κ + ∑ κ ∈ B, f κ) + ∑ κ ∈ C, f κ := by rw [Finset.sum_union hAB]
  let P := Finset.univ.filter (fun ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} =>
    ab.1.1 + ab.1.2 = γ)
  have hB_eq : ∑ κ ∈ B, f κ = ∑ ab ∈ P, f ab.1.1 := by
    refine Finset.sum_bij (fun κ hκ => ⟨(κ, γ - κ), (Finset.mem_filter.mp hκ).2⟩) ?_ ?_ ?_ ?_
    · intro κ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by ring⟩
    · intro κ₁ _ κ₂ _ heq; exact congrArg (fun x => x.1.1) heq
    · intro ab hab
      rw [Finset.mem_filter] at hab
      have h2 : ab.1.2 = γ - ab.1.1 := by linear_combination hab.2
      have hlt : ab.1.1.val < (γ - ab.1.1).val := h2 ▸ ab.2
      refine ⟨ab.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, Subtype.ext (Prod.ext rfl h2.symm)⟩
    · intro _ _; rfl
  have hC_eq : ∑ κ ∈ C, f κ = ∑ ab ∈ P, f ab.1.2 := by
    refine Finset.sum_bij (fun κ hκ => ⟨(γ - κ, κ), (Finset.mem_filter.mp hκ).2⟩) ?_ ?_ ?_ ?_
    · intro κ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by ring⟩
    · intro κ₁ _ κ₂ _ heq; exact congrArg (fun x => x.1.2) heq
    · intro ab hab
      rw [Finset.mem_filter] at hab
      have h1 : ab.1.1 = γ - ab.1.2 := eq_sub_of_add_eq hab.2
      have hlt : (γ - ab.1.2).val < ab.1.2.val := h1 ▸ ab.2
      refine ⟨ab.1.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, Subtype.ext (Prod.ext h1.symm rfl)⟩
    · intro _ _; rfl
  rw [hsum, add_assoc, hB_eq, hC_eq, ← Finset.sum_add_distrib]
  simp only [A, P, Finset.sum_filter]

private lemma lab2_mul_q_sq (D : FieldData) (k : D.Lab2) :
    (D.q : D.Lab2) * ((D.q : D.Lab2) * k) = k := by
  have hq2 : (D.q : D.Lab2) * (D.q : D.Lab2) = 1 := by
    have hmod : D.q * D.q ≡ 1 [MOD (D.q ^ 2 - 1)] := by
      rw [Nat.modEq_iff_dvd]
      refine ⟨-1, ?_⟩
      have hq : 1 < D.q := D.one_lt_q
      have hq2' : 1 ≤ D.q ^ 2 := by nlinarith
      zify [hq2']
      ring
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

private def fixedTheta (D : FieldData) (γ : D.Lab) (δ : D.Lab) (hδ : 2 * δ = γ) :
    {θ : D.Lab2 // D.restrLab θ = γ} :=
  ⟨(((D.q + 1) * δ.val : ℕ) : D.Lab2), by rw [restrLab_q_add_one_mul, hδ]⟩

private def cuspTheta1 (D : FieldData) (γ : D.Lab) (k : {k : D.Lab2 // D.IsCuspLabel k})
    (hk : D.restrLab k.1 = γ) : {θ : D.Lab2 // D.restrLab θ = γ} :=
  ⟨k.1, hk⟩

private def cuspTheta2 (D : FieldData) (γ : D.Lab) (k : {k : D.Lab2 // D.IsCuspLabel k})
    (hk : D.restrLab k.1 = γ) : {θ : D.Lab2 // D.restrLab θ = γ} :=
  ⟨(D.q : D.Lab2) * k.1, by rw [restrLab_mul_q, hk]⟩

private lemma sum_restrLab_split {M : Type*} [AddCommMonoid M] (D : FieldData) (hq : 2 < D.q)
    (γ : D.Lab) (f : {θ : D.Lab2 // D.restrLab θ = γ} → M) :
    ∑ θ : {θ : D.Lab2 // D.restrLab θ = γ}, f θ =
      (∑ δ : D.Lab, if hδ : 2 * δ = γ then f (fixedTheta D γ δ hδ) else 0) +
      ∑ k : {k : D.Lab2 // D.IsCuspLabel k},
        if hk : D.restrLab k.1 = γ then
          f (cuspTheta1 D γ k hk) + f (cuspTheta2 D γ k hk)
        else 0 := by
  let A := Finset.univ.filter (fun θ : {θ : D.Lab2 // D.restrLab θ = γ} => D.q + 1 ∣ θ.1.val)
  let B := Finset.univ.filter (fun θ : {θ : D.Lab2 // D.restrLab θ = γ} =>
    ¬ (D.q + 1 ∣ θ.1.val) ∧ θ.1.val ≤ ((D.q : D.Lab2) * θ.1).val)
  let C := Finset.univ.filter (fun θ : {θ : D.Lab2 // D.restrLab θ = γ} =>
    ¬ (D.q + 1 ∣ θ.1.val) ∧ ((D.q : D.Lab2) * θ.1).val < θ.1.val)
  have hAB : Disjoint A B := Finset.disjoint_filter.mpr (fun _ _ hA hB => hB.1 hA)
  have hAC : Disjoint A C := Finset.disjoint_filter.mpr (fun _ _ hA hC => hC.1 hA)
  have hBC : Disjoint B C := Finset.disjoint_filter.mpr (fun _ _ hB hC => hC.2.not_ge hB.2)
  have huniv : Finset.univ = (A ∪ B) ∪ C := by
    ext θ
    simp only [Finset.mem_univ, Finset.mem_union, A, B, C, Finset.mem_filter, true_and]
    rw [true_iff]
    by_cases hd : D.q + 1 ∣ θ.1.val
    · left; left; exact hd
    · rcases le_or_gt θ.1.val ((D.q : D.Lab2) * θ.1).val with h | h
      · left; right; exact ⟨hd, h⟩
      · right; exact ⟨hd, h⟩
  have hsum : ∑ θ : {θ : D.Lab2 // D.restrLab θ = γ}, f θ =
      (∑ θ ∈ A, f θ) + (∑ θ ∈ B, f θ) + (∑ θ ∈ C, f θ) := by
    calc ∑ θ : {θ : D.Lab2 // D.restrLab θ = γ}, f θ = ∑ θ ∈ (A ∪ B) ∪ C, f θ := by rw [← huniv]
      _ = ∑ θ ∈ A ∪ B, f θ + ∑ θ ∈ C, f θ :=
          Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)
      _ = (∑ θ ∈ A, f θ + ∑ θ ∈ B, f θ) + ∑ θ ∈ C, f θ := by rw [Finset.sum_union hAB]
  let Dset := Finset.univ.filter (fun δ : D.Lab => 2 * δ = γ)
  have hA_eq : ∑ θ ∈ A, f θ =
      ∑ δ : D.Lab, if hδ : 2 * δ = γ then f (fixedTheta D γ δ hδ) else 0 := by
    have hfilt_d : ∑ δ : D.Lab, (if hδ : 2 * δ = γ then f (fixedTheta D γ δ hδ) else 0) =
        ∑ δ ∈ Dset.attach, f (fixedTheta D γ δ.1 (Finset.mem_filter.mp δ.2).2) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun δ : D.Lab => 2 * δ = γ)]
      have hnot : ∑ δ ∈ Finset.univ.filter (fun δ : D.Lab => ¬ 2 * δ = γ),
          (if hδ : 2 * δ = γ then f (fixedTheta D γ δ hδ) else 0) = 0 :=
        Finset.sum_eq_zero fun δ hδ => dif_neg (Finset.mem_filter.mp hδ).2
      rw [hnot, add_zero]
      change ∑ δ ∈ Dset, (if hδ : 2 * δ = γ then f (fixedTheta D γ δ hδ) else 0) = _
      rw [← Finset.sum_attach Dset]
      refine Finset.sum_congr rfl fun δ _ => dif_pos (Finset.mem_filter.mp δ.2).2
    rw [hfilt_d]
    symm
    refine Finset.sum_bij (fun δ _ => fixedTheta D γ δ.1 (Finset.mem_filter.mp δ.2).2) ?_ ?_ ?_ ?_
    · intro δ _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hlt : (D.q + 1) * δ.1.val < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul]
        exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt δ.1) (by omega)
      simp only [fixedTheta, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      exact ⟨δ.1.val, rfl⟩
    · intro δ₁ _ δ₂ _ heq
      have hval := congrArg (fun x : {θ : D.Lab2 // D.restrLab θ = γ} => x.1.val) heq
      have hlt₁ : (D.q + 1) * δ₁.1.val < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt δ₁.1) (by omega)
      have hlt₂ : (D.q + 1) * δ₂.1.val < D.q ^ 2 - 1 := by
        rw [q_sq_sub_one_eq_mul]; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt δ₂.1) (by omega)
      simp only [fixedTheta, ZMod.val_natCast, Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hval
      exact Subtype.ext (ZMod.val_injective (D.q - 1) (Nat.eq_of_mul_eq_mul_left (by omega) hval))
    · intro θ hθ
      rw [Finset.mem_filter] at hθ
      obtain ⟨m, hm⟩ := hθ.2
      have hmlt : m < D.q - 1 := by
        have hlt : (D.q + 1) * m < (D.q + 1) * (D.q - 1) := by
          rw [← q_sq_sub_one_eq_mul, ← hm]; exact ZMod.val_lt θ.1
        exact Nat.lt_of_mul_lt_mul_left hlt
      let δ : D.Lab := (m : D.Lab)
      have hδval : δ.val = m := by simp [δ, ZMod.val_natCast, Nat.mod_eq_of_lt hmlt]
      have hδeq : 2 * δ = γ := by
        rw [← θ.2, ← restrLab_q_add_one_mul D δ, hδval, ← hm, ZMod.natCast_zmod_val]
      refine ⟨⟨δ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hδeq⟩⟩, Finset.mem_univ _,
        Subtype.ext ?_⟩
      change (((D.q + 1) * δ.val : ℕ) : D.Lab2) = θ.1
      rw [hδval, ← hm, ZMod.natCast_zmod_val]
    · intro _ _; rfl
  let Kset := Finset.univ.filter (fun k : {k : D.Lab2 // D.IsCuspLabel k} => D.restrLab k.1 = γ)
  have hK_split : (∑ k : {k : D.Lab2 // D.IsCuspLabel k},
        if hk : D.restrLab k.1 = γ then f (cuspTheta1 D γ k hk) + f (cuspTheta2 D γ k hk) else 0) =
      (∑ k ∈ Kset.attach, f (cuspTheta1 D γ k.1 (Finset.mem_filter.mp k.2).2)) +
      (∑ k ∈ Kset.attach, f (cuspTheta2 D γ k.1 (Finset.mem_filter.mp k.2).2)) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun k : {k : D.Lab2 // D.IsCuspLabel k} => D.restrLab k.1 = γ)]
    have hnot : ∑ k ∈ Finset.univ.filter
        (fun k : {k : D.Lab2 // D.IsCuspLabel k} => ¬ D.restrLab k.1 = γ),
        (if hk : D.restrLab k.1 = γ then f (cuspTheta1 D γ k hk) + f (cuspTheta2 D γ k hk) else 0) =
        0 :=
      Finset.sum_eq_zero fun k hk => dif_neg (Finset.mem_filter.mp hk).2
    rw [hnot, add_zero]
    change ∑ k ∈ Kset, (if hk : D.restrLab k.1 = γ then
      f (cuspTheta1 D γ k hk) + f (cuspTheta2 D γ k hk) else 0) = _
    rw [← Finset.sum_attach Kset, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => by rw [dif_pos (Finset.mem_filter.mp k.2).2]
  have hB_eq : ∑ θ ∈ B, f θ =
      ∑ k ∈ Kset.attach, f (cuspTheta1 D γ k.1 (Finset.mem_filter.mp k.2).2) := by
    symm
    refine Finset.sum_bij (fun k _ => cuspTheta1 D γ k.1 (Finset.mem_filter.mp k.2).2) ?_ ?_ ?_ ?_
    · intro k _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, k.1.2⟩
    · intro k₁ _ k₂ _ heq
      exact Subtype.ext (Subtype.ext (congrArg (fun x : {θ : D.Lab2 // D.restrLab θ = γ} => x.1) heq))
    · intro θ hθ
      rw [Finset.mem_filter] at hθ
      refine ⟨⟨⟨θ.1, hθ.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, θ.2⟩⟩, Finset.mem_univ _,
        Subtype.ext rfl⟩
    · intro _ _; rfl
  have hC_eq : ∑ θ ∈ C, f θ =
      ∑ k ∈ Kset.attach, f (cuspTheta2 D γ k.1 (Finset.mem_filter.mp k.2).2) := by
    symm
    refine Finset.sum_bij (fun k _ => cuspTheta2 D γ k.1 (Finset.mem_filter.mp k.2).2) ?_ ?_ ?_ ?_
    · intro k _
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro hdvd
        have hfix : (D.q : D.Lab2) * ((D.q : D.Lab2) * k.1.1) = (D.q : D.Lab2) * k.1.1 :=
          (lab2_fixed_iff_dvd D hq _).mpr hdvd
        rw [lab2_mul_q_sq] at hfix
        exact k.1.2.1 ((lab2_fixed_iff_dvd D hq k.1.1).mp hfix.symm)
      · rw [cuspTheta2, lab2_mul_q_sq]
        have hne : (D.q : D.Lab2) * k.1.1 ≠ k.1.1 := by
          intro hfix
          exact k.1.2.1 ((lab2_fixed_iff_dvd D hq k.1.1).mp hfix)
        exact lt_of_le_of_ne k.1.2.2 (fun heq => hne (ZMod.val_injective _ heq.symm))
    · intro k₁ _ k₂ _ heq
      have hk := congrArg (fun x : {θ : D.Lab2 // D.restrLab θ = γ} => (D.q : D.Lab2) * x.1) heq
      simp only [cuspTheta2, lab2_mul_q_sq] at hk
      exact Subtype.ext (Subtype.ext hk)
    · intro θ hθ
      rw [Finset.mem_filter] at hθ
      have hk_ndvd : ¬ (D.q + 1 ∣ ((D.q : D.Lab2) * θ.1).val) := by
        intro hdvd
        have hfix : (D.q : D.Lab2) * ((D.q : D.Lab2) * θ.1) = (D.q : D.Lab2) * θ.1 :=
          (lab2_fixed_iff_dvd D hq _).mpr hdvd
        rw [lab2_mul_q_sq] at hfix
        exact hθ.2.1 ((lab2_fixed_iff_dvd D hq θ.1).mp hfix.symm)
      have hk_le : ((D.q : D.Lab2) * θ.1).val ≤ ((D.q : D.Lab2) * ((D.q : D.Lab2) * θ.1)).val := by
        rw [lab2_mul_q_sq]; exact hθ.2.2.le
      have hk_res : D.restrLab ((D.q : D.Lab2) * θ.1) = γ := by rw [restrLab_mul_q, θ.2]
      refine ⟨⟨⟨(D.q : D.Lab2) * θ.1, ⟨hk_ndvd, hk_le⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_res⟩⟩, Finset.mem_univ _, Subtype.ext ?_⟩
      change (D.q : D.Lab2) * ((D.q : D.Lab2) * θ.1) = θ.1
      exact lab2_mul_q_sq D θ.1
    · intro _ _; rfl
  rw [hsum, add_assoc, hA_eq, hK_split, hB_eq, hC_eq]

/-! ### Layer 4: Columns of `T := Rfix * Mbr * Bgate * FxDag`, Lemmas 6.23, 6.24, and 6.25 -/

private def eOpt (D : FieldData) (c : Option D.Lab) : Option D.Lab → ℂ :=
  fun c' => if c' = c then 1 else 0

private lemma mulVec_eOpt {D : FieldData} {ι : Type*} (M : Matrix ι (Option D.Lab) ℂ) (c : Option D.Lab) (i : ι) :
    M.mulVec (eOpt D c) i = M i c := by
  simp [Matrix.mulVec, dotProduct, eOpt]

private lemma eB_apply (D : FieldData) (γ : D.Lab) (o o' : BranchOut D γ) :
    eB D γ o o' = if o' = o then 1 else 0 := by
  simp [eB]

private lemma eO_apply {D : FieldData} {U : Type} (μ μ' : D.Irr ⊕ U) :
    eO D μ μ' = if μ' = μ then 1 else 0 := by
  simp [eO]

private lemma sqrt_two_mul_isqrt_two : (Real.sqrt 2 : ℂ) * isqrt 2 = 1 := by
  simp only [isqrt, ← Complex.ofReal_mul]
  rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num)).ne', Complex.ofReal_one]

private lemma sqrt_div_two_q_mul_isqrt (q a : ℝ) (hq : 0 < q) (ha : 0 < a) :
    (Real.sqrt (a / (2 * q)) : ℂ) * (isqrt 2 * isqrt a) =
      ((2 * Real.sqrt q : ℝ)⁻¹ : ℂ) := by
  have hr : Real.sqrt (a / (2 * q)) * ((Real.sqrt 2)⁻¹ * (Real.sqrt a)⁻¹) = (2 * Real.sqrt q)⁻¹ := by
    rw [Real.sqrt_div ha.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
    have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    field_simp [hs2, hsq, hsa]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [isqrt, Complex.ofReal_mul, Complex.ofReal_inv] using congrArg Complex.ofReal hr

private lemma det_none_coeff (D : FieldData) (hq : 2 < D.q) :
    (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (isqrt 2 * isqrt (D.q - 1)) -
    (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (isqrt 2 * isqrt (D.q + 1)) = 0 := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) < (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  rw [sqrt_div_two_q_mul_isqrt D.q (D.q - 1) hq0 hq1,
    sqrt_div_two_q_mul_isqrt D.q (D.q + 1) hq0 hq2, sub_self]

private lemma St_none_coeff (D : FieldData) (hq : 2 < D.q) :
    (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (isqrt 2 * isqrt (D.q - 1)) +
    (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (isqrt 2 * isqrt (D.q + 1)) =
      (Real.sqrt ((D.q : ℝ) / (((D.q : ℝ) - 1) * ((D.q : ℝ) + 1))) : ℂ) := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) < (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  have hr : Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) * ((Real.sqrt 2)⁻¹ * (Real.sqrt ((D.q : ℝ) - 1))⁻¹) +
      Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) * ((Real.sqrt 2)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹) =
      Real.sqrt ((D.q : ℝ) / (((D.q : ℝ) - 1) * ((D.q : ℝ) + 1))) := by
    rw [Real.sqrt_div hq2.le, Real.sqrt_div hq1.le, Real.sqrt_div hq0.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hq1.le]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq : Real.sqrt D.q ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    have hsm : Real.sqrt ((D.q : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
    have hsp : Real.sqrt ((D.q : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
    field_simp [hs2, hsq, hsm, hsp]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hq2.le,
      Real.sq_sqrt hq1.le, Real.sq_sqrt hq0.le]
    ring
  simpa only [isqrt, Complex.ofReal_add, Complex.ofReal_mul] using congrArg Complex.ofReal hr

private lemma det_some_neq_coeff (D : FieldData) (hq : 2 < D.q) :
    (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2) -
    (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1)) = 0 := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) < (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  have hr : Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) * (((D.q : ℝ) - 1)⁻¹ * (Real.sqrt 2)⁻¹) -
      Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) *
        ((Real.sqrt ((D.q : ℝ) - 1))⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹) = 0 := by
    rw [Real.sqrt_div hq1.le, Real.sqrt_div hq2.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq : Real.sqrt D.q ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    have hsm : Real.sqrt ((D.q : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
    have hsp : Real.sqrt ((D.q : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
    field_simp [hs2, hsq, hsm, hsp, hq1.ne']
    rw [Real.sq_sqrt hq1.le]
    ring
  simpa only [isqrt, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_zero] using congrArg Complex.ofReal hr

private lemma St_some_neq_coeff (D : FieldData) (hq : 2 < D.q) :
    (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2) +
    (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1)) =
      (Real.sqrt D.q : ℂ) * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1) := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) < (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  have hr : Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) * (((D.q : ℝ) - 1)⁻¹ * (Real.sqrt 2)⁻¹) +
      Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) *
        ((Real.sqrt ((D.q : ℝ) - 1))⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹) =
      Real.sqrt D.q * ((D.q : ℝ) - 1)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹ := by
    rw [Real.sqrt_div hq2.le, Real.sqrt_div hq1.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq : Real.sqrt D.q ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    have hsm : Real.sqrt ((D.q : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
    have hsp : Real.sqrt ((D.q : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
    field_simp [hs2, hsq, hsm, hsp, hq1.ne']
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hq2.le, Real.sq_sqrt hq0.le]
    ring
  simpa only [isqrt, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_one] using congrArg Complex.ofReal hr

private lemma det_some_eq_coeff (D : FieldData) (hq : 2 < D.q) :
    (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2 * ((D.q : ℂ) - 2)) -
    (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (-(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * (D.q : ℂ))) =
      (Real.sqrt (((D.q : ℝ) - 1) / D.q) : ℂ) := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) < (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  have hr : Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) * (((D.q : ℝ) - 1)⁻¹ * (Real.sqrt 2)⁻¹ * ((D.q : ℝ) - 2)) -
      Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) *
        (-((Real.sqrt ((D.q : ℝ) - 1))⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹ * D.q)) =
      Real.sqrt (((D.q : ℝ) - 1) / D.q) := by
    rw [Real.sqrt_div hq1.le, Real.sqrt_div hq2.le, Real.sqrt_div hq1.le,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq : Real.sqrt D.q ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    have hsm : Real.sqrt ((D.q : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
    have hsp : Real.sqrt ((D.q : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
    field_simp [hs2, hsq, hsm, hsp, hq1.ne']
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hq1.le]
    ring
  simpa only [isqrt, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat] using
      congrArg Complex.ofReal hr

private lemma St_some_eq_coeff (D : FieldData) (hq : 2 < D.q) :
    (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2 * ((D.q : ℂ) - 2)) +
    (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (-(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * (D.q : ℂ))) =
      -(isqrt D.q * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1)) := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) < (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  have hr : Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) * (((D.q : ℝ) - 1)⁻¹ * (Real.sqrt 2)⁻¹ * ((D.q : ℝ) - 2)) +
      Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) *
        (-((Real.sqrt ((D.q : ℝ) - 1))⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹ * D.q)) =
      -((Real.sqrt D.q)⁻¹ * ((D.q : ℝ) - 1)⁻¹ * (Real.sqrt ((D.q : ℝ) + 1))⁻¹) := by
    rw [Real.sqrt_div hq2.le, Real.sqrt_div hq1.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hsq : Real.sqrt D.q ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
    have hsm : Real.sqrt ((D.q : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hq1).ne'
    have hsp : Real.sqrt ((D.q : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.mpr hq2).ne'
    field_simp [hs2, hsq, hsm, hsp, hq1.ne']
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hq2.le]
    ring
  simpa only [isqrt, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat] using congrArg Complex.ofReal hr

private lemma isqrt_q_mul_sq_sub_one (D : FieldData) (hq : 2 < D.q) :
    isqrt D.q * (isqrt (D.q - 1) * isqrt (D.q + 1)) = isqrt (D.q * (D.q ^ 2 - 1)) := by
  have hq0 : (0 : ℝ) ≤ D.q := by positivity
  have hq1 : (0 : ℝ) ≤ (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hq2 : (0 : ℝ) ≤ (D.q : ℝ) + 1 := by positivity
  rw [← isqrt_mul hq1 hq2, ← isqrt_mul hq0 (mul_nonneg hq1 hq2)]
  congr 1
  ring

private lemma isqrt_q_sq_mul_q (D : FieldData) : isqrt D.q * isqrt D.q * (D.q : ℂ) = 1 := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  rw [isqrt_mul_self hq0.le]
  have hqc : (D.q : ℂ) ≠ 0 := by exact_mod_cast (q_pos D).ne'
  exact inv_mul_cancel₀ hqc

private lemma isqrt_q_mul_q (D : FieldData) : isqrt D.q * (D.q : ℂ) = (Real.sqrt D.q : ℂ) := by
  have hq0 : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  simp only [isqrt]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_inj]
  have hsq : Real.sqrt D.q ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
  calc (Real.sqrt D.q)⁻¹ * D.q
      = (Real.sqrt D.q)⁻¹ * (Real.sqrt D.q * Real.sqrt D.q) := by rw [Real.mul_self_sqrt hq0.le]
    _ = Real.sqrt D.q := by rw [← mul_assoc, inv_mul_cancel₀ hsq, one_mul]

private lemma vec_eq_sum_eB (D : FieldData) (γ : D.Lab) (v : BranchOut D γ → ℂ) :
    v = (∑ κ : D.Lab, v (.inl κ) • eB D γ (.inl κ)) +
      (∑ θ : {θ : D.Lab2 // D.restrLab θ = γ}, v (.inr θ) • eB D γ (.inr θ)) := by
  ext o
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, eB_apply]
  rcases o with κ | θ
  · simp [Finset.sum_ite_eq']
  · simp [Finset.sum_ite_eq']

private lemma Rfix_mulVec_of_symm (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (v : BranchOut D γ → ℂ)
    (hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2))
    (hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk))) :
    Rfix.mulVec v =
      (∑ δ : D.Lab, if hδ : 2 * δ = γ then
        ((Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inl δ) +
         (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ hδ))) •
          eO D (.inl (.inr (.inl δ))) +
        ((Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inl δ) -
         (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ hδ))) •
          eO D (.inl (.inl δ))
      else 0) +
      (∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
        if ab.1.1 + ab.1.2 = γ then
          ((Real.sqrt 2 : ℂ) * v (.inl ab.1.1)) • eO D (.inl (.inr (.inr (.inl ab))))
        else 0) +
      (∑ k : {k : D.Lab2 // D.IsCuspLabel k},
        if hk : D.restrLab k.1 = γ then
          ((Real.sqrt 2 : ℂ) * v (.inr (cuspTheta1 D γ k hk))) • eO D (.inl (.inr (.inr (.inr k))))
        else 0) := by
  conv_lhs => rw [vec_eq_sum_eB D γ v, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]
  rw [sum_lab_split (M := (D.Irr ⊕ U → ℂ)) D γ (fun κ => v (.inl κ) • Rfix.mulVec (eB D γ (.inl κ)))]
  rw [sum_restrLab_split (M := (D.Irr ⊕ U → ℂ)) D hq γ
    (fun θ => v (.inr θ) • Rfix.mulVec (eB D γ (.inr θ)))]
  have hfix_sum :
      (∑ δ : D.Lab, if 2 * δ = γ then v (.inl δ) • Rfix.mulVec (eB D γ (.inl δ)) else 0) +
      (∑ δ : D.Lab, if hδ : 2 * δ = γ then v (.inr (fixedTheta D γ δ hδ)) •
        Rfix.mulVec (eB D γ (.inr (fixedTheta D γ δ hδ))) else 0) =
      (∑ δ : D.Lab, if hδ : 2 * δ = γ then
        ((Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inl δ) +
         (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ hδ))) •
          eO D (.inl (.inr (.inl δ))) +
        ((Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inl δ) -
         (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ hδ))) •
          eO D (.inl (.inl δ))
      else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun δ _ => ?_
    split_ifs with hδ
    · rw [(hRfix.2.2.1 δ hδ).1, (hRfix.2.2.1 δ hδ).2 (fixedTheta D γ δ hδ) rfl]
      ext o
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · simp
  have hps_sum :
      (∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
        if ab.1.1 + ab.1.2 = γ then
          v (.inl ab.1.1) • Rfix.mulVec (eB D γ (.inl ab.1.1)) +
          v (.inl ab.1.2) • Rfix.mulVec (eB D γ (.inl ab.1.2))
        else 0) =
      (∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
        if ab.1.1 + ab.1.2 = γ then
          ((Real.sqrt 2 : ℂ) * v (.inl ab.1.1)) • eO D (.inl (.inr (.inr (.inl ab))))
        else 0) := by
    refine Finset.sum_congr rfl fun ab _ => ?_
    split_ifs with hab
    · rw [← hsym_lab ab hab, ← smul_add]
      have h1 := (hRfix.1 ab hab).1
      rw [Matrix.mulVec_smul, Matrix.mulVec_add] at h1
      calc v (.inl ab.1.1) • (Rfix.mulVec (eB D γ (.inl ab.1.1)) + Rfix.mulVec (eB D γ (.inl ab.1.2)))
          = ((Real.sqrt 2 : ℂ) * v (.inl ab.1.1)) •
              (isqrt 2 • (Rfix.mulVec (eB D γ (.inl ab.1.1)) + Rfix.mulVec (eB D γ (.inl ab.1.2)))) := by
                rw [smul_smul, mul_assoc, mul_comm (v (.inl ab.1.1)) (isqrt 2), ← mul_assoc,
                  sqrt_two_mul_isqrt_two, one_mul]
        _ = ((Real.sqrt 2 : ℂ) * v (.inl ab.1.1)) • eO D (.inl (.inr (.inr (.inl ab)))) := by
              rw [h1]
    · rfl
  have hcusp_sum :
      (∑ k : {k : D.Lab2 // D.IsCuspLabel k},
        if hk : D.restrLab k.1 = γ then
          v (.inr (cuspTheta1 D γ k hk)) • Rfix.mulVec (eB D γ (.inr (cuspTheta1 D γ k hk))) +
          v (.inr (cuspTheta2 D γ k hk)) • Rfix.mulVec (eB D γ (.inr (cuspTheta2 D γ k hk)))
        else 0) =
      (∑ k : {k : D.Lab2 // D.IsCuspLabel k},
        if hk : D.restrLab k.1 = γ then
          ((Real.sqrt 2 : ℂ) * v (.inr (cuspTheta1 D γ k hk))) • eO D (.inl (.inr (.inr (.inr k))))
        else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [← hsym_cusp k hk, ← smul_add]
      have hk2 : D.restrLab ((D.q : D.Lab2) * k.1) = γ := (cuspTheta2 D γ k hk).2
      have h1 := (hRfix.2.1 k hk hk2).1
      rw [Matrix.mulVec_smul, Matrix.mulVec_add] at h1
      have heq1 : cuspTheta1 D γ k hk = ⟨k.1, hk⟩ := rfl
      have heq2 : cuspTheta2 D γ k hk = ⟨(D.q : D.Lab2) * k.1, hk2⟩ := rfl
      rw [heq1, heq2]
      calc v (.inr ⟨k.1, hk⟩) •
            (Rfix.mulVec (eB D γ (.inr ⟨k.1, hk⟩)) +
             Rfix.mulVec (eB D γ (.inr ⟨(D.q : D.Lab2) * k.1, hk2⟩)))
          = ((Real.sqrt 2 : ℂ) * v (.inr ⟨k.1, hk⟩)) •
              (isqrt 2 • (Rfix.mulVec (eB D γ (.inr ⟨k.1, hk⟩)) +
                Rfix.mulVec (eB D γ (.inr ⟨(D.q : D.Lab2) * k.1, hk2⟩)))) := by
                rw [smul_smul, mul_assoc, mul_comm (v (.inr ⟨k.1, hk⟩)) (isqrt 2),
                  ← mul_assoc, sqrt_two_mul_isqrt_two, one_mul]
        _ = ((Real.sqrt 2 : ℂ) * v (.inr ⟨k.1, hk⟩)) • eO D (.inl (.inr (.inr (.inr k)))) := by
              rw [h1]
    · rfl
  calc (∑ δ : D.Lab, if 2 * δ = γ then v (.inl δ) • Rfix.mulVec (eB D γ (.inl δ)) else 0) +
        (∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
          if ab.1.1 + ab.1.2 = γ then
            v (.inl ab.1.1) • Rfix.mulVec (eB D γ (.inl ab.1.1)) +
            v (.inl ab.1.2) • Rfix.mulVec (eB D γ (.inl ab.1.2))
          else 0) +
        ((∑ δ : D.Lab, if hδ : 2 * δ = γ then
            v (.inr (fixedTheta D γ δ hδ)) • Rfix.mulVec (eB D γ (.inr (fixedTheta D γ δ hδ)))
          else 0) +
         (∑ k : {k : D.Lab2 // D.IsCuspLabel k},
           if hk : D.restrLab k.1 = γ then
             v (.inr (cuspTheta1 D γ k hk)) • Rfix.mulVec (eB D γ (.inr (cuspTheta1 D γ k hk))) +
             v (.inr (cuspTheta2 D γ k hk)) • Rfix.mulVec (eB D γ (.inr (cuspTheta2 D γ k hk)))
           else 0))
      = ((∑ δ : D.Lab, if 2 * δ = γ then v (.inl δ) • Rfix.mulVec (eB D γ (.inl δ)) else 0) +
         (∑ δ : D.Lab, if hδ : 2 * δ = γ then
            v (.inr (fixedTheta D γ δ hδ)) • Rfix.mulVec (eB D γ (.inr (fixedTheta D γ δ hδ)))
          else 0)) +
        (∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
          if ab.1.1 + ab.1.2 = γ then
            v (.inl ab.1.1) • Rfix.mulVec (eB D γ (.inl ab.1.1)) +
            v (.inl ab.1.2) • Rfix.mulVec (eB D γ (.inl ab.1.2))
          else 0) +
        (∑ k : {k : D.Lab2 // D.IsCuspLabel k},
          if hk : D.restrLab k.1 = γ then
            v (.inr (cuspTheta1 D γ k hk)) • Rfix.mulVec (eB D γ (.inr (cuspTheta1 D γ k hk))) +
            v (.inr (cuspTheta2 D γ k hk)) • Rfix.mulVec (eB D γ (.inr (cuspTheta2 D γ k hk)))
          else 0) := by abel
    _ = _ := by rw [hfix_sum, hps_sum, hcusp_sum]

private lemma dite_zero_self {P : Prop} [Decidable P] :
    (if _ : P then (0 : ℂ) else 0) = 0 := by
  split_ifs <;> rfl

private lemma dite_zero_apply {α β : Type*} [Zero β] (P : Prop) [Decidable P]
    (f : P → α → β) (a : α) :
    (if h : P then f h else 0) a = if h : P then f h a else 0 := by
  split_ifs <;> rfl

private lemma ite_zero_apply {α β : Type*} [Zero β] (P : Prop) [Decidable P]
    (f : α → β) (a : α) :
    (if P then f else 0) a = if P then f a else 0 := by
  split_ifs <;> rfl

private lemma sum_mul_ite_eq {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℂ) (a : α) (c : ℂ) :
    ∑ x : α, f x * (if x = a then c else 0) = f a * c := by
  have h : ∀ x : α, f x * (if x = a then c else 0) = if x = a then f a * c else 0 := by
    intro x; split_ifs with hx <;> simp [hx]
  simp_rw [h]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma Rfix_mulVec_of_symm_apply_det (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (v : BranchOut D γ → ℂ)
    (hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2))
    (hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)))
    (δ : D.Lab) :
    Rfix.mulVec v (.inl (.inl δ)) =
      if hδ : 2 * δ = γ then
        (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inl δ) -
        (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ hδ))
      else 0 := by
  rw [Rfix_mulVec_of_symm D hq γ U Rfix hRfix v hsym_lab hsym_cusp]
  simp only [Pi.add_apply, Finset.sum_apply, dite_zero_apply, ite_zero_apply, Pi.smul_apply,
    smul_eq_mul, eO_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, mul_one,
    mul_zero, zero_add, add_zero, ite_self, dite_zero_self, Finset.sum_const_zero]
  have hterm : ∀ δ' : D.Lab,
      (if hδ : 2 * δ' = γ then
        ((Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inl δ') -
         (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ' hδ))) *
          (if δ = δ' then 1 else 0)
      else 0) =
      if δ = δ' then
        if hδ : 2 * δ' = γ then
          (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inl δ') -
          (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ' hδ))
        else 0
      else 0 := by
    intro δ'; split_ifs <;> simp
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private lemma Rfix_mulVec_of_symm_apply_st (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (v : BranchOut D γ → ℂ)
    (hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2))
    (hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)))
    (δ : D.Lab) :
    Rfix.mulVec v (.inl (.inr (.inl δ))) =
      if hδ : 2 * δ = γ then
        (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inl δ) +
        (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ hδ))
      else 0 := by
  rw [Rfix_mulVec_of_symm D hq γ U Rfix hRfix v hsym_lab hsym_cusp]
  simp only [Pi.add_apply, Finset.sum_apply, dite_zero_apply, ite_zero_apply, Pi.smul_apply,
    smul_eq_mul, eO_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, mul_one,
    mul_zero, zero_add, add_zero, ite_self, dite_zero_self, Finset.sum_const_zero]
  have hterm : ∀ δ' : D.Lab,
      (if hδ : 2 * δ' = γ then
        ((Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inl δ') +
         (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ' hδ))) *
          (if δ = δ' then 1 else 0)
      else 0) =
      if δ = δ' then
        if hδ : 2 * δ' = γ then
          (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * v (.inl δ') +
          (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * v (.inr (fixedTheta D γ δ' hδ))
        else 0
      else 0 := by
    intro δ'; split_ifs <;> simp
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private lemma Rfix_mulVec_of_symm_apply_ps (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (v : BranchOut D γ → ℂ)
    (hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2))
    (hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)))
    (ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}) :
    Rfix.mulVec v (.inl (.inr (.inr (.inl ab)))) =
      if ab.1.1 + ab.1.2 = γ then (Real.sqrt 2 : ℂ) * v (.inl ab.1.1) else 0 := by
  rw [Rfix_mulVec_of_symm D hq γ U Rfix hRfix v hsym_lab hsym_cusp]
  simp only [Pi.add_apply, Finset.sum_apply, dite_zero_apply, ite_zero_apply, Pi.smul_apply,
    smul_eq_mul, eO_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, mul_one,
    mul_zero, zero_add, add_zero, ite_self, dite_zero_self, Finset.sum_const_zero]
  have hterm : ∀ ab' : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      (if ab'.1.1 + ab'.1.2 = γ then
        (Real.sqrt 2 : ℂ) * v (.inl ab'.1.1) * (if ab = ab' then 1 else 0)
      else 0) =
      if ab = ab' then
        if ab'.1.1 + ab'.1.2 = γ then (Real.sqrt 2 : ℂ) * v (.inl ab'.1.1) else 0
      else 0 := by
    intro ab'; split_ifs <;> simp
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private lemma Rfix_mulVec_of_symm_apply_cusp (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (v : BranchOut D γ → ℂ)
    (hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2))
    (hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)))
    (k : {k : D.Lab2 // D.IsCuspLabel k}) :
    Rfix.mulVec v (.inl (.inr (.inr (.inr k)))) =
      if hk : D.restrLab k.1 = γ then
        (Real.sqrt 2 : ℂ) * v (.inr (cuspTheta1 D γ k hk))
      else 0 := by
  rw [Rfix_mulVec_of_symm D hq γ U Rfix hRfix v hsym_lab hsym_cusp]
  simp only [Pi.add_apply, Finset.sum_apply, dite_zero_apply, ite_zero_apply, Pi.smul_apply,
    smul_eq_mul, eO_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ↓reduceIte, mul_one,
    mul_zero, zero_add, add_zero, ite_self, dite_zero_self, Finset.sum_const_zero]
  have hterm : ∀ k' : {k : D.Lab2 // D.IsCuspLabel k},
      (if hk : D.restrLab k'.1 = γ then
        (Real.sqrt 2 : ℂ) * v (.inr (cuspTheta1 D γ k' hk)) * (if k = k' then 1 else 0)
      else 0) =
      if k = k' then
        if hk : D.restrLab k'.1 = γ then (Real.sqrt 2 : ℂ) * v (.inr (cuspTheta1 D γ k' hk)) else 0
      else 0 := by
    intro k'; split_ifs <;> simp
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

private lemma Rfix_mulVec_of_symm_apply_inr (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (v : BranchOut D γ → ℂ)
    (hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2))
    (hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)))
    (u : U) :
    Rfix.mulVec v (.inr u) = 0 := by
  rw [Rfix_mulVec_of_symm D hq γ U Rfix hRfix v hsym_lab hsym_cusp]
  simp only [Pi.add_apply, Finset.sum_apply, dite_zero_apply, ite_zero_apply, Pi.smul_apply,
    smul_eq_mul, eO_apply, reduceCtorEq, ↓reduceIte, mul_zero, add_zero, zero_add,
    ite_self, dite_zero_self, Finset.sum_const_zero]

private lemma Bgate_FxDag_none (D : FieldData) (γ : D.Lab) (br : Bool × D.Fq2) :
    (Bgate D γ * FxDag D) br none = if br.2 = 1 then isqrt 2 else 0 := by
  simp only [Matrix.mul_apply]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
  have hrest : ∑ t ∈ Finset.univ.erase (0 : D.Fq), Bgate D γ br t * FxDag D t none = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    simp [FxDag, Finset.ne_of_mem_erase ht]
  rw [hrest, add_zero]
  simp [Bgate, FxDag]

private lemma Mbr_Bgate_FxDag_none (D : FieldData) (γ : D.Lab)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (o : BranchOut D γ) :
    (Mbr * (Bgate D γ * FxDag D)) o none =
      match o with
      | .inl _ => isqrt 2 * isqrt (D.q - 1)
      | .inr _ => isqrt 2 * isqrt (D.q + 1) := by
  rw [Matrix.mul_apply]
  simp_rw [Bgate_FxDag_none]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  dsimp only
  simp_rw [sum_mul_ite_eq]
  rcases o with κ | θ
  · have hm : Mbr (.inl κ) (true, 1) = 0 := hMbr.2 1 one_ne_zero (one_pow _) (.inl κ)
    have hp : Mbr (.inl κ) (false, 1) = isqrt (D.q - 1) := by
      have h1 := hMbr.1 1 one_ne_zero (.inl κ)
      rw [map_one] at h1
      simpa [chi_one_right] using h1
    rw [hm, hp, zero_mul, zero_add, mul_comm]
  · have hp : Mbr (.inr θ) (false, 1) = 0 := by
      have h1 := hMbr.1 1 one_ne_zero (.inr θ)
      rw [map_one] at h1
      exact h1
    have hm : Mbr (.inr θ) (true, 1) = isqrt (D.q + 1) := by
      have h1 := hMbr.2 1 one_ne_zero (one_pow _) (.inr θ)
      have hk : D.restrLab (θ.1 - theta0Lab D γ) = 0 := by
        rw [restrLab_sub, θ.2, restrLab_theta0, sub_self]
      simpa [kerChar_one D hk] using h1
    rw [hm, hp, zero_mul, add_zero, mul_comm]

private lemma T_col_none (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (o : D.Irr ⊕ U) :
    (Rfix * Mbr * Bgate D γ * FxDag D) o none = AGammaExt D γ U o none := by
  have hT : (Rfix * Mbr * Bgate D γ * FxDag D) o none =
      Rfix.mulVec (fun b => (Mbr * (Bgate D γ * FxDag D)) b none) o := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hT]
  set v : BranchOut D γ → ℂ := fun b => (Mbr * (Bgate D γ * FxDag D)) b none
  have hv_inl : ∀ κ : D.Lab, v (.inl κ) = isqrt 2 * isqrt (D.q - 1) :=
    fun κ => Mbr_Bgate_FxDag_none D γ Mbr hMbr (.inl κ)
  have hv_inr : ∀ θ : {θ : D.Lab2 // D.restrLab θ = γ}, v (.inr θ) = isqrt 2 * isqrt (D.q + 1) :=
    fun θ => Mbr_Bgate_FxDag_none D γ Mbr hMbr (.inr θ)
  have hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2) := by
    intro ab _; rw [hv_inl, hv_inl]
  have hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)) := by
    intro k hk; rw [hv_inr, hv_inr]
  rcases o with μ | u
  · rcases μ with δ | δ | ab | k
    · rw [Rfix_mulVec_of_symm_apply_det D hq γ U Rfix hRfix v hsym_lab hsym_cusp δ]
      simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
      split_ifs with hδ
      · rw [hv_inl, hv_inr, det_none_coeff D hq]
      · rfl
    · rw [Rfix_mulVec_of_symm_apply_st D hq γ U Rfix hRfix v hsym_lab hsym_cusp δ]
      simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
      split_ifs with hδ
      · rw [hv_inl, hv_inr, St_none_coeff D hq]
      · rfl
    · rw [Rfix_mulVec_of_symm_apply_ps D hq γ U Rfix hRfix v hsym_lab hsym_cusp ab]
      simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
      split_ifs with hab
      · rw [hv_inl, ← mul_assoc, sqrt_two_mul_isqrt_two, one_mul]
      · rfl
    · rw [Rfix_mulVec_of_symm_apply_cusp D hq γ U Rfix hRfix v hsym_lab hsym_cusp k]
      simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
      split_ifs with hk
      · rw [hv_inr, ← mul_assoc, sqrt_two_mul_isqrt_two, one_mul]
      · rfl
  · rw [Rfix_mulVec_of_symm_apply_inr D hq γ U Rfix hRfix v hsym_lab hsym_cusp u]
    simp [AGammaExt]

private lemma Bgate_FxDag_some (D : FieldData) (γ α : D.Lab) (br : Bool × D.Fq2) :
    (Bgate D γ * FxDag D) br (some α) =
      isqrt (D.q - 1) * isqrt 2 *
        if br.1 then
          -∑ z ∈ Z_all D,
            if br.2 = z / z ^ D.q then D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z) else 0
        else
          ∑ x ∈ X_all D,
            if br.2 = algebraMap D.Fq D.Fq2 (x / (1 - x)) then
              D.chi γ (1 - x) * D.chi (-α) (x * (1 - x))
            else 0 := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq))]
  have h0 : Bgate D γ br 0 * FxDag D 0 (some α) = 0 := by simp [FxDag]
  rw [h0, zero_add]
  have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun t : D.Fq => t ≠ 0) := by
    ext t; simp [Finset.mem_erase]
  rw [hfilt]
  have hfx : ∀ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0),
      Bgate D γ br t * FxDag D t (some α) =
      isqrt (D.q - 1) * (Bgate D γ br t * D.chi (-α) t) := by
    intro t ht
    have ht0 : t ≠ 0 := (Finset.mem_filter.mp ht).2
    simp only [FxDag, Matrix.of_apply, if_neg ht0]
    rw [← RCLike.star_def, ← chi_neg_lab]
    ring
  rw [Finset.sum_congr rfl hfx, ← Finset.mul_sum]
  let T2 := Finset.univ.filter (B_T2 D)
  let T3 := Finset.univ.filter (B_T3 D)
  let T4 := Finset.univ.filter (B_T4 D)
  have h23 : Disjoint T2 T3 := Finset.disjoint_filter.mpr (fun _ _ h2 h3 => h3.2.1 h2)
  have h24 : Disjoint T2 T4 := Finset.disjoint_filter.mpr (fun _ _ h2 h4 => h4.2.1 h2)
  have h34 : Disjoint T3 T4 := Finset.disjoint_filter.mpr (fun _ _ h3 h4 => h4.2.2 h3.2.2)
  have hpart : Finset.univ.filter (fun t : D.Fq => t ≠ 0) = (T2 ∪ T3) ∪ T4 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, T2, T3, T4]
    constructor
    · intro ht0
      by_cases h2 : B_T2 D t
      · exact Or.inl (Or.inl h2)
      · by_cases h3 : ∃ x : D.Fq, x ^ 2 - x + t = 0
        · exact Or.inl (Or.inr ⟨ht0, h2, h3⟩)
        · exact Or.inr ⟨ht0, h2, h3⟩
    · rintro ((h2 | h3) | h4)
      · rcases h2 with ⟨hc, rfl⟩; exact inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
      · exact h3.1
      · exact h4.1
  rw [hpart, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨h24, h34⟩), Finset.sum_union h23]
  cases hbr1 : br.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hT4_zero : ∑ t ∈ T4, Bgate D γ br t * D.chi (-α) t = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      have ht4 := (Finset.mem_filter.mp ht).2
      have ht1 : t ≠ 0 := ht4.1
      have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht4.2.1
      have ht3 : ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0 := ht4.2.2
      simp only [Bgate, Matrix.of_apply]
      rw [if_neg ht1, if_neg ht2, if_neg ht3, hbr1]
      simp
    have hT3_val : ∑ t ∈ T3, Bgate D γ br t * D.chi (-α) t =
        isqrt 2 * ∑ x ∈ S_nb D,
          if br.2 = algebraMap D.Fq D.Fq2 (x / (1 - x)) then
            D.chi γ (1 - x) * D.chi (-α) (x * (1 - x)) else 0 := by
      have hcongr : ∑ t ∈ T3, Bgate D γ br t * D.chi (-α) t =
          ∑ t ∈ T3, isqrt 2 * ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ^ 2 - x + t = 0),
            if br.2 = algebraMap D.Fq D.Fq2 (x / (1 - x)) then
              D.chi γ (1 - x) * D.chi (-α) (x * (1 - x)) else 0 := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have ht3 := (Finset.mem_filter.mp ht).2
        have ht1 : t ≠ 0 := ht3.1
        have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht3.2.1
        have htx : ∃ x : D.Fq, x ^ 2 - x + t = 0 := ht3.2.2
        simp only [Bgate, Matrix.of_apply]
        rw [if_neg ht1, if_neg ht2, if_pos htx, hbr1, if_neg Bool.false_ne_true, mul_assoc,
          Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxeq : x * (1 - x) = t := by linear_combination -(Finset.mem_filter.mp hx).2
        split_ifs with hb
        · rw [hxeq]
        · rw [zero_mul]
      rw [hcongr, ← Finset.mul_sum, sum_T3_roots]
    rw [hT4_zero, add_zero, hT3_val]
    have hxsplit := X_all_eq_split D
    by_cases hc : ringChar D.Fq ≠ 2
    · rw [if_pos hc] at hxsplit
      have h2 : (2 : D.Fq) ≠ 0 := mt (fq_two_eq_zero_iff D).mp hc
      have h12 : 1 - (2 : D.Fq)⁻¹ = (2 : D.Fq)⁻¹ := by
        apply mul_left_cancel₀ h2; rw [mul_sub, mul_one, mul_inv_cancel₀ h2]; ring
      have hdiv2 : (2 : D.Fq)⁻¹ / (1 - (2 : D.Fq)⁻¹) = 1 := by
        rw [h12, div_self (inv_ne_zero h2)]
      have hmul2 : (2 : D.Fq)⁻¹ * (1 - (2 : D.Fq)⁻¹) = (4 : D.Fq)⁻¹ := by
        have h4 : (4 : D.Fq) = 2 * 2 := by norm_num
        rw [h12, h4, field_mul_inv]
      have hT2_eq : T2 = {(4 : D.Fq)⁻¹} := by
        ext t; simp [T2, B_T2, hc]
      rw [hT2_eq, Finset.sum_singleton]
      have hB2 : Bgate D γ br (4 : D.Fq)⁻¹ * D.chi (-α) (4 : D.Fq)⁻¹ =
          isqrt 2 * (if br.2 = algebraMap D.Fq D.Fq2 ((2 : D.Fq)⁻¹ / (1 - (2 : D.Fq)⁻¹)) then
            D.chi γ (1 - (2 : D.Fq)⁻¹) * D.chi (-α) ((2 : D.Fq)⁻¹ * (1 - (2 : D.Fq)⁻¹)) else 0) := by
        have ht40 : (4 : D.Fq)⁻¹ ≠ 0 := inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        simp only [Bgate, Matrix.of_apply]
        rw [if_neg ht40]
        simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hbr1, Bool.false_eq_true]
        rw [hdiv2, map_one, hmul2, h12]
        split_ifs <;> ring
      rw [hB2, ← mul_add, ← hxsplit.1, Finset.sum_insert hxsplit.2]
      ring
    · rw [if_neg hc] at hxsplit
      have hT2_eq : T2 = ∅ := by
        ext t; simp [T2, B_T2, hc]
      rw [hT2_eq, Finset.sum_empty, zero_add, hxsplit]
      ring
  · simp only [↓reduceIte]
    have hT3_zero : ∑ t ∈ T3, Bgate D γ br t * D.chi (-α) t = 0 := by
      refine Finset.sum_eq_zero fun t ht => ?_
      have ht3 := (Finset.mem_filter.mp ht).2
      have ht1 : t ≠ 0 := ht3.1
      have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht3.2.1
      have ht3x : ∃ x : D.Fq, x ^ 2 - x + t = 0 := ht3.2.2
      simp only [Bgate, Matrix.of_apply]
      rw [if_neg ht1, if_neg ht2, if_pos ht3x, hbr1]
      simp
    have hT4_val : ∑ t ∈ T4, Bgate D γ br t * D.chi (-α) t =
        -(isqrt 2 * ∑ z ∈ Z_nb D,
          if br.2 = z / z ^ D.q then D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z) else 0) := by
      have hcongr : ∑ t ∈ T4, Bgate D γ br t * D.chi (-α) t =
          -(isqrt 2 * ∑ t ∈ T4, ∑ z ∈ Finset.univ.filter
            (fun z : D.Fq2 => z ^ 2 - z + algebraMap D.Fq D.Fq2 t = 0),
              if br.2 = z / z ^ D.q then D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z) else 0) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun t ht => ?_
        have ht4 := (Finset.mem_filter.mp ht).2
        have ht1 : t ≠ 0 := ht4.1
        have ht2 : ¬ (ringChar D.Fq ≠ 2 ∧ t = (4 : D.Fq)⁻¹) := ht4.2.1
        have ht3x : ¬ ∃ x : D.Fq, x ^ 2 - x + t = 0 := ht4.2.2
        simp only [Bgate, Matrix.of_apply]
        rw [if_neg ht1, if_neg ht2, if_neg ht3x, hbr1, if_pos rfl, neg_mul, mul_assoc,
          Finset.sum_mul]
        congr 1
        congr 1
        refine Finset.sum_congr rfl fun z hz => ?_
        have hnrm : D.nrm z = t := ((B_T4_root_iff D ht4 z).mp (Finset.mem_filter.mp hz).2).2
        split_ifs with hb
        · rw [hnrm]
        · rw [zero_mul]
      rw [hcongr, sum_T4_roots]
    rw [hT3_zero, add_zero, hT4_val]
    have hzsplit := Z_all_eq_split D
    by_cases hc : ringChar D.Fq ≠ 2
    · rw [if_pos hc] at hzsplit
      have h2' : (2 : D.Fq2) ≠ 0 := fq2_two_ne_zero D hc
      have hpow2 : ((2 : D.Fq2)⁻¹) ^ D.q = (2 : D.Fq2)⁻¹ :=
        (fq2_pow_q_eq_self_iff D _).mpr ⟨(2 : D.Fq)⁻¹, algebraMap_two_inv D hc⟩
      have hdiv2 : (2 : D.Fq2)⁻¹ / ((2 : D.Fq2)⁻¹) ^ D.q = 1 := by
        rw [hpow2, div_self (inv_ne_zero h2')]
      have hnrm2 : D.nrm (2 : D.Fq2)⁻¹ = (4 : D.Fq)⁻¹ := by
        apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
        rw [algebraMap_nrm_mul, hpow2, algebraMap_four_inv D hc]
        have h4 : (4 : D.Fq2) = 2 * 2 := by norm_num
        rw [h4, field_mul_inv]
      have hth2 : D.theta (theta0Lab D γ) (2 : D.Fq2)⁻¹ = D.chi γ (2 : D.Fq)⁻¹ := by
        rw [← algebraMap_two_inv D hc, theta_algebraMap, restrLab_theta0]
      have hT2_eq : T2 = {(4 : D.Fq)⁻¹} := by
        ext t; simp [T2, B_T2, hc]
      rw [hT2_eq, Finset.sum_singleton]
      have hB2 : Bgate D γ br (4 : D.Fq)⁻¹ * D.chi (-α) (4 : D.Fq)⁻¹ =
          -(isqrt 2 * (if br.2 = (2 : D.Fq2)⁻¹ / ((2 : D.Fq2)⁻¹) ^ D.q then
            D.theta (theta0Lab D γ) (2 : D.Fq2)⁻¹ * D.chi (-α) (D.nrm (2 : D.Fq2)⁻¹) else 0)) := by
        have ht40 : (4 : D.Fq)⁻¹ ≠ 0 := inv_ne_zero (mt (fq_four_eq_zero_iff D).mp hc)
        simp only [Bgate, Matrix.of_apply]
        rw [if_neg ht40]
        simp only [hc, ne_eq, not_false_eq_true, and_self, ↓reduceIte, hbr1, hdiv2, hth2, hnrm2]
        split_ifs <;> ring
      rw [hB2, ← hzsplit.1, Finset.sum_insert hzsplit.2]
      ring
    · rw [if_neg hc] at hzsplit
      have hT2_eq : T2 = ∅ := by
        ext t; simp [T2, B_T2, hc]
      rw [hT2_eq, Finset.sum_empty, zero_add, hzsplit]
      ring

private def S1 (D : FieldData) (θ : D.Lab2) (α : D.Lab) : ℂ :=
  ∑ z ∈ Z_all D, D.theta θ z * D.chi (-α) (D.nrm z)

private lemma tr_ne_zero_implies_ne_zero (D : FieldData) {z : D.Fq2} (htr : D.tr z = 1) :
    z ≠ 0 := by
  intro h0
  rw [h0, show D.tr 0 = 0 from by simp [FieldData.tr]] at htr
  exact zero_ne_one htr

private lemma div_pow_q_mem_dom (D : FieldData) {z : D.Fq2} (hz0 : z ≠ 0) :
    z / z ^ D.q ≠ 0 ∧ (z / z ^ D.q) ^ (D.q + 1) = 1 := by
  have hzq : z ^ D.q ≠ 0 := fq2_pow_ne_zero D hz0 D.q
  refine ⟨div_ne_zero hz0 hzq, ?_⟩
  rw [field_div_pow, field_div_eq_one_iff_eq (fq2_pow_ne_zero D hzq (D.q + 1))]
  calc z ^ (D.q + 1) = z * z ^ D.q := pow_succ' z D.q
    _ = z ^ (D.q ^ 2) * z ^ D.q := by rw [fq2_pow_q_sq]
    _ = z ^ (D.q ^ 2 + D.q) := (pow_add z _ _).symm
    _ = (z ^ D.q) ^ (D.q + 1) := by rw [← pow_mul, show D.q * (D.q + 1) = D.q ^ 2 + D.q from by ring]

private lemma sum_mbr_mul_sum_ite (D : FieldData) {ι : Type*} (s : Finset ι)
    (m : D.Fq2 → ℂ) (c : ℂ) (g : ι → D.Fq2) (f : ι → ℂ) :
    ∑ w : D.Fq2, m w * (c * ∑ i ∈ s, if w = g i then f i else 0) =
      c * ∑ i ∈ s, m (g i) * f i := by
  have h1 : ∀ w : D.Fq2, m w * (c * ∑ i ∈ s, if w = g i then f i else 0) =
      c * ∑ i ∈ s, (if w = g i then m w * f i else 0) := by
    intro w
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  simp_rw [h1, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ∀ w : D.Fq2, (if w = g i then m w * f i else 0) =
      if w = g i then m (g i) * f i else 0 := fun w => by
    split_ifs with hw <;> simp [hw]
  simp_rw [h2]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma Mbr_Bgate_FxDag_some (D : FieldData) (γ α : D.Lab)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (o : BranchOut D γ) :
    (Mbr * (Bgate D γ * FxDag D)) o (some α) =
      match o with
      | .inl κ => ((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (κ - α) (γ - α - κ)
      | .inr θ => -(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * S1 D θ.1 α) := by
  rw [Matrix.mul_apply]
  simp_rw [Bgate_FxDag_some]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  dsimp only
  simp only [Bool.false_eq_true, ↓reduceIte]
  rcases o with κ | θ
  · have ht : ∑ w : D.Fq2, Mbr (.inl κ) (true, w) *
        (isqrt (D.q - 1) * isqrt 2 * -∑ z ∈ Z_all D,
          if w = z / z ^ D.q then D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z) else 0) = 0 := by
      simp_rw [mul_neg, Finset.sum_neg_distrib,
        sum_mbr_mul_sum_ite D (Z_all D) (fun w => Mbr (.inl κ) (true, w))
          (isqrt (D.q - 1) * isqrt 2) (fun z => z / z ^ D.q)
          (fun z => D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z))]
      have hz_zero : ∀ z ∈ Z_all D,
          Mbr (.inl κ) (true, z / z ^ D.q) *
            (D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z)) = 0 := by
        intro z hz
        have hz0 : z ≠ 0 := tr_ne_zero_implies_ne_zero D (Finset.mem_filter.mp hz).2
        obtain ⟨hw0, hw1⟩ := div_pow_q_mem_dom D hz0
        rw [hMbr.2 (z / z ^ D.q) hw0 hw1 (.inl κ), zero_mul]
      rw [Finset.sum_eq_zero hz_zero, mul_zero, neg_zero]
    have hf : ∑ w : D.Fq2, Mbr (.inl κ) (false, w) *
        (isqrt (D.q - 1) * isqrt 2 * ∑ x ∈ X_all D,
          if w = algebraMap D.Fq D.Fq2 (x / (1 - x)) then
            D.chi γ (1 - x) * D.chi (-α) (x * (1 - x)) else 0) =
        ((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (κ - α) (γ - α - κ) := by
      rw [sum_mbr_mul_sum_ite D (X_all D) (fun w => Mbr (.inl κ) (false, w))
        (isqrt (D.q - 1) * isqrt 2) (fun x => algebraMap D.Fq D.Fq2 (x / (1 - x)))
        (fun x => D.chi γ (1 - x) * D.chi (-α) (x * (1 - x)))]
      have hx_term : ∀ x ∈ X_all D,
          Mbr (.inl κ) (false, algebraMap D.Fq D.Fq2 (x / (1 - x))) *
            (D.chi γ (1 - x) * D.chi (-α) (x * (1 - x))) =
          isqrt (D.q - 1) * (D.chi (κ - α) x * D.chi (γ - α - κ) (1 - x)) := by
        intro x hx
        have hx01 := (Finset.mem_filter.mp hx).2
        have hrx : x / (1 - x) ≠ 0 := div_ne_zero hx01.1 (sub_ne_zero.mpr hx01.2.symm)
        rw [hMbr.1 (x / (1 - x)) hrx (.inl κ)]
        dsimp only
        rw [chi_div, chi_mul]
        have h1 : D.chi κ x * D.chi (-α) x = D.chi (κ - α) x := by
          rw [← chi_add_lab, sub_eq_add_neg]
        have h2 : D.chi (-κ) (1 - x) * D.chi γ (1 - x) * D.chi (-α) (1 - x) =
            D.chi (γ - α - κ) (1 - x) := by
          rw [← chi_add_lab, ← chi_add_lab]
          congr 1; ring
        calc isqrt (D.q - 1) * (D.chi κ x * D.chi (-κ) (1 - x)) *
              (D.chi γ (1 - x) * (D.chi (-α) x * D.chi (-α) (1 - x)))
            = isqrt (D.q - 1) * ((D.chi κ x * D.chi (-α) x) *
                (D.chi (-κ) (1 - x) * D.chi γ (1 - x) * D.chi (-α) (1 - x))) := by ring
          _ = isqrt (D.q - 1) * (D.chi (κ - α) x * D.chi (γ - α - κ) (1 - x)) := by rw [h1, h2]
      rw [Finset.sum_congr rfl hx_term, ← Finset.mul_sum]
      calc isqrt (D.q - 1) * isqrt 2 * (isqrt (D.q - 1) * ∑ x ∈ X_all D,
            D.chi (κ - α) x * D.chi (γ - α - κ) (1 - x))
          = (isqrt (D.q - 1) * isqrt (D.q - 1)) * isqrt 2 * D.jacobi (κ - α) (γ - α - κ) := by
              simp only [FieldData.jacobi, X_all]; ring
        _ = ((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (κ - α) (γ - α - κ) := by
              rw [isqrt_q_sub_one_sq]
    rw [ht, zero_add, hf]
  · have hf : ∑ w : D.Fq2, Mbr (.inr θ) (false, w) *
        (isqrt (D.q - 1) * isqrt 2 * ∑ x ∈ X_all D,
          if w = algebraMap D.Fq D.Fq2 (x / (1 - x)) then
            D.chi γ (1 - x) * D.chi (-α) (x * (1 - x)) else 0) = 0 := by
      rw [sum_mbr_mul_sum_ite D (X_all D) (fun w => Mbr (.inr θ) (false, w))
        (isqrt (D.q - 1) * isqrt 2) (fun x => algebraMap D.Fq D.Fq2 (x / (1 - x)))
        (fun x => D.chi γ (1 - x) * D.chi (-α) (x * (1 - x)))]
      have hx_zero : ∀ x ∈ X_all D,
          Mbr (.inr θ) (false, algebraMap D.Fq D.Fq2 (x / (1 - x))) *
            (D.chi γ (1 - x) * D.chi (-α) (x * (1 - x))) = 0 := by
        intro x hx
        have hx01 := (Finset.mem_filter.mp hx).2
        rw [hMbr.1 (x / (1 - x)) (div_ne_zero hx01.1 (sub_ne_zero.mpr hx01.2.symm)) (.inr θ), zero_mul]
      rw [Finset.sum_eq_zero hx_zero, mul_zero]
    have ht : ∑ w : D.Fq2, Mbr (.inr θ) (true, w) *
        (isqrt (D.q - 1) * isqrt 2 * -∑ z ∈ Z_all D,
          if w = z / z ^ D.q then D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z) else 0) =
        -(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * S1 D θ.1 α) := by
      simp_rw [mul_neg, Finset.sum_neg_distrib,
        sum_mbr_mul_sum_ite D (Z_all D) (fun w => Mbr (.inr θ) (true, w))
          (isqrt (D.q - 1) * isqrt 2) (fun z => z / z ^ D.q)
          (fun z => D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z))]
      have hz_term : ∀ z ∈ Z_all D,
          Mbr (.inr θ) (true, z / z ^ D.q) *
            (D.theta (theta0Lab D γ) z * D.chi (-α) (D.nrm z)) =
          isqrt (D.q + 1) * (D.theta θ.1 z * D.chi (-α) (D.nrm z)) := by
        intro z hz
        have hz0 : z ≠ 0 := tr_ne_zero_implies_ne_zero D (Finset.mem_filter.mp hz).2
        obtain ⟨hw0, hw1⟩ := div_pow_q_mem_dom D hz0
        rw [hMbr.2 (z / z ^ D.q) hw0 hw1 (.inr θ)]
        dsimp only
        rw [mul_assoc, ← mul_assoc (kerChar _ _ _),
          mul_comm (kerChar _ _ _) (D.theta (theta0Lab D γ) z), kerChar_mul_theta0 D γ θ hz0]
      rw [Finset.sum_congr rfl hz_term, ← Finset.mul_sum]
      simp only [S1]
      ring
    rw [hf, add_zero, ht]

private lemma tr_pow_q (D : FieldData) (z : D.Fq2) : D.tr (z ^ D.q) = D.tr z := by
  apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
  rw [algebraMap_tr, algebraMap_tr, ← pow_mul, ← sq, fq2_pow_q_sq, add_comm]

private lemma nrm_pow_q (D : FieldData) (z : D.Fq2) : D.nrm (z ^ D.q) = D.nrm z := by
  apply FaithfulSMul.algebraMap_injective D.Fq D.Fq2
  rw [algebraMap_nrm_mul, algebraMap_nrm_mul, ← pow_mul, ← sq, fq2_pow_q_sq, mul_comm]

private lemma nrm_ne_zero_of_ne_zero (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) :
    D.nrm z ≠ 0 := by
  intro h0
  have h1 : z ^ (D.q + 1) = 0 := by rw [← algebraMap_nrm, h0, map_zero]
  exact hz (field_pow_eq_zero h1)

private lemma S1_mul_q (D : FieldData) (k : D.Lab2) (α : D.Lab) :
    S1 D ((D.q : D.Lab2) * k) α = S1 D k α := by
  simp only [S1]
  refine Finset.sum_bij (fun z _ => z ^ D.q) ?_ ?_ ?_ ?_
  · intro z hz
    rw [Z_all, Finset.mem_filter] at hz ⊢
    exact ⟨Finset.mem_univ _, by rw [tr_pow_q, hz.2]⟩
  · intro z₁ _ z₂ _ heq
    have h1 := congrArg (fun x : D.Fq2 => x ^ D.q) heq
    rw [← pow_mul, ← pow_mul, ← sq, fq2_pow_q_sq, fq2_pow_q_sq] at h1
    exact h1
  · intro w hw
    rw [Z_all, Finset.mem_filter] at hw
    refine ⟨w ^ D.q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [tr_pow_q, hw.2]⟩, ?_⟩
    rw [← pow_mul, ← sq, fq2_pow_q_sq]
  · intro z _
    rw [theta_pow_q, nrm_pow_q]

private lemma S1_fixed (D : FieldData) (δ α : D.Lab) :
    S1 D (((D.q + 1) * δ.val : ℕ) : D.Lab2) α = ∑ z ∈ Z_all D, D.chi (δ - α) (D.nrm z) := by
  simp only [S1]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [theta_mul_q_add_one, ← chi_add_lab, sub_eq_add_neg]

private lemma jacobi_zero_zero (D : FieldData) (hq : 2 < D.q) :
    D.jacobi 0 0 = (D.q : ℂ) - 2 := by
  simp only [FieldData.jacobi]
  have hterm : ∀ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1),
      D.chi 0 x * D.chi 0 (1 - x) = 1 := by
    intro x hx
    have hx01 := (Finset.mem_filter.mp hx).2
    rw [chi_zero_left D hx01.1, chi_zero_left D (sub_ne_zero.mpr hx01.2.symm), mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hfilt : Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1) =
      Finset.univ \ ({0, 1} : Finset D.Fq) := by
    ext x; simp
  rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_fq,
    Finset.card_pair (zero_ne_one : (0 : D.Fq) ≠ 1)]
  rw [Nat.cast_sub (by omega), Nat.cast_two]

private lemma T_col_some (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (α : D.Lab) (o : D.Irr ⊕ U) :
    (Rfix * Mbr * Bgate D γ * FxDag D) o (some α) =
      match o with
      | .inl (.inl δ) =>
          if 2 * δ = γ ∧ δ = α then (Real.sqrt (((D.q : ℝ) - 1) / D.q) : ℂ) else 0
      | .inl (.inr (.inl δ)) =>
          if 2 * δ = γ then
            if δ = α then -(isqrt D.q * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1))
            else (Real.sqrt D.q : ℂ) * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1) * D.jacobi (δ - α) (δ - α)
          else 0
      | .inl (.inr (.inr (.inl ab))) =>
          if ab.1.1 + ab.1.2 = γ then
            ((D.q : ℂ) - 1)⁻¹ * D.jacobi (ab.1.1 - α) (ab.1.2 - α)
          else 0
      | .inl (.inr (.inr (.inr k))) =>
          if D.restrLab k.1 = γ then
            -(isqrt (D.q - 1) * isqrt (D.q + 1) * S1 D k.1 α)
          else 0
      | .inr _ => 0 := by
  have hT : (Rfix * Mbr * Bgate D γ * FxDag D) o (some α) =
      Rfix.mulVec (fun b => (Mbr * (Bgate D γ * FxDag D)) b (some α)) o := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hT]
  set v : BranchOut D γ → ℂ := fun b => (Mbr * (Bgate D γ * FxDag D)) b (some α)
  have hv_inl : ∀ κ : D.Lab, v (.inl κ) = ((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (κ - α) (γ - α - κ) :=
    fun κ => Mbr_Bgate_FxDag_some D γ α Mbr hMbr (.inl κ)
  have hv_inr : ∀ θ : {θ : D.Lab2 // D.restrLab θ = γ},
      v (.inr θ) = -(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * S1 D θ.1 α) :=
    fun θ => Mbr_Bgate_FxDag_some D γ α Mbr hMbr (.inr θ)
  have hsym_lab : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      ab.1.1 + ab.1.2 = γ → v (.inl ab.1.1) = v (.inl ab.1.2) := by
    intro ab hab
    rw [hv_inl, hv_inl]
    have h1 : γ - α - ab.1.1 = ab.1.2 - α := by linear_combination -hab
    have h2 : γ - α - ab.1.2 = ab.1.1 - α := by linear_combination -hab
    rw [h1, h2, jacobi_symm]
  have hsym_cusp : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
      (hk : D.restrLab k.1 = γ) →
        v (.inr (cuspTheta1 D γ k hk)) = v (.inr (cuspTheta2 D γ k hk)) := by
    intro k hk
    rw [hv_inr, hv_inr]
    change -(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * S1 D k.1 α) =
      -(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * S1 D ((D.q : D.Lab2) * k.1) α)
    rw [S1_mul_q]
  have hS1_eq : ∀ (δ : D.Lab) (hδ : 2 * δ = γ), δ = α →
      S1 D (fixedTheta D γ δ hδ).1 α = (D.q : ℂ) := by
    intro δ hδ hδα
    dsimp only [fixedTheta]
    rw [S1_fixed, hδα, sub_self]
    have hterm : ∀ z ∈ Z_all D, D.chi 0 (D.nrm z) = 1 := fun z hz =>
      chi_zero_left D (nrm_ne_zero_of_ne_zero D (tr_ne_zero_implies_ne_zero D (Finset.mem_filter.mp hz).2))
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    change ((Z_all D).card : ℂ) = D.q
    rw [Z_all, card_tr_eq_one]
  rcases o with μ | u
  · rcases μ with δ | δ | ab | k
    · dsimp only
      rw [Rfix_mulVec_of_symm_apply_det D hq γ U Rfix hRfix v hsym_lab hsym_cusp δ]
      by_cases hδ : 2 * δ = γ
      · rw [dif_pos hδ]
        by_cases hδα : δ = α
        · rw [if_pos ⟨hδ, hδα⟩]
          have heq : γ - α - δ = δ - α := by linear_combination -hδ
          rw [hv_inl, hv_inr, hS1_eq δ hδ hδα, heq, hδα, sub_self, jacobi_zero_zero D hq]
          exact det_some_eq_coeff D hq
        · rw [if_neg (fun h => hδα h.2)]
          have heq : γ - α - δ = δ - α := by linear_combination -hδ
          have hξ : δ - α ≠ 0 := sub_ne_zero.mpr hδα
          have hS1 : S1 D (fixedTheta D γ δ hδ).1 α = -D.jacobi (δ - α) (δ - α) := by
            dsimp only [fixedTheta]
            rw [S1_fixed]
            exact sum_tr1_chi_nrm_eq_neg_jacobi D hq hξ
          rw [hv_inl, hv_inr, hS1, heq]
          have hfac : (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (δ - α) (δ - α)) -
                (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (-(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * -D.jacobi (δ - α) (δ - α))) =
              ((Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2) -
               (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1))) * D.jacobi (δ - α) (δ - α) := by ring
          rw [hfac, det_some_neq_coeff D hq, zero_mul]
      · rw [dif_neg hδ, if_neg (fun h => hδ h.1)]
    · dsimp only
      rw [Rfix_mulVec_of_symm_apply_st D hq γ U Rfix hRfix v hsym_lab hsym_cusp δ]
      by_cases hδ : 2 * δ = γ
      · rw [dif_pos hδ, if_pos hδ]
        by_cases hδα : δ = α
        · rw [if_pos hδα]
          have heq : γ - α - δ = δ - α := by linear_combination -hδ
          rw [hv_inl, hv_inr, hS1_eq δ hδ hδα, heq, hδα, sub_self, jacobi_zero_zero D hq]
          exact St_some_eq_coeff D hq
        · rw [if_neg hδα]
          have heq : γ - α - δ = δ - α := by linear_combination -hδ
          have hξ : δ - α ≠ 0 := sub_ne_zero.mpr hδα
          have hS1 : S1 D (fixedTheta D γ δ hδ).1 α = -D.jacobi (δ - α) (δ - α) := by
            dsimp only [fixedTheta]
            rw [S1_fixed]
            exact sum_tr1_chi_nrm_eq_neg_jacobi D hq hξ
          rw [hv_inl, hv_inr, hS1, heq]
          have hfac : (Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (δ - α) (δ - α)) +
                (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (-(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * -D.jacobi (δ - α) (δ - α))) =
              ((Real.sqrt (((D.q : ℝ) + 1) / (2 * D.q)) : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2) +
               (Real.sqrt (((D.q : ℝ) - 1) / (2 * D.q)) : ℂ) * (isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1))) * D.jacobi (δ - α) (δ - α) := by ring
          rw [hfac, St_some_neq_coeff D hq]
      · rw [dif_neg hδ, if_neg hδ]
    · dsimp only
      rw [Rfix_mulVec_of_symm_apply_ps D hq γ U Rfix hRfix v hsym_lab hsym_cusp ab]
      by_cases hab : ab.1.1 + ab.1.2 = γ
      · rw [if_pos hab, if_pos hab, hv_inl]
        have heq : γ - α - ab.1.1 = ab.1.2 - α := by linear_combination -hab
        rw [heq]
        calc (Real.sqrt 2 : ℂ) * (((D.q : ℂ) - 1)⁻¹ * isqrt 2 * D.jacobi (ab.1.1 - α) (ab.1.2 - α))
            = ((Real.sqrt 2 : ℂ) * isqrt 2) * ((D.q : ℂ) - 1)⁻¹ * D.jacobi (ab.1.1 - α) (ab.1.2 - α) := by ring
          _ = ((D.q : ℂ) - 1)⁻¹ * D.jacobi (ab.1.1 - α) (ab.1.2 - α) := by
                rw [sqrt_two_mul_isqrt_two, one_mul]
      · rw [if_neg hab, if_neg hab]
    · dsimp only
      rw [Rfix_mulVec_of_symm_apply_cusp D hq γ U Rfix hRfix v hsym_lab hsym_cusp k]
      by_cases hk : D.restrLab k.1 = γ
      · rw [dif_pos hk, if_pos hk, hv_inr]
        dsimp only [cuspTheta1]
        calc (Real.sqrt 2 : ℂ) * -(isqrt (D.q - 1) * isqrt 2 * isqrt (D.q + 1) * S1 D k.1 α)
            = -(((Real.sqrt 2 : ℂ) * isqrt 2) * (isqrt (D.q - 1) * isqrt (D.q + 1) * S1 D k.1 α)) := by ring
          _ = -(isqrt (D.q - 1) * isqrt (D.q + 1) * S1 D k.1 α) := by
                rw [sqrt_two_mul_isqrt_two, one_mul]
      · rw [dif_neg hk, if_neg hk]
  · dsimp only
    exact Rfix_mulVec_of_symm_apply_inr D hq γ U Rfix hRfix v hsym_lab hsym_cusp u

private lemma cusp_shift_ne_zero (D : FieldData) (hq : 2 < D.q)
    (k : {k : D.Lab2 // D.IsCuspLabel k}) (α : D.Lab) :
    k.1 + (((D.q + 1) * (-α).val : ℕ) : D.Lab2) ≠ 0 := by
  intro h0
  set c : D.Lab2 := (((D.q + 1) * (-α).val : ℕ) : D.Lab2)
  have hc : (D.q : D.Lab2) * c = c := by
    rw [← sub_eq_zero]
    have hq1 : 1 ≤ D.q := by omega
    calc (D.q : D.Lab2) * c - c
        = ((D.q - 1 : ℕ) : D.Lab2) * c := by rw [Nat.cast_sub hq1, Nat.cast_one, sub_mul, one_mul]
      _ = (((D.q ^ 2 - 1) * (-α).val : ℕ) : D.Lab2) := by
            simp only [c, ← Nat.cast_mul]; congr 1
            rw [← mul_assoc, mul_comm (D.q - 1) (D.q + 1), ← q_sq_sub_one_eq_mul]
      _ = (((D.q ^ 2 - 1 : ℕ) : D.Lab2) * ((-α).val : D.Lab2)) := by rw [Nat.cast_mul]
      _ = 0 := by rw [ZMod.natCast_self, zero_mul]
  have hk : k.1 = -c := eq_neg_of_add_eq_zero_left h0
  have hfix : (D.q : D.Lab2) * k.1 = k.1 := by rw [hk, mul_neg, hc]
  exact k.2.1 ((lab2_fixed_iff_dvd D hq k.1).mp hfix)

private lemma S1_eq_sum_shifted (D : FieldData) (k : D.Lab2) (α : D.Lab) :
    S1 D k α = ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => D.tr z = 1),
      D.theta (k + (((D.q + 1) * (-α).val : ℕ) : D.Lab2)) z := by
  simp only [S1, Z_all]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [theta_add_lab, theta_mul_q_add_one]

private lemma gaussQ2_shifted (D : FieldData) (k : D.Lab2) (α : D.Lab) :
    D.gaussQ2 (fun z => D.theta k z * D.chi (-α) (D.nrm z)) =
      D.gaussQ2 (D.theta (k + (((D.q + 1) * (-α).val : ℕ) : D.Lab2))) := by
  simp only [FieldData.gaussQ2]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [theta_add_lab, theta_mul_q_add_one]

private lemma T_Dgate_generic (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (o : D.Irr ⊕ U) (c : Option D.Lab) (hc : ∀ α : D.Lab, c = some α → 2 * α ≠ γ) :
    ((Rfix * Mbr * Bgate D γ * FxDag D) * Dgate D γ) o c = AGammaExt D γ U o c := by
  rw [Matrix.mul_apply]
  have hcol : ∑ c' : Option D.Lab, (Rfix * Mbr * Bgate D γ * FxDag D) o c' * Dgate D γ c' c =
      (Rfix * Mbr * Bgate D γ * FxDag D) o c * Dgate D γ c c := by
    refine Finset.sum_eq_single c ?_ (fun hc0 => False.elim (hc0 (Finset.mem_univ _)))
    intro c' _ hc'
    simp only [Dgate, Matrix.diagonal_apply, if_neg hc', mul_zero]
  rw [hcol]
  cases c with
  | none =>
      have hd : Dgate D γ none none = 1 := by simp [Dgate]
      rw [hd, mul_one, T_col_none D hq γ U Rfix hRfix Mbr hMbr o]
  | some α =>
      have hα : 2 * α ≠ γ := hc α rfl
      have hne : α ≠ γ - α := fun h => hα (by linear_combination h)
      have hd : Dgate D γ (some α) (some α) =
          D.chi (γ - α) (-1) * D.gauss (γ - 2 * α) * isqrt D.q := by
        simp only [Dgate, zeta, Matrix.diagonal_apply, ↓reduceIte, if_pos hne, div_eq_mul_inv]
        have hisq : ((Real.sqrt D.q : ℂ)⁻¹) = isqrt D.q := by simp [isqrt]
        rw [hisq, show (γ - α) - α = γ - 2 * α from by ring]
      rw [hd, T_col_some D hq γ U Rfix hRfix Mbr hMbr α o]
      rcases o with μ | u
      · rcases μ with δ | δ | ab | k
        · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
          have hfalse : ¬ (2 * δ = γ ∧ δ = α) := by
            rintro ⟨h1, rfl⟩; exact hα h1
          rw [if_neg hfalse, zero_mul]
        · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
          split_ifs with hδ hδα
          · exact False.elim (hα (hδα ▸ hδ))
          · have hsum : (δ - α) + (δ - α) ≠ 0 := by
              rw [show (δ - α) + (δ - α) = 2 * δ - 2 * α from by ring, hδ]
              exact sub_ne_zero.mpr hα.symm
            have hg : D.jacobi (δ - α) (δ - α) * D.gauss (γ - 2 * α) = D.gauss (δ - α) ^ 2 := by
              have heq : (δ - α) + (δ - α) = γ - 2 * α := by
                rw [show (δ - α) + (δ - α) = 2 * δ - 2 * α from by ring, hδ]
              rw [← heq, ← gauss_mul_gauss D hq hsum, sq]
            calc (Real.sqrt D.q : ℂ) * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1) * D.jacobi (δ - α) (δ - α) *
                  (D.chi (γ - α) (-1) * D.gauss (γ - 2 * α) * isqrt D.q)
                = ((Real.sqrt D.q : ℂ) * isqrt D.q) * D.chi (γ - α) (-1) *
                    (((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1)) *
                    (D.jacobi (δ - α) (δ - α) * D.gauss (γ - 2 * α)) := by ring
              _ = D.chi (γ - α) (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1)) * D.gauss (δ - α) ^ 2 := by
                    have hsq1 : (Real.sqrt D.q : ℂ) * isqrt D.q = 1 := by
                      simp only [isqrt, Complex.ofReal_inv]
                      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast q_pos D : (0 : ℝ) < D.q)).ne')
                    rw [hsq1, one_mul, hg]
          · rw [zero_mul]
        · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
          split_ifs with hab
          · have hsum : (ab.1.1 - α) + (ab.1.2 - α) ≠ 0 := by
              rw [show (ab.1.1 - α) + (ab.1.2 - α) = (ab.1.1 + ab.1.2) - 2 * α from by ring, hab]
              exact sub_ne_zero.mpr hα.symm
            have hg : D.jacobi (ab.1.1 - α) (ab.1.2 - α) * D.gauss (γ - 2 * α) =
                D.gauss (ab.1.1 - α) * D.gauss (ab.1.2 - α) := by
              have heq : (ab.1.1 - α) + (ab.1.2 - α) = γ - 2 * α := by
                rw [show (ab.1.1 - α) + (ab.1.2 - α) = (ab.1.1 + ab.1.2) - 2 * α from by ring, hab]
              rw [← heq, ← gauss_mul_gauss D hq hsum]
            calc ((D.q : ℂ) - 1)⁻¹ * D.jacobi (ab.1.1 - α) (ab.1.2 - α) *
                  (D.chi (γ - α) (-1) * D.gauss (γ - 2 * α) * isqrt D.q)
                = D.chi (γ - α) (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt D.q) *
                    (D.jacobi (ab.1.1 - α) (ab.1.2 - α) * D.gauss (γ - 2 * α)) := by ring
              _ = D.chi (γ - α) (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt D.q) *
                    D.gauss (ab.1.1 - α) * D.gauss (ab.1.2 - α) := by rw [hg]; ring
          · rw [zero_mul]
        · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply]
          split_ifs with hk
          · let k' : D.Lab2 := k.1 + (((D.q + 1) * (-α).val : ℕ) : D.Lab2)
            have hk'0 : k' ≠ 0 := cusp_shift_ne_zero D hq k α
            have hres : D.restrLab k' = γ - 2 * α := by
              simp only [k', restrLab_add, hk, restrLab_q_add_one_mul]
              ring
            have hres0 : D.restrLab k' ≠ 0 := by rw [hres]; exact sub_ne_zero.mpr hα.symm
            have hg2 := gaussQ2_theta_eq D hq hk'0
            rw [if_neg hres0, hres] at hg2
            rw [gaussQ2_shifted D k.1 α, hg2, S1_eq_sum_shifted]
            calc -(isqrt (D.q - 1) * isqrt (D.q + 1) * ∑ z with D.tr z = 1, D.theta k' z) *
                  (D.chi (γ - α) (-1) * D.gauss (γ - 2 * α) * isqrt D.q)
                = -(D.chi (γ - α) (-1) * (isqrt D.q * (isqrt (D.q - 1) * isqrt (D.q + 1)))) *
                    (D.gauss (γ - 2 * α) * ∑ z with D.tr z = 1, D.theta k' z) := by ring
              _ = -(D.chi (γ - α) (-1) * isqrt (D.q * (D.q ^ 2 - 1))) *
                    (D.gauss (γ - 2 * α) * ∑ z with D.tr z = 1, D.theta k' z) := by
                    rw [isqrt_q_mul_sq_sub_one D hq]
          · rw [zero_mul]
      · simp [AGammaExt]

private lemma T_exceptional (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    {α : D.Lab} (hα : 2 * α = γ) (o : D.Irr ⊕ U) :
    (Rfix * Mbr * Bgate D γ * FxDag D) o (some α) =
      -(D.chi α (-1) * isqrt D.q) * AGammaExt D γ U o (some α) +
        (Real.sqrt (((D.q : ℝ) - 1) / D.q) : ℂ) * eO D (.inl (.inl α)) o := by
  rw [T_col_some D hq γ U Rfix hRfix Mbr hMbr α o]
  have hga : γ - α = α := by linear_combination -hα
  rcases o with μ | u
  · rcases μ with δ | δ | ab | k
    · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply, mul_zero, zero_add, eO_apply,
        Sum.inl.injEq]
      split_ifs with h1 h2 h3
      · rw [mul_one]
      · exact False.elim (h2 h1.2)
      · subst h3; exact False.elim (h1 ⟨hα, rfl⟩)
      · rw [mul_zero]
    · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply, eO_apply, Sum.inl.injEq,
        reduceCtorEq, ↓reduceIte, mul_zero, add_zero]
      split_ifs with hδ hδα
      · rw [hδα, sub_self, gauss_zero, neg_one_sq, mul_one, hga]
        calc -(isqrt D.q * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1))
            = -(D.chi α (-1) ^ 2) *
                (isqrt D.q * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1)) := by
                  rw [chi_neg_one_sq, neg_mul, one_mul]
          _ = -(D.chi α (-1) * isqrt D.q) *
                (D.chi α (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1))) := by ring
      · have hξ : δ - α ≠ 0 := sub_ne_zero.mpr hδα
        have hξ_neg : -(δ - α) = δ - α := by
          have h2ξ : 2 * (δ - α) = 0 := by linear_combination hδ - hα
          linear_combination -h2ξ
        have hj : D.jacobi (δ - α) (δ - α) = -D.chi (δ - α) (-1) := by
          conv_lhs => arg 3; rw [← hξ_neg]
          rw [jacobi_neg D hq (δ - α), if_neg hξ]
        have hg : D.gauss (δ - α) ^ 2 = D.chi (δ - α) (-1) * (D.q : ℂ) := by
          rw [sq]
          conv_lhs => arg 2; arg 2; rw [← hξ_neg]
          rw [gauss_mul_gauss_neg D hq (δ - α), if_neg hξ]
        rw [hj, hg, hga]
        calc (Real.sqrt D.q : ℂ) * ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1) * -D.chi (δ - α) (-1)
            = -(D.chi α (-1) ^ 2) * (isqrt D.q * (D.q : ℂ)) *
                ((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1) * D.chi (δ - α) (-1) := by
                  rw [chi_neg_one_sq, isqrt_q_mul_q]; ring
          _ = -(D.chi α (-1) * isqrt D.q) *
                (D.chi α (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt (D.q + 1)) *
                  (D.chi (δ - α) (-1) * (D.q : ℂ))) := by ring
      · rw [mul_zero]
    · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply, eO_apply, Sum.inl.injEq,
        reduceCtorEq, ↓reduceIte, mul_zero, add_zero]
      split_ifs with hab
      · have hu0 : ab.1.1 - α ≠ 0 := by
          intro hu
          have ha1 : ab.1.1 = α := sub_eq_zero.mp hu
          have ha2 : ab.1.2 = α := by linear_combination hab - ha1 - hα
          have hlt := ab.2
          rw [ha1, ha2] at hlt
          exact lt_irrefl _ hlt
        have hu2 : ab.1.2 - α = -(ab.1.1 - α) := by linear_combination hab - hα
        rw [hu2, jacobi_neg D hq (ab.1.1 - α), if_neg hu0,
          mul_assoc _ (D.gauss (ab.1.1 - α)) (D.gauss (-(ab.1.1 - α))),
          gauss_mul_gauss_neg D hq (ab.1.1 - α), if_neg hu0, hga]
        calc ((D.q : ℂ) - 1)⁻¹ * -D.chi (ab.1.1 - α) (-1)
            = -(D.chi α (-1) ^ 2) * (isqrt D.q * isqrt D.q * (D.q : ℂ)) *
                ((D.q : ℂ) - 1)⁻¹ * D.chi (ab.1.1 - α) (-1) := by
                  rw [chi_neg_one_sq, isqrt_q_sq_mul_q]; ring
          _ = -(D.chi α (-1) * isqrt D.q) *
                (D.chi α (-1) * (((D.q : ℂ) - 1)⁻¹ * isqrt D.q) *
                  (D.chi (ab.1.1 - α) (-1) * (D.q : ℂ))) := by ring
      · rw [mul_zero]
    · simp only [AGammaExt, FieldData.AGamma, Matrix.of_apply, eO_apply, Sum.inl.injEq,
        reduceCtorEq, ↓reduceIte, mul_zero, add_zero]
      split_ifs with hk
      · let k' : D.Lab2 := k.1 + (((D.q + 1) * (-α).val : ℕ) : D.Lab2)
        have hk'0 : k' ≠ 0 := cusp_shift_ne_zero D hq k α
        have hres : D.restrLab k' = 0 := by
          simp only [k', restrLab_add, hk, restrLab_q_add_one_mul]
          linear_combination -hα
        have hg2 := gaussQ2_theta_eq D hq hk'0
        rw [if_pos hres] at hg2
        rw [gaussQ2_shifted D k.1 α, hg2, S1_eq_sum_shifted, hga]
        calc -(isqrt (D.q - 1) * isqrt (D.q + 1) * ∑ z with D.tr z = 1, D.theta k' z)
            = -(D.chi α (-1) ^ 2 * (isqrt D.q * isqrt D.q * (D.q : ℂ)) *
                (isqrt (D.q - 1) * isqrt (D.q + 1) * ∑ z with D.tr z = 1, D.theta k' z)) := by
                  rw [chi_neg_one_sq, isqrt_q_sq_mul_q]; ring
          _ = -(D.chi α (-1) * isqrt D.q) *
                (-(D.chi α (-1) * (isqrt D.q * (isqrt (D.q - 1) * isqrt (D.q + 1)))) *
                  (-(D.q : ℂ) * ∑ z with D.tr z = 1, D.theta k' z)) := by ring
          _ = -(D.chi α (-1) * isqrt D.q) *
                (-(D.chi α (-1) * isqrt (D.q * (D.q ^ 2 - 1))) *
                  (-(D.q : ℂ) * ∑ z with D.tr z = 1, D.theta k' z)) := by
                    rw [isqrt_q_mul_sq_sub_one D hq]
      · rw [mul_zero]
  · simp [AGammaExt, eO_apply]

/-! ### Layer 5: Exceptional reflection `Rexc` and main theorem -/

private lemma sum_mulVec {ι m : Type*} [Fintype m]
    (s : Finset ι) (A : ι → Matrix m m ℂ) (v : m → ℂ) :
    (∑ i ∈ s, A i).mulVec v = ∑ i ∈ s, (A i).mulVec v := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      ext o
      simp [Matrix.mulVec, dotProduct]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_mulVec, ih]

private lemma vecMulVec_mulVec {m : Type*} [Fintype m] (u v w : m → ℂ) :
    (Matrix.vecMulVec u (star v)).mulVec w = (star v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.star_apply, Pi.smul_apply,
    smul_eq_mul]
  calc ∑ j : m, u i * star (v j) * w j
      = ∑ j : m, (star (v j) * w j) * u i :=
          Finset.sum_congr rfl fun j _ => by ring
    _ = (∑ j : m, star (v j) * w j) * u i := (Finset.sum_mul _ _ _).symm

private lemma dotProduct_star_d (D : FieldData) (U : Type) [Fintype U]
    (α : D.Lab) (v : D.Irr ⊕ U → ℂ) :
    star (eO D (.inl (.inl α))) ⬝ᵥ v = v (.inl (.inl α)) := by
  simp only [dotProduct, Pi.star_apply]
  refine (Finset.sum_eq_single (.inl (.inl α)) ?_
    (fun h => False.elim (h (Finset.mem_univ _)))).trans ?_
  · intro o _ ho
    simp [eO_apply, ho]
  · simp [eO_apply]

private lemma dotProduct_star_a_d (D : FieldData) (γ : D.Lab) (U : Type) [Fintype U]
    (α' α : D.Lab) :
    star (fun o => AGammaExt D γ U o (some α')) ⬝ᵥ eO D (.inl (.inl α)) = 0 := by
  simp only [dotProduct, Pi.star_apply]
  refine (Finset.sum_eq_single (.inl (.inl α)) ?_
    (fun h => False.elim (h (Finset.mem_univ _)))).trans ?_
  · intro o _ ho
    simp [eO_apply, ho]
  · simp [AGammaExt, FieldData.AGamma, Matrix.of_apply]

private lemma dotProduct_star_d_a (D : FieldData) (γ : D.Lab) (U : Type) [Fintype U]
    (α' α : D.Lab) :
    star (eO D (.inl (.inl α'))) ⬝ᵥ (fun o => AGammaExt D γ U o (some α)) = 0 := by
  rw [dotProduct_star_d]
  simp [AGammaExt, FieldData.AGamma, Matrix.of_apply]

private lemma dotProduct_add_right {m : Type*} [Fintype m] (u v w : m → ℂ) :
    u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma dotProduct_smul_right {m : Type*} [Fintype m] (u : m → ℂ) (c : ℂ) (v : m → ℂ) :
    u ⬝ᵥ (c • v) = c * (u ⬝ᵥ v) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma Rexc_comp_T_Dgate (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr)
    (o : D.Irr ⊕ U) (c : Option D.Lab) :
    (Rexc D γ U * (Rfix * Mbr * Bgate D γ * FxDag D) * Dgate D γ) o c = AGammaExt D γ U o c := by
  have hmul : ((Rexc D γ U * (Rfix * Mbr * Bgate D γ * FxDag D)) * Dgate D γ) o c =
      (Rexc D γ U).mulVec (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c) o * Dgate D γ c c := by
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single c ?_ (fun h => False.elim (h (Finset.mem_univ _)))).trans ?_
    · intro c' _ hc'
      simp only [Dgate, Matrix.diagonal_apply, if_neg hc', mul_zero]
    · simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  set a : D.Lab → (D.Irr ⊕ U → ℂ) := fun α o' => AGammaExt D γ U o' (some α)
  set d : D.Lab → (D.Irr ⊕ U → ℂ) := fun α => eO D (.inl (.inl α))
  set s : D.Lab → ℂ := fun α => D.chi α (-1) / (Real.sqrt D.q : ℂ)
  set c₀ : ℂ := (Real.sqrt (((D.q : ℝ) - 1) / D.q) : ℂ)
  set S_exc : Finset D.Lab := Finset.univ.filter (fun α : D.Lab => 2 * α = γ)
  have hT_exc : ∀ α : D.Lab, 2 * α = γ →
      (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)) = (-s α) • a α + c₀ • d α := by
    intro α hα
    ext o'
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [T_exceptional D hq γ U Rfix hRfix Mbr hMbr hα o']
    simp only [s, c₀, a, d, isqrt, div_eq_mul_inv, Complex.ofReal_inv]
  have hRexc_mulVec : ∀ v : D.Irr ⊕ U → ℂ,
      (Rexc D γ U).mulVec v = v + ∑ α ∈ S_exc,
        (((-s α - 1) * (star (a α) ⬝ᵥ v) + c₀ * (star (d α) ⬝ᵥ v)) • a α +
         (c₀ * (star (a α) ⬝ᵥ v) + (s α - 1) * (star (d α) ⬝ᵥ v)) • d α) := by
    intro v
    dsimp only [Rexc, S_exc, s, c₀, a, d]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, sum_mulVec]
    congr 1
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
      vecMulVec_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, vecMulVec_mulVec]
    ext o'
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hqpos : (0 : ℝ) < D.q := by exact_mod_cast q_pos D
  have hq1 : (0 : ℝ) ≤ (D.q : ℝ) - 1 := by
    have : (2 : ℝ) < D.q := by exact_mod_cast hq
    linarith
  have hqc : (D.q : ℂ) ≠ 0 := by exact_mod_cast (q_pos D).ne'
  have hsq_ne : (Real.sqrt D.q : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hqpos).ne'
  have hs_ne : ∀ α : D.Lab, -s α ≠ 0 := by
    intro α
    simp only [s, neg_ne_zero]
    exact div_ne_zero (chi_ne_zero D α (neg_ne_zero.mpr one_ne_zero)) hsq_ne
  have hs_star : ∀ α : D.Lab, star (s α) = s α := by
    intro α
    simp only [s]
    rw [Complex.star_def, map_div₀, Complex.conj_ofReal, ← Complex.star_def, star_chi_neg_one]
  have hs_sq : ∀ α : D.Lab, s α ^ 2 = (D.q : ℂ)⁻¹ := by
    intro α
    simp only [s]
    rw [div_pow, chi_neg_one_sq, ← Complex.ofReal_pow, Real.sq_sqrt hqpos.le,
      Complex.ofReal_natCast, one_div]
  have hc0_star : star c₀ = c₀ := by
    simp only [c₀, Complex.star_def, Complex.conj_ofReal]
  have hc0_sq : c₀ ^ 2 = ((D.q : ℂ) - 1) / (D.q : ℂ) := by
    simp only [c₀]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (div_nonneg hq1 hqpos.le)]
    push_cast; rfl
  have hsc_id : ∀ α : D.Lab, s α ^ 2 + c₀ ^ 2 = 1 := by
    intro α
    rw [hs_sq, hc0_sq]
    field_simp [hqc]
    ring
  have hd_T_col : ∀ (α' : D.Lab) (c' : Option D.Lab), 2 * α' = γ →
      star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c') =
        match c' with
        | none => 0
        | some α => if α' = α then c₀ else 0 := by
    intro α' c' hα'
    rw [dotProduct_star_d]
    cases c' with
    | none =>
        rw [T_col_none D hq γ U Rfix hRfix Mbr hMbr (.inl (.inl α'))]
        simp [AGammaExt, FieldData.AGamma]
    | some α =>
        rw [T_col_some D hq γ U Rfix hRfix Mbr hMbr α (.inl (.inl α'))]
        dsimp only
        by_cases heq : α' = α
        · rw [if_pos ⟨hα', heq⟩, if_pos heq]
        · rw [if_neg (fun h => heq h.2), if_neg heq]
  have ha_T_col_generic : ∀ (α' : D.Lab) (c' : Option D.Lab),
      2 * α' = γ → (∀ α : D.Lab, c' = some α → 2 * α ≠ γ) →
      star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c') = 0 := by
    intro α' c' hα' hc'
    have hisom : (∑ o' : D.Irr ⊕ U,
        star ((Rfix * Mbr * Bgate D γ * FxDag D) o' (some α')) *
          (Rfix * Mbr * Bgate D γ * FxDag D) o' c') = 0 := by
      rw [T_isometry D hq γ U Rfix hRfix Mbr hMbr (some α') c']
      have hne : some α' ≠ c' := by
        intro h
        cases c' with
        | none => cases h
        | some α => exact hc' α rfl ((Option.some.inj h) ▸ hα')
      rw [if_neg hne]
    have hdot_d : star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c') = 0 := by
      rw [hd_T_col α' c' hα']
      cases c' with
      | none => rfl
      | some α => exact if_neg (fun (h : α' = α) => hc' α rfl (h ▸ hα'))
    have hexp : ∑ o' : D.Irr ⊕ U,
          star ((Rfix * Mbr * Bgate D γ * FxDag D) o' (some α')) *
            (Rfix * Mbr * Bgate D γ * FxDag D) o' c' =
        star (-s α') * (star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c')) +
          star c₀ * (star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c')) := by
      have h1 : ∀ o' : D.Irr ⊕ U,
          star ((Rfix * Mbr * Bgate D γ * FxDag D) o' (some α')) *
            (Rfix * Mbr * Bgate D γ * FxDag D) o' c' =
          star (-s α') * (star (a α' o') * (Rfix * Mbr * Bgate D γ * FxDag D) o' c') +
            star c₀ * (star (d α' o') * (Rfix * Mbr * Bgate D γ * FxDag D) o' c') := by
        intro o'
        have hT := congrFun (hT_exc α' hα') o'
        rw [hT, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
          Complex.star_def, map_add, map_mul, map_mul, ← Complex.star_def]
        ring
      simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    rw [hexp, hdot_d, mul_zero, add_zero] at hisom
    exact (mul_eq_zero.mp hisom).resolve_left (star_ne_zero.mpr (hs_ne α'))
  have ha_a : ∀ α' α : D.Lab, 2 * α' = γ → 2 * α = γ →
      star (a α') ⬝ᵥ a α = if α' = α then 1 else 0 := by
    intro α' α hα' hα
    have hisom := T_isometry D hq γ U Rfix hRfix Mbr hMbr (some α') (some α)
    have hdd : star (d α') ⬝ᵥ d α = if α' = α then 1 else 0 := by
      rw [dotProduct_star_d]
      simp only [d, eO_apply, Sum.inl.injEq]
    have h1 : ∀ o' : D.Irr ⊕ U,
        star ((Rfix * Mbr * Bgate D γ * FxDag D) o' (some α')) *
          (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α) =
        star (-s α') * (-s α) * (star (a α' o') * a α o') +
        star (-s α') * c₀ * (star (a α' o') * d α o') +
        star c₀ * (-s α) * (star (d α' o') * a α o') +
        star c₀ * c₀ * (star (d α' o') * d α o') := by
      intro o'
      have hT1 := congrFun (hT_exc α' hα') o'
      have hT2 := congrFun (hT_exc α hα) o'
      rw [hT1, hT2, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
        Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
        Complex.star_def, map_add, map_mul, map_mul, ← Complex.star_def]
      ring
    have hexp : ∑ o' : D.Irr ⊕ U,
          star ((Rfix * Mbr * Bgate D γ * FxDag D) o' (some α')) *
            (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α) =
        star (-s α') * (-s α) * (star (a α') ⬝ᵥ a α) +
        star (-s α') * c₀ * (star (a α') ⬝ᵥ d α) +
        star c₀ * (-s α) * (star (d α') ⬝ᵥ a α) +
        star c₀ * c₀ * (star (d α') ⬝ᵥ d α) := by
      simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    have htot : star (-s α') * (-s α) * (star (a α') ⬝ᵥ a α) +
        star c₀ * c₀ * (if α' = α then 1 else 0) = if α' = α then 1 else 0 := by
      rw [dotProduct_star_a_d, dotProduct_star_d_a, hdd, mul_zero, mul_zero, add_zero, add_zero] at hexp
      rw [← hexp, hisom]
      by_cases h : α' = α <;> simp [h]
    by_cases heq : α' = α
    · subst heq
      rw [if_pos rfl] at htot ⊢
      rw [star_neg, neg_mul_neg, hs_star, ← sq, hs_sq, hc0_star, ← sq, mul_one] at htot
      have hid := hsc_id α'
      rw [hs_sq] at hid
      have hmul_inv : (D.q : ℂ)⁻¹ * (star (a α') ⬝ᵥ a α') = (D.q : ℂ)⁻¹ := by
        linear_combination htot - hid
      exact mul_left_cancel₀ (inv_ne_zero hqc) (hmul_inv.trans (mul_one _).symm)
    · rw [if_neg heq] at htot ⊢
      rw [mul_zero, add_zero] at htot
      exact (mul_eq_zero.mp htot).resolve_left
        (mul_ne_zero (star_ne_zero.mpr (hs_ne α')) (hs_ne α))
  by_cases hgen : ∀ α : D.Lab, c = some α → 2 * α ≠ γ
  · have hRm : (Rexc D γ U).mulVec (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c) =
        fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c := by
      rw [hRexc_mulVec]
      have hzero : ∑ α' ∈ S_exc,
          (((-s α' - 1) * (star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c)) +
              c₀ * (star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c))) • a α' +
           (c₀ * (star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c)) +
              (s α' - 1) * (star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c))) • d α') = 0 := by
        refine Finset.sum_eq_zero fun α' hα' => ?_
        have hα'eq : 2 * α' = γ := (Finset.mem_filter.mp hα').2
        have ha0 := ha_T_col_generic α' c hα'eq hgen
        have hd0 : star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' c) = 0 := by
          rw [hd_T_col α' c hα'eq]
          cases c with
          | none => rfl
          | some α => exact if_neg (fun (h : α' = α) => hgen α rfl (h ▸ hα'eq))
        rw [ha0, hd0]
        simp
      rw [hzero, add_zero]
    rw [hmul, hRm]
    have hTD : ((Rfix * Mbr * Bgate D γ * FxDag D) * Dgate D γ) o c =
        (Rfix * Mbr * Bgate D γ * FxDag D) o c * Dgate D γ c c := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_single c ?_ (fun h => False.elim (h (Finset.mem_univ _)))
      intro c' _ hc'
      simp only [Dgate, Matrix.diagonal_apply, if_neg hc', mul_zero]
    rw [← hTD]
    exact T_Dgate_generic D hq γ U Rfix hRfix Mbr hMbr o c hgen
  · push Not at hgen
    obtain ⟨α, rfl, hα⟩ := hgen
    have hne_false : ¬ (α ≠ γ - α) := not_not.mpr (by linear_combination hα)
    have hdg : Dgate D γ (some α) (some α) = 1 := by
      simp only [Dgate, Matrix.diagonal_apply, ↓reduceIte, if_neg hne_false]
    have hRm_o : (Rexc D γ U).mulVec (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)) o = a α o := by
      rw [hRexc_mulVec]
      have hterm : ∀ α' ∈ S_exc, α' ≠ α →
          (((-s α' - 1) * (star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α))) +
              c₀ * (star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)))) • a α' +
           (c₀ * (star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α))) +
              (s α' - 1) * (star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)))) • d α') = 0 := by
        intro α' hα' hne
        have hα'eq : 2 * α' = γ := (Finset.mem_filter.mp hα').2
        have ha0 : star (a α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)) = 0 := by
          rw [hT_exc α hα, dotProduct_add_right, dotProduct_smul_right, dotProduct_smul_right,
            ha_a α' α hα'eq hα, dotProduct_star_a_d, if_neg hne, mul_zero, mul_zero, add_zero]
        have hd0 : star (d α') ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)) = 0 := by
          rw [hd_T_col α' (some α) hα'eq]
          exact if_neg hne
        rw [ha0, hd0]
        simp
      have hmem : α ∈ S_exc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩
      rw [Finset.sum_eq_single α hterm (fun h => False.elim (h hmem))]
      have ha_self : star (a α) ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)) = -s α := by
        rw [hT_exc α hα, dotProduct_add_right, dotProduct_smul_right, dotProduct_smul_right,
          ha_a α α hα hα, dotProduct_star_a_d, if_pos rfl, mul_one, mul_zero, add_zero]
      have hd_self : star (d α) ⬝ᵥ (fun o' => (Rfix * Mbr * Bgate D γ * FxDag D) o' (some α)) = c₀ := by
        rw [hd_T_col α (some α) hα]
        dsimp only
        rw [if_pos rfl]
      rw [ha_self, hd_self, hT_exc α hα]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc (-s α * a α o + c₀ * d α o) +
            (((-s α - 1) * -s α + c₀ * c₀) * a α o + (c₀ * -s α + (s α - 1) * c₀) * d α o)
          = (s α ^ 2 + c₀ ^ 2) * a α o := by ring
        _ = 1 * a α o := by rw [hsc_id α]
        _ = a α o := one_mul _
    rw [hmul, hRm_o, hdg, mul_one]

end GL2QFT.Supplement.Thm627Helpers

section
open GL2QFT GL2QFT.Supplement FieldData AGammaGates

theorem solution (D : FieldData) (hq : 2 < D.q) (γ : D.Lab) (U : Type) [Fintype U]
    (Rfix : Matrix (D.Irr ⊕ U) (BranchOut D γ) ℂ) (hRfix : IsFixingGate D γ Rfix)
    (Mbr : Matrix (BranchOut D γ) (Bool × D.Fq2) ℂ) (hMbr : IsBranchTransform D γ Mbr) :
    Rexc D γ U * (Rfix * Mbr * Bgate D γ * FxDag D) * Dgate D γ = AGammaExt D γ U := by
  ext o c
  exact GL2QFT.Supplement.Thm627Helpers.Rexc_comp_T_Dgate D hq γ U Rfix hRfix Mbr hMbr o c

end

