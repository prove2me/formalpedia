-- Prove2me | solution 1 for GL2QFT.table_2_completeness
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:32:32.683926+00:00
-- url     : https://prove2.me/submissions/80497c35-f60c-4c64-95c4-cbf3a32000b1

import Definitions.Def_GL2QFT_Irreps
import Theorems.Thm_GL2QFT_lemma_6_5
import Theorems.Thm_GL2QFT_lemma_6_7
import Theorems.Thm_GL2QFT_lemma_A_4
import Theorems.Thm_GL2QFT_lemma_A_5

noncomputable section

open Classical

namespace GL2QFT.Table2Aux

open GL2QFT FieldData Polynomial
open scoped ComplexConjugate Matrix

local instance (D : FieldData) : Field D.Fq := AdjoinRoot.instField
local instance (D : FieldData) : Field D.Fq2 := AdjoinRoot.instField
local instance (D : FieldData) : IsDomain D.Fq2 := inferInstance
local instance (D : FieldData) : IsReduced D.Fq2 := inferInstance

/-! ### Section 1: Finite field cardinalities, Frobenius, trace, norm, and characters -/

lemma card_Fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  have hdim : Module.finrank (ZMod D.p) D.Fq = D.r := by
    rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]
  rw [Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq), ZMod.card, hdim, FieldData.q]

lemma card_Fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  have hdim : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  rw [Module.card_eq_pow_finrank (K := D.Fq) (V := D.Fq2), card_Fq, hdim]

lemma card_Fq_units (D : FieldData) : Fintype.card D.Fqˣ = D.q - 1 := by
  rw [@Fintype.card_units D.Fq _ _ _, card_Fq]

lemma card_Fq2_units (D : FieldData) : Fintype.card D.Fq2ˣ = D.q ^ 2 - 1 := by
  rw [@Fintype.card_units D.Fq2 _ _ _, card_Fq2]

lemma card_Lab (D : FieldData) : Fintype.card D.Lab = D.q - 1 := by
  rw [ZMod.card]

lemma card_Lab2 (D : FieldData) : Fintype.card D.Lab2 = D.q ^ 2 - 1 := by
  rw [ZMod.card]

lemma q_pos (D : FieldData) : (0 : ℝ) < D.q := by
  exact_mod_cast (by have := D.one_lt_q; omega : 0 < D.q)

lemma q_complex_ne (D : FieldData) : (D.q : ℂ) ≠ 0 := by
  exact_mod_cast (by have := D.one_lt_q; omega : D.q ≠ 0)

lemma q_sub_one_pos (D : FieldData) : (0 : ℝ) < (D.q : ℝ) - 1 := by
  have : (1 : ℝ) < D.q := by exact_mod_cast D.one_lt_q
  linarith

lemma q_sub_one_complex_ne (D : FieldData) : ((D.q : ℂ) - 1) ≠ 0 := by
  have h : (1 : ℝ) < D.q := by exact_mod_cast D.one_lt_q
  intro hc
  have hr := congrArg Complex.re hc
  simp at hr
  linarith

lemma q_add_one_complex_ne (D : FieldData) : ((D.q : ℂ) + 1) ≠ 0 := by
  have h : (0 : ℝ) < D.q := q_pos D
  intro hc
  have hr := congrArg Complex.re hc
  simp at hr
  linarith

lemma h_order_eq (D : FieldData) : orderOf D.h = D.q ^ 2 - 1 := by
  rw [D.h_order, FieldData.q]

lemma h_ne_zero (D : FieldData) : D.h ≠ 0 := by
  intro h0
  have ho := h_order_eq D
  rw [h0, orderOf_zero] at ho
  exact NeZero.ne (D.q ^ 2 - 1) ho.symm

lemma algebraMap_gen (D : FieldData) :
    algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  unfold FieldData.gen
  have hnorm := @FiniteField.algebraMap_norm_eq_pow D.Fq D.Fq2 _ _ _ _ D.h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_Fq2, card_Fq] at hnorm
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hdiv : (D.q ^ 2 - 1) / (D.q - 1) = D.q + 1 := by
    have hmul : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
      zify [hq.le, hsq]; ring
    rw [hmul, Nat.mul_div_cancel _ (by omega)]
  rwa [hdiv] at hnorm

lemma orderOf_gen (D : FieldData) : orderOf D.gen = D.q - 1 := by
  have hinj : Function.Injective (algebraMap D.Fq D.Fq2).toMonoidHom :=
    (algebraMap D.Fq D.Fq2).injective
  rw [← orderOf_injective (algebraMap D.Fq D.Fq2).toMonoidHom hinj D.gen]
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = D.q - 1
  rw [algebraMap_gen, orderOf_pow' D.h (by omega), h_order_eq]
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hmul : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    zify [hq.le, hsq]; ring
  change (D.q ^ 2 - 1) / ((D.q ^ 2 - 1).gcd (D.q + 1)) = D.q - 1
  rw [hmul, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h0
  have ho := orderOf_gen D
  rw [h0, orderOf_zero] at ho
  exact NeZero.ne (D.q - 1) ho.symm

lemma exists_pow_gen (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : ∃ n : ℕ, D.gen ^ n = x := by
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu_ord : orderOf u = D.q - 1 := by
    rw [← orderOf_units, Units.val_mk0, orderOf_gen]
  let φ : Fin (D.q - 1) → D.Fqˣ := fun k => u ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have hmod : i.val ≡ j.val [MOD orderOf u] := pow_eq_pow_iff_modEq.mp hij
    rw [hu_ord] at hmod
    ext
    exact Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt
  have hbij := (Fintype.bijective_iff_injective_and_card φ).mpr
    ⟨hinj, by rw [Fintype.card_fin, card_Fq_units]⟩
  obtain ⟨k, hk⟩ := hbij.2 (Units.mk0 x hx)
  exact ⟨k.val, by simpa [φ, u] using congrArg Units.val hk⟩

lemma gen_pow_dlog (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  have hex := exists_pow_gen D hx
  unfold FieldData.dlog
  rw [dif_pos hex]
  exact Nat.find_spec hex

lemma dlog_lt (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.dlog x < D.q - 1 := by
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu_ord : orderOf u = D.q - 1 := by
    rw [← orderOf_units, Units.val_mk0, orderOf_gen]
  obtain ⟨k, hk⟩ := (Fintype.bijective_iff_injective_and_card (fun k : Fin (D.q - 1) => u ^ k.val)).mpr
    ⟨fun i j hij => by
      have hmod : i.val ≡ j.val [MOD orderOf u] := pow_eq_pow_iff_modEq.mp hij
      rw [hu_ord] at hmod
      ext; exact Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt,
     by rw [Fintype.card_fin, card_Fq_units]⟩ |>.2 (Units.mk0 x hx)
  have hpow : D.gen ^ k.val = x := by simpa [u] using congrArg Units.val hk
  have hex : ∃ n : ℕ, D.gen ^ n = x := ⟨k.val, hpow⟩
  unfold FieldData.dlog
  rw [dif_pos hex]
  exact lt_of_le_of_lt (Nat.find_min' hex hpow) k.isLt

lemma exists_pow_h (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) : ∃ n : ℕ, D.h ^ n = z := by
  let u : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  have hu_ord : orderOf u = D.q ^ 2 - 1 := by
    rw [← orderOf_units, Units.val_mk0, h_order_eq]
  let φ : Fin (D.q ^ 2 - 1) → D.Fq2ˣ := fun k => u ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have hmod : i.val ≡ j.val [MOD orderOf u] := pow_eq_pow_iff_modEq.mp hij
    rw [hu_ord] at hmod
    ext
    exact Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt
  have hbij := (Fintype.bijective_iff_injective_and_card φ).mpr
    ⟨hinj, by rw [Fintype.card_fin, card_Fq2_units]⟩
  obtain ⟨k, hk⟩ := hbij.2 (Units.mk0 z hz)
  exact ⟨k.val, by simpa [φ, u] using congrArg Units.val hk⟩

lemma h_pow_dlog2 (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) : D.h ^ D.dlog2 z = z := by
  have hex := exists_pow_h D hz
  unfold FieldData.dlog2
  rw [dif_pos hex]
  exact Nat.find_spec hex

lemma charP_Fq (D : FieldData) : CharP D.Fq D.p :=
  charP_of_injective_algebraMap (algebraMap (ZMod D.p) D.Fq).injective D.p

lemma charP_Fq2 (D : FieldData) : CharP D.Fq2 D.p := by
  have : CharP D.Fq D.p := charP_Fq D
  exact charP_of_injective_algebraMap (algebraMap D.Fq D.Fq2).injective D.p

lemma finrank_Fq2 (D : FieldData) : Module.finrank D.Fq D.Fq2 = 2 := by
  rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]

lemma algebraMap_tr (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.tr z) = z + z ^ D.q := by
  rw [FieldData.tr, FiniteField.algebraMap_trace_eq_sum_pow D.Fq D.Fq2 z, finrank_Fq2,
    ← Fintype.card_eq_nat_card, card_Fq, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one, pow_one]

lemma algebraMap_nrm (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.nrm z) = z * z ^ D.q := by
  rw [FieldData.nrm, FiniteField.algebraMap_norm_eq_prod_pow D.Fq D.Fq2 z, finrank_Fq2,
    ← Fintype.card_eq_nat_card, card_Fq, Finset.prod_range_succ, Finset.prod_range_one,
    pow_zero, pow_one, pow_one]

lemma algebraMap_pow_q (D : FieldData) (x : D.Fq) :
    (algebraMap D.Fq D.Fq2 x) ^ D.q = algebraMap D.Fq D.Fq2 x := by
  rw [← map_pow, ← card_Fq D, FiniteField.pow_card]

lemma pow_q_sq (D : FieldData) (z : D.Fq2) : (z ^ D.q) ^ D.q = z := by
  rw [← pow_mul, ← sq, ← card_Fq2 D]
  exact @FiniteField.pow_card D.Fq2 _ _ z

lemma add_pow_q (D : FieldData) (a b : D.Fq2) : (a + b) ^ D.q = a ^ D.q + b ^ D.q := by
  have : Fact D.p.Prime := ⟨D.hp⟩
  have : CharP D.Fq2 D.p := charP_Fq2 D
  exact add_pow_char_pow a b D.p D.r

lemma neg_pow_q (D : FieldData) (a : D.Fq2) : (-a) ^ D.q = -(a ^ D.q) := by
  apply eq_neg_of_add_eq_zero_left
  rw [← add_pow_q D (-a) a, neg_add_cancel, zero_pow (by have := D.one_lt_q; omega)]

lemma tr_pow_q (D : FieldData) (z : D.Fq2) : D.tr (z ^ D.q) = D.tr z := by
  apply (algebraMap D.Fq D.Fq2).injective
  rw [algebraMap_tr, algebraMap_tr, pow_q_sq, add_comm]

lemma tr_neg (D : FieldData) (z : D.Fq2) : D.tr (-z) = -D.tr z :=
  map_neg (Algebra.trace D.Fq D.Fq2) z

lemma tr_add (D : FieldData) (z w : D.Fq2) : D.tr (z + w) = D.tr z + D.tr w :=
  map_add (Algebra.trace D.Fq D.Fq2) z w

lemma tr_algebraMap_mul (D : FieldData) (x : D.Fq) (z : D.Fq2) :
    D.tr (algebraMap D.Fq D.Fq2 x * z) = x * D.tr z := by
  rw [FieldData.tr, ← Algebra.smul_def, map_smul, smul_eq_mul]; rfl

lemma nrm_mul (D : FieldData) (z w : D.Fq2) : D.nrm (z * w) = D.nrm z * D.nrm w :=
  map_mul (Algebra.norm D.Fq) z w

lemma nrm_one (D : FieldData) : D.nrm 1 = 1 :=
  map_one (Algebra.norm D.Fq)

lemma nrm_zero (D : FieldData) : D.nrm 0 = 0 := by
  apply (algebraMap D.Fq D.Fq2).injective
  rw [map_zero, algebraMap_nrm, zero_mul]

lemma nrm_inv (D : FieldData) (z : D.Fq2) : D.nrm z⁻¹ = (D.nrm z)⁻¹ := by
  by_cases hz : z = 0
  · subst hz; simp [nrm_zero]
  · have h1 : D.nrm z⁻¹ * D.nrm z = 1 := by
      rw [← nrm_mul, inv_mul_cancel₀ hz, nrm_one]
    exact eq_inv_of_mul_eq_one_left h1

lemma nrm_neg (D : FieldData) (z : D.Fq2) : D.nrm (-z) = D.nrm z := by
  apply (algebraMap D.Fq D.Fq2).injective
  rw [algebraMap_nrm, algebraMap_nrm, neg_pow_q, neg_mul_neg]

lemma nrm_pow (D : FieldData) (z : D.Fq2) (n : ℕ) : D.nrm (z ^ n) = D.nrm z ^ n :=
  map_pow (Algebra.norm D.Fq) z n

lemma nrm_algebraMap (D : FieldData) (x : D.Fq) : D.nrm (algebraMap D.Fq D.Fq2 x) = x ^ 2 := by
  apply (algebraMap D.Fq D.Fq2).injective
  rw [algebraMap_nrm, algebraMap_pow_q, map_pow, sq]

lemma nrm_h (D : FieldData) : D.nrm D.h = D.gen := rfl

lemma nrm_eq_zero (D : FieldData) (z : D.Fq2) : D.nrm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h1 : z * z ^ D.q = 0 := by
      rw [← algebraMap_nrm, hz, map_zero]
    rcases mul_eq_zero.mp h1 with rfl | hq
    · rfl
    · exact eq_zero_of_pow_eq_zero hq
  · rintro rfl; exact nrm_zero D

lemma nrm_add (D : FieldData) (v α : D.Fq2) :
    D.nrm (v + α) = D.nrm v + D.tr (α ^ D.q * v) + D.nrm α := by
  apply (algebraMap D.Fq D.Fq2).injective
  simp only [map_add, algebraMap_nrm, algebraMap_tr, add_pow_q, mul_pow, pow_q_sq]
  ring

lemma nrm_algebraMap_add (D : FieldData) (x : D.Fq) (u : D.Fq2) :
    D.nrm (algebraMap D.Fq D.Fq2 x + u) = x ^ 2 + x * D.tr u + D.nrm u := by
  apply (algebraMap D.Fq D.Fq2).injective
  simp only [map_add, map_mul, map_pow, algebraMap_nrm, algebraMap_tr, add_pow_q, algebraMap_pow_q]
  ring

lemma pow_q_eq_self_iff (D : FieldData) (z : D.Fq2) :
    z ^ D.q = z ↔ ∃ x : D.Fq, algebraMap D.Fq D.Fq2 x = z := by
  constructor
  · intro hz
    let ι := algebraMap D.Fq D.Fq2
    let S : Finset D.Fq2 := Finset.univ.image ι
    let P : D.Fq2[X] := X ^ D.q - X
    have hP_ne : P ≠ 0 := @FiniteField.X_pow_card_sub_X_ne_zero D.Fq2 _ _ D.one_lt_q
    have hP_deg : P.natDegree = D.q :=
      @FiniteField.X_pow_card_sub_X_natDegree_eq D.Fq2 _ _ D.one_lt_q
    let R : Finset D.Fq2 := P.roots.toFinset
    have hSR : S ⊆ R := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
      rw [Multiset.mem_toFinset, mem_roots hP_ne, IsRoot.def,
        eval_sub, eval_pow, eval_X, algebraMap_pow_q, sub_self]
    have hcardS : S.card = D.q := by
      rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, card_Fq]
    have hcardR : R.card ≤ S.card := by
      rw [hcardS, ← hP_deg]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
    have hEq : S = R := Finset.eq_of_subset_of_card_le hSR hcardR
    have hzR : z ∈ R := by
      rw [Multiset.mem_toFinset, mem_roots hP_ne, IsRoot.def,
        eval_sub, eval_pow, eval_X, hz, sub_self]
    rw [← hEq] at hzR
    exact Finset.mem_image.mp hzR |> fun ⟨x, _, hx⟩ => ⟨x, hx⟩
  · rintro ⟨x, rfl⟩
    exact algebraMap_pow_q D x

/-! ### Section 2: Cardinality counts, `GL₂(F_q)` order, and dimension sum -/

lemma card_ps_labels (D : FieldData) :
    Fintype.card {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} = (D.q - 1) * (D.q - 2) / 2 := by
  let n := D.q - 1
  have hn_pos : 0 < n := by have := D.one_lt_q; omega
  let e : D.Lab ≃ Fin n :=
    { toFun := fun x => ⟨x.val, ZMod.val_lt x⟩
      invFun := fun i => (i.val : D.Lab)
      left_inv := fun x => by simp
      right_inv := fun i => by
        ext
        change ((i.val : D.Lab).val) = i.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt] }
  have he_val : ∀ α : D.Lab, (e α).val = α.val := fun _ => rfl
  let e2 : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} ≃
      {p : Fin n × Fin n // p.1 < p.2} :=
    { toFun := fun ⟨ab, h⟩ => ⟨(e ab.1, e ab.2), h⟩
      invFun := fun ⟨p, h⟩ => ⟨(e.symm p.1, e.symm p.2), by
        have h1 : (e.symm p.1).val = p.1.val := by
          change ((p.1.val : D.Lab).val) = p.1.val
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt p.1.isLt]
        have h2 : (e.symm p.2).val = p.2.val := by
          change ((p.2.val : D.Lab).val) = p.2.val
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt p.2.isLt]
        rw [h1, h2]
        exact h⟩
      left_inv := fun ⟨ab, _⟩ => by ext <;> simp
      right_inv := fun ⟨p, _⟩ => by ext <;> simp }
  rw [Fintype.card_congr e2]
  let S_lt := Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)
  let S_gt := Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1)
  let S_eq := Finset.univ.filter (fun p : Fin n × Fin n => p.1 = p.2)
  have hcard_lt : Fintype.card {p : Fin n × Fin n // p.1 < p.2} = S_lt.card :=
    Fintype.card_subtype _
  have hgt_eq_lt : S_gt.card = S_lt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [S_gt, S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp
      simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨(p.2, p.1), by simp only [S_gt, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp, rfl⟩
  have heq_card : S_eq.card = n := by
    have hbij : S_eq.card = (Finset.univ : Finset (Fin n)).card := by
      refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro p₁ hp₁ p₂ hp₂ h
        simp only [S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
        exact Prod.ext h (hp₁.symm.trans (h.trans hp₂))
      · intro i _; exact ⟨(i, i), by simp [S_eq], rfl⟩
    rw [hbij, Finset.card_fin]
  have hpart : S_lt.card + S_gt.card + S_eq.card = n * n := by
    have hd1 : Disjoint S_lt S_gt := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; exact lt_asymm h1 h2
    have hd2 : Disjoint (S_lt ∪ S_gt) S_eq := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_union, S_lt, S_gt, S_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      rcases hp1 with h | h <;> omega
    have hunion : (S_lt ∪ S_gt) ∪ S_eq = Finset.univ := by
      ext p
      simp only [Finset.mem_union, S_lt, S_gt, S_eq, Finset.mem_filter, Finset.mem_univ, true_and,
        iff_true]
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
    rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2, hunion,
      Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [hcard_lt]
  rw [hgt_eq_lt, heq_card] at hpart
  have h2 : 2 * S_lt.card = (D.q - 1) * (D.q - 2) := by
    obtain ⟨k, hk⟩ : ∃ k, D.q = k + 2 := ⟨D.q - 2, by have := D.one_lt_q; omega⟩
    have hmul : n * n - n = (D.q - 1) * (D.q - 2) := by
      change (D.q - 1) * (D.q - 1) - (D.q - 1) = (D.q - 1) * (D.q - 2)
      rw [hk]
      have h1 : k + 2 - 1 = k + 1 := by omega
      have h2' : k + 2 - 2 = k := by omega
      rw [h1, h2']
      have : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      omega
    omega
  omega

lemma q_sq_cast_Lab2 (D : FieldData) : ((D.q : D.Lab2) * (D.q : D.Lab2)) = 1 := by
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 < D.q ^ 2 := by nlinarith
  have hmod : (D.q * D.q : ℕ) ≡ 1 [MOD (D.q ^ 2 - 1)] := by
    rw [← sq]
    have h : D.q ^ 2 = (D.q ^ 2 - 1) + 1 := by omega
    rw [Nat.ModEq, h]
    simp
  rw [← Nat.cast_mul]
  simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod

lemma q_mul_eq_self_iff (D : FieldData) (k : D.Lab2) :
    (D.q : D.Lab2) * k = k ↔ D.q + 1 ∣ k.val := by
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hfac : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by zify [hq.le, hsq]; ring
  constructor
  · intro hk
    have hdiff : ((D.q - 1 : ℕ) : D.Lab2) * k = 0 := by
      have h1 : ((D.q - 1 : ℕ) : D.Lab2) = (D.q : D.Lab2) - 1 := by
        rw [Nat.cast_sub hq.le, Nat.cast_one]
      rw [h1, sub_mul, one_mul, hk, sub_self]
    have hdvd : D.q ^ 2 - 1 ∣ (D.q - 1) * k.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simpa [ZMod.natCast_zmod_val] using hdiff
    have hdvd' : (D.q - 1) * (D.q + 1) ∣ (D.q - 1) * k.val := hfac ▸ hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd'
  · intro hdvd
    rcases hdvd with ⟨m, hm⟩
    have hdvd2 : D.q ^ 2 - 1 ∣ (D.q - 1) * k.val := by
      have h : (D.q - 1) * (D.q + 1) ∣ (D.q - 1) * k.val := by
        rw [hm]; exact ⟨m, by ring⟩
      rwa [← hfac] at h
    have hzero : ((D.q - 1 : ℕ) : D.Lab2) * k = 0 := by
      have := (ZMod.natCast_eq_zero_iff ((D.q - 1) * k.val) (D.q ^ 2 - 1)).mpr hdvd2
      push_cast at this
      simpa [ZMod.natCast_zmod_val] using this
    have h1 : ((D.q - 1 : ℕ) : D.Lab2) = (D.q : D.Lab2) - 1 := by
      rw [Nat.cast_sub hq.le, Nat.cast_one]
    rw [h1, sub_mul, one_mul] at hzero
    exact sub_eq_zero.mp hzero

lemma card_cusp_labels (D : FieldData) :
    Fintype.card {k : D.Lab2 // D.IsCuspLabel k} = D.q * (D.q - 1) / 2 := by
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hfac : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by zify [hq.le, hsq]; ring
  let S_fixed := Finset.univ.filter (fun k : D.Lab2 => D.q + 1 ∣ k.val)
  let S_reg := Finset.univ.filter (fun k : D.Lab2 => ¬ (D.q + 1 ∣ k.val))
  let S_lt := Finset.univ.filter (fun k : D.Lab2 => ¬ (D.q + 1 ∣ k.val) ∧ k.val < ((D.q : D.Lab2) * k).val)
  let S_gt := Finset.univ.filter (fun k : D.Lab2 => ¬ (D.q + 1 ∣ k.val) ∧ ((D.q : D.Lab2) * k).val < k.val)
  have hfixed_card : S_fixed.card = D.q - 1 := by
    have hbij : S_fixed.card = (Finset.univ : Finset (Fin (D.q - 1))).card := by
      refine Finset.card_bij (fun k _ => ⟨k.val / (D.q + 1), by
        have hk : k.val < (D.q + 1) * (D.q - 1) := hfac ▸ ZMod.val_lt k
        exact Nat.div_lt_of_lt_mul hk⟩) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro k₁ hk₁ k₂ hk₂ h
        simp only [S_fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
        have hv : k₁.val = k₂.val := by
          have hdiv : k₁.val / (D.q + 1) = k₂.val / (D.q + 1) := congrArg Fin.val h
          rw [← Nat.mul_div_cancel' hk₁, ← Nat.mul_div_cancel' hk₂, hdiv]
        exact ZMod.val_injective _ hv
      · intro m _
        let k : D.Lab2 := (((D.q + 1) * m.val : ℕ) : D.Lab2)
        have hlt : (D.q + 1) * m.val < D.q ^ 2 - 1 := by
          rw [hfac]; exact Nat.mul_lt_mul_of_pos_left m.isLt (by omega)
        have hk_val : k.val = (D.q + 1) * m.val := by
          simp only [k, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        refine ⟨k, by simp [S_fixed, hk_val], ?_⟩
        ext; simp [hk_val, Nat.mul_div_cancel_left _ (by omega : 0 < D.q + 1)]
    rw [hbij, Finset.card_fin]
  have hreg_card : S_reg.card = D.q * (D.q - 1) := by
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D.Lab2))
      (p := fun k => D.q + 1 ∣ k.val)
    rw [Finset.card_univ, card_Lab2] at hsum
    change S_fixed.card + S_reg.card = D.q ^ 2 - 1 at hsum
    rw [hfixed_card] at hsum
    have hq_mul : D.q * (D.q - 1) + (D.q - 1) = D.q ^ 2 - 1 := by
      zify [hq.le, hsq]; ring
    omega
  have hgt_eq_lt : S_gt.card = S_lt.card := by
    refine Finset.card_bij (fun k _ => (D.q : D.Lab2) * k) ?_ ?_ ?_
    · intro k hk
      simp only [S_gt, S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      have hkk : (D.q : D.Lab2) * ((D.q : D.Lab2) * k) = k := by
        rw [← mul_assoc, q_sq_cast_Lab2, one_mul]
      refine ⟨?_, by rw [hkk]; exact hk.2⟩
      intro hdvd
      rw [← q_mul_eq_self_iff, hkk] at hdvd
      exact hk.1 ((q_mul_eq_self_iff D k).mp hdvd.symm)
    · intro k₁ _ k₂ _ heq
      have h1 := congrArg (fun x => (D.q : D.Lab2) * x) heq
      rwa [← mul_assoc, ← mul_assoc, q_sq_cast_Lab2, one_mul, one_mul] at h1
    · intro k hk
      simp only [S_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hkk : (D.q : D.Lab2) * ((D.q : D.Lab2) * k) = k := by
        rw [← mul_assoc, q_sq_cast_Lab2, one_mul]
      refine ⟨(D.q : D.Lab2) * k, ?_, hkk⟩
      simp only [S_gt, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, by rw [hkk]; exact hk.2⟩
      intro hdvd
      rw [← q_mul_eq_self_iff, hkk] at hdvd
      exact hk.1 ((q_mul_eq_self_iff D k).mp hdvd.symm)
  have hpart : S_lt.card + S_gt.card = S_reg.card := by
    have hd : Disjoint S_lt S_gt := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2; exact lt_asymm h1.2 h2.2
    have hunion : S_lt ∪ S_gt = S_reg := by
      ext k
      simp only [Finset.mem_union, S_lt, S_gt, S_reg, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        have hne : k ≠ (D.q : D.Lab2) * k := fun heq => h ((q_mul_eq_self_iff D k).mp heq.symm)
        have hvne : k.val ≠ ((D.q : D.Lab2) * k).val := fun hv => hne (ZMod.val_injective _ hv)
        rcases lt_or_gt_of_ne hvne with hlt | hgt
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, hgt⟩
    rw [← Finset.card_union_of_disjoint hd, hunion]
  have hcusp_eq : Fintype.card {k : D.Lab2 // D.IsCuspLabel k} = S_lt.card := by
    rw [← Fintype.card_coe S_lt]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun k => ⟨k.1, ?_⟩
        invFun := fun k => ⟨k.1, ?_⟩
        left_inv := fun k => rfl
        right_inv := fun k => rfl }
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, k.2.1, ?_⟩
      have hne : k.1.val ≠ ((D.q : D.Lab2) * k.1).val := fun hv =>
        k.2.1 ((q_mul_eq_self_iff D k.1).mp (ZMod.val_injective _ hv).symm)
      exact lt_of_le_of_ne k.2.2 hne
    · have hk := k.2
      rw [Finset.mem_filter] at hk
      exact ⟨hk.2.1, hk.2.2.le⟩
  rw [hcusp_eq]
  rw [hgt_eq_lt, hreg_card] at hpart
  omega

lemma card_gl_fin_two {K : Type} [Field K] [Fintype K] [DecidableEq K] :
    Fintype.card (GL (Fin 2) K) = (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
  let q := Fintype.card K
  have hdet_ne : ∀ g : GL (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    intro g h0
    have hmul : (g : Matrix (Fin 2) (Fin 2) K) * ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      exact_mod_cast Units.mul_inv g
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at hd
    exact zero_ne_one hd
  let eGL : GL (Fin 2) K ≃ {M : Matrix (Fin 2) (Fin 2) K // M.det ≠ 0} :=
    { toFun := fun g => ⟨(g : Matrix (Fin 2) (Fin 2) K), hdet_ne g⟩
      invFun := fun M => Matrix.nonsingInvUnit M.1 (isUnit_iff_ne_zero.mpr M.2)
      left_inv := fun g => by ext i j; rfl
      right_inv := fun M => by ext i j; rfl }
  rw [Fintype.card_congr eGL]
  let eMat : Matrix (Fin 2) (Fin 2) K ≃ (K × K) × (K × K) :=
    { toFun := fun M => ((M 0 0, M 1 0), (M 0 1, M 1 1))
      invFun := fun p => !![p.1.1, p.2.1; p.1.2, p.2.2]
      left_inv := fun M => by ext i j; fin_cases i <;> fin_cases j <;> rfl
      right_inv := fun p => by ext <;> rfl }
  let P : (K × K) × (K × K) → Prop := fun p => p.1.1 * p.2.2 - p.2.1 * p.1.2 ≠ 0
  let eSub : {M : Matrix (Fin 2) (Fin 2) K // M.det ≠ 0} ≃ {p : (K × K) × (K × K) // P p} :=
    { toFun := fun M => ⟨eMat M.1, by simpa [P, eMat, Matrix.det_fin_two] using M.2⟩
      invFun := fun p => ⟨eMat.symm p.1, by simpa [P, eMat, Matrix.det_fin_two] using p.2⟩
      left_inv := fun M => Subtype.ext (eMat.left_inv M.1)
      right_inv := fun p => Subtype.ext (eMat.right_inv p.1) }
  rw [Fintype.card_congr eSub, Fintype.card_subtype]
  have hfib : (Finset.univ.filter P).card =
      ∑ c1 ∈ Finset.univ.filter (fun v : K × K => v ≠ (0, 0)),
        (Finset.univ.filter (fun v2 : K × K => c1.1 * v2.2 - v2.1 * c1.2 ≠ 0)).card := by
    have hsplit := Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (s := Finset.univ.filter P)
      (t := Finset.univ.filter (fun v : K × K => v ≠ (0, 0))) ?_
    · rw [hsplit]
      refine Finset.sum_congr rfl fun c1 _ => ?_
      refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, P] at hp ⊢
        rw [← hp.2]
        exact hp.1
      · intro p₁ hp₁ p₂ hp₂ h
        simp only [Finset.mem_filter] at hp₁ hp₂
        exact Prod.ext (hp₁.2.trans hp₂.2.symm) h
      · intro v2 hv2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
        exact ⟨(c1, v2), by simp [P, hv2], rfl⟩
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, P] at hp ⊢
      intro h0
      rw [h0] at hp
      simp at hp
  rw [hfib]
  have hcol2 : ∀ c1 : K × K, c1 ≠ (0, 0) →
      (Finset.univ.filter (fun v2 : K × K => c1.1 * v2.2 - v2.1 * c1.2 ≠ 0)).card = q ^ 2 - q := by
    intro ⟨a, c⟩ hc1
    dsimp only
    let bad := Finset.univ.filter (fun v2 : K × K => a * v2.2 - v2.1 * c = 0)
    have hbad_eq : bad = Finset.univ.image (fun t : K => (t * a, t * c)) := by
      ext ⟨b, d⟩
      simp only [bad, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hdet
        by_cases ha : a = 0
        · have hc : c ≠ 0 := fun hc0 => hc1 (Prod.ext ha hc0)
          refine ⟨d / c, Prod.ext ?_ (div_mul_cancel₀ d hc)⟩
          have : b * c = 0 := by simpa [ha] using hdet
          rw [(mul_eq_zero.mp this).resolve_right hc, ha, mul_zero]
        · refine ⟨b / a, Prod.ext (div_mul_cancel₀ b ha) ?_⟩
          dsimp only
          have had : a * d = b * c := sub_eq_zero.mp hdet
          apply mul_left_cancel₀ ha
          calc a * ((b / a) * c) = ((b / a) * a) * c := by ring
            _ = b * c := by rw [div_mul_cancel₀ b ha]
            _ = a * d := had.symm
      · rintro ⟨t, rfl, rfl⟩; ring
    have hinj : Function.Injective (fun t : K => (t * a, t * c)) := by
      intro t₁ t₂ heq
      by_cases ha : a = 0
      · have hc : c ≠ 0 := fun hc0 => hc1 (Prod.ext ha hc0)
        exact mul_right_cancel₀ hc (congrArg Prod.snd heq)
      · exact mul_right_cancel₀ ha (congrArg Prod.fst heq)
    have hbad_card : bad.card = q := by
      rw [hbad_eq, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (K × K)))
      (p := fun v2 => a * v2.2 - v2.1 * c = 0)
    rw [Finset.card_univ, Fintype.card_prod, ← sq] at htot
    change bad.card + (Finset.univ.filter (fun v2 : K × K => a * v2.2 - v2.1 * c ≠ 0)).card = q ^ 2 at htot
    rw [hbad_card] at htot
    have hq_le : q ≤ q ^ 2 := by nlinarith [Fintype.card_pos (α := K)]
    omega
  rw [Finset.sum_congr rfl (fun c1 hc1 => hcol2 c1 (Finset.mem_filter.mp hc1).2)]
  rw [Finset.sum_const, smul_eq_mul]
  have hcol1 : (Finset.univ.filter (fun v : K × K => v ≠ (0, 0))).card = q ^ 2 - 1 := by
    have hfilt : Finset.univ.filter (fun v : K × K => v ≠ (0, 0)) = Finset.univ.erase (0, 0) := by
      ext v; simp
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod, ← sq]
  rw [hcol1]

lemma card_G (D : FieldData) : Fintype.card D.G = (D.q ^ 2 - 1) * (D.q ^ 2 - D.q) := by
  simpa [card_Fq] using card_gl_fin_two (K := D.Fq)

lemma sum_bas_sq (D : FieldData) :
    ∑ μ : D.Irr, Fintype.card (D.Bas μ) ^ 2 = Fintype.card D.G := by
  rw [card_G]
  simp only [Fintype.sum_sum_type]
  have h1 : ∑ α : D.Lab, Fintype.card (D.Bas (.inl α)) ^ 2 = D.q - 1 := by
    have hc : ∀ α : D.Lab, Fintype.card (D.Bas (.inl α)) ^ 2 = 1 := fun _ => by
      change Fintype.card Unit ^ 2 = 1; simp
    simp [hc]
  have h2 : ∑ α : D.Lab, Fintype.card (D.Bas (.inr (.inl α))) ^ 2 = (D.q - 1) * D.q ^ 2 := by
    have hc : ∀ α : D.Lab, Fintype.card (D.Bas (.inr (.inl α))) ^ 2 = D.q ^ 2 := fun _ => by
      change Fintype.card (Option D.Lab) ^ 2 = D.q ^ 2
      rw [Fintype.card_option, card_Lab]
      have := D.one_lt_q
      rw [Nat.sub_add_cancel (by omega)]
    simp [hc]
  have h3 : ∑ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      Fintype.card (D.Bas (.inr (.inr (.inl ab)))) ^ 2 =
      ((D.q - 1) * (D.q - 2) / 2) * (D.q + 1) ^ 2 := by
    have hc : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
        Fintype.card (D.Bas (.inr (.inr (.inl ab)))) ^ 2 = (D.q + 1) ^ 2 := fun _ => by
      change Fintype.card (Option (Option D.Lab)) ^ 2 = (D.q + 1) ^ 2
      rw [Fintype.card_option, Fintype.card_option, card_Lab]
      have := D.one_lt_q
      rw [Nat.sub_add_cancel (by omega)]
    simp [hc, card_ps_labels]
  have h4 : ∑ k : {k : D.Lab2 // D.IsCuspLabel k},
      Fintype.card (D.Bas (.inr (.inr (.inr k)))) ^ 2 =
      (D.q * (D.q - 1) / 2) * (D.q - 1) ^ 2 := by
    have hc : ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
        Fintype.card (D.Bas (.inr (.inr (.inr k)))) ^ 2 = (D.q - 1) ^ 2 := fun _ => by
      change Fintype.card D.Lab ^ 2 = (D.q - 1) ^ 2
      rw [card_Lab]
    simp [hc, card_cusp_labels]
  rw [h1, h2, h3, h4]
  obtain ⟨k, hk⟩ : ∃ k, D.q = k + 2 := ⟨D.q - 2, by have := D.one_lt_q; omega⟩
  rw [hk]
  have hq1 : k + 2 - 1 = k + 1 := by omega
  have hq2 : k + 2 - 2 = k := by omega
  rw [hq1, hq2]
  have heven1 : 2 ∣ (k + 1) * k := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨(k + 1) * m, ?_⟩; rw [hm]; ring
    · refine ⟨(m + 1) * k, ?_⟩; rw [hm]; ring
  have heven2 : 2 ∣ (k + 2) * (k + 1) := by
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨(m + 1) * (k + 1), ?_⟩; rw [hm]; ring
    · refine ⟨(k + 2) * (m + 1), ?_⟩; rw [hm]; ring
  have hdiv1 : ((k + 1) * k / 2) * 2 = (k + 1) * k := Nat.div_mul_cancel heven1
  have hdiv2 : ((k + 2) * (k + 1) / 2) * 2 = (k + 2) * (k + 1) := Nat.div_mul_cancel heven2
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
  have hmul : (k + 1 + ((k + 1) * (k + 2) ^ 2 +
      ((k + 1) * k / 2 * (k + 2 + 1) ^ 2 + (k + 2) * (k + 1) / 2 * (k + 1) ^ 2))) * 2 =
      2 * (k + 1) + 2 * (k + 1) * (k + 2) ^ 2 +
        (((k + 1) * k / 2) * 2) * (k + 2 + 1) ^ 2 +
        (((k + 2) * (k + 1) / 2) * 2) * (k + 1) ^ 2 := by ring
  rw [hmul, hdiv1, hdiv2]
  have hsub : ((k + 2) ^ 2 - 1) * ((k + 2) ^ 2 - (k + 2)) =
      (k ^ 2 + 4 * k + 3) * (k ^ 2 + 3 * k + 2) := by
    have h1' : (k + 2) ^ 2 - 1 = k ^ 2 + 4 * k + 3 := by
      have : (k + 2) ^ 2 = (k ^ 2 + 4 * k + 3) + 1 := by ring
      omega
    have h2' : (k + 2) ^ 2 - (k + 2) = k ^ 2 + 3 * k + 2 := by
      have : (k + 2) ^ 2 = (k ^ 2 + 3 * k + 2) + (k + 2) := by ring
      omega
    rw [h1', h2']
  rw [hsub]
  ring

/-! ### Section 3: Characters (`chi`, `theta`, `psi`) and norm fiber identities -/

lemma exp_two_pi_I_div_congr {N : ℕ} (hN : 0 < N) {a b : ℕ} (h : a % N = b % N) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (N : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (N : ℂ)) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have step (m : ℕ) :
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (N : ℂ)) =
        Complex.exp (2 * Real.pi * Complex.I * ((m % N : ℕ) : ℂ) / (N : ℂ)) := by
    have hdiv : (m : ℂ) = ((m / N : ℕ) : ℂ) * (N : ℂ) + ((m % N : ℕ) : ℂ) := by
      have hm : m / N * N + m % N = m := Nat.div_add_mod' m N
      exact_mod_cast hm.symm
    have harg : 2 * Real.pi * Complex.I * (m : ℂ) / (N : ℂ) =
        2 * Real.pi * Complex.I * ((m % N : ℕ) : ℂ) / (N : ℂ) +
          ((m / N : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hdiv]
      field_simp [hN0]
      ring
    rw [harg]
    exact Complex.exp_periodic.nat_mul (m / N) _
  rw [step a, step b, h]

lemma chi_zero (D : FieldData) (α : D.Lab) : D.chi α 0 = 0 := by
  simp [FieldData.chi]

lemma dlog_one (D : FieldData) : D.dlog 1 = 0 := by
  have hex : ∃ n : ℕ, D.gen ^ n = 1 := ⟨0, pow_zero _⟩
  unfold FieldData.dlog
  rw [dif_pos hex]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex (pow_zero _))

lemma chi_one (D : FieldData) (α : D.Lab) : D.chi α 1 = 1 := by
  simp [FieldData.chi, dlog_one]

lemma chi_ne_zero (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) : D.chi α x ≠ 0 := by
  simp [FieldData.chi, hx, Complex.exp_ne_zero]

lemma dlog_mul_mod (D : FieldData) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.dlog (x * y) % (D.q - 1) = (D.dlog x + D.dlog y) % (D.q - 1) := by
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu_ord : orderOf u = D.q - 1 := by
    rw [← orderOf_units, Units.val_mk0, orderOf_gen]
  have hpow : u ^ D.dlog (x * y) = u ^ (D.dlog x + D.dlog y) := by
    ext
    simp only [Units.val_pow_eq_pow_val, u, Units.val_mk0]
    rw [pow_add, gen_pow_dlog D (mul_ne_zero hx hy), gen_pow_dlog D hx, gen_pow_dlog D hy]
  have hmod := pow_eq_pow_iff_modEq.mp hpow
  simpa [hu_ord, Nat.ModEq] using hmod

lemma chi_pow_gen (D : FieldData) (α : D.Lab) (n : ℕ) :
    D.chi α (D.gen ^ n) =
      Complex.exp (2 * Real.pi * Complex.I * ((α.val * n : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ)) := by
  have hgn : D.gen ^ n ≠ 0 := pow_ne_zero n (gen_ne_zero D)
  simp only [FieldData.chi, if_neg hgn]
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu_ord : orderOf u = D.q - 1 := by
    rw [← orderOf_units, Units.val_mk0, orderOf_gen]
  have hpow : u ^ D.dlog (D.gen ^ n) = u ^ n := by
    ext
    simp only [Units.val_pow_eq_pow_val, u, Units.val_mk0]
    exact gen_pow_dlog D hgn
  have hmod : D.dlog (D.gen ^ n) % (D.q - 1) = n % (D.q - 1) := by
    simpa [hu_ord, Nat.ModEq] using pow_eq_pow_iff_modEq.mp hpow
  have hq : 0 < D.q - 1 := by have := D.one_lt_q; omega
  exact exp_two_pi_I_div_congr hq (by rw [Nat.mul_mod, hmod, ← Nat.mul_mod])

lemma chi_mul (D : FieldData) (α : D.Lab) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.chi α (x * y) = D.chi α x * D.chi α y := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [FieldData.chi, hx, hy, hxy, ↓reduceIte]
  rw [← Complex.exp_add]
  have hmod : (α.val * D.dlog (x * y)) % (D.q - 1) =
      (α.val * D.dlog x + α.val * D.dlog y) % (D.q - 1) := by
    rw [← mul_add, Nat.mul_mod, dlog_mul_mod D hx hy, ← Nat.mul_mod]
  have hq : 0 < D.q - 1 := by have := D.one_lt_q; omega
  have harg : 2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) +
      2 * Real.pi * Complex.I * ((α.val * D.dlog y : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) =
      2 * Real.pi * Complex.I * (((α.val * D.dlog x + α.val * D.dlog y : ℕ) : ℂ)) /
        ((D.q - 1 : ℕ) : ℂ) := by
    push_cast; ring
  rw [harg]
  exact exp_two_pi_I_div_congr hq hmod

lemma chi_add_label (D : FieldData) (α β : D.Lab) (x : D.Fq) :
    D.chi (α + β) x = D.chi α x * D.chi β x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero]
  · simp only [FieldData.chi, hx, ↓reduceIte]
    rw [← Complex.exp_add]
    have hq : 0 < D.q - 1 := by have := D.one_lt_q; omega
    have hmod : ((α + β).val * D.dlog x) % (D.q - 1) =
        (α.val * D.dlog x + β.val * D.dlog x) % (D.q - 1) := by
      rw [← add_mul, ZMod.val_add, Nat.mod_mul_mod]
    have harg : 2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) +
        2 * Real.pi * Complex.I * ((β.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) =
        2 * Real.pi * Complex.I * (((α.val * D.dlog x + β.val * D.dlog x : ℕ) : ℂ)) /
          ((D.q - 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [harg]
    exact exp_two_pi_I_div_congr hq hmod

lemma chi_zero_label (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.chi 0 x = 1 := by
  simp [FieldData.chi, hx]

lemma conj_chi (D : FieldData) (α : D.Lab) (x : D.Fq) :
    conj (D.chi α x) = D.chi (-α) x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero]
  · have hmul : D.chi (-α) x * D.chi α x = 1 := by
      rw [← chi_add_label, neg_add_cancel, chi_zero_label D hx]
    have hnorm : conj (D.chi α x) * D.chi α x = 1 := by
      simp only [FieldData.chi, hx, ↓reduceIte]
      let r : ℝ := 2 * Real.pi * ((α.val * D.dlog x : ℕ) : ℝ) / ((D.q - 1 : ℕ) : ℝ)
      have hreal : (r : ℂ) * Complex.I =
          2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) := by
        simp only [r]; push_cast; ring
      rw [← hreal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    exact mul_right_cancel₀ (chi_ne_zero D α hx) (hnorm.trans hmul.symm)

lemma chi_inv (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    D.chi α x⁻¹ = D.chi (-α) x := by
  have h1 : D.chi α x⁻¹ * D.chi α x = 1 := by
    rw [← chi_mul D α (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, chi_one]
  have h2 : D.chi (-α) x * D.chi α x = 1 := by
    rw [← chi_add_label, neg_add_cancel, chi_zero_label D hx]
  exact mul_right_cancel₀ (chi_ne_zero D α hx) (h1.trans h2.symm)

lemma chi_div (D : FieldData) (α : D.Lab) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.chi α (x / y) = D.chi α x * D.chi (-α) y := by
  rw [div_eq_mul_inv, chi_mul D α hx (inv_ne_zero hy), chi_inv D α hy]

lemma chi_neg_one_sq (D : FieldData) (α : D.Lab) : D.chi α (-1) * D.chi α (-1) = 1 := by
  have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [← chi_mul D α hm1 hm1, neg_mul_neg, one_mul, chi_one]

lemma chi_gen_ne (D : FieldData) {α β : D.Lab} (h : α ≠ β) :
    D.chi α D.gen ≠ D.chi β D.gen := by
  have h1 : D.gen ^ 1 = D.gen := pow_one D.gen
  rw [← h1, chi_pow_gen, chi_pow_gen, mul_one, mul_one]
  intro heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨k, hk⟩ := heq
  have hq1 : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by
    have := D.one_lt_q
    exact Nat.cast_ne_zero.mpr (by omega)
  have hk' : ((α.val : ℂ) - (β.val : ℂ)) / ((D.q - 1 : ℕ) : ℂ) = k := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    calc 2 * Real.pi * Complex.I * (((α.val : ℂ) - (β.val : ℂ)) / ((D.q - 1 : ℕ) : ℂ))
        = 2 * Real.pi * Complex.I * (α.val : ℂ) / ((D.q - 1 : ℕ) : ℂ) -
          2 * Real.pi * Complex.I * (β.val : ℂ) / ((D.q - 1 : ℕ) : ℂ) := by ring
      _ = (k : ℂ) * (2 * Real.pi * Complex.I) := by rw [hk]; ring
      _ = 2 * Real.pi * Complex.I * (k : ℂ) := by ring
  have hk'' : ((α.val : ℤ) - (β.val : ℤ)) = k * ((D.q - 1 : ℕ) : ℤ) := by
    exact_mod_cast (div_eq_iff hq1).mp hk'
  have ha : (α.val : ℤ) < (D.q - 1 : ℕ) := Int.ofNat_lt.mpr (ZMod.val_lt α)
  have hb : (β.val : ℤ) < (D.q - 1 : ℕ) := Int.ofNat_lt.mpr (ZMod.val_lt β)
  have ha0 : (0 : ℤ) ≤ α.val := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ β.val := Int.natCast_nonneg _
  have hk0 : k = 0 := by nlinarith
  have hval : α.val = β.val := by
    have : (α.val : ℤ) = (β.val : ℤ) := by nlinarith
    exact Int.ofNat.inj this
  exact h (ZMod.val_injective (D.q - 1) hval)

lemma sum_chi_units (D : FieldData) (α : D.Lab) :
    ∑ x : D.Fqˣ, D.chi α (x : D.Fq) = if α = 0 then ((D.q - 1 : ℕ) : ℂ) else 0 := by
  by_cases h0 : α = 0
  · subst h0
    simp only [↓reduceIte]
    have hterm : ∀ x : D.Fqˣ, D.chi 0 (x : D.Fq) = 1 := fun x => chi_zero_label D x.ne_zero
    simp [hterm, card_Fq_units]
  · simp only [h0, ↓reduceIte]
    let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
    have hreidx : ∑ x : D.Fqˣ, D.chi α (x : D.Fq) =
        ∑ x : D.Fqˣ, D.chi α ((u * x : D.Fqˣ) : D.Fq) :=
      (Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun _ => rfl).symm
    have hfac : ∑ x : D.Fqˣ, D.chi α ((u * x : D.Fqˣ) : D.Fq) =
        D.chi α D.gen * ∑ x : D.Fqˣ, D.chi α (x : D.Fq) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast
      exact chi_mul D α (gen_ne_zero D) x.ne_zero
    have hdiff : D.chi α D.gen - 1 ≠ 0 := by
      rw [← chi_zero_label D (gen_ne_zero D)]
      exact sub_ne_zero.mpr (chi_gen_ne D h0)
    have hmul0 : (D.chi α D.gen - 1) * ∑ x : D.Fqˣ, D.chi α (x : D.Fq) = 0 := by
      have heq := hreidx.trans hfac
      linear_combination -heq
    exact mul_eq_zero.mp hmul0 |>.resolve_left hdiff

lemma theta_zero (D : FieldData) (k : D.Lab2) : D.theta k 0 = 0 := by
  simp [FieldData.theta]

lemma dlog2_one (D : FieldData) : D.dlog2 1 = 0 := by
  have hex : ∃ n : ℕ, D.h ^ n = 1 := ⟨0, pow_zero _⟩
  unfold FieldData.dlog2
  rw [dif_pos hex]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex (pow_zero _))

lemma theta_one (D : FieldData) (k : D.Lab2) : D.theta k 1 = 1 := by
  simp [FieldData.theta, dlog2_one]

lemma theta_ne_zero (D : FieldData) (k : D.Lab2) {z : D.Fq2} (hz : z ≠ 0) : D.theta k z ≠ 0 := by
  simp [FieldData.theta, hz, Complex.exp_ne_zero]

lemma theta_pow_h (D : FieldData) (k : D.Lab2) (n : ℕ) :
    D.theta k (D.h ^ n) =
      Complex.exp (2 * Real.pi * Complex.I * ((k.val * n : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ)) := by
  have hhn : D.h ^ n ≠ 0 := pow_ne_zero n (h_ne_zero D)
  simp only [FieldData.theta, if_neg hhn]
  let u : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  have hu_ord : orderOf u = D.q ^ 2 - 1 := by
    rw [← orderOf_units, Units.val_mk0, h_order_eq]
  have hpow : u ^ D.dlog2 (D.h ^ n) = u ^ n := by
    ext
    simp only [Units.val_pow_eq_pow_val, u, Units.val_mk0]
    exact h_pow_dlog2 D hhn
  have hmod : D.dlog2 (D.h ^ n) % (D.q ^ 2 - 1) = n % (D.q ^ 2 - 1) := by
    simpa [hu_ord, Nat.ModEq] using pow_eq_pow_iff_modEq.mp hpow
  have hq : 0 < D.q ^ 2 - 1 := by
    have hq1 : 1 < D.q := D.one_lt_q
    have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq1 (by decide)
    omega
  exact exp_two_pi_I_div_congr hq (by rw [Nat.mul_mod, hmod, ← Nat.mul_mod])

lemma theta_mul (D : FieldData) (k : D.Lab2) (z₁ z₂ : D.Fq2) :
    D.theta k (z₁ * z₂) = D.theta k z₁ * D.theta k z₂ := by
  by_cases hz₁ : z₁ = 0
  · subst hz₁; simp [theta_zero]
  by_cases hz₂ : z₂ = 0
  · subst hz₂; simp [theta_zero]
  have hz : z₁ * z₂ ≠ 0 := mul_ne_zero hz₁ hz₂
  conv_lhs => rw [← h_pow_dlog2 D hz₁, ← h_pow_dlog2 D hz₂, ← pow_add]
  rw [theta_pow_h]
  simp only [FieldData.theta, if_neg hz₁, if_neg hz₂, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma theta_add_label (D : FieldData) (k₁ k₂ : D.Lab2) (z : D.Fq2) :
    D.theta (k₁ + k₂) z = D.theta k₁ z * D.theta k₂ z := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero]
  · simp only [FieldData.theta, hz, ↓reduceIte, ← Complex.exp_add]
    have hq : 0 < D.q ^ 2 - 1 := by
      have hq1 : 1 < D.q := D.one_lt_q
      have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq1 (by decide)
      omega
    have hmod : ((k₁ + k₂).val * D.dlog2 z) % (D.q ^ 2 - 1) =
        (k₁.val * D.dlog2 z + k₂.val * D.dlog2 z) % (D.q ^ 2 - 1) := by
      rw [← add_mul, ZMod.val_add, Nat.mod_mul_mod]
    have harg : 2 * Real.pi * Complex.I * ((k₁.val * D.dlog2 z : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ) +
        2 * Real.pi * Complex.I * ((k₂.val * D.dlog2 z : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ) =
        2 * Real.pi * Complex.I * (((k₁.val * D.dlog2 z + k₂.val * D.dlog2 z : ℕ) : ℂ)) /
          ((D.q ^ 2 - 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [harg]
    exact exp_two_pi_I_div_congr hq hmod

lemma theta_zero_label (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) : D.theta 0 z = 1 := by
  simp [FieldData.theta, hz]

lemma conj_theta (D : FieldData) (k : D.Lab2) (z : D.Fq2) :
    conj (D.theta k z) = D.theta (-k) z := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero]
  · have hmul : D.theta (-k) z * D.theta k z = 1 := by
      rw [← theta_add_label, neg_add_cancel, theta_zero_label D hz]
    have hnorm : conj (D.theta k z) * D.theta k z = 1 := by
      simp only [FieldData.theta, hz, ↓reduceIte]
      let r : ℝ := 2 * Real.pi * ((k.val * D.dlog2 z : ℕ) : ℝ) / ((D.q ^ 2 - 1 : ℕ) : ℝ)
      have hreal : (r : ℂ) * Complex.I =
          2 * Real.pi * Complex.I * ((k.val * D.dlog2 z : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ) := by
        simp only [r]; push_cast; ring
      rw [← hreal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    exact mul_right_cancel₀ (theta_ne_zero D k hz) (hnorm.trans hmul.symm)

lemma theta_inv (D : FieldData) (k : D.Lab2) {z : D.Fq2} (hz : z ≠ 0) :
    D.theta k z⁻¹ = D.theta (-k) z := by
  have h1 : D.theta k z⁻¹ * D.theta k z = 1 := by
    rw [← theta_mul, inv_mul_cancel₀ hz, theta_one]
  have h2 : D.theta (-k) z * D.theta k z = 1 := by
    rw [← theta_add_label, neg_add_cancel, theta_zero_label D hz]
  exact mul_right_cancel₀ (theta_ne_zero D k hz) (h1.trans h2.symm)

lemma theta_h_ne_one (D : FieldData) {k : D.Lab2} (hk : k ≠ 0) : D.theta k D.h ≠ 1 := by
  have h1 : D.h ^ 1 = D.h := pow_one D.h
  rw [← h1, theta_pow_h, mul_one]
  rw [Ne, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (NeZero.ne (D.q ^ 2 - 1))]
  have hk_pos : 0 < k.val := Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero k).mp hk)
  exact Nat.not_dvd_of_pos_of_lt hk_pos (ZMod.val_lt k)

lemma sum_theta_units (D : FieldData) (k : D.Lab2) :
    ∑ z : D.Fq2ˣ, D.theta k (z : D.Fq2) = if k = 0 then ((D.q ^ 2 - 1 : ℕ) : ℂ) else 0 := by
  by_cases h0 : k = 0
  · subst h0
    simp only [↓reduceIte]
    have hterm : ∀ z : D.Fq2ˣ, D.theta 0 (z : D.Fq2) = 1 := fun z => theta_zero_label D z.ne_zero
    simp [hterm, card_Fq2_units]
  · simp only [h0, ↓reduceIte]
    let u : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
    have hreidx : ∑ z : D.Fq2ˣ, D.theta k (z : D.Fq2) =
        ∑ z : D.Fq2ˣ, D.theta k ((u * z : D.Fq2ˣ) : D.Fq2) :=
      (Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun _ => rfl).symm
    have hfac : ∑ z : D.Fq2ˣ, D.theta k ((u * z : D.Fq2ˣ) : D.Fq2) =
        D.theta k D.h * ∑ z : D.Fq2ˣ, D.theta k (z : D.Fq2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      push_cast
      exact theta_mul D k D.h (z : D.Fq2)
    have hdiff : D.theta k D.h - 1 ≠ 0 := sub_ne_zero.mpr (theta_h_ne_one D h0)
    have hmul0 : (D.theta k D.h - 1) * ∑ z : D.Fq2ˣ, D.theta k (z : D.Fq2) = 0 := by
      have heq := hreidx.trans hfac
      linear_combination -heq
    exact mul_eq_zero.mp hmul0 |>.resolve_left hdiff

lemma theta_pow_q (D : FieldData) (k : D.Lab2) (z : D.Fq2) :
    D.theta k (z ^ D.q) = D.theta ((D.q : D.Lab2) * k) z := by
  by_cases hz : z = 0
  · subst hz
    have hq : D.q ≠ 0 := by have := D.one_lt_q; omega
    simp [zero_pow hq, theta_zero]
  · conv_lhs => rw [← h_pow_dlog2 D hz, ← pow_mul, mul_comm (D.dlog2 z) D.q]
    rw [theta_pow_h]
    simp only [FieldData.theta, if_neg hz]
    have hq : 0 < D.q ^ 2 - 1 := by
      have hq1 : 1 < D.q := D.one_lt_q
      have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq1 (by decide)
      omega
    apply exp_two_pi_I_div_congr hq
    have hmod1 : ((D.q : D.Lab2) * k).val % (D.q ^ 2 - 1) = (D.q * k.val) % (D.q ^ 2 - 1) := by
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod, Nat.mod_mod]
    have hmod : Nat.ModEq (D.q ^ 2 - 1) (((D.q : D.Lab2) * k).val * D.dlog2 z)
        (k.val * (D.q * D.dlog2 z)) := by
      have h' : Nat.ModEq (D.q ^ 2 - 1) (((D.q : D.Lab2) * k).val) (D.q * k.val) := hmod1
      calc (((D.q : D.Lab2) * k).val * D.dlog2 z)
          ≡ (D.q * k.val) * D.dlog2 z [MOD (D.q ^ 2 - 1)] := h'.mul_right (D.dlog2 z)
        _ = k.val * (D.q * D.dlog2 z) := by ring
    exact hmod.symm

lemma theta_algebraMap (D : FieldData) (k : D.Lab2) (x : D.Fq) :
    D.theta k (algebraMap D.Fq D.Fq2 x) = D.chi (D.restrLab k) x := by
  by_cases hx : x = 0
  · subst hx; simp [map_zero, theta_zero, chi_zero]
  · conv_lhs => rw [← gen_pow_dlog D hx, map_pow, algebraMap_gen, ← pow_mul]
    rw [theta_pow_h]
    simp only [FieldData.chi, if_neg hx]
    have hq : 1 < D.q := D.one_lt_q
    have hq2_pos : 0 < D.q ^ 2 - 1 := by
      have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq (by decide)
      omega
    have hq_sq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
      zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]; ring
    have harg_eq :
        2 * Real.pi * Complex.I * (((D.restrLab k).val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) =
        2 * Real.pi * Complex.I * (((D.restrLab k).val * D.dlog x * (D.q + 1) : ℕ) : ℂ) /
          ((D.q ^ 2 - 1 : ℕ) : ℂ) := by
      have hqp1 : ((D.q + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : D.q + 1 ≠ 0)
      have hqm1 : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : D.q - 1 ≠ 0)
      rw [hq_sq]
      push_cast
      field_simp [hqp1, hqm1]
    rw [harg_eq]
    apply exp_two_pi_I_div_congr hq2_pos
    have hrestr : (D.restrLab k).val = k.val % (D.q - 1) := by
      change ZMod.val (k.val : D.Lab) = k.val % (D.q - 1)
      exact ZMod.val_natCast (n := D.q - 1) k.val
    rw [hrestr]
    have hmod_sub : Nat.ModEq (D.q - 1) (k.val % (D.q - 1) * D.dlog x) (k.val * D.dlog x) :=
      Nat.mod_mul_mod k.val (D.dlog x) (D.q - 1)
    have hmod_mul : Nat.ModEq ((D.q - 1) * (D.q + 1))
        ((k.val % (D.q - 1) * D.dlog x) * (D.q + 1)) ((k.val * D.dlog x) * (D.q + 1)) := by
      rw [Nat.ModEq, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
      exact congrArg (· * (D.q + 1)) hmod_sub
    have hmod_fin : Nat.ModEq (D.q ^ 2 - 1)
        (k.val * ((D.q + 1) * D.dlog x)) ((k.val % (D.q - 1) * D.dlog x) * (D.q + 1)) := by
      have h : Nat.ModEq ((D.q - 1) * (D.q + 1))
          (k.val * ((D.q + 1) * D.dlog x)) ((k.val % (D.q - 1) * D.dlog x) * (D.q + 1)) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmod_mul.symm
      rwa [← hq_sq] at h
    exact hmod_fin

lemma theta_chi_nrm (D : FieldData) (k : D.Lab2) (ε : D.Lab) (z : D.Fq2) :
    D.theta k z * D.chi (-ε) (D.nrm z) =
      D.theta (k - ((ε.val * (D.q + 1) : ℕ) : D.Lab2)) z := by
  by_cases hz : z = 0
  · subst hz; simp [theta_zero, nrm_zero, chi_zero]
  · have hq : 1 < D.q := D.one_lt_q
    have hq2_pos : 0 < D.q ^ 2 - 1 := by
      have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq (by decide)
      omega
    have hq_sq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
      zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]; ring
    have hz_pow : z = D.h ^ D.dlog2 z := (h_pow_dlog2 D hz).symm
    have hnrm : D.nrm z = D.gen ^ D.dlog2 z := by
      conv_lhs => rw [hz_pow, nrm_pow, nrm_h]
    have hchi_eq : D.chi (-ε) (D.nrm z) = D.theta (-((ε.val * (D.q + 1) : ℕ) : D.Lab2)) z := by
      rw [hnrm, chi_pow_gen]
      conv_rhs => rw [hz_pow, theta_pow_h]
      have harg_eq :
          2 * Real.pi * Complex.I * (((-ε).val * D.dlog2 z : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) =
          2 * Real.pi * Complex.I * ((((-ε).val * (D.q + 1)) * D.dlog2 z : ℕ) : ℂ) /
            ((D.q ^ 2 - 1 : ℕ) : ℂ) := by
        have hqp1 : ((D.q + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : D.q + 1 ≠ 0)
        have hqm1 : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : D.q - 1 ≠ 0)
        rw [hq_sq]
        push_cast
        field_simp [hqp1, hqm1]
      rw [harg_eq]
      apply exp_two_pi_I_div_congr hq2_pos
      have hneg_sum : ((-ε).val + ε.val) % (D.q - 1) = 0 := by
        have h0 : ZMod.val (-ε + ε) = 0 := by rw [neg_add_cancel, ZMod.val_zero]
        rwa [ZMod.val_add (-ε) ε] at h0
      have hdvd1 : D.q - 1 ∣ (-ε).val + ε.val := Nat.dvd_of_mod_eq_zero hneg_sum
      have hdvd2 : D.q ^ 2 - 1 ∣ ((-ε).val + ε.val) * (D.q + 1) := by
        rw [hq_sq]
        rcases hdvd1 with ⟨m, hm⟩
        exact ⟨m, by rw [hm]; ring⟩
      have hlab2 : (((-ε).val * (D.q + 1) : ℕ) : D.Lab2) =
          -((ε.val * (D.q + 1) : ℕ) : D.Lab2) := by
        apply eq_neg_of_add_eq_zero_left
        rw [← Nat.cast_add, ← add_mul]
        exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvd2
      have hval_mod : ((-ε).val * (D.q + 1)) % (D.q ^ 2 - 1) =
          (-((ε.val * (D.q + 1) : ℕ) : D.Lab2)).val % (D.q ^ 2 - 1) := by
        rw [← hlab2, ZMod.val_natCast, Nat.mod_mod]
      rw [Nat.mul_mod, hval_mod, ← Nat.mul_mod]
    rw [hchi_eq, ← theta_add_label, sub_eq_add_neg]

lemma cusp_shift_ne_zero (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val))
    (ε : D.Lab) :
    k - ((ε.val * (D.q + 1) : ℕ) : D.Lab2) ≠ 0 := by
  intro h0
  have heq : k = ((ε.val * (D.q + 1) : ℕ) : D.Lab2) := sub_eq_zero.mp h0
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hdvd_mod : D.q + 1 ∣ D.q ^ 2 - 1 := by
    have hfac : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by zify [hq.le, hsq]; ring
    exact ⟨D.q - 1, hfac⟩
  let φ : D.Lab2 →+* ZMod (D.q + 1) := ZMod.castHom hdvd_mod (ZMod (D.q + 1))
  have hφ : φ k = φ ((ε.val * (D.q + 1) : ℕ) : D.Lab2) := congrArg φ heq
  have hzero : φ ((ε.val * (D.q + 1) : ℕ) : D.Lab2) = 0 := by
    rw [map_natCast, Nat.cast_mul]
    have hself : ((D.q + 1 : ℕ) : ZMod (D.q + 1)) = 0 := by simp
    rw [hself, mul_zero]
  rw [hzero] at hφ
  have hk_cast : (k.val : ZMod (D.q + 1)) = 0 := by
    simpa [φ] using hφ
  exact hreg ((ZMod.natCast_eq_zero_iff k.val (D.q + 1)).mp hk_cast)

lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by
  simp [FieldData.psi]

lemma psi_add (D : FieldData) (x y : D.Fq) : D.psi (x + y) = D.psi x * D.psi y := by
  simp only [FieldData.psi, map_add, ← Complex.exp_add]
  have hmod : (Algebra.trace (ZMod D.p) D.Fq x + Algebra.trace (ZMod D.p) D.Fq y).val % D.p =
      ((Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val) % D.p := by
    rw [ZMod.val_add, Nat.mod_mod]
  have harg : 2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) / (D.p : ℂ) +
      2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq y).val : ℕ) : ℂ) / (D.p : ℂ) =
      2 * Real.pi * Complex.I *
        ((((Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val : ℕ) : ℂ)) /
        (D.p : ℂ) := by
    push_cast; ring
  rw [harg]
  exact exp_two_pi_I_div_congr D.hp.pos hmod

lemma conj_psi (D : FieldData) (x : D.Fq) : conj (D.psi x) = D.psi (-x) := by
  have hmul : D.psi (-x) * D.psi x = 1 := by rw [← psi_add, neg_add_cancel, psi_zero]
  have hnorm : conj (D.psi x) * D.psi x = 1 := by
    simp only [FieldData.psi]
    let r : ℝ := 2 * Real.pi * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℝ) / (D.p : ℝ)
    have hreal : (r : ℂ) * Complex.I =
        2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) / (D.p : ℂ) := by
      simp only [r]; push_cast; ring
    rw [← hreal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hne : D.psi x ≠ 0 := by simp [FieldData.psi, Complex.exp_ne_zero]
  exact mul_right_cancel₀ hne (hnorm.trans hmul.symm)

lemma psi_nontrivial (D : FieldData) : ∃ x₀ : D.Fq, D.psi x₀ ≠ 1 := by
  have htr : Algebra.trace (ZMod D.p) D.Fq ≠ 0 := Algebra.trace_ne_zero (ZMod D.p) D.Fq
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : D.Fq, Algebra.trace (ZMod D.p) D.Fq x₀ ≠ 0 := by
    by_contra! hall
    exact htr (LinearMap.ext hall)
  refine ⟨x₀, fun heq => ?_⟩
  simp only [FieldData.psi] at heq
  rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff D.hp.ne_zero] at heq
  have hval_pos : 0 < (Algebra.trace (ZMod D.p) D.Fq x₀).val := by
    rw [Nat.pos_iff_ne_zero]
    intro hz
    exact hx₀ ((ZMod.val_eq_zero _).mp hz)
  exact absurd (Nat.le_of_dvd hval_pos heq) (not_le_of_gt (ZMod.val_lt _))

lemma sum_psi (D : FieldData) (u : D.Fq) :
    ∑ x : D.Fq, D.psi (u * x) = if u = 0 then (D.q : ℂ) else 0 := by
  by_cases hu : u = 0
  · subst hu; simp [psi_zero, card_Fq]
  · simp only [hu, ↓reduceIte]
    obtain ⟨x₀, hx₀⟩ := psi_nontrivial D
    let x₁ : D.Fq := x₀ / u
    have hreidx : ∑ x : D.Fq, D.psi (u * x) = ∑ x : D.Fq, D.psi (u * (x₁ + x)) :=
      (Fintype.sum_equiv (Equiv.addLeft x₁) _ _ fun _ => rfl).symm
    have hfac : ∑ x : D.Fq, D.psi (u * (x₁ + x)) = D.psi x₀ * ∑ x : D.Fq, D.psi (u * x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hmul : u * (x₁ + x) = x₀ + u * x := by simp [x₁, mul_add, mul_div_cancel₀ _ hu]
      rw [hmul, psi_add]
    have hmul0 : (D.psi x₀ - 1) * ∑ x : D.Fq, D.psi (u * x) = 0 := by
      have heq := hreidx.trans hfac
      linear_combination -heq
    exact mul_eq_zero.mp hmul0 |>.resolve_left (sub_ne_zero.mpr hx₀)

lemma sum_psi_ne_zero (D : FieldData) (u : D.Fq) (hu : u ≠ 0) :
    ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.psi (u * x) = -1 := by
  have htot := sum_psi D u
  simp only [if_neg hu] at htot
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.Fq)
    (fun x => x ≠ 0) (fun x => D.psi (u * x))
  have hzero_set : Finset.univ.filter (fun x : D.Fq => ¬ x ≠ 0) = {0} := by
    ext x; simp
  rw [hzero_set, Finset.sum_singleton, mul_zero, psi_zero, htot] at hpart
  linear_combination hpart

lemma nrm_surjective (D : FieldData) {u : D.Fq} (hu : u ≠ 0) :
    ∃ v : D.Fq2, v ≠ 0 ∧ D.nrm v = u := by
  refine ⟨D.h ^ D.dlog u, pow_ne_zero _ (h_ne_zero D), ?_⟩
  rw [nrm_pow, nrm_h, gen_pow_dlog D hu]

lemma sum_theta_nrm_fiber (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val))
    (u : D.Fq) (_hu : u ≠ 0) :
    ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = u), D.theta k v = 0 := by
  let ζ : D.Fq2 := D.h ^ (D.q - 1)
  have hζ_ne : ζ ≠ 0 := pow_ne_zero _ (h_ne_zero D)
  have hζ_nrm : D.nrm ζ = 1 := by
    dsimp [ζ]
    rw [nrm_pow, nrm_h, ← orderOf_gen D, pow_orderOf_eq_one]
  let S := ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = u), D.theta k v
  have hshift : D.theta k ζ * S = S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun v _ => ζ * v) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨mul_ne_zero hζ_ne hv.1, by rw [nrm_mul, hζ_nrm, one_mul, hv.2]⟩
    · intro v₁ _ v₂ _ heq
      exact mul_left_cancel₀ hζ_ne heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨ζ⁻¹ * w, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hζ_ne, one_mul]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨mul_ne_zero (inv_ne_zero hζ_ne) hw.1,
        by rw [nrm_mul, nrm_inv, hζ_nrm, inv_one, one_mul, hw.2]⟩
    · intro v _
      exact (theta_mul D k ζ v).symm
  have hθ_ne : D.theta k ζ ≠ 1 := by
    dsimp [ζ]
    rw [theta_pow_h, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (NeZero.ne (D.q ^ 2 - 1))]
    intro hdvd
    have hq : 1 < D.q := D.one_lt_q
    have hq_sq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
      zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]; ring
    have hdvd' : (D.q + 1) * (D.q - 1) ∣ k.val * (D.q - 1) := by
      simpa [← hq_sq] using hdvd
    exact hreg (Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd')
  have hmul0 : (D.theta k ζ - 1) * S = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hθ_ne)

lemma card_nrm_fiber (D : FieldData) {u : D.Fq} (hu : u ≠ 0) :
    (Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = u)).card = D.q + 1 := by
  obtain ⟨v₀, hv₀_ne, hv₀_nrm⟩ := nrm_surjective D hu
  let ζ : D.Fq2 := D.h ^ (D.q - 1)
  have hζ_ne : ζ ≠ 0 := pow_ne_zero _ (h_ne_zero D)
  have hζ_nrm : D.nrm ζ = 1 := by
    dsimp [ζ]; rw [nrm_pow, nrm_h, ← orderOf_gen D, pow_orderOf_eq_one]
  have hζ_ord : orderOf ζ = D.q + 1 := by
    dsimp [ζ]
    rw [orderOf_pow' D.h (by have := D.one_lt_q; omega), h_order_eq]
    have hq : 1 < D.q := D.one_lt_q
    have hq_sq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
      zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]; ring
    change (D.q ^ 2 - 1) / ((D.q ^ 2 - 1).gcd (D.q - 1)) = D.q + 1
    rw [hq_sq, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]
  have hbij : (Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = u)).card =
      (Finset.univ : Finset (Fin (D.q + 1))).card := by
    symm
    refine Finset.card_bij (fun j _ => v₀ * ζ ^ j.val) ?_ ?_ ?_
    · intro j _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨mul_ne_zero hv₀_ne (pow_ne_zero _ hζ_ne),
        by rw [nrm_mul, nrm_pow, hζ_nrm, one_pow, mul_one, hv₀_nrm]⟩
    · intro j₁ _ j₂ _ heq
      have hpow : ζ ^ j₁.val = ζ ^ j₂.val := mul_left_cancel₀ hv₀_ne heq
      let uζ : D.Fq2ˣ := Units.mk0 ζ hζ_ne
      have huζ : uζ ^ j₁.val = uζ ^ j₂.val := Units.ext hpow
      have hmod : j₁.val ≡ j₂.val [MOD orderOf uζ] := pow_eq_pow_iff_modEq.mp huζ
      rw [← orderOf_units, Units.val_mk0, hζ_ord] at hmod
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod j₁.isLt j₂.isLt)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      let w := v * v₀⁻¹
      have hw_ne : w ≠ 0 := mul_ne_zero hv.1 (inv_ne_zero hv₀_ne)
      have hw_nrm : D.nrm w = 1 := by
        rw [nrm_mul, nrm_inv, hv.2, hv₀_nrm, mul_inv_cancel₀ hu]
      have hw_pow : D.h ^ ((D.q + 1) * D.dlog2 w) = 1 := by
        have h1 : D.nrm w = D.gen ^ D.dlog2 w := by
          conv_lhs => rw [← h_pow_dlog2 D hw_ne, nrm_pow, nrm_h]
        have h2 : algebraMap D.Fq D.Fq2 (D.nrm w) = 1 := by rw [hw_nrm, map_one]
        rw [h1, map_pow, algebraMap_gen, ← pow_mul, mul_comm (D.q + 1)] at h2
        simpa [mul_comm] using h2
      have hdvd : D.q ^ 2 - 1 ∣ (D.q + 1) * D.dlog2 w := by
        rw [← h_order_eq]
        exact orderOf_dvd_of_pow_eq_one hw_pow
      have hq : 1 < D.q := D.one_lt_q
      have hq_sq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
        zify [hq.le, show 1 ≤ D.q ^ 2 by nlinarith]; ring
      rw [hq_sq] at hdvd
      have hdvd' : D.q - 1 ∣ D.dlog2 w := Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd
      rcases hdvd' with ⟨m, hm⟩
      let j : Fin (D.q + 1) := ⟨m % (D.q + 1), Nat.mod_lt m (by omega)⟩
      refine ⟨j, Finset.mem_univ _, ?_⟩
      have hj_pow : ζ ^ j.val = w := by
        have hord_pow : ζ ^ (D.q + 1) = 1 := by rw [← hζ_ord, pow_orderOf_eq_one]
        have hdiv : ζ ^ m = ζ ^ j.val := by
          have hdecomp : m = (D.q + 1) * (m / (D.q + 1)) + m % (D.q + 1) :=
            (Nat.div_add_mod m (D.q + 1)).symm
          conv_lhs => rw [hdecomp, pow_add, pow_mul, hord_pow, one_pow, one_mul]
        rw [← hdiv]
        dsimp [ζ]
        rw [← pow_mul, ← hm, h_pow_dlog2 D hw_ne]
      rw [hj_pow]
      dsimp [w]
      rw [mul_comm v v₀⁻¹, ← mul_assoc, mul_inv_cancel₀ hv₀_ne, one_mul]
  rw [hbij, Finset.card_fin]

lemma sum_psi_nrm (D : FieldData) {c : D.Fq} (hc : c ≠ 0) :
    ∑ w : D.Fq2, D.psi (c * D.nrm w) = -(D.q : ℂ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.Fq2)
    (fun w => w ≠ 0) (fun w => D.psi (c * D.nrm w))
  have h0set : Finset.univ.filter (fun w : D.Fq2 => ¬ w ≠ 0) = {0} := by ext w; simp
  rw [h0set, Finset.sum_singleton, nrm_zero, mul_zero, psi_zero] at hsplit
  have hpart := (Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun w : D.Fq2 => w ≠ 0))
    (t := Finset.univ.filter (fun u : D.Fq => u ≠ 0))
    (g := D.nrm) (f := fun w => D.psi (c * D.nrm w)) ?_).symm
  · have hfib : ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0),
        ∑ w ∈ (Finset.univ.filter (fun w : D.Fq2 => w ≠ 0)).filter (fun w => D.nrm w = u),
          D.psi (c * D.nrm w) =
        ((D.q : ℂ) + 1) * ∑ u ∈ Finset.univ.filter (fun u : D.Fq => u ≠ 0), D.psi (c * u) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u hu => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      rw [Finset.filter_filter]
      have hconst : ∑ w ∈ Finset.univ.filter (fun w : D.Fq2 => w ≠ 0 ∧ D.nrm w = u),
          D.psi (c * D.nrm w) =
          ∑ _w ∈ Finset.univ.filter (fun w : D.Fq2 => w ≠ 0 ∧ D.nrm w = u), D.psi (c * u) :=
        Finset.sum_congr rfl fun w hw => by
          simp only [Finset.mem_filter] at hw
          rw [hw.2.2]
      rw [hconst, Finset.sum_const, card_nrm_fiber D hu, nsmul_eq_mul]
      push_cast; rfl
    rw [← hsplit, hpart, hfib, sum_psi_ne_zero D c hc]
    ring
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact fun h0 => hw ((nrm_eq_zero D w).mp h0)

/-! ### Section 4: Orthonormal bases and unitary / irreducibility transfer (`det`, `st`, `ps`) -/

def basisMatrix {X ι : Type} (b : ι → X → ℂ) : Matrix X ι ℂ :=
  Matrix.of fun x j => b j x

lemma basisMatrix_conjTranspose_mul {X ι : Type} [Fintype X] [DecidableEq ι]
    (b : ι → X → ℂ)
    (horth : ∀ i j : ι, dotProduct (star (b i)) (b j) = if i = j then 1 else 0) :
    (basisMatrix b)ᴴ * basisMatrix b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsum : (∑ x : X, (basisMatrix b)ᴴ i x * basisMatrix b x j) =
      dotProduct (star (b i)) (b j) := by
    simp only [dotProduct, Matrix.conjTranspose_apply, basisMatrix, Matrix.of_apply, Pi.star_apply]
  rw [hsum, horth i j]

lemma matrix_mul_eq_one_symm {X : Type} [Fintype X] [DecidableEq X]
    {A B : Matrix X X ℂ} (h : A * B = 1) : B * A = 1 := by
  have hdet : IsUnit B.det := isUnit_iff_exists_inv.mpr ⟨A.det, by
    rw [mul_comm, ← Matrix.det_mul, h, Matrix.det_one]⟩
  have hAB : A = B⁻¹ := by
    calc A = A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hdet, Matrix.mul_one]
      _ = (A * B) * B⁻¹ := by rw [Matrix.mul_assoc]
      _ = B⁻¹ := by rw [h, Matrix.one_mul]
  rw [hAB, Matrix.mul_nonsing_inv B hdet]

lemma basisMatrix_mul_conjTranspose {X ι : Type} [Fintype X] [Fintype ι] [DecidableEq X] [DecidableEq ι]
    (b : ι → X → ℂ) (hcard : Fintype.card ι = Fintype.card X)
    (horth : ∀ i j : ι, dotProduct (star (b i)) (b j) = if i = j then 1 else 0) :
    basisMatrix b * (basisMatrix b)ᴴ = 1 := by
  let e : ι ≃ X := Fintype.equivOfCardEq hcard
  let Q' : Matrix X X ℂ := Matrix.of fun x y => basisMatrix b x (e.symm y)
  have hQ'_left : Q'ᴴ * Q' = 1 := by
    ext y₁ y₂
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 := congr_fun (congr_fun (basisMatrix_conjTranspose_mul b horth) (e.symm y₁)) (e.symm y₂)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    have heq : (e.symm y₁ = e.symm y₂) ↔ (y₁ = y₂) := e.symm.apply_eq_iff_eq
    simpa [Q', heq] using h1
  have hQ'_right : Q' * Q'ᴴ = 1 := matrix_mul_eq_one_symm hQ'_left
  ext x₁ x₂
  have h1 := congr_fun (congr_fun hQ'_right x₁) x₂
  simp only [Matrix.mul_apply, Matrix.one_apply] at h1 ⊢
  refine (Fintype.sum_equiv e (fun j => basisMatrix b x₁ j * (basisMatrix b)ᴴ j x₂)
    (fun y => Q' x₁ y * Q'ᴴ y x₂) fun j => ?_).trans h1
  simp [Q', Matrix.conjTranspose_apply]

lemma matEntry_eq_basisMatrix_mul {X ι : Type} [Fintype X]
    (M : Matrix X X ℂ) (b : ι → X → ℂ) (i j : ι) :
    matEntry M (b i) (b j) = ((basisMatrix b)ᴴ * M * basisMatrix b) i j := by
  simp only [matEntry, Matrix.mul_apply, Matrix.conjTranspose_apply, basisMatrix, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => by simp only [starRingEnd_apply]

lemma matEntry_eq_dot_mulVec {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v : X → ℂ) :
    matEntry M u v = dotProduct (star u) (M *ᵥ v) := by
  simp only [matEntry, dotProduct, Matrix.mulVec, Pi.star_apply, Complex.star_def,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    simp only [starRingEnd_apply]; ring

lemma isUnitaryRep_of_unitary_conj {G X ι : Type} [Monoid G] [Fintype X] [Fintype ι]
    [DecidableEq X] [DecidableEq ι]
    {R : G → Matrix X X ℂ} (hR : IsUnitaryRep R)
    (Q : Matrix X ι ℂ) (hQl : Qᴴ * Q = 1) (hQr : Q * Qᴴ = 1) :
    IsUnitaryRep (fun g => Qᴴ * R g * Q) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp [hR.1.1, hQl]
  · intro g h
    calc Qᴴ * R (g * h) * Q
        = Qᴴ * (R g * R h) * Q := by rw [hR.1.2]
      _ = Qᴴ * R g * (Q * Qᴴ) * R h * Q := by rw [hQr]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (Qᴴ * R g * Q) * (Qᴴ * R h * Q) := by simp only [Matrix.mul_assoc]
  · intro g
    dsimp only
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    have hU : R g * (R g)ᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (hR.2 g)
    calc (Qᴴ * R g * Q) * (Qᴴ * ((R g)ᴴ * Q))
        = Qᴴ * (R g * ((Q * Qᴴ) * (R g)ᴴ) * Q) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (R g * (R g)ᴴ * Q) := by rw [hQr, Matrix.one_mul]
      _ = Qᴴ * Q := by rw [hU, Matrix.one_mul]
      _ = 1 := hQl

lemma repEquiv_of_unitary_conj {G X ι : Type} [Fintype X] [Fintype ι]
    [DecidableEq X] [DecidableEq ι]
    (R : G → Matrix X X ℂ) (Q : Matrix X ι ℂ) (hQl : Qᴴ * Q = 1) (hQr : Q * Qᴴ = 1) :
    RepEquiv (fun g => Qᴴ * R g * Q) R :=
  ⟨Q, Qᴴ, hQr, hQl, fun g _ => by simp only [← Matrix.mul_assoc, hQr, Matrix.one_mul]⟩

lemma repEquiv_symm {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ} (h : RepEquiv R₁ R₂) :
    RepEquiv R₂ R₁ := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  refine ⟨B, A, hBA, hAB, fun g hg => ?_⟩
  calc B * R₂ g = B * R₂ g * (A * B) := by rw [hAB, Matrix.mul_one]
    _ = B * (R₂ g * A) * B := by simp only [Matrix.mul_assoc]
    _ = B * (A * R₁ g) * B := by rw [hinter g hg]
    _ = (B * A) * R₁ g * B := by simp only [Matrix.mul_assoc]
    _ = R₁ g * B := by rw [hBA, Matrix.one_mul]

lemma repEquiv_trans {G ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ} {R₃ : G → Matrix ι₃ ι₃ ℂ}
    (h12 : RepEquiv R₁ R₂) (h23 : RepEquiv R₂ R₃) : RepEquiv R₁ R₃ := by
  obtain ⟨A₁, B₁, hAB₁, hBA₁, hi₁⟩ := h12
  obtain ⟨A₂, B₂, hAB₂, hBA₂, hi₂⟩ := h23
  refine ⟨A₂ * A₁, B₁ * B₂, ?_, ?_, fun g hg => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, hAB₁, Matrix.one_mul, hAB₂]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA₂, Matrix.one_mul, hBA₁]
  · rw [Matrix.mul_assoc, hi₁ g hg, ← Matrix.mul_assoc, hi₂ g hg, Matrix.mul_assoc]

lemma isIrreducibleRep_of_repEquiv {G ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {R : G → Matrix ι ι ℂ} {R' : G → Matrix κ κ ℂ}
    (hi : IsIrreducibleRep R) (heq : RepEquiv R' R) : IsIrreducibleRep R' := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := heq
  have hne : Nonempty κ := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    obtain ⟨i₀⟩ := hi.1
    have h1 := congr_fun (congr_fun hAB i₀) i₀
    simp only [Matrix.mul_apply, Matrix.one_apply, ↓reduceIte] at h1
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  refine ⟨hne, fun W hW => ?_⟩
  let W' : Submodule ℂ (ι → ℂ) := W.map A.mulVecLin
  have hW' : IsInvariantSubspace R W' := by
    intro g u hu
    rcases hu with ⟨v, hv, rfl⟩
    refine ⟨R' g *ᵥ v, hW g v hv, ?_⟩
    change A *ᵥ (R' g *ᵥ v) = R g *ᵥ (A *ᵥ v)
    rw [Matrix.mulVec_mulVec, hinter g (Set.mem_univ g), ← Matrix.mulVec_mulVec]
  rcases hi.2 W' hW' with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hav : A *ᵥ v ∈ W' := ⟨v, hv, rfl⟩
    rw [hbot, Submodule.mem_bot] at hav
    have hbv : B *ᵥ (A *ᵥ v) = 0 := by rw [hav, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at hbv
  · right
    rw [eq_top_iff]
    intro v _
    have hav : A *ᵥ v ∈ W' := htop.symm ▸ Submodule.mem_top
    rcases hav with ⟨w, hw, hweq⟩
    have hbw : B *ᵥ (A *ᵥ w) = B *ᵥ (A *ᵥ v) := congrArg (fun x => B *ᵥ x) hweq
    rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec] at hbw
    rwa [← hbw]

lemma conj_isqrt (x : ℝ) : conj (isqrt x) = isqrt x := by simp [FieldData.isqrt]

lemma conj_isqrt_mul_isqrt {x : ℝ} (hx : 0 < x) :
    conj (isqrt x) * isqrt x = ((x : ℝ) : ℂ)⁻¹ := by
  rw [conj_isqrt]
  simp only [FieldData.isqrt, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hx.le, Complex.ofReal_inv]

lemma dot_conj_vT (D : FieldData) (s t : D.Fq) :
    dotProduct (star (D.vT s)) (D.vT t) = if s = t then 1 else 0 := by
  change (∑ y : Option D.Fq, conj (D.vT s y) * D.vT t y) = _
  rw [Fintype.sum_option]
  simp only [FieldData.vT, map_zero, zero_mul, zero_add, map_mul, starRingEnd_self_apply]
  have hterm : ∀ x : D.Fq,
      conj (isqrt D.q) * D.psi (s * x) * (isqrt D.q * conj (D.psi (t * x))) =
        (D.q : ℂ)⁻¹ * D.psi ((s - t) * x) := by
    intro x
    calc conj (isqrt D.q) * D.psi (s * x) * (isqrt D.q * conj (D.psi (t * x)))
        = (conj (isqrt D.q) * isqrt D.q) * (D.psi (s * x) * D.psi (-(t * x))) := by
          rw [conj_psi]; ring
      _ = (D.q : ℂ)⁻¹ * D.psi (s * x + -(t * x)) := by
          rw [conj_isqrt_mul_isqrt (q_pos D), ← psi_add, Complex.ofReal_natCast]
      _ = (D.q : ℂ)⁻¹ * D.psi ((s - t) * x) := by congr 2; ring
  simp_rw [hterm, ← Finset.mul_sum, sum_psi]
  by_cases hst : s = t
  · simp [hst, inv_mul_cancel₀ (q_complex_ne D)]
  · simp [hst, sub_eq_zero]

lemma vT_none (D : FieldData) (t : D.Fq) : D.vT t none = 0 := rfl

lemma vT_zero (D : FieldData) (β : D.Lab) : D.vT 0 = D.psVec β (some none) := by
  ext y; cases y <;> simp [FieldData.vT, FieldData.psVec, psi_zero]

lemma dot_star_add_left {X : Type} [Fintype X] (u₁ u₂ v : X → ℂ) :
    dotProduct (star (u₁ + u₂)) v = dotProduct (star u₁) v + dotProduct (star u₂) v := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

lemma dot_star_sub_left {X : Type} [Fintype X] (u₁ u₂ v : X → ℂ) :
    dotProduct (star (u₁ - u₂)) v = dotProduct (star u₁) v - dotProduct (star u₂) v := by
  simp [dotProduct, sub_mul, Finset.sum_sub_distrib]

lemma dot_star_smul_left {X : Type} [Fintype X] (c : ℂ) (u v : X → ℂ) :
    dotProduct (star (c • u)) v = conj c * dotProduct (star u) v := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma dot_star_add_right {X : Type} [Fintype X] (u v₁ v₂ : X → ℂ) :
    dotProduct (star u) (v₁ + v₂) = dotProduct (star u) v₁ + dotProduct (star u) v₂ := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

lemma dot_star_sub_right {X : Type} [Fintype X] (u v₁ v₂ : X → ℂ) :
    dotProduct (star u) (v₁ - v₂) = dotProduct (star u) v₁ - dotProduct (star u) v₂ := by
  simp [dotProduct, mul_sub, Finset.sum_sub_distrib]

lemma dot_star_smul_right {X : Type} [Fintype X] (c : ℂ) (u v : X → ℂ) :
    dotProduct (star u) (c • v) = c * dotProduct (star u) v := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

lemma dot_star_sum_left {X ι : Type} [Fintype X] (s : Finset ι) (f : ι → X → ℂ) (v : X → ℂ) :
    dotProduct (star (∑ i ∈ s, f i)) v = ∑ i ∈ s, dotProduct (star (f i)) v := by
  simp only [dotProduct, Pi.star_apply, Finset.sum_apply, star_sum, Finset.sum_mul]
  exact Finset.sum_comm

lemma dot_star_sum_right {X ι : Type} [Fintype X] (u : X → ℂ) (s : Finset ι) (f : ι → X → ℂ) :
    dotProduct (star u) (∑ i ∈ s, f i) = ∑ i ∈ s, dotProduct (star u) (f i) := by
  simp only [dotProduct, Pi.star_apply, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma wVec_eq_smul_sum (D : FieldData) (β δ : D.Lab) :
    D.wVec β δ = isqrt (D.q - 1) • ∑ t : D.Fqˣ,
      (D.chi δ (t : D.Fq) * D.chi (-β) (t : D.Fq)) • D.vT (t : D.Fq) := by
  ext y
  simp only [FieldData.wVec, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  symm
  refine Finset.sum_bij (fun (t : D.Fqˣ) _ => (t : D.Fq))
    (fun t _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.ne_zero⟩)
    (fun _ _ _ _ h => Units.ext h)
    (fun t ht => ⟨Units.mk0 t (Finset.mem_filter.mp ht).2, Finset.mem_univ _, rfl⟩)
    (fun _ _ => by simp [mul_assoc])

lemma dot_conj_wVec (D : FieldData) (β δ δ' : D.Lab) :
    dotProduct (star (D.wVec β δ)) (D.wVec β δ') = if δ = δ' then 1 else 0 := by
  rw [wVec_eq_smul_sum, wVec_eq_smul_sum]
  rw [dot_star_smul_left, dot_star_smul_right, dot_star_sum_left]
  simp_rw [dot_star_sum_right, dot_star_smul_left, dot_star_smul_right]
  have hsum_t : (∑ t : D.Fqˣ, ∑ s : D.Fqˣ,
        conj (D.chi δ (t : D.Fq) * D.chi (-β) (t : D.Fq)) *
          (D.chi δ' (s : D.Fq) * D.chi (-β) (s : D.Fq) *
            dotProduct (star (D.vT (t : D.Fq))) (D.vT (s : D.Fq)))) =
      ∑ t : D.Fqˣ, D.chi (δ' - δ) (t : D.Fq) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single t]
    · rw [dot_conj_vT, if_pos rfl, mul_one, map_mul, conj_chi, conj_chi, neg_neg]
      rw [← chi_add_label, ← chi_add_label, ← chi_add_label]
      congr 1; ring
    · intro s _ hs
      have hne : (t : D.Fq) ≠ (s : D.Fq) := fun heq => hs (Units.ext heq).symm
      rw [dot_conj_vT, if_neg hne, mul_zero, mul_zero]
    · intro hmem; exact (hmem (Finset.mem_univ t)).elim
  rw [hsum_t]
  have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := by
    have h1 := conj_isqrt_mul_isqrt (q_sub_one_pos D)
    simpa [Complex.ofReal_sub, Complex.ofReal_one] using h1
  calc conj (isqrt (D.q - 1)) * (isqrt (D.q - 1) * ∑ t : D.Fqˣ, D.chi (δ' - δ) (t : D.Fq))
      = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) * ∑ t : D.Fqˣ, D.chi (δ' - δ) (t : D.Fq) := by
        ring
    _ = ((D.q : ℂ) - 1)⁻¹ * (if δ' - δ = 0 then ((D.q - 1 : ℕ) : ℂ) else 0) := by
        rw [hisqrt, sum_chi_units]
    _ = if δ = δ' then 1 else 0 := by
        by_cases hdd : δ = δ'
        · subst hdd
          simp only [sub_self, ↓reduceIte]
          have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
            have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
          rw [hcard, inv_mul_cancel₀ (q_sub_one_complex_ne D)]
        · have hsub : δ' - δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hdd)
          simp [hdd, hsub]

lemma dot_conj_infty_vT (D : FieldData) (t : D.Fq) :
    dotProduct (star (fun y : Option D.Fq => if y = none then (1 : ℂ) else 0)) (D.vT t) = 0 := by
  simp [dotProduct, vT_none]

lemma dot_conj_vT_infty (D : FieldData) (t : D.Fq) :
    dotProduct (star (D.vT t)) (fun y : Option D.Fq => if y = none then (1 : ℂ) else 0) = 0 := by
  simp [dotProduct, vT_none]

lemma dot_conj_infty_wVec (D : FieldData) (β δ : D.Lab) :
    dotProduct (star (fun y : Option D.Fq => if y = none then (1 : ℂ) else 0)) (D.wVec β δ) = 0 := by
  rw [wVec_eq_smul_sum]
  simp only [dot_star_smul_right, dot_star_sum_right, dot_conj_infty_vT, mul_zero,
    Finset.sum_const_zero]

lemma dot_conj_wVec_infty (D : FieldData) (β δ : D.Lab) :
    dotProduct (star (D.wVec β δ)) (fun y : Option D.Fq => if y = none then (1 : ℂ) else 0) = 0 := by
  rw [wVec_eq_smul_sum]
  simp only [dot_star_smul_left, dot_star_sum_left, dot_conj_vT_infty, mul_zero,
    Finset.sum_const_zero]

lemma dot_conj_v0_wVec (D : FieldData) (β δ : D.Lab) :
    dotProduct (star (D.vT 0)) (D.wVec β δ) = 0 := by
  rw [wVec_eq_smul_sum]
  simp only [dot_star_smul_right, dot_star_sum_right]
  have hterm : ∀ t : D.Fqˣ, D.chi δ (t : D.Fq) * D.chi (-β) (t : D.Fq) *
      dotProduct (star (D.vT 0)) (D.vT (t : D.Fq)) = 0 := fun t => by
    rw [dot_conj_vT, if_neg t.ne_zero.symm, mul_zero]
  simp [hterm]

lemma dot_conj_wVec_v0 (D : FieldData) (β δ : D.Lab) :
    dotProduct (star (D.wVec β δ)) (D.vT 0) = 0 := by
  rw [wVec_eq_smul_sum]
  simp only [dot_star_smul_left, dot_star_sum_left]
  rw [Finset.sum_eq_zero fun t _ => ?_, mul_zero]
  rw [dot_conj_vT, if_neg t.ne_zero, mul_zero]

lemma psVec_orthonormal (D : FieldData) (β : D.Lab) (i j : Option (Option D.Lab)) :
    dotProduct (star (D.psVec β i)) (D.psVec β j) = if i = j then 1 else 0 := by
  rcases i with _ | (_ | δ) <;> rcases j with _ | (_ | δ')
  · simp [dotProduct, FieldData.psVec]
  · rw [← vT_zero D β]; exact dot_conj_infty_vT D 0
  · exact dot_conj_infty_wVec D β δ'
  · rw [← vT_zero D β]; exact dot_conj_vT_infty D 0
  · rw [← vT_zero D β, dot_conj_vT, if_pos rfl, if_pos rfl]
  · rw [← vT_zero D β]; exact dot_conj_v0_wVec D β δ'
  · exact dot_conj_wVec_infty D β δ
  · rw [← vT_zero D β]; exact dot_conj_wVec_v0 D β δ
  · simpa [FieldData.psVec] using dot_conj_wVec D β δ δ'

lemma stVec_none_eq (D : FieldData) (α : D.Lab) :
    D.stVec α none =
      (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) • D.psVec α none -
        isqrt (D.q + 1) • D.vT 0 := by
  ext y
  cases y with
  | none => simp [FieldData.stVec, FieldData.psVec, vT_none, mul_assoc]
  | some x => simp [FieldData.stVec, FieldData.psVec, FieldData.vT, psi_zero]

lemma detVec_eq_psVec (D : FieldData) (α : D.Lab) :
    D.detVec α =
      (isqrt (D.q + 1) * D.chi α (-1)) • D.psVec α none +
        (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ)) • D.vT 0 := by
  ext y
  cases y with
  | none => simp [FieldData.detVec, FieldData.psVec, vT_none]
  | some x =>
    simp only [FieldData.detVec, FieldData.psVec, FieldData.vT, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, zero_mul, psi_zero, mul_one, map_one, Option.some_ne_none, ↓reduceIte,
      mul_zero, zero_add]
    have hq_pos : (0 : ℝ) < D.q := q_pos D
    have hsq : (Real.sqrt D.q : ℂ) * isqrt D.q = 1 := by
      simp only [FieldData.isqrt, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hq_pos),
        Complex.ofReal_one]
    trans isqrt (D.q + 1) * ((Real.sqrt D.q : ℂ) * isqrt D.q)
    · rw [hsq, mul_one]
    · ring

lemma dot_conj_detVec_detVec (D : FieldData) (α : D.Lab) :
    dotProduct (star (D.detVec α)) (D.detVec α) = 1 := by
  have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have h1 : conj (D.chi α (-1)) * D.chi α (-1) = 1 := by
    rw [conj_chi, ← chi_add_label, neg_add_cancel, chi_zero_label D hm1]
  have hisqrt : conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = ((D.q : ℂ) + 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (by linarith [q_pos D] : (0 : ℝ) < D.q + 1)
    simpa [Complex.ofReal_add, Complex.ofReal_one] using h
  simp only [dotProduct, FieldData.detVec, Fintype.sum_option, Pi.star_apply, Complex.star_def,
    map_mul, map_one, mul_one]
  have hsum : (∑ _x : D.Fq, conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) =
      (D.q : ℂ) * ((D.q : ℂ) + 1)⁻¹ := by
    simp [hisqrt, card_Fq]
  trans (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) * (conj (D.chi α (-1)) * D.chi α (-1)) +
      (D.q : ℂ) * ((D.q : ℂ) + 1)⁻¹
  · rw [hsum]; ring
  · rw [hisqrt, h1]
    calc ((D.q : ℂ) + 1)⁻¹ * 1 + (D.q : ℂ) * ((D.q : ℂ) + 1)⁻¹
        = ((D.q : ℂ) + 1)⁻¹ * ((D.q : ℂ) + 1) := by ring
      _ = 1 := inv_mul_cancel₀ (q_add_one_complex_ne D)

lemma dot_conj_detVec_stVec (D : FieldData) (α : D.Lab) (j : Option D.Lab) :
    dotProduct (star (D.detVec α)) (D.stVec α j) = 0 := by
  have h_e : dotProduct (star (D.psVec α none)) (D.psVec α none) = 1 := by
    simpa using psVec_orthonormal D α none none
  have h_v : dotProduct (star (D.vT 0)) (D.vT 0) = 1 := by rw [dot_conj_vT, if_pos rfl]
  have h_ev : dotProduct (star (D.psVec α none)) (D.vT 0) = 0 := dot_conj_infty_vT D 0
  have h_ve : dotProduct (star (D.vT 0)) (D.psVec α none) = 0 := dot_conj_vT_infty D 0
  cases j with
  | none =>
    rw [detVec_eq_psVec, stVec_none_eq]
    simp only [dot_star_add_left, dot_star_sub_right, dot_star_smul_left, dot_star_smul_right,
      h_e, h_v, h_ev, h_ve]
    have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hchi : conj (D.chi α (-1)) * D.chi α (-1) = 1 := by
      rw [conj_chi, ← chi_add_label, neg_add_cancel, chi_zero_label D hm1]
    have hsq : conj (Real.sqrt D.q : ℂ) = (Real.sqrt D.q : ℂ) := Complex.conj_ofReal _
    simp only [map_mul, hsq]
    trans (conj (isqrt (D.q + 1)) * isqrt (D.q + 1) * (Real.sqrt D.q : ℂ)) *
        (conj (D.chi α (-1)) * D.chi α (-1) - 1)
    · ring
    · rw [hchi, sub_self, mul_zero]
  | some δ =>
    rw [detVec_eq_psVec]
    change dotProduct (star _) (D.wVec α δ) = 0
    have h1 : dotProduct (star (D.psVec α none)) (D.wVec α δ) = 0 := dot_conj_infty_wVec D α δ
    simp only [dot_star_add_left, dot_star_smul_left, h1, dot_conj_v0_wVec, mul_zero, add_zero]

lemma dot_conj_stVec (D : FieldData) (α : D.Lab) (i j : Option D.Lab) :
    dotProduct (star (D.stVec α i)) (D.stVec α j) = if i = j then 1 else 0 := by
  rcases i with _ | δ <;> rcases j with _ | δ'
  · rw [if_pos rfl, stVec_none_eq]
    have h_e : dotProduct (star (D.psVec α none)) (D.psVec α none) = 1 := by
      simpa using psVec_orthonormal D α none none
    have h_v : dotProduct (star (D.vT 0)) (D.vT 0) = 1 := by rw [dot_conj_vT, if_pos rfl]
    have h_ev : dotProduct (star (D.psVec α none)) (D.vT 0) = 0 := dot_conj_infty_vT D 0
    have h_ve : dotProduct (star (D.vT 0)) (D.psVec α none) = 0 := dot_conj_vT_infty D 0
    have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hchi : conj (D.chi α (-1)) * D.chi α (-1) = 1 := by
      rw [conj_chi, ← chi_add_label, neg_add_cancel, chi_zero_label D hm1]
    have hisqrt : conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = ((D.q : ℂ) + 1)⁻¹ := by
      have h := conj_isqrt_mul_isqrt (by linarith [q_pos D] : (0 : ℝ) < D.q + 1)
      simpa [Complex.ofReal_add, Complex.ofReal_one] using h
    have hsq : conj (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ) = (D.q : ℂ) := by
      rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (q_pos D).le]
      simp
    simp only [dot_star_sub_left, dot_star_sub_right, dot_star_smul_left, dot_star_smul_right,
      h_e, h_v, h_ev, h_ve, map_mul]
    trans (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
        (conj (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ)) *
        (conj (D.chi α (-1)) * D.chi α (-1)) +
      conj (isqrt (D.q + 1)) * isqrt (D.q + 1)
    · ring
    · rw [hisqrt, hsq, hchi]
      calc ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ) * 1 + ((D.q : ℂ) + 1)⁻¹
          = ((D.q : ℂ) + 1)⁻¹ * ((D.q : ℂ) + 1) := by ring
        _ = 1 := inv_mul_cancel₀ (q_add_one_complex_ne D)
  · rw [if_neg (by simp), stVec_none_eq]
    change dotProduct (star _) (D.wVec α δ') = 0
    have h1 : dotProduct (star (D.psVec α none)) (D.wVec α δ') = 0 := dot_conj_infty_wVec D α δ'
    simp only [dot_star_sub_left, dot_star_smul_left, h1, dot_conj_v0_wVec, mul_zero, sub_self]
  · rw [if_neg (by simp), stVec_none_eq]
    change dotProduct (star (D.wVec α δ)) _ = 0
    have h1 : dotProduct (star (D.wVec α δ)) (D.psVec α none) = 0 := dot_conj_wVec_infty D α δ
    simp only [dot_star_sub_right, dot_star_smul_right, h1, dot_conj_wVec_v0, mul_zero, sub_self]
  · by_cases hdd : δ = δ'
    · subst hdd; simp [FieldData.stVec, dot_conj_wVec]
    · simp [FieldData.stVec, hdd, dot_conj_wVec]

lemma multVec_orthonormal (D : FieldData) (i j : D.Lab) :
    dotProduct (star (D.multVec i)) (D.multVec j) = if i = j then 1 else 0 := by
  simp only [dotProduct, FieldData.multVec, Pi.star_apply, Complex.star_def, map_mul]
  have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (q_sub_one_pos D)
    simpa [Complex.ofReal_sub, Complex.ofReal_one] using h
  have hsum : (∑ x : D.Fqˣ, conj (isqrt (D.q - 1)) * conj (D.chi i (x : D.Fq)) *
        (isqrt (D.q - 1) * D.chi j (x : D.Fq))) =
      ((D.q : ℂ) - 1)⁻¹ * ∑ x : D.Fqˣ, D.chi (j - i) (x : D.Fq) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [conj_chi, show j - i = j + -i from sub_eq_add_neg j i, chi_add_label D j (-i)]
    calc conj (isqrt (D.q - 1)) * D.chi (-i) (x : D.Fq) * (isqrt (D.q - 1) * D.chi j (x : D.Fq))
        = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) * (D.chi j (x : D.Fq) * D.chi (-i) (x : D.Fq)) := by
          ring
      _ = ((D.q : ℂ) - 1)⁻¹ * (D.chi j (x : D.Fq) * D.chi (-i) (x : D.Fq)) := by rw [hisqrt]
  rw [hsum, sum_chi_units]
  by_cases hij : i = j
  · subst hij
    simp only [sub_self, ↓reduceIte]
    have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
      have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard, inv_mul_cancel₀ (q_sub_one_complex_ne D)]
  · have hsub : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp [hij, hsub]

/-! `psModel` as a unitary representation -/

def tRep (D : FieldData) (x : Option D.Fq) : Matrix (Fin 2) (Fin 2) D.Fq :=
  match x with
  | none => !![1, 0; 0, 1]
  | some a => !![a, 1; 1, 0]

def tRepInv (D : FieldData) (x : Option D.Fq) : Matrix (Fin 2) (Fin 2) D.Fq :=
  match x with
  | none => !![1, 0; 0, 1]
  | some a => !![0, 1; 1, -a]

def mobius (D : FieldData) (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) : Option D.Fq :=
  let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
  match x with
  | none => if c ≠ 0 then some (a / c) else none
  | some u => if c * u + d ≠ 0 then some ((a * u + b) / (c * u + d)) else none

def bMat (D : FieldData) (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) :
    Matrix (Fin 2) (Fin 2) D.Fq :=
  let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
  let det := M.det
  match x with
  | none => if c ≠ 0 then !![c, d; 0, -det / c] else !![a, b; 0, d]
  | some u => if c * u + d ≠ 0 then !![c * u + d, c; 0, det / (c * u + d)] else !![a * u + b, a; 0, c]

def cocycle (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) : ℂ :=
  D.chi α ((bMat D M x) 0 0) * D.chi β ((bMat D M x) 1 1)

lemma psModel_eq_ite (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (y x : Option D.Fq) :
    D.psModel α β M y x = if y = mobius D M x then cocycle D α β M x else 0 := by
  unfold FieldData.psModel mobius cocycle bMat
  rw [Matrix.det_fin_two]
  cases x <;> dsimp <;> split_ifs <;> simp_all

lemma bMat_upper (D : FieldData) (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) :
    (bMat D M x) 1 0 = 0 := by
  cases x <;> dsimp [bMat] <;> split_ifs <;> simp

lemma mul_tRep (D : FieldData) (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) :
    M * tRep D x = tRep D (mobius D M x) * bMat D M x := by
  cases x with
  | none =>
    dsimp [mobius, bMat]
    by_cases hc : M 1 0 = 0
    · simp only [hc, not_true_eq_false, ↓reduceIte]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [tRep, Matrix.mul_apply, Fin.sum_univ_two, hc]
    · simp only [hc, not_false_eq_true, ↓reduceIte]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [tRep, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
      · field_simp [hc]
      · field_simp [hc]; ring
  | some u =>
    dsimp [mobius, bMat]
    by_cases hcd : M 1 0 * u + M 1 1 = 0
    · simp only [hcd, not_true_eq_false, ↓reduceIte]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [tRep, Matrix.mul_apply, Fin.sum_univ_two, hcd]
    · simp only [hcd, not_false_eq_true, ↓reduceIte]
      have hcd' : u * M 1 0 + M 1 1 ≠ 0 := by rwa [mul_comm]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [tRep, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
      · field_simp [hcd, hcd']
      · field_simp [hcd, hcd']; ring

lemma tRepInv_mul_tRep (D : FieldData) (x : Option D.Fq) : tRepInv D x * tRep D x = 1 := by
  cases x <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two]

lemma tRep_det_ne_zero (D : FieldData) (x : Option D.Fq) : (tRep D x).det ≠ 0 := by
  cases x <;> simp [tRep, Matrix.det_fin_two]

lemma bMat_diag_ne_zero (D : FieldData) {M : Matrix (Fin 2) (Fin 2) D.Fq} (hM : M.det ≠ 0)
    (x : Option D.Fq) :
    (bMat D M x) 0 0 ≠ 0 ∧ (bMat D M x) 1 1 ≠ 0 := by
  have hdet_lhs : (M * tRep D x).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero hM (tRep_det_ne_zero D x)
  rw [mul_tRep D M x, Matrix.det_mul] at hdet_lhs
  have hdet_b : (bMat D M x).det ≠ 0 := right_ne_zero_of_mul hdet_lhs
  rw [Matrix.det_fin_two, bMat_upper, mul_zero, sub_zero] at hdet_b
  exact mul_ne_zero_iff.mp hdet_b

lemma tRep_mul_unique (D : FieldData) {y y' : Option D.Fq} {B₁ B₂ : Matrix (Fin 2) (Fin 2) D.Fq}
    (h10 : B₁ 1 0 = 0) (h20 : B₂ 1 0 = 0) (hB₂ : B₂ 0 0 ≠ 0)
    (heq : tRep D y * B₁ = tRep D y' * B₂) :
    y = y' ∧ B₁ = B₂ := by
  have hmul : B₁ = (tRepInv D y * tRep D y') * B₂ := by
    calc B₁ = 1 * B₁ := (one_mul B₁).symm
      _ = (tRepInv D y * tRep D y) * B₁ := by rw [tRepInv_mul_tRep]
      _ = tRepInv D y * (tRep D y * B₁) := Matrix.mul_assoc _ _ _
      _ = tRepInv D y * (tRep D y' * B₂) := by rw [heq]
      _ = (tRepInv D y * tRep D y') * B₂ := (Matrix.mul_assoc _ _ _).symm
  have hx10 : (tRepInv D y * tRep D y') 1 0 = 0 := by
    have h10' := congrArg (fun M : Matrix (Fin 2) (Fin 2) D.Fq => M 1 0) hmul
    rw [h10, Matrix.mul_apply, Fin.sum_univ_two, h20, mul_zero, add_zero] at h10'
    exact (mul_eq_zero.mp h10'.symm).resolve_right hB₂
  have hy : y = y' := by
    cases y with
    | none =>
      cases y' with
      | none => rfl
      | some b => simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two] at hx10
    | some a =>
      cases y' with
      | none => simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two] at hx10
      | some b =>
        simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two] at hx10
        rw [← sub_eq_add_neg] at hx10
        exact congrArg some (sub_eq_zero.mp hx10).symm
  refine ⟨hy, ?_⟩
  subst hy
  calc B₁ = (tRepInv D y * tRep D y) * B₁ := by rw [tRepInv_mul_tRep, one_mul]
    _ = tRepInv D y * (tRep D y * B₁) := Matrix.mul_assoc _ _ _
    _ = tRepInv D y * (tRep D y * B₂) := by rw [heq]
    _ = (tRepInv D y * tRep D y) * B₂ := (Matrix.mul_assoc _ _ _).symm
    _ = B₂ := by rw [tRepInv_mul_tRep, one_mul]

lemma mobius_bMat_mul (D : FieldData) {M₁ M₂ : Matrix (Fin 2) (Fin 2) D.Fq}
    (hM₁ : M₁.det ≠ 0) (hM₂ : M₂.det ≠ 0) (x : Option D.Fq) :
    mobius D (M₁ * M₂) x = mobius D M₁ (mobius D M₂ x) ∧
    bMat D (M₁ * M₂) x = bMat D M₁ (mobius D M₂ x) * bMat D M₂ x := by
  have hmul : tRep D (mobius D (M₁ * M₂) x) * bMat D (M₁ * M₂) x =
      tRep D (mobius D M₁ (mobius D M₂ x)) * (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) := by
    calc tRep D (mobius D (M₁ * M₂) x) * bMat D (M₁ * M₂) x
        = (M₁ * M₂) * tRep D x := (mul_tRep D (M₁ * M₂) x).symm
      _ = M₁ * (M₂ * tRep D x) := Matrix.mul_assoc _ _ _
      _ = M₁ * (tRep D (mobius D M₂ x) * bMat D M₂ x) := by rw [mul_tRep]
      _ = (M₁ * tRep D (mobius D M₂ x)) * bMat D M₂ x := (Matrix.mul_assoc _ _ _).symm
      _ = (tRep D (mobius D M₁ (mobius D M₂ x)) * bMat D M₁ (mobius D M₂ x)) * bMat D M₂ x := by
          rw [mul_tRep]
      _ = tRep D (mobius D M₁ (mobius D M₂ x)) * (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) :=
          Matrix.mul_assoc _ _ _
  have hb1 : (bMat D (M₁ * M₂) x) 1 0 = 0 := bMat_upper D _ _
  have hb2 : (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) 1 0 = 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, bMat_upper, bMat_upper]; simp
  have hB2_00 : (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) 0 0 ≠ 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, bMat_upper, mul_zero, add_zero]
    exact mul_ne_zero (bMat_diag_ne_zero D hM₁ _).1 (bMat_diag_ne_zero D hM₂ _).1
  exact tRep_mul_unique D hb1 hb2 hB2_00 hmul

lemma cocycle_mul (D : FieldData) (α β : D.Lab) {M₁ M₂ : Matrix (Fin 2) (Fin 2) D.Fq}
    (hM₁ : M₁.det ≠ 0) (hM₂ : M₂.det ≠ 0) (x : Option D.Fq) :
    cocycle D α β (M₁ * M₂) x =
      cocycle D α β M₁ (mobius D M₂ x) * cocycle D α β M₂ x := by
  have hb := (mobius_bMat_mul D hM₁ hM₂ x).2
  unfold cocycle
  rw [hb]
  have h00 : (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) 0 0 =
      (bMat D M₁ (mobius D M₂ x)) 0 0 * (bMat D M₂ x) 0 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, bMat_upper, mul_zero, add_zero]
  have h11 : (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) 1 1 =
      (bMat D M₁ (mobius D M₂ x)) 1 1 * (bMat D M₂ x) 1 1 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, bMat_upper, zero_mul, zero_add]
  rw [h00, h11]
  have hd1 := bMat_diag_ne_zero D hM₁ (mobius D M₂ x)
  have hd2 := bMat_diag_ne_zero D hM₂ x
  rw [chi_mul D α hd1.1 hd2.1, chi_mul D β hd1.2 hd2.2]
  ring

lemma gl_det_ne_zero (D : FieldData) (g : D.G) : (g : Matrix (Fin 2) (Fin 2) D.Fq).det ≠ 0 := by
  intro h
  have h1 : (g : Matrix (Fin 2) (Fin 2) D.Fq) * ((g⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
    exact_mod_cast Units.mul_inv g
  have hd := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, h, zero_mul] at hd
  exact zero_ne_one hd

lemma psModel_isUnitaryRep (D : FieldData) (α β : D.Lab) :
    IsUnitaryRep (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  have h1 : D.psModel α β (1 : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
    ext y x
    have hm : mobius D 1 x = x := by cases x <;> simp [mobius]
    have hc : cocycle D α β 1 x = 1 := by cases x <;> simp [cocycle, bMat, chi_one]
    rw [psModel_eq_ite, hm, hc]
    simp [Matrix.one_apply]
  have hmul : ∀ g₁ g₂ : D.G,
      D.psModel α β ((g₁ * g₂ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) =
        D.psModel α β (g₁ : Matrix (Fin 2) (Fin 2) D.Fq) *
          D.psModel α β (g₂ : Matrix (Fin 2) (Fin 2) D.Fq) := by
    intro g₁ g₂
    ext y x
    have hd1 := gl_det_ne_zero D g₁
    have hd2 := gl_det_ne_zero D g₂
    have hm := mobius_bMat_mul D hd1 hd2 x
    have hc := cocycle_mul D α β hd1 hd2 x
    change D.psModel α β ((g₁ : Matrix _ _ _) * (g₂ : Matrix _ _ _)) y x = _
    rw [Matrix.mul_apply, psModel_eq_ite, hm.1, hc]
    simp_rw [psModel_eq_ite]
    rw [Finset.sum_eq_single (mobius D (g₂ : Matrix _ _ _) x)]
    · simp only [↓reduceIte]; split_ifs <;> simp [mul_comm]
    · intro z _ hzne; simp [hzne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hunit : ∀ g : D.G,
      (D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))ᴴ *
        D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
    intro g
    ext x₁ x₂
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp_rw [Matrix.conjTranspose_apply, psModel_eq_ite]
    have hinj : Function.Injective (mobius D (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
      intro a b hab
      have ha := (mobius_bMat_mul D (gl_det_ne_zero D g⁻¹) (gl_det_ne_zero D g) a).1
      have hb := (mobius_bMat_mul D (gl_det_ne_zero D g⁻¹) (gl_det_ne_zero D g) b).1
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one] at ha hb
      have hone : ∀ u, mobius D 1 u = u := fun u => by cases u <;> simp [mobius]
      rw [hone] at ha hb
      rw [ha, hb, hab]
    by_cases h : x₁ = x₂
    · subst h
      rw [if_pos rfl, Finset.sum_eq_single (mobius D g x₁)]
      · simp only [↓reduceIte]
        have hd := bMat_diag_ne_zero D (gl_det_ne_zero D g) x₁
        unfold cocycle
        rw [star_mul, Complex.star_def, conj_chi, conj_chi]
        calc D.chi (-β) _ * D.chi (-α) _ * (D.chi α _ * D.chi β _)
            = (D.chi (-α) _ * D.chi α _) * (D.chi (-β) _ * D.chi β _) := by ring
          _ = D.chi (-α + α) _ * D.chi (-β + β) _ := by
              rw [chi_add_label, chi_add_label]
          _ = 1 := by simp [neg_add_cancel, chi_zero_label D hd.1, chi_zero_label D hd.2]
      · intro y _ hyne; simp [hyne]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy1 : y = mobius D g x₁
      · subst hy1
        have hy2 : mobius D g x₁ ≠ mobius D g x₂ := fun heq => h (hinj heq)
        simp [hy2]
      · simp [hy1]
  refine ⟨⟨h1, hmul⟩, fun g => ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact matrix_mul_eq_one_symm (hunit g)

lemma det_st_isUnitary_and_irred (D : FieldData) (α : D.Lab) :
    IsUnitaryRep (D.R (.inl α)) ∧ IsIrreducibleRep (D.R (.inl α)) ∧
    IsUnitaryRep (D.R (.inr (.inl α))) ∧ IsIrreducibleRep (D.R (.inr (.inl α))) := by
  let b : Unit ⊕ Option D.Lab → Option D.Fq → ℂ
    | .inl _ => D.detVec α
    | .inr i => D.stVec α i
  have horth : ∀ i j : Unit ⊕ Option D.Lab, dotProduct (star (b i)) (b j) = if i = j then 1 else 0 := by
    rintro (_ | i) (_ | j)
    · simp only [b, ↓reduceIte]; exact dot_conj_detVec_detVec D α
    · simp only [b]; rw [if_neg Sum.inl_ne_inr]; exact dot_conj_detVec_stVec D α j
    · simp only [b]; rw [if_neg Sum.inr_ne_inl]
      have h0 := dot_conj_detVec_stVec D α i
      have hconj : dotProduct (star (D.stVec α i)) (D.detVec α) =
          conj (dotProduct (star (D.detVec α)) (D.stVec α i)) := by
        simp only [dotProduct, Pi.star_apply, Complex.star_def, map_sum, map_mul,
          starRingEnd_self_apply]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [hconj, h0, map_zero]
    · simp only [b, Sum.inr.injEq]
      exact dot_conj_stVec D α i j
  have hcard : Fintype.card (Unit ⊕ Option D.Lab) = Fintype.card (Option D.Fq) := by
    rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_option, Fintype.card_option,
      card_Lab, card_Fq]
    have := D.one_lt_q; omega
  let Q := basisMatrix b
  have hQl : Qᴴ * Q = 1 := basisMatrix_conjTranspose_mul b horth
  have hQr : Q * Qᴴ = 1 := basisMatrix_mul_conjTranspose b hcard horth
  let M_block : D.G → Matrix (Unit ⊕ Option D.Lab) (Unit ⊕ Option D.Lab) ℂ :=
    fun g => Qᴴ * D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq) * Q
  have hU_block : IsUnitaryRep M_block :=
    isUnitaryRep_of_unitary_conj (psModel_isUnitaryRep D α α) Q hQl hQr
  have h65 := (GL2QFT.lemma_6_5 D).2.1 α
  let R_det : D.G → Matrix Unit Unit ℂ := fun g => Matrix.of fun i j => D.R (.inl α) g i j
  let R_st : D.G → Matrix (Option D.Lab) (Option D.Lab) ℂ :=
    fun g => Matrix.of fun i j => D.R (.inr (.inl α)) g i j
  have hblock_diag : ∀ g : D.G,
      (∀ (u : Unit) (j : Option D.Lab), M_block g (.inl u) (.inr j) = 0) ∧
      (∀ (i : Option D.Lab) (u : Unit), M_block g (.inr i) (.inl u) = 0) ∧
      (∀ u v : Unit, M_block g (.inl u) (.inl v) = R_det g u v) ∧
      (∀ i j : Option D.Lab, M_block g (.inr i) (.inr j) = R_st g i j) := by
    intro g
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u j
      dsimp only [M_block]
      rw [← matEntry_eq_basisMatrix_mul]
      dsimp only [b]
      rw [matEntry_eq_dot_mulVec]
      have h0 : dotProduct (star (D.detVec α)) (D.stVec α j) = 0 := dot_conj_detVec_stVec D α j
      have h1 := h65.2.1 g (D.stVec α j) h0
      simpa [dotProduct] using h1
    · intro i u
      dsimp only [M_block]
      rw [← matEntry_eq_basisMatrix_mul]
      dsimp only [b]
      rw [matEntry_eq_dot_mulVec]
      obtain ⟨c, hc⟩ := h65.1 g
      rw [hc]
      have h0 : dotProduct (star (D.stVec α i)) (D.detVec α) = 0 := by
        have hconj : dotProduct (star (D.stVec α i)) (D.detVec α) =
            conj (dotProduct (star (D.detVec α)) (D.stVec α i)) := by
          simp only [dotProduct, Pi.star_apply, Complex.star_def, map_sum, map_mul,
            starRingEnd_self_apply]
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [hconj, dot_conj_detVec_stVec, map_zero]
      have h1 : dotProduct (star (D.stVec α i)) (c • D.detVec α) =
          c * dotProduct (star (D.stVec α i)) (D.detVec α) := by
        simp only [dotProduct, Pi.star_apply, Complex.star_def, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [h1, h0, mul_zero]
    · intro u v
      exact (matEntry_eq_basisMatrix_mul (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) b
        (.inl u) (.inl v)).symm
    · intro i j
      exact (matEntry_eq_basisMatrix_mul (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) b
        (.inr i) (.inr j)).symm
  have hdet_u : IsUnitaryRep R_det := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext u v
      have h1 := congr_fun (congr_fun hU_block.1.1 (.inl u)) (.inl v)
      rw [← (hblock_diag 1).2.2.1 u v]
      simpa [Matrix.one_apply] using h1
    · intro g₁ g₂
      ext u v
      have hm := congr_fun (congr_fun (hU_block.1.2 g₁ g₂) (.inl u)) (.inl v)
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton] at hm
      rw [(hblock_diag _).2.2.1 u v, (hblock_diag g₁).2.2.1 u default,
        (hblock_diag g₂).2.2.1 default v] at hm
      have hz : (∑ x : Option D.Lab, M_block g₁ (.inl u) (.inr x) * M_block g₂ (.inr x) (.inl v)) = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [(hblock_diag g₁).1 u x, zero_mul]
      rw [hz, add_zero] at hm
      simpa [Matrix.mul_apply] using hm
    · intro g
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext u v
      have hu := Matrix.mem_unitaryGroup_iff.mp (hU_block.2 g)
      have hu0 := congr_fun (congr_fun hu (.inl u)) (.inl v)
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton] at hu0
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at hu0
      simp_rw [(hblock_diag g).2.2.1] at hu0
      have hz : (∑ x : Option D.Lab, M_block g (.inl u) (.inr x) * star (M_block g (.inl v) (.inr x))) = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [(hblock_diag g).1 u x, zero_mul]
      rw [hz, add_zero] at hu0
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using hu0
  have hdet_irr : IsIrreducibleRep R_det := by
    refine ⟨⟨()⟩, fun W _ => ?_⟩
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      rw [eq_top_iff]
      obtain ⟨v, hvW, hv0⟩ : ∃ v ∈ W, v ≠ 0 := by
        by_contra h
        push Not at h
        apply hbot
        rw [Submodule.eq_bot_iff]
        exact h
      have hv_ne : v () ≠ 0 := fun h0 => hv0 (funext fun ⟨⟩ => h0)
      intro w _
      have hw : (w () * (v ())⁻¹) • v = w := by
        ext ⟨⟩
        simp [mul_assoc, inv_mul_cancel₀ hv_ne]
      rw [← hw]
      exact W.smul_mem _ hvW
  have hst_u : IsUnitaryRep R_st := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext i j
      have h1 := congr_fun (congr_fun hU_block.1.1 (.inr i)) (.inr j)
      rw [← (hblock_diag 1).2.2.2 i j]
      simpa [Matrix.one_apply, Sum.inr.injEq] using h1
    · intro g₁ g₂
      ext i j
      have hm := congr_fun (congr_fun (hU_block.1.2 g₁ g₂) (.inr i)) (.inr j)
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton] at hm
      rw [(hblock_diag _).2.2.2 i j, (hblock_diag g₁).2.1 i default, zero_mul, zero_add] at hm
      simp_rw [(hblock_diag g₁).2.2.2, (hblock_diag g₂).2.2.2] at hm
      simpa [Matrix.mul_apply] using hm
    · intro g
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      have hu := Matrix.mem_unitaryGroup_iff.mp (hU_block.2 g)
      have hu0 := congr_fun (congr_fun hu (.inr i)) (.inr j)
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton] at hu0
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] at hu0
      rw [(hblock_diag g).2.1 i default, zero_mul, zero_add] at hu0
      simp_rw [(hblock_diag g).2.2.2] at hu0
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Sum.inr.injEq] using hu0
  have hst_irr : IsIrreducibleRep R_st := by
    refine ⟨⟨none⟩, fun W hW => ?_⟩
    let Qst : Matrix (Option D.Fq) (Option D.Lab) ℂ := basisMatrix (D.stVec α)
    have hQst_l : Qstᴴ * Qst = 1 := basisMatrix_conjTranspose_mul (D.stVec α) (dot_conj_stVec D α)
    have hQst_det : ∀ v : Option D.Lab → ℂ, dotProduct (star (D.detVec α)) (Qst *ᵥ v) = 0 := by
      intro v
      simp only [dotProduct, Matrix.mulVec, Qst, basisMatrix, Matrix.of_apply, Pi.star_apply,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h0 : (∑ x : Option D.Fq, star (D.detVec α x) * (D.stVec α j x * v j)) =
          v j * dotProduct (star (D.detVec α)) (D.stVec α j) := by
        simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [h0, dot_conj_detVec_stVec, mul_zero]
    have hQst_proj : ∀ u : Option D.Fq → ℂ, dotProduct (star (D.detVec α)) u = 0 →
        Qst *ᵥ (Qstᴴ *ᵥ u) = u := by
      intro u hu
      have hsum : Q *ᵥ (Qᴴ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, hQr, Matrix.one_mulVec]
      ext x
      have hx := congr_fun hsum x
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Finset.univ_unique,
        Finset.sum_singleton, Q, basisMatrix, Matrix.of_apply, Matrix.conjTranspose_apply, b,
        Complex.star_def] at hx
      simp only [dotProduct, Pi.star_apply, Complex.star_def] at hu
      rw [hu, mul_zero, zero_add] at hx
      simpa [Qst, basisMatrix, Matrix.mulVec, dotProduct, Complex.star_def] using hx
    have hQst_comm : ∀ g : D.G, ∀ v : Option D.Lab → ℂ,
        (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) *ᵥ (Qst *ᵥ v) =
          Qst *ᵥ (R_st g *ᵥ v) := by
      intro g v
      have horth_g : dotProduct (star (D.detVec α))
          ((D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) *ᵥ (Qst *ᵥ v)) = 0 :=
        h65.2.1 g (Qst *ᵥ v) (hQst_det v)
      rw [← hQst_proj _ horth_g]
      congr 1
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      ext i j
      rw [← matEntry_eq_basisMatrix_mul]
      rfl
    let W' : Submodule ℂ (Option D.Fq → ℂ) := W.map Qst.mulVecLin
    have hW'_orth : ∀ u ∈ W', dotProduct (star (D.detVec α)) u = 0 := by
      rintro u ⟨v, _, rfl⟩
      exact hQst_det v
    have hW'_inv : IsInvariantSubspace (fun g : D.G => D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) W' := by
      rintro g u ⟨v, hv, rfl⟩
      exact ⟨R_st g *ᵥ v, hW g v hv, (hQst_comm g v).symm⟩
    rcases h65.2.2 W' hW'_orth hW'_inv with hbot | htop
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hmem : Qst *ᵥ v ∈ W' := ⟨v, hv, rfl⟩
      rw [hbot, Submodule.mem_bot] at hmem
      have h1 : Qstᴴ *ᵥ (Qst *ᵥ v) = 0 := by rw [hmem, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hQst_l, Matrix.one_mulVec] at h1
    · right
      rw [eq_top_iff]
      intro v _
      have hmem : Qst *ᵥ v ∈ W' := htop (Qst *ᵥ v) (hQst_det v)
      rcases hmem with ⟨w, hw, hweq⟩
      have h1 : Qstᴴ *ᵥ (Qst *ᵥ w) = Qstᴴ *ᵥ (Qst *ᵥ v) := congrArg (fun u => Qstᴴ *ᵥ u) hweq
      rw [Matrix.mulVec_mulVec, hQst_l, Matrix.one_mulVec,
        Matrix.mulVec_mulVec, hQst_l, Matrix.one_mulVec] at h1
      rwa [← h1]
  exact ⟨hdet_u, hdet_irr, hst_u, hst_irr⟩

lemma ps_isUnitary_irred_equiv (D : FieldData) (ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}) :
    IsUnitaryRep (D.R (.inr (.inr (.inl ab)))) ∧
    IsIrreducibleRep (D.R (.inr (.inr (.inl ab)))) ∧
    RepEquiv (D.R (.inr (.inr (.inl ab))))
      (fun g : D.G => D.psModel ab.1.1 ab.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  let Q := basisMatrix (D.psVec ab.1.2)
  have hcard : Fintype.card (Option (Option D.Lab)) = Fintype.card (Option D.Fq) := by
    rw [Fintype.card_option, Fintype.card_option, Fintype.card_option, card_Lab, card_Fq]
    have := D.one_lt_q; omega
  have hQl : Qᴴ * Q = 1 := basisMatrix_conjTranspose_mul (D.psVec ab.1.2) (psVec_orthonormal D ab.1.2)
  have hQr : Q * Qᴴ = 1 := basisMatrix_mul_conjTranspose (D.psVec ab.1.2) hcard (psVec_orthonormal D ab.1.2)
  let R_ps : D.G → Matrix (Option (Option D.Lab)) (Option (Option D.Lab)) ℂ :=
    fun g => Matrix.of fun i j => D.R (.inr (.inr (.inl ab))) g i j
  have hReq : R_ps = fun g : D.G => Qᴴ * D.psModel ab.1.1 ab.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq) * Q := by
    ext g i j
    exact matEntry_eq_basisMatrix_mul (D.psModel ab.1.1 ab.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq))
      (D.psVec ab.1.2) i j
  have hU : IsUnitaryRep R_ps := by
    rw [hReq]
    exact isUnitaryRep_of_unitary_conj (psModel_isUnitaryRep D ab.1.1 ab.1.2) Q hQl hQr
  have heq : RepEquiv R_ps
      (fun g : D.G => D.psModel ab.1.1 ab.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
    rw [hReq]
    exact repEquiv_of_unitary_conj _ Q hQl hQr
  have hne : ab.1.1 ≠ ab.1.2 := fun h => by have := ab.2; rw [h] at this; exact lt_irrefl _ this
  have hirr : IsIrreducibleRep (D.R (.inr (.inr (.inl ab)))) :=
    isIrreducibleRep_of_repEquiv ((GL2QFT.lemma_6_5 D).1 ab.1.1 ab.1.2 hne) heq
  exact ⟨hU, hirr, heq⟩

/-! ### Section 5a: `borelModel` and `wprimeModel` identities -/

lemma borelModel_one (D : FieldData) (γ : D.Lab) :
    D.borelModel γ 1 0 1 = 1 := by
  ext y x
  simp only [FieldData.borelModel, Matrix.one_apply, div_one, one_mul, zero_mul,
    chi_one, psi_zero, mul_one]
  by_cases h : y = x
  · subst h; simp
  · have hne : (y : D.Fq) ≠ (x : D.Fq) := fun hval => h (Units.ext hval)
    simp [h, hne]

lemma borelModel_mul (D : FieldData) (γ : D.Lab)
    {a₁ d₁ a₂ d₂ : D.Fq} (ha₁ : a₁ ≠ 0) (_hd₁ : d₁ ≠ 0) (ha₂ : a₂ ≠ 0) (hd₂ : d₂ ≠ 0)
    (b₁ b₂ : D.Fq) :
    D.borelModel γ a₁ b₁ d₁ * D.borelModel γ a₂ b₂ d₂ =
      D.borelModel γ (a₁ * a₂) (a₁ * b₂ + b₁ * d₂) (d₁ * d₂) := by
  ext y x
  rw [Matrix.mul_apply]
  let z₀val : D.Fq := d₂ / a₂ * (x : D.Fq)
  have hz₀_ne : z₀val ≠ 0 := mul_ne_zero (div_ne_zero hd₂ ha₂) x.ne_zero
  let z₀ : D.Fqˣ := Units.mk0 z₀val hz₀_ne
  rw [Finset.sum_eq_single z₀]
  · have hz₀_cond : (z₀ : D.Fq) = d₂ / a₂ * (x : D.Fq) := rfl
    have hy_iff : ((y : D.Fq) = d₁ / a₁ * (z₀ : D.Fq)) ↔
        ((y : D.Fq) = (d₁ * d₂) / (a₁ * a₂) * (x : D.Fq)) := by
      simp only [hz₀_cond]
      constructor <;> intro h <;> rw [h] <;> field_simp [ha₁, ha₂]
    dsimp only [FieldData.borelModel]
    rw [if_pos hz₀_cond]
    by_cases hy : (y : D.Fq) = (d₁ * d₂) / (a₁ * a₂) * (x : D.Fq)
    · have hy1 : (y : D.Fq) = d₁ / a₁ * (z₀ : D.Fq) := hy_iff.mpr hy
      rw [if_pos hy1, if_pos hy]
      have hchi : D.chi γ d₁ * D.chi γ d₂ = D.chi γ (d₁ * d₂) := (chi_mul D γ _hd₁ hd₂).symm
      have harg : b₁ / a₁ * (z₀ : D.Fq) + b₂ / a₂ * (x : D.Fq) =
          (a₁ * b₂ + b₁ * d₂) / (a₁ * a₂) * (x : D.Fq) := by
        simp only [z₀, Units.val_mk0, z₀val]
        field_simp [ha₁, ha₂]
        ring
      have hpsi : D.psi (b₁ / a₁ * (z₀ : D.Fq)) * D.psi (b₂ / a₂ * (x : D.Fq)) =
          D.psi ((a₁ * b₂ + b₁ * d₂) / (a₁ * a₂) * (x : D.Fq)) := by
        rw [← psi_add, harg]
      calc D.chi γ d₁ * D.psi (b₁ / a₁ * (z₀ : D.Fq)) * (D.chi γ d₂ * D.psi (b₂ / a₂ * (x : D.Fq)))
          = (D.chi γ d₁ * D.chi γ d₂) *
              (D.psi (b₁ / a₁ * (z₀ : D.Fq)) * D.psi (b₂ / a₂ * (x : D.Fq))) := by ring
        _ = D.chi γ (d₁ * d₂) * D.psi ((a₁ * b₂ + b₁ * d₂) / (a₁ * a₂) * (x : D.Fq)) := by
            rw [hchi, hpsi]
    · have hy1 : (y : D.Fq) ≠ d₁ / a₁ * (z₀ : D.Fq) := fun h => hy (hy_iff.mp h)
      rw [if_neg hy1, if_neg hy, zero_mul]
  · intro z _ hz
    have hne : (z : D.Fq) ≠ d₂ / a₂ * (x : D.Fq) := fun h => hz (Units.ext h)
    simp [FieldData.borelModel, hne]
  · intro hmem; exact (hmem (Finset.mem_univ z₀)).elim

lemma borelModel_unitary (D : FieldData) (γ : D.Lab) {a d : D.Fq} (ha : a ≠ 0) (hd : d ≠ 0)
    (b : D.Fq) :
    D.borelModel γ a b d ∈ Matrix.unitaryGroup D.Fqˣ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext y₁ y₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  let x₀val : D.Fq := a / d * (y₁ : D.Fq)
  have hx₀_ne : x₀val ≠ 0 := mul_ne_zero (div_ne_zero ha hd) y₁.ne_zero
  let x₀ : D.Fqˣ := Units.mk0 x₀val hx₀_ne
  rw [Finset.sum_eq_single x₀]
  · have hy₁ : (y₁ : D.Fq) = d / a * (x₀ : D.Fq) := by
      simp only [x₀, Units.val_mk0, x₀val]; field_simp [ha, hd]
    have hy₂_iff : ((y₂ : D.Fq) = d / a * (x₀ : D.Fq)) ↔ y₁ = y₂ := by
      rw [← hy₁]
      exact ⟨fun h => Units.ext h.symm, fun h => by rw [h]⟩
    dsimp only [FieldData.borelModel, Matrix.conjTranspose_apply]
    rw [if_pos hy₁]
    by_cases hy : y₁ = y₂
    · subst hy
      rw [if_pos rfl, if_pos hy₁, Complex.star_def, map_mul, conj_chi, conj_psi]
      have hchi : D.chi γ d * D.chi (-γ) d = 1 := by
        rw [← chi_add_label, add_neg_cancel, chi_zero_label D hd]
      have hpsi : D.psi (b / a * (x₀ : D.Fq)) * D.psi (-(b / a * (x₀ : D.Fq))) = 1 := by
        rw [← psi_add, add_neg_cancel, psi_zero]
      calc D.chi γ d * D.psi (b / a * (x₀ : D.Fq)) * (D.chi (-γ) d * D.psi (-(b / a * (x₀ : D.Fq))))
          = (D.chi γ d * D.chi (-γ) d) *
              (D.psi (b / a * (x₀ : D.Fq)) * D.psi (-(b / a * (x₀ : D.Fq)))) := by ring
        _ = 1 := by rw [hchi, hpsi, mul_one]
    · have hy₂ : (y₂ : D.Fq) ≠ d / a * (x₀ : D.Fq) := fun h => hy (hy₂_iff.mp h)
      rw [if_neg hy, if_neg hy₂, star_zero, mul_zero]
  · intro x _ hx
    have hne : (y₁ : D.Fq) ≠ d / a * (x : D.Fq) := by
      intro h
      apply hx
      ext
      calc (x : D.Fq) = a / d * (d / a * (x : D.Fq)) := by field_simp [ha, hd]
        _ = a / d * (y₁ : D.Fq) := by rw [← h]
    simp [FieldData.borelModel, hne]
  · intro hmem; exact (hmem (Finset.mem_univ x₀)).elim

lemma borelModel_diag_comm_wprimeModel (D : FieldData) (k : D.Lab2)
    {u v : D.Fq} (hu : u ≠ 0) (hv : v ≠ 0) :
    D.borelModel (D.restrLab k) u 0 v * D.wprimeModel k =
      D.wprimeModel k * D.borelModel (D.restrLab k) v 0 u := by
  ext y x
  rw [Matrix.mul_apply, Matrix.mul_apply]
  let z₁ : D.Fqˣ := Units.mk0 (u / v * (y : D.Fq)) (mul_ne_zero (div_ne_zero hu hv) y.ne_zero)
  let z₂ : D.Fqˣ := Units.mk0 (u / v * (x : D.Fq)) (mul_ne_zero (div_ne_zero hu hv) x.ne_zero)
  rw [Finset.sum_eq_single z₁, Finset.sum_eq_single z₂]
  · have h1 : (y : D.Fq) = v / u * (z₁ : D.Fq) := by
      simp only [z₁, Units.val_mk0]; field_simp [hu, hv]
    have h2 : (z₂ : D.Fq) = u / v * (x : D.Fq) := rfl
    dsimp only [FieldData.borelModel, FieldData.wprimeModel]
    rw [if_pos h1, if_pos h2]
    simp only [zero_div, zero_mul, psi_zero, mul_one]
    have harg : (z₁ : D.Fq) * (x : D.Fq) = (y : D.Fq) * (z₂ : D.Fq) := by
      simp only [z₁, z₂, Units.val_mk0]; ring
    have htheta_lhs : D.chi (D.restrLab k) v * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) =
        D.theta k (algebraMap D.Fq D.Fq2 (z₂ : D.Fq)⁻¹) * D.chi (D.restrLab k) u := by
      have hx_ne : (x : D.Fq) ≠ 0 := x.ne_zero
      have hz₂_inv : (z₂ : D.Fq)⁻¹ = (v / u) * (x : D.Fq)⁻¹ := by
        simp only [z₂, Units.val_mk0]; field_simp [hu, hv, hx_ne]
      rw [hz₂_inv, map_mul, theta_mul, theta_algebraMap, theta_algebraMap, chi_div D _ hv hu]
      have hchinv : D.chi (-D.restrLab k) u * D.chi (D.restrLab k) u = 1 := by
        rw [← chi_add_label, neg_add_cancel, chi_zero_label D hu]
      calc D.chi (D.restrLab k) v * D.chi (D.restrLab k) (x : D.Fq)⁻¹
          = D.chi (D.restrLab k) v * D.chi (D.restrLab k) (x : D.Fq)⁻¹ *
              (D.chi (-D.restrLab k) u * D.chi (D.restrLab k) u) := by rw [hchinv, mul_one]
        _ = D.chi (D.restrLab k) v * D.chi (-D.restrLab k) u *
              D.chi (D.restrLab k) (x : D.Fq)⁻¹ * D.chi (D.restrLab k) u := by ring
    rw [harg]
    calc D.chi (D.restrLab k) v * (D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
            D.besselJ k ((y : D.Fq) * (z₂ : D.Fq)))
        = (D.chi (D.restrLab k) v * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹)) *
            D.besselJ k ((y : D.Fq) * (z₂ : D.Fq)) := by ring
      _ = (D.theta k (algebraMap D.Fq D.Fq2 (z₂ : D.Fq)⁻¹) * D.chi (D.restrLab k) u) *
            D.besselJ k ((y : D.Fq) * (z₂ : D.Fq)) := by rw [htheta_lhs]
      _ = D.theta k (algebraMap D.Fq D.Fq2 (z₂ : D.Fq)⁻¹) * D.besselJ k ((y : D.Fq) * (z₂ : D.Fq)) *
            D.chi (D.restrLab k) u := by ring
  · intro z _ hz
    have hne : (z : D.Fq) ≠ u / v * (x : D.Fq) := fun h => hz (Units.ext h)
    simp [FieldData.borelModel, hne]
  · intro hmem; exact (hmem (Finset.mem_univ z₂)).elim
  · intro z _ hz
    have hne : (y : D.Fq) ≠ v / u * (z : D.Fq) := by
      intro h
      apply hz
      ext
      calc (z : D.Fq) = u / v * (v / u * (z : D.Fq)) := by field_simp [hu, hv]
        _ = u / v * (y : D.Fq) := by rw [← h]
    simp [FieldData.borelModel, hne]
  · intro hmem; exact (hmem (Finset.mem_univ z₁)).elim

lemma borelModel_neg_one (D : FieldData) (k : D.Lab2) :
    D.borelModel (D.restrLab k) (-1) 0 (-1) =
      D.theta k (-1 : D.Fq2) • (1 : Matrix D.Fqˣ D.Fqˣ ℂ) := by
  ext y x
  simp only [FieldData.borelModel, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, div_neg,
    div_one, neg_neg, one_mul, neg_zero, zero_mul, psi_zero, mul_one]
  have hm1 : D.chi (D.restrLab k) (-1) = D.theta k (-1 : D.Fq2) := by
    rw [← theta_algebraMap, map_neg, map_one]
  by_cases h : y = x
  · subst h; simp [hm1]
  · have hne : (y : D.Fq) ≠ (x : D.Fq) := fun hval => h (Units.ext hval)
    simp [h, hne]

lemma algebraMap_ne_zero (D : FieldData) {x : D.Fq} (hx : x ≠ 0) :
    algebraMap D.Fq D.Fq2 x ≠ 0 :=
  (map_ne_zero_iff (algebraMap D.Fq D.Fq2) (algebraMap D.Fq D.Fq2).injective).mpr hx

lemma theta_neg_one_sq (D : FieldData) (k : D.Lab2) :
    D.theta k (-1 : D.Fq2) * D.theta k (-1 : D.Fq2) = 1 := by
  rw [← theta_mul, neg_mul_neg, one_mul, theta_one]

lemma wprimeModel_conjTranspose (D : FieldData) (k : D.Lab2) :
    (D.wprimeModel k)ᴴ = D.theta k (-1 : D.Fq2) • D.wprimeModel k := by
  ext y x
  simp only [Matrix.conjTranspose_apply, Complex.star_def, Matrix.smul_apply, smul_eq_mul,
    FieldData.wprimeModel, FieldData.besselJ, map_mul, map_neg, map_inv₀,
    map_sum, conj_psi, conj_theta]
  have hθ_y : D.theta (-k) (algebraMap D.Fq D.Fq2 (y : D.Fq))⁻¹ =
      D.theta k (algebraMap D.Fq D.Fq2 (y : D.Fq)) := by
    rw [theta_inv D (-k) (algebraMap_ne_zero D y.ne_zero), neg_neg]
  have hsum : (∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (x : D.Fq) * (y : D.Fq)),
        D.psi (-D.tr v) * D.theta (-k) v) =
      D.theta k (-1 : D.Fq2) * D.theta k (algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹)) *
        ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (y : D.Fq) * (x : D.Fq)),
          D.psi (D.tr v) * D.theta k v := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun v _ => -(v ^ D.q)) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      refine ⟨neg_ne_zero.mpr (pow_ne_zero _ hv.1), ?_⟩
      rw [nrm_neg]
      have hnrm_q : D.nrm (v ^ D.q) = D.nrm v := by
        apply (algebraMap D.Fq D.Fq2).injective
        rw [algebraMap_nrm, algebraMap_nrm, pow_q_sq, mul_comm]
      rw [hnrm_q, hv.2, mul_comm]
    · intro v₁ _ v₂ _ heq
      have hq : v₁ ^ D.q = v₂ ^ D.q := neg_inj.mp heq
      have hsq := congrArg (· ^ D.q) hq
      simpa [pow_q_sq] using hsq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨-(w ^ D.q), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨neg_ne_zero.mpr (pow_ne_zero _ hw.1), ?_⟩
        rw [nrm_neg]
        have hnrm_q : D.nrm (w ^ D.q) = D.nrm w := by
          apply (algebraMap D.Fq D.Fq2).injective
          rw [algebraMap_nrm, algebraMap_nrm, pow_q_sq, mul_comm]
        rw [hnrm_q, hw.2, mul_comm]
      · rw [neg_pow_q, pow_q_sq, neg_neg]
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have htr : D.tr (-(v ^ D.q)) = -D.tr v := by rw [tr_neg, tr_pow_q]
      have hvinv : v⁻¹ = algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹) * (-1) * (-(v ^ D.q)) := by
        have hmul : algebraMap D.Fq D.Fq2 (D.nrm v) = v * v ^ D.q := algebraMap_nrm D v
        have hvq_ne : v * v ^ D.q ≠ 0 := mul_ne_zero hv.1 (pow_ne_zero _ hv.1)
        calc v⁻¹ = v⁻¹ * (v * v ^ D.q) * (algebraMap D.Fq D.Fq2 (D.nrm v))⁻¹ := by
              rw [hmul, mul_assoc, mul_inv_cancel₀ hvq_ne, mul_one]
          _ = v ^ D.q * (algebraMap D.Fq D.Fq2 ((y : D.Fq) * (x : D.Fq)))⁻¹ := by
              rw [← mul_assoc, inv_mul_cancel₀ hv.1, one_mul, hv.2, mul_comm (x : D.Fq) (y : D.Fq)]
          _ = algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹) * (-1) * (-(v ^ D.q)) := by
              rw [← map_inv₀, mul_inv_rev, mul_comm ((x : D.Fq)⁻¹)]; ring
      have hθv : D.theta (-k) v =
          D.theta k (-1 : D.Fq2) * D.theta k (algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹)) *
            D.theta k (-(v ^ D.q)) := by
        rw [← theta_inv D k hv.1, hvinv, theta_mul, theta_mul]
        ring
      rw [htr, hθv]
      ring
  rw [hθ_y, hsum]
  have hy_canc : D.theta k (algebraMap D.Fq D.Fq2 (y : D.Fq)) *
      D.theta k (algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹)) =
      D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) := by
    rw [← theta_mul, ← map_mul, ← mul_assoc, mul_inv_cancel₀ y.ne_zero, one_mul]
  have hconj_q : (starRingEnd ℂ) (D.q : ℂ) = (D.q : ℂ) := Complex.conj_natCast D.q
  rw [hconj_q]
  calc D.theta k (algebraMap D.Fq D.Fq2 (y : D.Fq)) *
        (-((D.q : ℂ)⁻¹) *
          (D.theta k (-1 : D.Fq2) * D.theta k (algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹)) *
            ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (y : D.Fq) * (x : D.Fq)),
              D.psi (D.tr v) * D.theta k v))
      = D.theta k (-1 : D.Fq2) *
          ((D.theta k (algebraMap D.Fq D.Fq2 (y : D.Fq)) *
            D.theta k (algebraMap D.Fq D.Fq2 ((y : D.Fq)⁻¹ * (x : D.Fq)⁻¹))) *
            (-((D.q : ℂ)⁻¹) *
              ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (y : D.Fq) * (x : D.Fq)),
                D.psi (D.tr v) * D.theta k v)) := by ring
    _ = D.theta k (-1 : D.Fq2) *
          (D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
            (-((D.q : ℂ)⁻¹) *
              ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (y : D.Fq) * (x : D.Fq)),
                D.psi (D.tr v) * D.theta k v)) := by rw [hy_canc]
    _ = D.theta k (-1 : D.Fq2) *
          (D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq))⁻¹ *
            (-((D.q : ℂ)⁻¹) *
              ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (y : D.Fq) * (x : D.Fq)),
                D.psi (D.tr v) * D.theta k v)) := by rw [map_inv₀]

lemma wprimeModel_multVec_conj (D : FieldData) (k : D.Lab2) (ε δ : D.Lab) :
    ((basisMatrix D.multVec)ᴴ * D.wprimeModel k * basisMatrix D.multVec) ε δ =
      if ε + δ = D.restrLab k then
        -((D.q : ℂ)⁻¹) *
          D.gaussQ2 (D.theta (k - ((ε.val * (D.q + 1) : ℕ) : D.Lab2)))
      else 0 := by
  let γ := D.restrLab k
  let c : ℂ := conj (isqrt (D.q - 1)) * isqrt (D.q - 1)
  have hc : c = ((D.q : ℂ) - 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (q_sub_one_pos D)
    simpa [c, Complex.ofReal_sub, Complex.ofReal_one] using h
  have hmat : ((basisMatrix D.multVec)ᴴ * D.wprimeModel k * basisMatrix D.multVec) ε δ =
      c * ∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
        D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
          D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi δ (x : D.Fq) := by
    trans ∑ y : D.Fqˣ, ∑ x : D.Fqˣ, c *
        (D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
          D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi δ (x : D.Fq))
    · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, basisMatrix, Matrix.of_apply,
        FieldData.multVec, FieldData.wprimeModel, Complex.star_def, map_mul, conj_chi,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      dsimp only [c]; ring
    · simp_rw [← Finset.mul_sum]
  rw [hmat]
  have hreidx : (∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
        D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
          D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi δ (x : D.Fq)) =
      (∑ u : D.Fqˣ, D.chi (-ε) (u : D.Fq) * D.besselJ k (u : D.Fq)) *
        (∑ x : D.Fqˣ, D.chi (ε + δ - γ) (x : D.Fq)) := by
    let f1 : D.Fqˣ × D.Fqˣ → ℂ := fun p =>
      D.chi (-ε) (p.1 : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (p.2 : D.Fq)⁻¹) *
        D.besselJ k ((p.1 : D.Fq) * (p.2 : D.Fq)) * D.chi δ (p.2 : D.Fq)
    let f2 : D.Fqˣ × D.Fqˣ → ℂ := fun q =>
      (D.chi (-ε) (q.1 : D.Fq) * D.besselJ k (q.1 : D.Fq)) * D.chi (ε + δ - γ) (q.2 : D.Fq)
    have h1 : (∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
          D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi δ (x : D.Fq)) =
        ∑ p : D.Fqˣ × D.Fqˣ, f1 p := (Fintype.sum_prod_type f1).symm
    have h2 : (∑ u : D.Fqˣ, D.chi (-ε) (u : D.Fq) * D.besselJ k (u : D.Fq)) *
          (∑ x : D.Fqˣ, D.chi (ε + δ - γ) (x : D.Fq)) =
        ∑ q : D.Fqˣ × D.Fqˣ, f2 q := by
      rw [Fintype.sum_prod_type]
      simp only [f2, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    rw [h1, h2]
    let e : D.Fqˣ × D.Fqˣ ≃ D.Fqˣ × D.Fqˣ :=
      { toFun := fun ⟨y, x⟩ => (y * x, x)
        invFun := fun ⟨u, x⟩ => (u * x⁻¹, x)
        left_inv := fun ⟨y, x⟩ => by simp
        right_inv := fun ⟨u, x⟩ => by simp }
    refine Fintype.sum_equiv e f1 f2 fun ⟨y, x⟩ => ?_
    simp only [e, f1, f2, Equiv.coe_fn_mk]
    have hθx : D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) = D.chi (-γ) (x : D.Fq) := by
      rw [theta_algebraMap, chi_inv D γ x.ne_zero]
    have hmul_ε : D.chi (-ε) (((y * x : D.Fqˣ) : D.Fq)) =
        D.chi (-ε) (y : D.Fq) * D.chi (-ε) (x : D.Fq) := by
      push_cast; exact chi_mul D (-ε) y.ne_zero x.ne_zero
    have hlab_x : D.chi (-ε) (x : D.Fq) * D.chi (ε + δ - γ) (x : D.Fq) =
        D.chi (-γ) (x : D.Fq) * D.chi δ (x : D.Fq) := by
      rw [← chi_add_label, ← chi_add_label]
      congr 1; ring
    rw [hθx, hmul_ε]
    calc D.chi (-ε) (y : D.Fq) * D.chi (-γ) (x : D.Fq) * D.besselJ k ((y : D.Fq) * (x : D.Fq)) *
          D.chi δ (x : D.Fq)
        = D.chi (-ε) (y : D.Fq) * (D.chi (-γ) (x : D.Fq) * D.chi δ (x : D.Fq)) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq)) := by ring
      _ = D.chi (-ε) (y : D.Fq) * (D.chi (-ε) (x : D.Fq) * D.chi (ε + δ - γ) (x : D.Fq)) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq)) := by rw [hlab_x]
      _ = (D.chi (-ε) (y : D.Fq) * D.chi (-ε) (x : D.Fq) *
            D.besselJ k (((y * x : D.Fqˣ) : D.Fq))) * D.chi (ε + δ - γ) (x : D.Fq) := by
          push_cast; ring
  rw [hreidx, sum_chi_units]
  by_cases hsum_eq : ε + δ = γ
  · have hzero : ε + δ - γ = 0 := sub_eq_zero.mpr hsum_eq
    rw [if_pos hsum_eq, if_pos hzero]
    have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
      have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcard, hc, mul_comm (∑ u : D.Fqˣ, D.chi (-ε) (u : D.Fq) * D.besselJ k (u : D.Fq)),
      ← mul_assoc, inv_mul_cancel₀ (q_sub_one_complex_ne D), one_mul]
    simp only [FieldData.besselJ, Finset.mul_sum]
    have hpull : (∑ u : D.Fqˣ, ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (u : D.Fq)),
          D.chi (-ε) (u : D.Fq) * (-((D.q : ℂ)⁻¹) * (D.psi (D.tr v) * D.theta k v))) =
        -((D.q : ℂ)⁻¹) * ∑ u : D.Fqˣ, ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (u : D.Fq)),
          D.psi (D.tr v) * D.theta (k - ((ε.val * (D.q + 1) : ℕ) : D.Lab2)) v := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v hv => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rw [← theta_chi_nrm, hv.2]
      ring
    rw [hpull]
    congr 1
    let m := k - ((ε.val * (D.q + 1) : ℕ) : D.Lab2)
    have hfib : (∑ u : D.Fqˣ, ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (u : D.Fq)),
          D.psi (D.tr v) * D.theta m v) =
        ∑ v : D.Fq2, D.psi (D.tr v) * D.theta m v := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => ?_
      by_cases hv : v = 0
      · subst hv
        simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Finset.sum_const_zero,
          theta_zero, mul_zero]
      · have hnrm_ne : D.nrm v ≠ 0 := mt (nrm_eq_zero D v).mp hv
        let u₀ : D.Fqˣ := Units.mk0 (D.nrm v) hnrm_ne
        rw [Finset.sum_eq_single u₀]
        · rw [if_pos ⟨hv, rfl⟩]
        · intro u _ hu
          have hne : D.nrm v ≠ (u : D.Fq) := fun heq => hu (Units.ext heq.symm)
          simp [hv, hne]
        · intro hmem; exact (hmem (Finset.mem_univ u₀)).elim
    rw [hfib]
    unfold FieldData.gaussQ2
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v = 0
    · subst hv; simp [theta_zero]
    · rw [if_pos hv]; ring
  · have hnz : ε + δ - γ ≠ 0 := sub_ne_zero.mpr hsum_eq
    rw [if_neg hsum_eq, if_neg hnz, mul_zero, mul_zero]

lemma wprimeModel_unitary (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val)) :
    D.wprimeModel k ∈ Matrix.unitaryGroup D.Fqˣ ℂ := by
  let Q := basisMatrix D.multVec
  have hcard : Fintype.card D.Lab = Fintype.card D.Fqˣ := by
    rw [card_Lab, card_Fq_units]
  have hQl : Qᴴ * Q = 1 := basisMatrix_conjTranspose_mul D.multVec (multVec_orthonormal D)
  have hQr : Q * Qᴴ = 1 := basisMatrix_mul_conjTranspose D.multVec hcard (multVec_orthonormal D)
  let M := Qᴴ * D.wprimeModel k * Q
  let γ := D.restrLab k
  have hMM : M * Mᴴ = 1 := by
    ext ε₁ ε₂
    rw [Matrix.mul_apply, Matrix.one_apply]
    let δ₀ : D.Lab := γ - ε₁
    rw [Finset.sum_eq_single δ₀]
    · have h1 : ε₁ + δ₀ = γ := add_sub_cancel ε₁ γ
      have h2_iff : (ε₂ + δ₀ = γ) ↔ ε₁ = ε₂ := by
        constructor
        · intro h
          have : ε₂ + (γ - ε₁) = ε₁ + (γ - ε₁) := h.trans h1.symm
          exact (add_right_cancel this).symm
        · intro h; rw [← h, h1]
      dsimp only [M, Matrix.conjTranspose_apply]
      rw [wprimeModel_multVec_conj D k ε₁ δ₀, if_pos h1, wprimeModel_multVec_conj D k ε₂ δ₀]
      by_cases he : ε₁ = ε₂
      · subst he
        rw [if_pos h1, Complex.star_def, starRingEnd_apply]
        have hm : k - ((ε₁.val * (D.q + 1) : ℕ) : D.Lab2) ≠ 0 := cusp_shift_ne_zero D hreg ε₁
        have hgauss := (GL2QFT.lemma_A_4 D).2.2.2.2.2 _ hm
        have hq_pos : (0 : ℝ) < D.q := q_pos D
        have hnorm : ‖-((D.q : ℂ)⁻¹) *
            D.gaussQ2 (D.theta (k - ((ε₁.val * (D.q + 1) : ℕ) : D.Lab2)))‖ = 1 := by
          rw [norm_mul, norm_neg, norm_inv, Complex.norm_natCast, hgauss, inv_mul_cancel₀ hq_pos.ne']
        have hsq : (-((D.q : ℂ)⁻¹) *
              D.gaussQ2 (D.theta (k - ((ε₁.val * (D.q + 1) : ℕ) : D.Lab2)))) *
            star (-((D.q : ℂ)⁻¹) *
              D.gaussQ2 (D.theta (k - ((ε₁.val * (D.q + 1) : ℕ) : D.Lab2)))) = 1 := by
          rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow,
            Complex.ofReal_one]
        rw [if_pos rfl]
        exact hsq
      · have h2 : ε₂ + δ₀ ≠ γ := fun h => he (h2_iff.mp h)
        rw [if_neg h2, if_neg he, star_zero, mul_zero]
    · intro δ _ hδ
      have hne : ε₁ + δ ≠ γ := fun h => hδ (eq_sub_of_add_eq' h)
      dsimp only [M, Matrix.conjTranspose_apply]
      rw [wprimeModel_multVec_conj D k ε₁ δ, if_neg hne, zero_mul]
    · intro hmem; exact (hmem (Finset.mem_univ δ₀)).elim
  have hw_eq : D.wprimeModel k = Q * M * Qᴴ := by
    calc D.wprimeModel k
        = (Q * Qᴴ) * D.wprimeModel k * (Q * Qᴴ) := by rw [hQr, Matrix.one_mul, Matrix.mul_one]
      _ = Q * M * Qᴴ := by dsimp [M]; simp only [Matrix.mul_assoc]
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hw_eq,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (Q * M * Qᴴ) * (Q * (Mᴴ * Qᴴ))
      = Q * (M * (Qᴴ * Q) * Mᴴ) * Qᴴ := by simp only [Matrix.mul_assoc]
    _ = Q * (M * Mᴴ) * Qᴴ := by rw [hQl, Matrix.mul_one]
    _ = Q * Qᴴ := by rw [hMM, Matrix.mul_one]
    _ = 1 := hQr

lemma wprimeModel_sq (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val)) :
    D.wprimeModel k * D.wprimeModel k = D.theta k (-1 : D.Fq2) • (1 : Matrix D.Fqˣ D.Fqˣ ℂ) := by
  have hwU : D.wprimeModel k * (D.wprimeModel k)ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (wprimeModel_unitary D hreg)
  have hconj : (D.wprimeModel k)ᴴ * D.wprimeModel k = 1 := matrix_mul_eq_one_symm hwU
  have h1 : D.wprimeModel k = D.theta k (-1 : D.Fq2) • (D.wprimeModel k)ᴴ := by
    rw [wprimeModel_conjTranspose, smul_smul, theta_neg_one_sq, one_smul]
  conv_lhs => arg 1; rw [h1]
  rw [Matrix.smul_mul, hconj]

lemma wprimeModel_bruhat_rel (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val))
    {s : D.Fq} (hs : s ≠ 0) :
    D.wprimeModel k * D.borelModel (D.restrLab k) 1 s 1 * D.wprimeModel k =
      D.borelModel (D.restrLab k) 1 (-s⁻¹) 1 * D.wprimeModel k *
        D.borelModel (D.restrLab k) (-s) 1 (-s⁻¹) := by
  let γ := D.restrLab k
  have hm_ne : -s⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs)
  have hneg_s : -s ≠ 0 := neg_ne_zero.mpr hs
  ext y x
  let fib := fun t : D.Fq => Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = t)
  have hRHS : (D.borelModel γ 1 (-s⁻¹) 1 * D.wprimeModel k * D.borelModel γ (-s) 1 (-s⁻¹)) y x =
      D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * (-((D.q : ℂ)⁻¹)) *
        ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
          D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u := by
    rw [Matrix.mul_apply]
    let z₀val : D.Fq := (-s⁻¹) / (-s) * (x : D.Fq)
    have hz₀_ne : z₀val ≠ 0 := mul_ne_zero (div_ne_zero hm_ne hneg_s) x.ne_zero
    let z₀ : D.Fqˣ := Units.mk0 z₀val hz₀_ne
    rw [Finset.sum_eq_single z₀]
    · have hB1 : (D.borelModel γ 1 (-s⁻¹) 1 * D.wprimeModel k) y z₀ =
          D.psi (-s⁻¹ * (y : D.Fq)) * D.wprimeModel k y z₀ := by
        rw [Matrix.mul_apply, Finset.sum_eq_single y]
        · simp [FieldData.borelModel, chi_one]
        · intro z _ hz
          have hne : (y : D.Fq) ≠ (z : D.Fq) := fun heq => hz (Units.ext heq.symm)
          simp [FieldData.borelModel, hne]
        · intro hmem; exact (hmem (Finset.mem_univ y)).elim
      have hz₀_eq : (z₀ : D.Fq) = s⁻¹ * s⁻¹ * (x : D.Fq) := by
        simp only [z₀, Units.val_mk0, z₀val, div_neg]; ring
      have hB2_cond : (z₀ : D.Fq) = (-s⁻¹) / (-s) * (x : D.Fq) := rfl
      rw [hB1]
      dsimp only [FieldData.borelModel]
      rw [if_pos hB2_cond]
      dsimp only [FieldData.wprimeModel, FieldData.besselJ]
      have hz₀_inv : (z₀ : D.Fq)⁻¹ = s * s * (x : D.Fq)⁻¹ := by
        rw [hz₀_eq, mul_inv, mul_inv, inv_inv]
      have hθ_out : D.theta k (algebraMap D.Fq D.Fq2 (z₀ : D.Fq)⁻¹) * D.chi γ (-s⁻¹) =
          D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * D.chi γ (-s) := by
        rw [hz₀_inv, map_mul, theta_mul, theta_algebraMap]
        have hx_θ : D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) =
            D.chi γ (x : D.Fq)⁻¹ := theta_algebraMap D k _
        dsimp only [γ] at hx_θ ⊢
        rw [hx_θ, mul_comm (D.chi (D.restrLab k) (s * s)) (D.chi (D.restrLab k) (x : D.Fq)⁻¹),
          mul_assoc, ← chi_mul D (D.restrLab k) (mul_ne_zero hs hs) hm_ne,
          show s * s * -s⁻¹ = -s from by field_simp [hs]]
      have hsum_reidx : (∑ v ∈ fib ((y : D.Fq) * (z₀ : D.Fq)), D.psi (D.tr v) * D.theta k v) =
          D.chi γ (-s⁻¹) * ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
            D.psi (-(s⁻¹ * D.tr u)) * D.theta k u := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun v _ => algebraMap D.Fq D.Fq2 (-s) * v) ?_ ?_ ?_ ?_
        · intro v hv
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          refine ⟨mul_ne_zero (algebraMap_ne_zero D hneg_s) hv.1, ?_⟩
          rw [nrm_mul, nrm_algebraMap, hv.2, hz₀_eq]
          field_simp [hs]
        · intro v₁ _ v₂ _ heq
          exact mul_left_cancel₀ (algebraMap_ne_zero D hneg_s) heq
        · intro u hu
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hu
          refine ⟨algebraMap D.Fq D.Fq2 (-s⁻¹) * u, ?_, ?_⟩
          · simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨mul_ne_zero (algebraMap_ne_zero D hm_ne) hu.1, ?_⟩
            rw [nrm_mul, nrm_algebraMap, hu.2, hz₀_eq]
            field_simp [hs]
          · rw [← mul_assoc, ← map_mul]
            have h1 : (-s) * (-s⁻¹) = 1 := by field_simp [hs]
            rw [h1, map_one, one_mul]
        · intro v hv
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          have htr : D.tr v = -(s⁻¹ * D.tr (algebraMap D.Fq D.Fq2 (-s) * v)) := by
            rw [tr_algebraMap_mul]
            field_simp [hs]
          have hθ : D.theta k v = D.chi γ (-s⁻¹) * D.theta k (algebraMap D.Fq D.Fq2 (-s) * v) := by
            have hv' : v = algebraMap D.Fq D.Fq2 (-s⁻¹) * (algebraMap D.Fq D.Fq2 (-s) * v) := by
              rw [← mul_assoc, ← map_mul]
              have h1 : (-s⁻¹) * (-s) = 1 := by field_simp [hs]
              rw [h1, map_one, one_mul]
            conv_lhs => rw [hv']
            rw [theta_mul, theta_algebraMap]
          rw [htr, hθ]
          ring
      have hχ_one : D.chi γ (-s) * D.chi γ (-s⁻¹) = 1 := by
        rw [← chi_mul D γ hneg_s hm_ne]
        have h1 : (-s) * (-s⁻¹) = 1 := by field_simp [hs]
        rw [h1, chi_one]
      have hψ_arg : ∀ u : D.Fq2,
          -s⁻¹ * (y : D.Fq) + (1 / (-s) * (x : D.Fq) + -(s⁻¹ * D.tr u)) =
            -(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u)) := by
        intro u; field_simp [hs]; ring
      rw [mul_assoc, hsum_reidx]
      calc D.psi (-s⁻¹ * (y : D.Fq)) *
            (D.theta k (algebraMap D.Fq D.Fq2 (z₀ : D.Fq)⁻¹) *
              (-((D.q : ℂ)⁻¹) *
                (D.chi γ (-s⁻¹) * ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
                  D.psi (-(s⁻¹ * D.tr u)) * D.theta k u)) *
              (D.chi γ (-s⁻¹) * D.psi (1 / (-s) * (x : D.Fq))))
          = (D.theta k (algebraMap D.Fq D.Fq2 (z₀ : D.Fq)⁻¹) * D.chi γ (-s⁻¹)) *
              D.chi γ (-s⁻¹) * (-((D.q : ℂ)⁻¹)) *
              ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
                (D.psi (-s⁻¹ * (y : D.Fq)) * (D.psi (1 / (-s) * (x : D.Fq)) *
                  D.psi (-(s⁻¹ * D.tr u)))) * D.theta k u := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun u _ => by ring
        _ = D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * (D.chi γ (-s) * D.chi γ (-s⁻¹)) *
              (-((D.q : ℂ)⁻¹)) *
              ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
                D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u := by
            have hsum_psi : (∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
                  (D.psi (-s⁻¹ * (y : D.Fq)) * (D.psi (1 / (-s) * (x : D.Fq)) *
                    D.psi (-(s⁻¹ * D.tr u)))) * D.theta k u) =
                ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
                  D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u := by
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [← psi_add, ← psi_add, hψ_arg u]
            rw [hθ_out, hsum_psi]
            ring
        _ = D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * (-((D.q : ℂ)⁻¹)) *
              ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
                D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u := by
            rw [hχ_one, mul_one]
    · intro z _ hz
      have hne : (z : D.Fq) ≠ (-s⁻¹) / (-s) * (x : D.Fq) := fun h => hz (Units.ext h)
      simp only [FieldData.borelModel, hne, ↓reduceIte, mul_zero]
    · intro hmem; exact (hmem (Finset.mem_univ z₀)).elim
  have hLHS : (D.wprimeModel k * D.borelModel γ 1 s 1 * D.wprimeModel k) y x =
      D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * (-((D.q : ℂ)⁻¹)) *
        ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
          D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u := by
    have hstep1 : ∀ z : D.Fqˣ, (D.wprimeModel k * D.borelModel γ 1 s 1) y z =
        D.wprimeModel k y z * D.psi (s * (z : D.Fq)) := by
      intro z
      rw [Matrix.mul_apply, Finset.sum_eq_single z]
      · simp [FieldData.borelModel, chi_one]
      · intro w _ hw
        have hne : (w : D.Fq) ≠ (z : D.Fq) := fun h => hw (Units.ext h)
        dsimp only [FieldData.borelModel]
        rw [div_one, one_mul, if_neg hne, mul_zero]
      · intro hmem; exact (hmem (Finset.mem_univ z)).elim
    rw [Matrix.mul_apply]
    simp_rw [hstep1]
    have hexp : (∑ z : D.Fqˣ, D.wprimeModel k y z * D.psi (s * (z : D.Fq)) * D.wprimeModel k z x) =
        D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * ((D.q : ℂ)⁻¹ * (D.q : ℂ)⁻¹) *
          ∑ z : D.Fqˣ, ∑ v₁ ∈ fib ((y : D.Fq) * (z : D.Fq)), ∑ v₂ ∈ fib ((z : D.Fq) * (x : D.Fq)),
            D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹ * v₁ * v₂) *
              D.psi (s * (z : D.Fq) + D.tr v₁ + D.tr v₂) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      trans ∑ v₁ ∈ fib ((y : D.Fq) * (z : D.Fq)), ∑ v₂ ∈ fib ((z : D.Fq) * (x : D.Fq)),
          (D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) * ((D.q : ℂ)⁻¹ * (D.q : ℂ)⁻¹)) *
            (D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹ * v₁ * v₂) *
              D.psi (s * (z : D.Fq) + D.tr v₁ + D.tr v₂))
      · have hp1 : D.wprimeModel k y z * D.psi (s * (z : D.Fq)) =
            ∑ v₁ ∈ fib ((y : D.Fq) * (z : D.Fq)),
              D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹) *
                (-((D.q : ℂ)⁻¹) * (D.psi (D.tr v₁) * D.theta k v₁)) * D.psi (s * (z : D.Fq)) := by
          dsimp only [FieldData.wprimeModel, FieldData.besselJ]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        have hp2 : D.wprimeModel k z x =
            ∑ v₂ ∈ fib ((z : D.Fq) * (x : D.Fq)),
              D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
                (-((D.q : ℂ)⁻¹) * (D.psi (D.tr v₂) * D.theta k v₂)) := by
          dsimp only [FieldData.wprimeModel, FieldData.besselJ]
          rw [Finset.mul_sum, Finset.mul_sum]
        rw [hp1, hp2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun v₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v₂ _ => ?_
        rw [theta_mul, theta_mul, psi_add, psi_add]
        ring
      · simp_rw [← Finset.mul_sum]
    rw [hexp]
    let S₁ := Finset.univ.filter (fun p : D.Fqˣ × D.Fq2 × D.Fq2 =>
      p.2.1 ≠ 0 ∧ D.nrm p.2.1 = (y : D.Fq) * (p.1 : D.Fq) ∧
        p.2.2 ≠ 0 ∧ D.nrm p.2.2 = (p.1 : D.Fq) * (x : D.Fq))
    let S₂ := Finset.univ.filter (fun q : D.Fq2 × D.Fq2 =>
      q.1 ≠ 0 ∧ D.nrm q.1 = (y : D.Fq) * (x : D.Fq) ∧ q.2 ≠ 0)
    have hS1 : (∑ z : D.Fqˣ, ∑ v₁ ∈ fib ((y : D.Fq) * (z : D.Fq)),
          ∑ v₂ ∈ fib ((z : D.Fq) * (x : D.Fq)),
            D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹ * v₁ * v₂) *
              D.psi (s * (z : D.Fq) + D.tr v₁ + D.tr v₂)) =
        ∑ p ∈ S₁, D.theta k (algebraMap D.Fq D.Fq2 (p.1 : D.Fq)⁻¹ * p.2.1 * p.2.2) *
          D.psi (s * (p.1 : D.Fq) + D.tr p.2.1 + D.tr p.2.2) := by
      have hf : ∀ z : D.Fqˣ,
          (∑ v₁ ∈ fib ((y : D.Fq) * (z : D.Fq)), ∑ v₂ ∈ fib ((z : D.Fq) * (x : D.Fq)),
            D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹ * v₁ * v₂) *
              D.psi (s * (z : D.Fq) + D.tr v₁ + D.tr v₂)) =
          ∑ v₁ : D.Fq2, ∑ v₂ : D.Fq2,
            if v₁ ≠ 0 ∧ D.nrm v₁ = (y : D.Fq) * (z : D.Fq) ∧
                v₂ ≠ 0 ∧ D.nrm v₂ = (z : D.Fq) * (x : D.Fq) then
              D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹ * v₁ * v₂) *
                D.psi (s * (z : D.Fq) + D.tr v₁ + D.tr v₂)
            else 0 := by
        intro z
        simp only [fib, Finset.sum_filter]
        refine Finset.sum_congr rfl fun v₁ _ => ?_
        by_cases h1 : v₁ ≠ 0 ∧ D.nrm v₁ = (y : D.Fq) * (z : D.Fq)
        · rw [if_pos h1]
          refine Finset.sum_congr rfl fun v₂ _ => ?_
          by_cases h2 : v₂ ≠ 0 ∧ D.nrm v₂ = (z : D.Fq) * (x : D.Fq)
          · simp [h1, h2]
          · simp [h2]
        · rw [if_neg h1]
          symm
          exact Finset.sum_eq_zero fun v₂ _ => if_neg fun h => h1 ⟨h.1, h.2.1⟩
      simp_rw [hf]
      have hprod : (∑ z : D.Fqˣ, ∑ v₁ : D.Fq2, ∑ v₂ : D.Fq2,
            if v₁ ≠ 0 ∧ D.nrm v₁ = (y : D.Fq) * (z : D.Fq) ∧
                v₂ ≠ 0 ∧ D.nrm v₂ = (z : D.Fq) * (x : D.Fq) then
              D.theta k (algebraMap D.Fq D.Fq2 (z : D.Fq)⁻¹ * v₁ * v₂) *
                D.psi (s * (z : D.Fq) + D.tr v₁ + D.tr v₂)
            else 0) =
          ∑ p : D.Fqˣ × D.Fq2 × D.Fq2,
            if p.2.1 ≠ 0 ∧ D.nrm p.2.1 = (y : D.Fq) * (p.1 : D.Fq) ∧
                p.2.2 ≠ 0 ∧ D.nrm p.2.2 = (p.1 : D.Fq) * (x : D.Fq) then
              D.theta k (algebraMap D.Fq D.Fq2 (p.1 : D.Fq)⁻¹ * p.2.1 * p.2.2) *
                D.psi (s * (p.1 : D.Fq) + D.tr p.2.1 + D.tr p.2.2)
            else 0 := by
        symm
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun z _ => Fintype.sum_prod_type _
      rw [hprod]
      symm
      exact Finset.sum_filter _ _
    have hbij : (∑ p ∈ S₁, D.theta k (algebraMap D.Fq D.Fq2 (p.1 : D.Fq)⁻¹ * p.2.1 * p.2.2) *
          D.psi (s * (p.1 : D.Fq) + D.tr p.2.1 + D.tr p.2.2)) =
        ∑ q ∈ S₂, D.theta k q.1 *
          D.psi (s * (D.nrm q.2 * (x : D.Fq)⁻¹) +
            D.tr (algebraMap D.Fq D.Fq2 (D.nrm q.2 * (x : D.Fq)⁻¹) * q.1 * q.2⁻¹) + D.tr q.2) := by
      refine Finset.sum_bij (fun p _ => (algebraMap D.Fq D.Fq2 (p.1 : D.Fq)⁻¹ * p.2.1 * p.2.2, p.2.2))
        ?_ ?_ ?_ ?_
      · intro p hp
        simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rcases hp with ⟨h1, hn1, h2, hn2⟩
        refine ⟨mul_ne_zero (mul_ne_zero (algebraMap_ne_zero D (inv_ne_zero p.1.ne_zero)) h1) h2,
          ?_, h2⟩
        rw [nrm_mul, nrm_mul, nrm_algebraMap, hn1, hn2]
        field_simp [p.1.ne_zero]
      · intro p₁ hp₁ p₂ hp₂ heq
        simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
        obtain ⟨h1_prod, h2⟩ := Prod.mk.inj heq
        have hz_val : (p₁.1 : D.Fq) = (p₂.1 : D.Fq) := by
          have h : (p₁.1 : D.Fq) * (x : D.Fq) = (p₂.1 : D.Fq) * (x : D.Fq) := by
            rw [← hp₁.2.2.2, h2, hp₂.2.2.2]
          exact mul_right_cancel₀ x.ne_zero h
        have hz : p₁.1 = p₂.1 := Units.ext hz_val
        have h1 : p₁.2.1 = p₂.2.1 := by
          rw [hz, h2] at h1_prod
          have := mul_right_cancel₀ hp₂.2.2.1 h1_prod
          exact mul_left_cancel₀ (algebraMap_ne_zero D (inv_ne_zero p₂.1.ne_zero)) this
        exact Prod.ext hz (Prod.ext h1 h2)
      · intro q hq
        simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        rcases hq with ⟨hq1, hqn, hq2⟩
        have hn2 : D.nrm q.2 ≠ 0 := mt (nrm_eq_zero D q.2).mp hq2
        let zval : D.Fq := D.nrm q.2 * (x : D.Fq)⁻¹
        have hz_ne : zval ≠ 0 := mul_ne_zero hn2 (inv_ne_zero x.ne_zero)
        let z : D.Fqˣ := Units.mk0 zval hz_ne
        let v₁ : D.Fq2 := algebraMap D.Fq D.Fq2 zval * q.1 * q.2⁻¹
        have hv₁_ne : v₁ ≠ 0 :=
          mul_ne_zero (mul_ne_zero (algebraMap_ne_zero D hz_ne) hq1) (inv_ne_zero hq2)
        refine ⟨(z, v₁, q.2), ?_, ?_⟩
        · simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hv₁_ne, ?_, hq2, ?_⟩
          · dsimp only [v₁, z, Units.val_mk0]
            rw [nrm_mul, nrm_mul, nrm_algebraMap, nrm_inv, hqn]
            dsimp only [zval]
            field_simp [x.ne_zero, hn2]
          · dsimp only [z, Units.val_mk0, zval]
            rw [mul_assoc, inv_mul_cancel₀ x.ne_zero, mul_one]
        · ext1
          · dsimp only [v₁, z, Units.val_mk0]
            calc algebraMap D.Fq D.Fq2 zval⁻¹ * (algebraMap D.Fq D.Fq2 zval * q.1 * q.2⁻¹) * q.2
                = (algebraMap D.Fq D.Fq2 zval⁻¹ * algebraMap D.Fq D.Fq2 zval) * q.1 * (q.2⁻¹ * q.2) := by
                  ring
              _ = q.1 := by
                  rw [← map_mul, inv_mul_cancel₀ hz_ne, map_one, one_mul, inv_mul_cancel₀ hq2, mul_one]
          · rfl
      · intro p hp
        simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        have hz_eq : (p.1 : D.Fq) = D.nrm p.2.2 * (x : D.Fq)⁻¹ := by
          rw [hp.2.2.2, mul_assoc, mul_inv_cancel₀ x.ne_zero, mul_one]
        have hv₁_eq : p.2.1 = algebraMap D.Fq D.Fq2 (p.1 : D.Fq) *
            (algebraMap D.Fq D.Fq2 (p.1 : D.Fq)⁻¹ * p.2.1 * p.2.2) * p.2.2⁻¹ := by
          calc p.2.1
              = (algebraMap D.Fq D.Fq2 ((p.1 : D.Fq) * (p.1 : D.Fq)⁻¹)) * p.2.1 *
                  (p.2.2 * p.2.2⁻¹) := by
                rw [mul_inv_cancel₀ p.1.ne_zero, map_one, one_mul,
                  mul_inv_cancel₀ hp.2.2.1, mul_one]
            _ = algebraMap D.Fq D.Fq2 (p.1 : D.Fq) *
                  (algebraMap D.Fq D.Fq2 (p.1 : D.Fq)⁻¹ * p.2.1 * p.2.2) * p.2.2⁻¹ := by
                rw [map_mul]; ring
        congr 1
        dsimp only
        rw [← hz_eq, ← hv₁_eq]
    rw [hS1, hbij]
    have hS2 : (∑ q ∈ S₂, D.theta k q.1 *
          D.psi (s * (D.nrm q.2 * (x : D.Fq)⁻¹) +
            D.tr (algebraMap D.Fq D.Fq2 (D.nrm q.2 * (x : D.Fq)⁻¹) * q.1 * q.2⁻¹) + D.tr q.2)) =
        ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)), D.theta k u *
          ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0),
            D.psi (s * (D.nrm v * (x : D.Fq)⁻¹) +
              D.tr (algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹) + D.tr v) := by
      simp only [S₂, fib, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : u ≠ 0 ∧ D.nrm u = (y : D.Fq) * (x : D.Fq)
      · rw [if_pos hu, Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv : v ≠ 0 <;> simp [hu, hv]
      · rw [if_neg hu]
        exact Finset.sum_eq_zero fun v _ => if_neg fun ⟨h1, h2, _⟩ => hu ⟨h1, h2⟩
    rw [hS2]
    have hinner_v : ∀ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
        (∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0),
          D.psi (s * (D.nrm v * (x : D.Fq)⁻¹) +
            D.tr (algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹) + D.tr v)) =
        -((D.q : ℂ) * D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u)))) - 1 := by
      intro u hu
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      let α : D.Fq2 := algebraMap D.Fq D.Fq2 s⁻¹ * (algebraMap D.Fq D.Fq2 (x : D.Fq) + u)
      let c : D.Fq := s * (x : D.Fq)⁻¹
      have hc : c ≠ 0 := mul_ne_zero hs (inv_ne_zero x.ne_zero)
      have hc_nrm_α : c * D.nrm α = s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u) := by
        dsimp only [c, α]
        rw [nrm_mul, nrm_algebraMap, nrm_algebraMap_add, hu.2]
        field_simp [hs, x.ne_zero]
        ring
      have harg_eq : ∀ v : D.Fq2, v ≠ 0 →
          s * (D.nrm v * (x : D.Fq)⁻¹) +
            D.tr (algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹) + D.tr v =
          c * D.nrm (v + α) - s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u) := by
        intro v hv
        have hnv_q : algebraMap D.Fq D.Fq2 (D.nrm v) * v⁻¹ = v ^ D.q := by
          rw [algebraMap_nrm]; field_simp [hv]
        have h_v1 : algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹ =
            algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹ * (u * v ^ D.q) := by
          rw [map_mul, ← hnv_q]; ring
        have hα_q : α ^ D.q = algebraMap D.Fq D.Fq2 s⁻¹ *
            (algebraMap D.Fq D.Fq2 (x : D.Fq) + u ^ D.q) := by
          dsimp only [α]
          rw [mul_pow, add_pow_q, algebraMap_pow_q, algebraMap_pow_q]
        have htr_cross : D.tr (α ^ D.q * v) =
            s⁻¹ * ((x : D.Fq) * D.tr v + D.tr (u * v ^ D.q)) := by
          rw [hα_q, mul_add, add_mul, tr_add]
          simp only [mul_assoc, tr_algebraMap_mul]
          have htr_uq : D.tr (u ^ D.q * v) = D.tr (u * v ^ D.q) := by
            rw [← tr_pow_q D (u ^ D.q * v), mul_pow, pow_q_sq]
          rw [htr_uq]; ring
        rw [nrm_add, mul_add, mul_add, hc_nrm_α, h_v1, tr_algebraMap_mul, htr_cross]
        dsimp only [c]
        field_simp [hs, x.ne_zero]
        ring
      have hsum_v : (∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0),
            D.psi (s * (D.nrm v * (x : D.Fq)⁻¹) +
              D.tr (algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹) + D.tr v)) =
          D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) *
            ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0), D.psi (c * D.nrm (v + α)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v hv => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        rw [harg_eq v hv, sub_eq_add_neg, add_comm, psi_add]
      have hsum_nrm_shift :
          (∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0), D.psi (c * D.nrm (v + α))) =
            -(D.q : ℂ) - D.psi (c * D.nrm α) := by
        have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.Fq2)
          (fun v => v ≠ 0) (fun v => D.psi (c * D.nrm (v + α)))
        have h0set : Finset.univ.filter (fun v : D.Fq2 => ¬ v ≠ 0) = {0} := by ext v; simp
        rw [h0set, Finset.sum_singleton, zero_add] at hsplit
        have htot : (∑ v : D.Fq2, D.psi (c * D.nrm (v + α))) = -(D.q : ℂ) := by
          rw [Fintype.sum_equiv (Equiv.addRight α) (fun v => D.psi (c * D.nrm (v + α)))
            (fun w => D.psi (c * D.nrm w)) fun _ => rfl]
          exact sum_psi_nrm D hc
        calc (∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0), D.psi (c * D.nrm (v + α)))
            = (∑ v : D.Fq2, D.psi (c * D.nrm (v + α))) - D.psi (c * D.nrm α) :=
              eq_sub_of_add_eq hsplit
          _ = -(D.q : ℂ) - D.psi (c * D.nrm α) := by rw [htot]
      rw [hsum_v, hsum_nrm_shift, hc_nrm_α]
      have hψ_one : D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) *
          D.psi (s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u)) = 1 := by
        rw [← psi_add, neg_add_cancel, psi_zero]
      calc D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) *
            (-(D.q : ℂ) - D.psi (s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u)))
          = -((D.q : ℂ) * D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u)))) -
              (D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) *
                D.psi (s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) := by ring
        _ = -((D.q : ℂ) * D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u)))) - 1 := by
            rw [hψ_one]
    have hsum_u : (∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)), D.theta k u *
          ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0),
            D.psi (s * (D.nrm v * (x : D.Fq)⁻¹) +
              D.tr (algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹) + D.tr v)) =
        -(D.q : ℂ) * ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
          D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u := by
      have h1 : (∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)), D.theta k u *
            ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0),
              D.psi (s * (D.nrm v * (x : D.Fq)⁻¹) +
                D.tr (algebraMap D.Fq D.Fq2 (D.nrm v * (x : D.Fq)⁻¹) * u * v⁻¹) + D.tr v)) =
          ∑ u ∈ fib ((y : D.Fq) * (x : D.Fq)),
            (-((D.q : ℂ) * D.psi (-(s⁻¹ * ((y : D.Fq) + (x : D.Fq) + D.tr u))) * D.theta k u) -
              D.theta k u) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [hinner_v u hu]
        ring
      rw [h1, Finset.sum_sub_distrib, sum_theta_nrm_fiber D hreg ((y : D.Fq) * (x : D.Fq))
        (mul_ne_zero y.ne_zero x.ne_zero), sub_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => by ring
    rw [hsum_u]
    have hq_ne : (D.q : ℂ) ≠ 0 := q_complex_ne D
    field_simp [hq_ne]
  exact hLHS.trans hRHS.symm

/-! ### Section 5b: Cuspidal models (`piModel`), irreducibility, traces, and pairwise inequivalence -/

lemma borelModel_congr (D : FieldData) (γ : D.Lab) {a₁ a₂ b₁ b₂ d₁ d₂ : D.Fq}
    (ha : a₁ = a₂) (hb : b₁ = b₂) (hd : d₁ = d₂) :
    D.borelModel γ a₁ b₁ d₁ = D.borelModel γ a₂ b₂ d₂ := by
  subst ha hb hd; rfl

lemma piModel_one (D : FieldData) (k : D.Lab2) :
    D.piModel k 1 = 1 := by
  dsimp only [FieldData.piModel]
  have h10 : (1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := rfl
  have h00 : (1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = 1 := rfl
  have h01 : (1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 := rfl
  have h11 : (1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = 1 := rfl
  rw [if_pos h10, h00, h01, h11]
  exact borelModel_one D (D.restrLab k)

lemma piModel_unitary (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val))
    {M : Matrix (Fin 2) (Fin 2) D.Fq} (hdet : M.det ≠ 0) :
    D.piModel k M ∈ Matrix.unitaryGroup D.Fqˣ ℂ := by
  dsimp only [FieldData.piModel]
  by_cases hc : M 1 0 = 0
  · rw [if_pos hc]
    have hdet' : M 0 0 * M 1 1 ≠ 0 := by
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact hdet
    exact borelModel_unitary D _ (mul_ne_zero_iff.mp hdet').1 (mul_ne_zero_iff.mp hdet').2 _
  · rw [if_neg hc]
    have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
      rwa [Matrix.det_fin_two] at hdet
    have hB1 : D.borelModel (D.restrLab k) 1 (M 0 0 / M 1 0) 1 ∈ Matrix.unitaryGroup D.Fqˣ ℂ :=
      borelModel_unitary D _ one_ne_zero one_ne_zero _
    have hB2 : D.borelModel (D.restrLab k) (-M 1 0) (-M 1 1)
        (-(M 0 0 * M 1 1 - M 0 1 * M 1 0) / M 1 0) ∈ Matrix.unitaryGroup D.Fqˣ ℂ :=
      borelModel_unitary D _ (neg_ne_zero.mpr hc) (div_ne_zero (neg_ne_zero.mpr hdet') hc) _
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hB1 (wprimeModel_unitary D hreg)) hB2

lemma piModel_mul (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val))
    {M₁ M₂ : Matrix (Fin 2) (Fin 2) D.Fq} (hdet₁ : M₁.det ≠ 0) (hdet₂ : M₂.det ≠ 0) :
    D.piModel k (M₁ * M₂) = D.piModel k M₁ * D.piModel k M₂ := by
  let a₁ := M₁ 0 0; let b₁ := M₁ 0 1; let c₁ := M₁ 1 0; let d₁ := M₁ 1 1
  let a₂ := M₂ 0 0; let b₂ := M₂ 0 1; let c₂ := M₂ 1 0; let d₂ := M₂ 1 1
  let Δ₁ := a₁ * d₁ - b₁ * c₁
  let Δ₂ := a₂ * d₂ - b₂ * c₂
  have hΔ₁ : Δ₁ ≠ 0 := by rwa [Matrix.det_fin_two] at hdet₁
  have hΔ₂ : Δ₂ ≠ 0 := by rwa [Matrix.det_fin_two] at hdet₂
  let γ := D.restrLab k
  have haM : (M₁ * M₂) 0 0 = a₁ * a₂ + b₁ * c₂ := by simp [Matrix.mul_apply, Fin.sum_univ_two, a₁, b₁, a₂, c₂]
  have hbM : (M₁ * M₂) 0 1 = a₁ * b₂ + b₁ * d₂ := by simp [Matrix.mul_apply, Fin.sum_univ_two, a₁, b₁, b₂, d₂]
  have hcM : (M₁ * M₂) 1 0 = c₁ * a₂ + d₁ * c₂ := by simp [Matrix.mul_apply, Fin.sum_univ_two, c₁, d₁, a₂, c₂]
  have hdM : (M₁ * M₂) 1 1 = c₁ * b₂ + d₁ * d₂ := by simp [Matrix.mul_apply, Fin.sum_univ_two, c₁, d₁, b₂, d₂]
  have hdetM : (M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 - (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0 = Δ₁ * Δ₂ := by
    rw [haM, hbM, hcM, hdM]; dsimp only [Δ₁, Δ₂]; ring
  dsimp only [FieldData.piModel]
  change (if (M₁ * M₂) 1 0 = 0 then D.borelModel γ ((M₁ * M₂) 0 0) ((M₁ * M₂) 0 1) ((M₁ * M₂) 1 1)
      else D.borelModel γ 1 ((M₁ * M₂) 0 0 / (M₁ * M₂) 1 0) 1 * D.wprimeModel k *
        D.borelModel γ (-(M₁ * M₂) 1 0) (-(M₁ * M₂) 1 1)
          (-((M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 - (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0) / (M₁ * M₂) 1 0)) =
    (if c₁ = 0 then D.borelModel γ a₁ b₁ d₁
      else D.borelModel γ 1 (a₁ / c₁) 1 * D.wprimeModel k * D.borelModel γ (-c₁) (-d₁) (-Δ₁ / c₁)) *
    (if c₂ = 0 then D.borelModel γ a₂ b₂ d₂
      else D.borelModel γ 1 (a₂ / c₂) 1 * D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂))
  by_cases hc₁ : c₁ = 0 <;> by_cases hc₂ : c₂ = 0
  · have ha₁ : a₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₁, hc₁] using hΔ₁)).1
    have hd₁ : d₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₁, hc₁] using hΔ₁)).2
    have ha₂ : a₂ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₂, hc₂] using hΔ₂)).1
    have hd₂ : d₂ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₂, hc₂] using hΔ₂)).2
    have hc : (M₁ * M₂) 1 0 = 0 := by rw [hcM, hc₁, hc₂]; ring
    rw [if_pos hc, if_pos hc₁, if_pos hc₂, haM, hbM, hdM, hc₂, mul_zero, add_zero, hc₁,
      zero_mul, zero_add]
    exact (borelModel_mul D γ ha₁ hd₁ ha₂ hd₂ b₁ b₂).symm
  · have ha₁ : a₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₁, hc₁] using hΔ₁)).1
    have hd₁ : d₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₁, hc₁] using hΔ₁)).2
    have hΔ₁_eq : Δ₁ = a₁ * d₁ := by simp [Δ₁, hc₁]
    have hc : (M₁ * M₂) 1 0 = d₁ * c₂ := by rw [hcM, hc₁, zero_mul, zero_add]
    have hc_ne : (M₁ * M₂) 1 0 ≠ 0 := by rw [hc]; exact mul_ne_zero hd₁ hc₂
    rw [if_neg hc_ne, if_pos hc₁, if_neg hc₂]
    have hB_left : D.borelModel γ a₁ b₁ d₁ * D.borelModel γ 1 (a₂ / c₂) 1 =
        D.borelModel γ 1 ((M₁ * M₂) 0 0 / (M₁ * M₂) 1 0) 1 * D.borelModel γ a₁ 0 d₁ := by
      rw [borelModel_mul D γ ha₁ hd₁ one_ne_zero one_ne_zero,
        borelModel_mul D γ one_ne_zero one_ne_zero ha₁ hd₁]
      refine borelModel_congr D γ (by ring) ?_ (by ring)
      rw [haM, hc]; field_simp [hd₁, hc₂]; ring
    have hB_right : D.borelModel γ d₁ 0 a₁ * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) =
        D.borelModel γ (-(M₁ * M₂) 1 0) (-(M₁ * M₂) 1 1)
          (-((M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 - (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0) / (M₁ * M₂) 1 0) := by
      rw [borelModel_mul D γ hd₁ ha₁ (neg_ne_zero.mpr hc₂)
        (div_ne_zero (neg_ne_zero.mpr hΔ₂) hc₂)]
      refine borelModel_congr D γ ?_ ?_ ?_
      · rw [hc]; ring
      · rw [hdM, hc₁]; ring
      · rw [hdetM, hc, hΔ₁_eq]; field_simp [ha₁, hd₁, hc₂]
    calc D.borelModel γ 1 ((M₁ * M₂) 0 0 / (M₁ * M₂) 1 0) 1 * D.wprimeModel k *
          D.borelModel γ (-(M₁ * M₂) 1 0) (-(M₁ * M₂) 1 1)
            (-((M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 - (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0) / (M₁ * M₂) 1 0)
        = D.borelModel γ 1 ((M₁ * M₂) 0 0 / (M₁ * M₂) 1 0) 1 *
            (D.wprimeModel k * D.borelModel γ d₁ 0 a₁) *
            D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
          rw [← hB_right]; simp only [Matrix.mul_assoc]
      _ = D.borelModel γ 1 ((M₁ * M₂) 0 0 / (M₁ * M₂) 1 0) 1 *
            (D.borelModel γ a₁ 0 d₁ * D.wprimeModel k) *
            D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
          rw [← borelModel_diag_comm_wprimeModel D k ha₁ hd₁]
      _ = (D.borelModel γ 1 ((M₁ * M₂) 0 0 / (M₁ * M₂) 1 0) 1 * D.borelModel γ a₁ 0 d₁) *
            D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
          simp only [Matrix.mul_assoc]
      _ = D.borelModel γ a₁ b₁ d₁ *
            (D.borelModel γ 1 (a₂ / c₂) 1 * D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂)) := by
          rw [← hB_left]; simp only [Matrix.mul_assoc]
  · have ha₂ : a₂ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₂, hc₂] using hΔ₂)).1
    have hd₂ : d₂ ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Δ₂, hc₂] using hΔ₂)).2
    have hΔ₂_eq : Δ₂ = a₂ * d₂ := by simp [Δ₂, hc₂]
    have hc : (M₁ * M₂) 1 0 = c₁ * a₂ := by rw [hcM, hc₂, mul_zero, add_zero]
    have hc_ne : (M₁ * M₂) 1 0 ≠ 0 := by rw [hc]; exact mul_ne_zero hc₁ ha₂
    rw [if_neg hc_ne, if_neg hc₁, if_pos hc₂]
    have ha_div_c : (M₁ * M₂) 0 0 / (M₁ * M₂) 1 0 = a₁ / c₁ := by
      rw [haM, hc, hc₂, mul_zero, add_zero]; field_simp [hc₁, ha₂]
    have hB_right : D.borelModel γ (-c₁) (-d₁) (-Δ₁ / c₁) * D.borelModel γ a₂ b₂ d₂ =
        D.borelModel γ (-(M₁ * M₂) 1 0) (-(M₁ * M₂) 1 1)
          (-((M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 - (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0) / (M₁ * M₂) 1 0) := by
      rw [borelModel_mul D γ (neg_ne_zero.mpr hc₁) (div_ne_zero (neg_ne_zero.mpr hΔ₁) hc₁)
        ha₂ hd₂]
      refine borelModel_congr D γ ?_ ?_ ?_
      · rw [hc]; ring
      · rw [hdM]; ring
      · rw [hdetM, hc, hΔ₂_eq]; field_simp [hc₁, ha₂, hd₂]
    rw [ha_div_c, ← hB_right]
    simp only [Matrix.mul_assoc]
  · rw [if_neg hc₁, if_neg hc₂]
    have hm1_ne : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    have hnc1 : -c₁ ≠ 0 := neg_ne_zero.mpr hc₁
    have hnc2 : -c₂ ≠ 0 := neg_ne_zero.mpr hc₂
    have hΔ₁_c : -Δ₁ / c₁ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hΔ₁) hc₁
    have hΔ₂_c : -Δ₂ / c₂ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hΔ₂) hc₂
    by_cases hc : (M₁ * M₂) 1 0 = 0
    · rw [if_pos hc]
      have hc_eq : c₁ * a₂ + d₁ * c₂ = 0 := by rwa [hcM] at hc
      have hB_mid : D.borelModel γ (-c₁) (-d₁) (-Δ₁ / c₁) * D.borelModel γ 1 (a₂ / c₂) 1 =
          D.borelModel γ (-c₁) 0 (-Δ₁ / c₁) := by
        rw [borelModel_mul D γ hnc1 hΔ₁_c one_ne_zero one_ne_zero]
        refine borelModel_congr D γ (by ring) ?_ (by ring)
        field_simp [hc₂]; linear_combination -hc_eq
      have h12 : D.borelModel γ 1 (a₁ / c₁) 1 * D.borelModel γ (-1) 0 (-1) =
          D.borelModel γ (-1) (-a₁ / c₁) (-1) := by
        rw [borelModel_mul D γ one_ne_zero one_ne_zero hm1_ne hm1_ne]
        refine borelModel_congr D γ (by ring) (by ring) (by ring)
      have h123 : D.borelModel γ (-1) (-a₁ / c₁) (-1) * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) =
          D.borelModel γ (Δ₁ / c₁) a₁ c₁ := by
        rw [borelModel_mul D γ hm1_ne hm1_ne hΔ₁_c hnc1]
        refine borelModel_congr D γ (by ring) ?_ (by ring)
        field_simp [hc₁]; ring
      have hB_all : D.borelModel γ 1 (a₁ / c₁) 1 * D.borelModel γ (-1) 0 (-1) *
            D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) =
          D.borelModel γ ((M₁ * M₂) 0 0) ((M₁ * M₂) 0 1) ((M₁ * M₂) 1 1) := by
        rw [h12, h123, borelModel_mul D γ (div_ne_zero hΔ₁ hc₁) hc₁ hnc2 hΔ₂_c, haM, hbM, hdM]
        refine borelModel_congr D γ ?_ ?_ ?_
        · field_simp [hc₁]; dsimp only [Δ₁]; linear_combination -a₁ * hc_eq
        · field_simp [hc₁, hc₂]
          dsimp only [Δ₁, Δ₂]
          calc _ = -a₁ * d₂ * (c₁ * a₂ + d₁ * c₂) + c₁ * c₂ * (a₁ * b₂ + b₁ * d₂) := by ring
            _ = c₁ * c₂ * (a₁ * b₂ + d₂ * b₁) := by rw [hc_eq, mul_zero, zero_add]; ring
        · field_simp [hc₂]; dsimp only [Δ₂]; linear_combination -d₂ * hc_eq
      calc D.borelModel γ ((M₁ * M₂) 0 0) ((M₁ * M₂) 0 1) ((M₁ * M₂) 1 1)
          = D.borelModel γ 1 (a₁ / c₁) 1 * D.borelModel γ (-1) 0 (-1) *
              D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) :=
            hB_all.symm
        _ = D.borelModel γ 1 (a₁ / c₁) 1 * (D.wprimeModel k * D.wprimeModel k) *
              D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [borelModel_neg_one D k, ← wprimeModel_sq D hreg]
        _ = D.borelModel γ 1 (a₁ / c₁) 1 * D.wprimeModel k *
              (D.wprimeModel k * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁)) *
              D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            simp only [Matrix.mul_assoc]
        _ = D.borelModel γ 1 (a₁ / c₁) 1 * D.wprimeModel k *
              (D.borelModel γ (-c₁) 0 (-Δ₁ / c₁) * D.wprimeModel k) *
              D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [borelModel_diag_comm_wprimeModel D k hnc1 hΔ₁_c]
        _ = (D.borelModel γ 1 (a₁ / c₁) 1 * D.wprimeModel k * D.borelModel γ (-c₁) (-d₁) (-Δ₁ / c₁)) *
              (D.borelModel γ 1 (a₂ / c₂) 1 * D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂)) := by
            rw [← hB_mid]; simp only [Matrix.mul_assoc]
    · rw [if_neg hc]
      let c := (M₁ * M₂) 1 0
      let s : D.Fq := c / (c₁ * c₂)
      have hs : s ≠ 0 := div_ne_zero hc (mul_ne_zero hc₁ hc₂)
      have hc_sum : c₁ * a₂ + d₁ * c₂ ≠ 0 := by rwa [← hcM]
      have hc_sum' : d₁ * c₂ + c₁ * a₂ ≠ 0 := by rw [add_comm]; exact hc_sum
      have hns : -s ≠ 0 := neg_ne_zero.mpr hs
      have hnsinv : -s⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hs)
      have hB_mid : D.borelModel γ (-c₁) (-d₁) (-Δ₁ / c₁) * D.borelModel γ 1 (a₂ / c₂) 1 =
          D.borelModel γ (-c₁) 0 (-Δ₁ / c₁) * D.borelModel γ 1 s 1 := by
        rw [borelModel_mul D γ hnc1 hΔ₁_c one_ne_zero one_ne_zero,
          borelModel_mul D γ hnc1 hΔ₁_c one_ne_zero one_ne_zero]
        refine borelModel_congr D γ (by ring) ?_ (by ring)
        dsimp only [s, c]; rw [hcM]; field_simp [hc₁, hc₂]; ring
      have hB_left : D.borelModel γ 1 (a₁ / c₁) 1 * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) *
            D.borelModel γ 1 (-s⁻¹) 1 =
          D.borelModel γ 1 ((M₁ * M₂) 0 0 / c) 1 * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) := by
        have hl1 : D.borelModel γ 1 (a₁ / c₁) 1 * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) =
            D.borelModel γ (-Δ₁ / c₁) (-a₁) (-c₁) := by
          rw [borelModel_mul D γ one_ne_zero one_ne_zero hΔ₁_c hnc1]
          refine borelModel_congr D γ (by ring) (by field_simp [hc₁]; ring) (by ring)
        rw [hl1, borelModel_mul D γ hΔ₁_c hnc1 one_ne_zero one_ne_zero,
          borelModel_mul D γ one_ne_zero one_ne_zero hΔ₁_c hnc1]
        refine borelModel_congr D γ (by ring) ?_ (by ring)
        dsimp only [s, c]; rw [haM, hcM]; field_simp [hc₁, hc₂, hc_sum, hc_sum']; dsimp only [Δ₁]; ring
      have hB_right : D.borelModel γ (-c₁) 0 (-Δ₁ / c₁) * D.borelModel γ (-s) 1 (-s⁻¹) *
            D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) =
          D.borelModel γ (-c) (-(M₁ * M₂) 1 1) (-((M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 -
            (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0) / c) := by
        have hr1 : D.borelModel γ (-c₁) 0 (-Δ₁ / c₁) * D.borelModel γ (-s) 1 (-s⁻¹) =
            D.borelModel γ (c₁ * s) (-c₁) (Δ₁ / (c₁ * s)) := by
          rw [borelModel_mul D γ hnc1 hΔ₁_c hns hnsinv]
          refine borelModel_congr D γ (by ring) (by ring) (by field_simp [hc₁, hs])
        rw [hr1, borelModel_mul D γ (mul_ne_zero hc₁ hs) (div_ne_zero hΔ₁ (mul_ne_zero hc₁ hs))
          hnc2 hΔ₂_c, hdetM, hdM]
        refine borelModel_congr D γ ?_ ?_ ?_
        · dsimp only [s, c]; rw [hcM]; field_simp [hc₁, hc₂]
        · dsimp only [s, c]; rw [hcM]; field_simp [hc₁, hc₂, hc_sum]; dsimp only [Δ₂]; ring
        · dsimp only [s, c]; rw [hcM]; field_simp [hc₁, hc₂, hc_sum, hc_sum']
      calc D.borelModel γ 1 ((M₁ * M₂) 0 0 / c) 1 * D.wprimeModel k *
            D.borelModel γ (-c) (-(M₁ * M₂) 1 1) (-((M₁ * M₂) 0 0 * (M₁ * M₂) 1 1 -
              (M₁ * M₂) 0 1 * (M₁ * M₂) 1 0) / c)
          = D.borelModel γ 1 ((M₁ * M₂) 0 0 / c) 1 *
              (D.wprimeModel k * D.borelModel γ (-c₁) 0 (-Δ₁ / c₁)) *
              D.borelModel γ (-s) 1 (-s⁻¹) * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [← hB_right]; simp only [Matrix.mul_assoc]
        _ = (D.borelModel γ 1 ((M₁ * M₂) 0 0 / c) 1 * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁)) *
              D.wprimeModel k * D.borelModel γ (-s) 1 (-s⁻¹) * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [← borelModel_diag_comm_wprimeModel D k hΔ₁_c hnc1]
            simp only [Matrix.mul_assoc]; rfl
        _ = D.borelModel γ 1 (a₁ / c₁) 1 * D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) *
              (D.borelModel γ 1 (-s⁻¹) 1 * D.wprimeModel k * D.borelModel γ (-s) 1 (-s⁻¹)) *
              D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [← hB_left]; simp only [Matrix.mul_assoc]
        _ = D.borelModel γ 1 (a₁ / c₁) 1 * (D.borelModel γ (-Δ₁ / c₁) 0 (-c₁) * D.wprimeModel k) *
              D.borelModel γ 1 s 1 * D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [← wprimeModel_bruhat_rel D hreg hs]; simp only [Matrix.mul_assoc]; rfl
        _ = D.borelModel γ 1 (a₁ / c₁) 1 * D.wprimeModel k *
              (D.borelModel γ (-c₁) 0 (-Δ₁ / c₁) * D.borelModel γ 1 s 1) *
              D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂) := by
            rw [borelModel_diag_comm_wprimeModel D k hΔ₁_c hnc1]
            simp only [Matrix.mul_assoc]; rfl
        _ = (D.borelModel γ 1 (a₁ / c₁) 1 * D.wprimeModel k * D.borelModel γ (-c₁) (-d₁) (-Δ₁ / c₁)) *
              (D.borelModel γ 1 (a₂ / c₂) 1 * D.wprimeModel k * D.borelModel γ (-c₂) (-d₂) (-Δ₂ / c₂)) := by
            rw [← hB_mid]; simp only [Matrix.mul_assoc]

lemma piModel_isUnitaryRep (D : FieldData) {k : D.Lab2} (hreg : ¬ (D.q + 1 ∣ k.val)) :
    IsUnitaryRep (fun g : D.G => D.piModel k (g : Matrix (Fin 2) (Fin 2) D.Fq)) :=
  ⟨⟨piModel_one D k, fun g₁ g₂ => piModel_mul D hreg (gl_det_ne_zero D g₁) (gl_det_ne_zero D g₂)⟩,
   fun g => piModel_unitary D hreg (gl_det_ne_zero D g)⟩

noncomputable def glLift (D : FieldData) (M : Matrix (Fin 2) (Fin 2) D.Fq) (hdet : M.det ≠ 0) : D.G :=
  Matrix.nonsingInvUnit M (isUnit_iff_ne_zero.mpr hdet)

lemma glLift_coe (D : FieldData) (M : Matrix (Fin 2) (Fin 2) D.Fq) (hdet : M.det ≠ 0) :
    ((glLift D M hdet : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) = M := by
  ext i j; rfl

lemma piModel_isIrreducibleRep (D : FieldData) (k : D.Lab2) :
    IsIrreducibleRep (fun g : D.G => D.piModel k (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  refine ⟨⟨1⟩, fun W hW => ?_⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    rw [eq_top_iff]
    obtain ⟨f, hfW, hf0⟩ : ∃ f ∈ W, f ≠ 0 := by
      by_contra h
      push Not at h
      exact hbot ((Submodule.eq_bot_iff W).mpr h)
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : D.Fqˣ, f y₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    let γ := D.restrLab k
    have hproj_mem : (∑ b : D.Fq, conj (D.psi (b * (y₀ : D.Fq))) •
        (D.piModel k ((glLift D !![1, b; 0, 1] (by simp) : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) *ᵥ f)) ∈ W :=
      W.sum_mem fun b _ => W.smul_mem _ (hW _ f hfW)
    have hproj_eq : (∑ b : D.Fq, conj (D.psi (b * (y₀ : D.Fq))) •
        (D.piModel k ((glLift D !![1, b; 0, 1] (by simp) : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) *ᵥ f)) =
        ((D.q : ℂ) * f y₀) • Pi.single y₀ 1 := by
      ext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, glLift_coe, Pi.single_apply]
      have hact : ∀ b : D.Fq,
          (D.piModel k !![1, b; 0, 1] *ᵥ f) x = D.psi (b * (x : D.Fq)) * f x := by
        intro b
        dsimp only [FieldData.piModel]
        have hc : (!![(1 : D.Fq), b; 0, 1] : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := rfl
        rw [if_pos hc]
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single x]
        · simp [FieldData.borelModel, chi_one]
        · intro z _ hz
          have hne : (x : D.Fq) ≠ (z : D.Fq) := fun h => hz (Units.ext h).symm
          simp [FieldData.borelModel, hne]
        · intro hmem; exact (hmem (Finset.mem_univ x)).elim
      simp_rw [hact]
      have hsum : (∑ b : D.Fq, conj (D.psi (b * (y₀ : D.Fq))) * (D.psi (b * (x : D.Fq)) * f x)) =
          f x * ∑ b : D.Fq, D.psi (((x : D.Fq) - (y₀ : D.Fq)) * b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [conj_psi, ← mul_assoc, ← psi_add]
        have harg : -(b * (y₀ : D.Fq)) + b * (x : D.Fq) = ((x : D.Fq) - (y₀ : D.Fq)) * b := by ring
        rw [harg, mul_comm _ (f x)]
      rw [hsum]
      by_cases hx : x = y₀
      · subst hx
        simp only [sub_self, zero_mul, psi_zero, Finset.sum_const, Finset.card_univ, card_Fq,
          nsmul_eq_mul, mul_one, ↓reduceIte]
        ring
      · have hdiff : (x : D.Fq) - (y₀ : D.Fq) ≠ 0 := sub_ne_zero.mpr fun h => hx (Units.ext h)
        rw [sum_psi, if_neg hdiff, mul_zero, if_neg hx, mul_zero]
    have hcoeff_ne : (D.q : ℂ) * f y₀ ≠ 0 := mul_ne_zero (q_complex_ne D) hy₀
    have he₀ : (Pi.single y₀ (1 : ℂ) : D.Fqˣ → ℂ) ∈ W := by
      rw [hproj_eq] at hproj_mem
      have h := W.smul_mem ((D.q : ℂ) * f y₀)⁻¹ hproj_mem
      rwa [smul_smul, inv_mul_cancel₀ hcoeff_ne, one_smul] at h
    have hsingle : ∀ z : D.Fqˣ, (Pi.single z (1 : ℂ) : D.Fqˣ → ℂ) ∈ W := by
      intro z
      let d : D.Fq := (z : D.Fq) * (y₀ : D.Fq)⁻¹
      have hd : d ≠ 0 := mul_ne_zero z.ne_zero (inv_ne_zero y₀.ne_zero)
      have hmem := hW (glLift D !![1, 0; 0, d] (by simp [hd])) (Pi.single y₀ 1) he₀
      have hact : (D.piModel k ((glLift D !![1, 0; 0, d] (by simp [hd]) : D.G) :
          Matrix (Fin 2) (Fin 2) D.Fq) *ᵥ Pi.single y₀ 1) =
          D.chi γ d • (Pi.single z (1 : ℂ) : D.Fqˣ → ℂ) := by
        ext w
        simp only [glLift_coe, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
        dsimp only [FieldData.piModel]
        have hc : (!![(1 : D.Fq), 0; 0, d] : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := rfl
        rw [if_pos hc]
        rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single y₀]
        · have hdz : d * (y₀ : D.Fq) = (z : D.Fq) := by
            dsimp only [d]; rw [mul_assoc, inv_mul_cancel₀ y₀.ne_zero, mul_one]
          have h00 : (!![(1 : D.Fq), 0; 0, d] : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = 1 := rfl
          have h01 : (!![(1 : D.Fq), 0; 0, d] : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 := rfl
          have h11 : (!![(1 : D.Fq), 0; 0, d] : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = d := rfl
          dsimp only [FieldData.borelModel]
          rw [h00, h01, h11, div_one, zero_div, zero_mul, psi_zero, mul_one, Pi.single_eq_same,
            mul_one, hdz]
          by_cases hw : w = z
          · subst hw; rw [if_pos rfl, if_pos rfl, mul_one]
          · have hne : (w : D.Fq) ≠ (z : D.Fq) := fun h => hw (Units.ext h)
            rw [if_neg hne, if_neg hw, mul_zero]
        · intro x _ hx; simp [hx]
        · intro hmem'; exact (hmem' (Finset.mem_univ y₀)).elim
      rw [hact] at hmem
      have h' := W.smul_mem (D.chi γ d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (chi_ne_zero D γ hd), one_smul] at h'
    intro v _
    have hv_eq : v = ∑ z : D.Fqˣ, v z • (Pi.single z (1 : ℂ) : D.Fqˣ → ℂ) := by
      ext w
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv_eq]
    exact W.sum_mem fun z _ => W.smul_mem (v z) (hsingle z)

lemma cusp_isUnitary_irred_equiv (D : FieldData) (k : {k : D.Lab2 // D.IsCuspLabel k}) :
    IsUnitaryRep (D.R (.inr (.inr (.inr k)))) ∧
    IsIrreducibleRep (D.R (.inr (.inr (.inr k)))) ∧
    RepEquiv (D.R (.inr (.inr (.inr k))))
      (fun g : D.G => D.piModel k.1 (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  let Q := basisMatrix D.multVec
  have hcard : Fintype.card D.Lab = Fintype.card D.Fqˣ := by rw [card_Lab, card_Fq_units]
  have hQl : Qᴴ * Q = 1 := basisMatrix_conjTranspose_mul D.multVec (multVec_orthonormal D)
  have hQr : Q * Qᴴ = 1 := basisMatrix_mul_conjTranspose D.multVec hcard (multVec_orthonormal D)
  let R_cusp : D.G → Matrix D.Lab D.Lab ℂ :=
    fun g => Matrix.of fun i j => D.R (.inr (.inr (.inr k))) g i j
  have hReq : R_cusp = fun g : D.G => Qᴴ * D.piModel k.1 (g : Matrix (Fin 2) (Fin 2) D.Fq) * Q := by
    ext g i j
    exact matEntry_eq_basisMatrix_mul (D.piModel k.1 (g : Matrix (Fin 2) (Fin 2) D.Fq))
      D.multVec i j
  have hU : IsUnitaryRep R_cusp := by
    rw [hReq]
    exact isUnitaryRep_of_unitary_conj (piModel_isUnitaryRep D k.2.1) Q hQl hQr
  have heq : RepEquiv R_cusp (fun g : D.G => D.piModel k.1 (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
    rw [hReq]
    exact repEquiv_of_unitary_conj _ Q hQl hQr
  have hirr : IsIrreducibleRep (D.R (.inr (.inr (.inr k)))) :=
    isIrreducibleRep_of_repEquiv (piModel_isIrreducibleRep D k.1) heq
  exact ⟨hU, hirr, heq⟩

lemma repEquiv_trace {G ι₁ ι₂ : Type} [Fintype G] [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {ρ₁ : G → Matrix ι₁ ι₁ ℂ} {ρ₂ : G → Matrix ι₂ ι₂ ℂ} (h : RepEquiv ρ₁ ρ₂) (g : G) :
    Matrix.trace (ρ₁ g) = Matrix.trace (ρ₂ g) := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  have h1 : A * ρ₁ g * B = ρ₂ g := by
    rw [hinter g (Set.mem_univ g), Matrix.mul_assoc, hAB, Matrix.mul_one]
  rw [← h1, Matrix.trace_mul_cycle, hBA, Matrix.one_mul]

lemma repEquiv_card_eq {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {ρ₁ : G → Matrix ι₁ ι₁ ℂ} {ρ₂ : G → Matrix ι₂ ι₂ ℂ} (h : RepEquiv ρ₁ ρ₂) :
    Fintype.card ι₁ = Fintype.card ι₂ := by
  obtain ⟨A, B, hAB, hBA, _⟩ := h
  have htr : ((Fintype.card ι₁ : ℕ) : ℂ) = ((Fintype.card ι₂ : ℕ) : ℂ) := by
    calc ((Fintype.card ι₁ : ℕ) : ℂ)
        = Matrix.trace (1 : Matrix ι₁ ι₁ ℂ) := by simp
      _ = Matrix.trace (B * A) := by rw [hBA]
      _ = Matrix.trace (A * B) := Matrix.trace_mul_comm B A
      _ = Matrix.trace (1 : Matrix ι₂ ι₂ ℂ) := by rw [hAB]
      _ = ((Fintype.card ι₂ : ℕ) : ℂ) := by simp
  exact Nat.cast_injective htr

lemma bas_card_cases (D : FieldData) (μ : D.Irr) :
    (∃ α, μ = .inl α ∧ Fintype.card (D.Bas μ) = 1) ∨
    (∃ α, μ = .inr (.inl α) ∧ Fintype.card (D.Bas μ) = D.q) ∨
    (∃ ab, μ = .inr (.inr (.inl ab)) ∧ Fintype.card (D.Bas μ) = D.q + 1) ∨
    (∃ k, μ = .inr (.inr (.inr k)) ∧ Fintype.card (D.Bas μ) = D.q - 1) := by
  rcases μ with α | (α | (ab | k))
  · exact Or.inl ⟨α, rfl, Fintype.card_unit⟩
  · refine Or.inr (Or.inl ⟨α, rfl, ?_⟩)
    change Fintype.card (Option D.Lab) = D.q
    rw [Fintype.card_option, card_Lab]
    have := D.one_lt_q; omega
  · refine Or.inr (Or.inr (Or.inl ⟨ab, rfl, ?_⟩))
    change Fintype.card (Option (Option D.Lab)) = D.q + 1
    rw [Fintype.card_option, Fintype.card_option, card_Lab]
    have := D.one_lt_q; omega
  · exact Or.inr (Or.inr (Or.inr ⟨k, rfl, card_Lab D⟩))

lemma piModel_trace_unipotent (D : FieldData) (m : D.Lab2) :
    Matrix.trace (D.piModel m !![1, 1; 0, 1]) = -1 := by
  rw [Matrix.trace]
  dsimp only [Matrix.diag, FieldData.piModel]
  have hc : (!![(1 : D.Fq), 1; 0, 1] : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := rfl
  have h00 : (!![(1 : D.Fq), 1; 0, 1] : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = 1 := rfl
  have h01 : (!![(1 : D.Fq), 1; 0, 1] : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 1 := rfl
  have h11 : (!![(1 : D.Fq), 1; 0, 1] : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = 1 := rfl
  rw [if_pos hc, h00, h01, h11]
  have hdiag : ∀ x : D.Fqˣ, D.borelModel (D.restrLab m) 1 1 1 x x = D.psi (x : D.Fq) := fun x => by
    simp [FieldData.borelModel, chi_one]
  simp_rw [hdiag]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.Fq)
    (fun x => x ≠ 0) (fun x => D.psi x)
  have h0set : Finset.univ.filter (fun x : D.Fq => ¬ x ≠ 0) = {0} := by ext x; simp
  have htot : (∑ x : D.Fq, D.psi x) = 0 := by simpa using sum_psi D 1
  rw [h0set, Finset.sum_singleton, psi_zero, htot] at hsplit
  have hbij : (∑ x : D.Fqˣ, D.psi (x : D.Fq)) =
      ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.psi x := by
    refine Finset.sum_bij (fun x _ => (x : D.Fq)) ?_ ?_ ?_ ?_
    · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.ne_zero⟩
    · intro x₁ _ x₂ _ h; exact Units.ext h
    · intro x hx
      refine ⟨Units.mk0 x (Finset.mem_filter.mp hx).2, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  rw [hbij]
  linear_combination hsplit

lemma piModel_trace_diag (D : FieldData) (m : D.Lab2) {x : D.Fq} (hx : x ≠ 0) :
    Matrix.trace (D.piModel m !![x, 0; 0, x]) = ((D.q : ℂ) - 1) * D.theta m (algebraMap D.Fq D.Fq2 x) := by
  rw [Matrix.trace]
  dsimp only [Matrix.diag, FieldData.piModel]
  have hc : (!![x, (0 : D.Fq); 0, x] : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := rfl
  have h00 : (!![x, (0 : D.Fq); 0, x] : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = x := rfl
  have h01 : (!![x, (0 : D.Fq); 0, x] : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 := rfl
  have h11 : (!![x, (0 : D.Fq); 0, x] : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = x := rfl
  rw [if_pos hc, h00, h01, h11]
  have hdiag : ∀ y : D.Fqˣ, D.borelModel (D.restrLab m) x 0 x y y =
      D.theta m (algebraMap D.Fq D.Fq2 x) := fun y => by
    simp only [FieldData.borelModel, div_self hx, one_mul, ↓reduceIte,
      zero_div, zero_mul, psi_zero, mul_one, theta_algebraMap]
  simp_rw [hdiag, Finset.sum_const, Finset.card_univ, card_Fq_units, nsmul_eq_mul]
  have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
    have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcard]

lemma piModel_trace_elliptic (D : FieldData) {m : D.Lab2} (hreg : ¬ (D.q + 1 ∣ m.val))
    {z : D.Fq2ˣ} (hzq : (z : D.Fq2) ^ D.q ≠ (z : D.Fq2)) :
    Matrix.trace (D.piModel m !![D.tr (z : D.Fq2), -D.nrm (z : D.Fq2); 1, 0]) =
      -(D.theta m (z : D.Fq2) + D.theta m ((z : D.Fq2) ^ D.q)) := by
  let M : Matrix (Fin 2) (Fin 2) D.Fq := !![D.tr (z : D.Fq2), -D.nrm (z : D.Fq2); 1, 0]
  let γ := D.restrLab m
  have hnrm_ne : D.nrm (z : D.Fq2) ≠ 0 := mt (nrm_eq_zero D (z : D.Fq2)).mp z.ne_zero
  let fib := Finset.univ.filter (fun w : D.Fq2 => w ≠ 0 ∧ D.nrm w = D.nrm (z : D.Fq2))
  have hM : ∀ x : D.Fqˣ, D.piModel m M x x =
      -((D.q : ℂ)⁻¹) * D.chi γ (-1) *
        ∑ w ∈ fib, D.psi ((x : D.Fq) * (D.tr (z : D.Fq2) + D.tr w)) * D.theta m w := by
    intro x
    dsimp only [FieldData.piModel]
    have hcM : M 1 0 ≠ 0 := by simp [M]
    rw [if_neg hcM]
    have h00 : M 0 0 = D.tr (z : D.Fq2) := rfl
    have h01 : M 0 1 = -D.nrm (z : D.Fq2) := rfl
    have h10 : M 1 0 = 1 := rfl
    have h11 : M 1 1 = 0 := rfl
    have hdetM : -(M 0 0 * M 1 1 - M 0 1 * M 1 0) / M 1 0 = -D.nrm (z : D.Fq2) := by
      rw [h00, h01, h10, h11]; ring
    rw [hdetM, h00, h10, h11, div_one, neg_zero]
    rw [Matrix.mul_apply]
    let y₀ : D.Fqˣ := Units.mk0 (D.nrm (z : D.Fq2) * (x : D.Fq))
      (mul_ne_zero hnrm_ne x.ne_zero)
    rw [Finset.sum_eq_single y₀]
    · have hy₀_cond : (y₀ : D.Fq) = (-D.nrm (z : D.Fq2)) / (-1) * (x : D.Fq) := by
        simp only [y₀, Units.val_mk0, div_neg, div_one, neg_neg]
      have hB1 : (D.borelModel γ 1 (D.tr (z : D.Fq2)) 1 * D.wprimeModel m) x y₀ =
          D.psi (D.tr (z : D.Fq2) * (x : D.Fq)) * D.wprimeModel m x y₀ := by
        rw [Matrix.mul_apply, Finset.sum_eq_single x]
        · simp [FieldData.borelModel, chi_one]
        · intro u _ hu
          have hne : (x : D.Fq) ≠ (u : D.Fq) := fun h => hu (Units.ext h).symm
          simp [FieldData.borelModel, hne]
        · intro hmem; exact (hmem (Finset.mem_univ x)).elim
      rw [hB1]
      dsimp only [FieldData.borelModel]
      rw [if_pos hy₀_cond, zero_div, zero_mul, psi_zero, mul_one]
      dsimp only [FieldData.wprimeModel, FieldData.besselJ]
      have hy₀_val : (y₀ : D.Fq) = D.nrm (z : D.Fq2) * (x : D.Fq) := rfl
      have hθ_y₀ : D.theta m (algebraMap D.Fq D.Fq2 (y₀ : D.Fq)⁻¹) * D.chi γ (-D.nrm (z : D.Fq2)) =
          D.chi γ (-1) * D.chi γ (x : D.Fq)⁻¹ := by
        rw [theta_algebraMap, show D.restrLab m = γ from rfl, hy₀_val, mul_inv,
          chi_mul D γ (inv_ne_zero hnrm_ne) (inv_ne_zero x.ne_zero),
          show -D.nrm (z : D.Fq2) = (-1) * D.nrm (z : D.Fq2) from by ring,
          chi_mul D γ (by simp) hnrm_ne]
        have hinv_nrm : D.chi γ (D.nrm (z : D.Fq2))⁻¹ * D.chi γ (D.nrm (z : D.Fq2)) = 1 := by
          rw [← chi_mul D γ (inv_ne_zero hnrm_ne) hnrm_ne, inv_mul_cancel₀ hnrm_ne, chi_one]
        calc D.chi γ (D.nrm (z : D.Fq2))⁻¹ * D.chi γ (x : D.Fq)⁻¹ *
              (D.chi γ (-1) * D.chi γ (D.nrm (z : D.Fq2)))
            = D.chi γ (-1) * D.chi γ (x : D.Fq)⁻¹ *
                (D.chi γ (D.nrm (z : D.Fq2))⁻¹ * D.chi γ (D.nrm (z : D.Fq2))) := by ring
          _ = D.chi γ (-1) * D.chi γ (x : D.Fq)⁻¹ := by rw [hinv_nrm, mul_one]
      have hfib_reidx :
          (∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (x : D.Fq) * (y₀ : D.Fq)),
            D.psi (D.tr v) * D.theta m v) =
          D.chi γ (x : D.Fq) * ∑ w ∈ fib, D.psi ((x : D.Fq) * D.tr w) * D.theta m w := by
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun v _ => algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹ * v) ?_ ?_ ?_ ?_
        · intro v hv
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          refine ⟨mul_ne_zero (algebraMap_ne_zero D (inv_ne_zero x.ne_zero)) hv.1, ?_⟩
          rw [nrm_mul, nrm_algebraMap, hv.2, hy₀_val]
          field_simp [x.ne_zero]
        · intro v₁ _ v₂ _ heq
          exact mul_left_cancel₀ (algebraMap_ne_zero D (inv_ne_zero x.ne_zero)) heq
        · intro w hw
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          refine ⟨algebraMap D.Fq D.Fq2 (x : D.Fq) * w, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨mul_ne_zero (algebraMap_ne_zero D x.ne_zero) hw.1, ?_⟩
            rw [nrm_mul, nrm_algebraMap, hw.2, hy₀_val]
            ring
          · rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ x.ne_zero, map_one, one_mul]
        · intro v _
          have hv_eq : v = algebraMap D.Fq D.Fq2 (x : D.Fq) *
              (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹ * v) := by
            rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ x.ne_zero, map_one, one_mul]
          have htr : D.tr v = (x : D.Fq) * D.tr (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹ * v) := by
            conv_lhs => rw [hv_eq]
            rw [tr_algebraMap_mul]
          have hθ : D.theta m v =
              D.chi γ (x : D.Fq) * D.theta m (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹ * v) := by
            conv_lhs => rw [hv_eq]
            rw [theta_mul, theta_algebraMap]
          rw [htr, hθ]
          ring
      have hχ_x : D.chi γ (x : D.Fq)⁻¹ * D.chi γ (x : D.Fq) = 1 := by
        rw [← chi_mul D γ (inv_ne_zero x.ne_zero) x.ne_zero, inv_mul_cancel₀ x.ne_zero, chi_one]
      rw [hfib_reidx, show D.restrLab m = γ from rfl]
      calc D.psi (D.tr (z : D.Fq2) * (x : D.Fq)) *
            (D.theta m (algebraMap D.Fq D.Fq2 (y₀ : D.Fq)⁻¹) *
              (-((D.q : ℂ)⁻¹) *
                (D.chi γ (x : D.Fq) * ∑ w ∈ fib, D.psi ((x : D.Fq) * D.tr w) * D.theta m w))) *
            D.chi γ (-D.nrm (z : D.Fq2))
          = -((D.q : ℂ)⁻¹) *
              ((D.theta m (algebraMap D.Fq D.Fq2 (y₀ : D.Fq)⁻¹) * D.chi γ (-D.nrm (z : D.Fq2))) *
                D.chi γ (x : D.Fq)) *
              ∑ w ∈ fib, (D.psi ((x : D.Fq) * D.tr (z : D.Fq2)) *
                D.psi ((x : D.Fq) * D.tr w)) * D.theta m w := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun w _ => by
              rw [mul_comm (D.tr (z : D.Fq2)) (x : D.Fq)]; ring
        _ = -((D.q : ℂ)⁻¹) * D.chi γ (-1) *
              ∑ w ∈ fib, D.psi ((x : D.Fq) * (D.tr (z : D.Fq2) + D.tr w)) * D.theta m w := by
            have hsum_add : (∑ w ∈ fib, (D.psi ((x : D.Fq) * D.tr (z : D.Fq2)) *
                  D.psi ((x : D.Fq) * D.tr w)) * D.theta m w) =
                ∑ w ∈ fib, D.psi ((x : D.Fq) * (D.tr (z : D.Fq2) + D.tr w)) * D.theta m w :=
              Finset.sum_congr rfl fun w _ => by rw [← psi_add, mul_add]
            rw [hθ_y₀, mul_assoc (D.chi γ (-1)), hχ_x, mul_one, hsum_add]
    · intro y _ hy
      have hne : (y : D.Fq) ≠ (-D.nrm (z : D.Fq2)) / (-1) * (x : D.Fq) := by
        intro h
        apply hy
        ext
        calc (y : D.Fq) = (-D.nrm (z : D.Fq2)) / (-1) * (x : D.Fq) := h
          _ = D.nrm (z : D.Fq2) * (x : D.Fq) := by rw [div_neg, div_one, neg_neg]
      simp only [FieldData.borelModel, hne, ↓reduceIte, mul_zero]
    · intro hmem; exact (hmem (Finset.mem_univ y₀)).elim
  rw [Matrix.trace]
  dsimp only [Matrix.diag]
  dsimp only [M] at hM
  simp_rw [hM, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hψ_sum : ∀ t : D.Fq, (∑ x : D.Fqˣ, D.psi ((x : D.Fq) * t)) =
      (if t = 0 then (D.q : ℂ) else 0) - 1 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp only [mul_zero, psi_zero, Finset.sum_const, Finset.card_univ, card_Fq_units,
        nsmul_eq_mul, mul_one, ↓reduceIte]
      have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
        have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hcard]
    · rw [if_neg ht, zero_sub]
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.Fq)
        (fun y => y ≠ 0) (fun y => D.psi (y * t))
      have h0set : Finset.univ.filter (fun y : D.Fq => ¬ y ≠ 0) = {0} := by ext y; simp
      have htot : (∑ y : D.Fq, D.psi (y * t)) = 0 := by
        simp_rw [mul_comm _ t]
        rw [sum_psi D t, if_neg ht]
      rw [h0set, Finset.sum_singleton, zero_mul, psi_zero, htot] at hsplit
      have hbij : (∑ x : D.Fqˣ, D.psi ((x : D.Fq) * t)) =
          ∑ y ∈ Finset.univ.filter (fun y : D.Fq => y ≠ 0), D.psi (y * t) := by
        refine Finset.sum_bij (fun x _ => (x : D.Fq)) ?_ ?_ ?_ ?_
        · intro x _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.ne_zero⟩
        · intro x₁ _ x₂ _ h; exact Units.ext h
        · intro y hy
          exact ⟨Units.mk0 y (Finset.mem_filter.mp hy).2, Finset.mem_univ _, rfl⟩
        · intro _ _; rfl
      rw [hbij]
      linear_combination hsplit
  have hswap : (∑ w ∈ fib, ∑ x : D.Fqˣ,
        D.psi ((x : D.Fq) * (D.tr (z : D.Fq2) + D.tr w)) * D.theta m w) =
      (∑ w ∈ fib, (if D.tr (z : D.Fq2) + D.tr w = 0 then (D.q : ℂ) else 0) * D.theta m w) -
        ∑ w ∈ fib, D.theta m w := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul, hψ_sum]
    ring
  have hfib_tr : (∑ w ∈ fib, (if D.tr (z : D.Fq2) + D.tr w = 0 then (D.q : ℂ) else 0) * D.theta m w) =
      (D.q : ℂ) * (D.theta m (-(z : D.Fq2)) + D.theta m (-((z : D.Fq2) ^ D.q))) := by
    let S := fib.filter (fun w => D.tr (z : D.Fq2) + D.tr w = 0)
    have hS_eq : S = ({-(z : D.Fq2), -((z : D.Fq2) ^ D.q)} : Finset D.Fq2) := by
      ext w
      simp only [S, fib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, hn⟩, htr⟩
        have htr_w : D.tr w = -D.tr (z : D.Fq2) := eq_neg_of_add_eq_zero_right htr
        have halg : (w + (z : D.Fq2)) * (w + (z : D.Fq2) ^ D.q) = 0 := by
          have h1 : algebraMap D.Fq D.Fq2 (D.nrm w) = algebraMap D.Fq D.Fq2 (D.nrm (z : D.Fq2)) :=
            congrArg (algebraMap D.Fq D.Fq2) hn
          rw [algebraMap_nrm, algebraMap_nrm] at h1
          have h2 : algebraMap D.Fq D.Fq2 (D.tr w) = algebraMap D.Fq D.Fq2 (-D.tr (z : D.Fq2)) :=
            congrArg (algebraMap D.Fq D.Fq2) htr_w
          rw [map_neg, algebraMap_tr, algebraMap_tr] at h2
          have hwq : w ^ D.q = -((z : D.Fq2) + (z : D.Fq2) ^ D.q) - w := by
            linear_combination h2
          rw [hwq] at h1
          linear_combination -h1
        rcases mul_eq_zero.mp halg with h | h
        · left; exact eq_neg_of_add_eq_zero_left h
        · right; exact eq_neg_of_add_eq_zero_left h
      · rintro (rfl | rfl)
        · refine ⟨⟨neg_ne_zero.mpr z.ne_zero, nrm_neg D (z : D.Fq2)⟩, ?_⟩
          rw [tr_neg, add_neg_cancel]
        · have hne : -((z : D.Fq2) ^ D.q) ≠ 0 := neg_ne_zero.mpr (pow_ne_zero _ z.ne_zero)
          have hnrm : D.nrm (-((z : D.Fq2) ^ D.q)) = D.nrm (z : D.Fq2) := by
            rw [nrm_neg]
            apply (algebraMap D.Fq D.Fq2).injective
            rw [algebraMap_nrm, algebraMap_nrm, pow_q_sq, mul_comm]
          have htr : D.tr (z : D.Fq2) + D.tr (-((z : D.Fq2) ^ D.q)) = 0 := by
            rw [tr_neg, tr_pow_q, add_neg_cancel]
          exact ⟨⟨hne, hnrm⟩, htr⟩
    have hsum1 : (∑ w ∈ fib, (if D.tr (z : D.Fq2) + D.tr w = 0 then (D.q : ℂ) else 0) * D.theta m w) =
        ∑ w ∈ S, (D.q : ℂ) * D.theta m w := by
      simp only [S, Finset.sum_filter]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases h : D.tr (z : D.Fq2) + D.tr w = 0 <;> simp [h]
    have hne_pair : -(z : D.Fq2) ≠ -((z : D.Fq2) ^ D.q) := fun h => hzq (neg_inj.mp h).symm
    rw [hsum1, hS_eq, Finset.sum_pair hne_pair, mul_add]
  rw [hswap, hfib_tr, sum_theta_nrm_fiber D hreg (D.nrm (z : D.Fq2)) hnrm_ne, sub_zero]
  have hθm1 : D.theta m (-1 : D.Fq2) = D.chi γ (-1) := by
    rw [← theta_algebraMap, map_neg, map_one]
  have hθ_neg : D.theta m (-(z : D.Fq2)) + D.theta m (-((z : D.Fq2) ^ D.q)) =
      D.chi γ (-1) * (D.theta m (z : D.Fq2) + D.theta m ((z : D.Fq2) ^ D.q)) := by
    rw [show -(z : D.Fq2) = (-1 : D.Fq2) * (z : D.Fq2) from by ring,
      show -((z : D.Fq2) ^ D.q) = (-1 : D.Fq2) * (z : D.Fq2) ^ D.q from by ring,
      theta_mul, theta_mul, hθm1, mul_add]
  have hχm1_sq : D.chi γ (-1) * D.chi γ (-1) = 1 := by
    rw [← chi_mul D γ (by simp) (by simp), neg_mul_neg, one_mul, chi_one]
  rw [hθ_neg]
  have hq_ne : (D.q : ℂ) ≠ 0 := q_complex_ne D
  calc -((D.q : ℂ)⁻¹) * D.chi γ (-1) *
        ((D.q : ℂ) * (D.chi γ (-1) * (D.theta m (z : D.Fq2) + D.theta m ((z : D.Fq2) ^ D.q))))
      = -(((D.q : ℂ)⁻¹ * (D.q : ℂ)) * (D.chi γ (-1) * D.chi γ (-1)) *
          (D.theta m (z : D.Fq2) + D.theta m ((z : D.Fq2) ^ D.q))) := by ring
    _ = -(D.theta m (z : D.Fq2) + D.theta m ((z : D.Fq2) ^ D.q)) := by
        rw [inv_mul_cancel₀ hq_ne, hχm1_sq, one_mul, one_mul]

lemma cusp_repEquiv_iff (D : FieldData) (k k' : {k : D.Lab2 // D.IsCuspLabel k})
    (h : RepEquiv (D.R (.inr (.inr (.inr k)))) (D.R (.inr (.inr (.inr k'))))) :
    k = k' := by
  have hk := (cusp_isUnitary_irred_equiv D k).2.2
  have hk' := (cusp_isUnitary_irred_equiv D k').2.2
  have hpi : RepEquiv (fun g : D.G => D.piModel k.1 (g : Matrix (Fin 2) (Fin 2) D.Fq))
      (fun g : D.G => D.piModel k'.1 (g : Matrix (Fin 2) (Fin 2) D.Fq)) :=
    repEquiv_trans (repEquiv_symm hk) (repEquiv_trans h hk')
  have hchar : ∀ z : D.Fq2ˣ,
      D.theta k.1 (z : D.Fq2) + D.theta k.1 ((z : D.Fq2) ^ D.q) =
        D.theta k'.1 (z : D.Fq2) + D.theta k'.1 ((z : D.Fq2) ^ D.q) := by
    intro z
    by_cases hzq : (z : D.Fq2) ^ D.q = (z : D.Fq2)
    · obtain ⟨x, hx⟩ := (pow_q_eq_self_iff D (z : D.Fq2)).mp hzq
      have hx_ne : x ≠ 0 := by
        intro hx0; apply z.ne_zero; rw [← hx, hx0, map_zero]
      let g := glLift D !![x, 0; 0, x] (by simp [Matrix.det_fin_two, hx_ne])
      have htr := repEquiv_trace hpi g
      simp only [g, glLift_coe] at htr
      rw [piModel_trace_diag D k.1 hx_ne, piModel_trace_diag D k'.1 hx_ne, hx] at htr
      have hθ := mul_left_cancel₀ (q_sub_one_complex_ne D) htr
      rw [hzq, hθ]
    · have hnrm_ne : D.nrm (z : D.Fq2) ≠ 0 := mt (nrm_eq_zero D (z : D.Fq2)).mp z.ne_zero
      let g := glLift D !![D.tr (z : D.Fq2), -D.nrm (z : D.Fq2); 1, 0]
        (by simp [Matrix.det_fin_two, hnrm_ne])
      have htr := repEquiv_trace hpi g
      simp only [g, glLift_coe] at htr
      rw [piModel_trace_elliptic D k.2.1 hzq, piModel_trace_elliptic D k'.2.1 hzq] at htr
      exact neg_inj.mp htr
  have hsum : (∑ z : D.Fq2ˣ,
        conj (D.theta k.1 (z : D.Fq2)) * (D.theta k.1 (z : D.Fq2) + D.theta k.1 ((z : D.Fq2) ^ D.q))) =
      ∑ z : D.Fq2ˣ,
        conj (D.theta k.1 (z : D.Fq2)) * (D.theta k'.1 (z : D.Fq2) + D.theta k'.1 ((z : D.Fq2) ^ D.q)) :=
    Finset.sum_congr rfl fun z _ => by rw [hchar z]
  have hsimp : ∀ m : D.Lab2, (∑ z : D.Fq2ˣ,
        conj (D.theta k.1 (z : D.Fq2)) * (D.theta m (z : D.Fq2) + D.theta m ((z : D.Fq2) ^ D.q))) =
      (∑ z : D.Fq2ˣ, D.theta (m - k.1) (z : D.Fq2)) +
        (∑ z : D.Fq2ˣ, D.theta ((D.q : D.Lab2) * m - k.1) (z : D.Fq2)) := by
    intro m
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [conj_theta, theta_pow_q, mul_add, ← theta_add_label, ← theta_add_label,
      add_comm (-k.1) m, add_comm (-k.1) ((D.q : D.Lab2) * m), ← sub_eq_add_neg, ← sub_eq_add_neg]
  rw [hsimp k.1, hsimp k'.1, sum_theta_units, sum_theta_units, sum_theta_units, sum_theta_units] at hsum
  have hk_ne : (D.q : D.Lab2) * k.1 - k.1 ≠ 0 := fun h0 =>
    k.2.1 ((q_mul_eq_self_iff D k.1).mp (sub_eq_zero.mp h0))
  rw [if_pos (sub_self k.1), if_neg hk_ne, add_zero] at hsum
  have hq2_ne : ((D.q ^ 2 - 1 : ℕ) : ℂ) ≠ 0 := by
    have hq := D.one_lt_q
    have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq (by decide)
    exact_mod_cast (by omega : D.q ^ 2 - 1 ≠ 0)
  by_cases h1 : k'.1 - k.1 = 0
  · exact Subtype.ext (sub_eq_zero.mp h1).symm
  · by_cases h2 : (D.q : D.Lab2) * k'.1 - k.1 = 0
    · have hqk' : (D.q : D.Lab2) * k'.1 = k.1 := sub_eq_zero.mp h2
      have hqk : (D.q : D.Lab2) * k.1 = k'.1 := by
        calc (D.q : D.Lab2) * k.1 = (D.q : D.Lab2) * ((D.q : D.Lab2) * k'.1) := by rw [hqk']
          _ = ((D.q : D.Lab2) * (D.q : D.Lab2)) * k'.1 := by ring
          _ = k'.1 := by rw [q_sq_cast_Lab2, one_mul]
      have hval1 : k.1.val ≤ k'.1.val := by simpa [hqk] using k.2.2
      have hval2 : k'.1.val ≤ k.1.val := by simpa [hqk'] using k'.2.2
      exact Subtype.ext (ZMod.val_injective _ (le_antisymm hval1 hval2))
    · rw [if_neg h1, if_neg h2, add_zero] at hsum
      exact (hq2_ne hsum).elim

lemma det_add_st_trace (D : FieldData) (α : D.Lab) (g : D.G) :
    Matrix.trace (D.R (.inl α) g) + Matrix.trace (D.R (.inr (.inl α)) g) =
      Matrix.trace (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  let b : Unit ⊕ Option D.Lab → Option D.Fq → ℂ
    | .inl _ => D.detVec α
    | .inr i => D.stVec α i
  have horth : ∀ i j : Unit ⊕ Option D.Lab, dotProduct (star (b i)) (b j) = if i = j then 1 else 0 := by
    rintro (_ | i) (_ | j)
    · simp only [b, ↓reduceIte]; exact dot_conj_detVec_detVec D α
    · simp only [b]; rw [if_neg Sum.inl_ne_inr]; exact dot_conj_detVec_stVec D α j
    · simp only [b]; rw [if_neg Sum.inr_ne_inl]
      have h0 := dot_conj_detVec_stVec D α i
      have hconj : dotProduct (star (D.stVec α i)) (D.detVec α) =
          conj (dotProduct (star (D.detVec α)) (D.stVec α i)) := by
        simp only [dotProduct, Pi.star_apply, Complex.star_def, map_sum, map_mul,
          starRingEnd_self_apply]
        refine Finset.sum_congr rfl fun x _ => by ring
      rw [hconj, h0, map_zero]
    · simp only [b, Sum.inr.injEq]; exact dot_conj_stVec D α i j
  have hcard : Fintype.card (Unit ⊕ Option D.Lab) = Fintype.card (Option D.Fq) := by
    rw [Fintype.card_sum, Fintype.card_unit, Fintype.card_option, Fintype.card_option,
      card_Lab, card_Fq]
    have := D.one_lt_q; omega
  let Q := basisMatrix b
  have hQr : Q * Qᴴ = 1 := basisMatrix_mul_conjTranspose b hcard horth
  let M_block : Matrix (Unit ⊕ Option D.Lab) (Unit ⊕ Option D.Lab) ℂ :=
    Qᴴ * D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq) * Q
  have htr_M : Matrix.trace M_block = Matrix.trace (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
    dsimp only [M_block]
    rw [Matrix.trace_mul_cycle, hQr, Matrix.one_mul]
  have hdet_eq : M_block (.inl ()) (.inl ()) = D.R (.inl α) g () () := by
    dsimp only [M_block]
    rw [← matEntry_eq_basisMatrix_mul]
    rfl
  have hst_eq : ∀ i : Option D.Lab, M_block (.inr i) (.inr i) = D.R (.inr (.inl α)) g i i := fun i => by
    dsimp only [M_block]
    rw [← matEntry_eq_basisMatrix_mul]
    rfl
  have hM_sum : (∑ u : Unit, M_block (.inl u) (.inl u)) = M_block (.inl ()) (.inl ()) :=
    Finset.sum_eq_single () (fun u _ hu => (hu (Subsingleton.elim u ())).elim)
      (fun h => (h (Finset.mem_univ ())).elim)
  have hsum_det : (∑ u : D.Bas (.inl α), D.R (.inl α) g u u) = D.R (.inl α) g () () := by
    change ∑ u : Unit, D.R (.inl α) g u u = _
    exact Finset.sum_eq_single () (fun u _ hu => (hu (Subsingleton.elim u ())).elim)
      (fun h => (h (Finset.mem_univ ())).elim)
  have hsum_st : (∑ i : D.Bas (.inr (.inl α)), D.R (.inr (.inl α)) g i i) =
      ∑ i : Option D.Lab, D.R (.inr (.inl α)) g i i := rfl
  rw [← htr_M, Matrix.trace, Matrix.trace, Matrix.trace]
  dsimp only [Matrix.diag]
  rw [Fintype.sum_sum_type, hM_sum, hsum_det, hsum_st, ← hdet_eq]
  congr 1
  exact Finset.sum_congr rfl fun i _ => (hst_eq i).symm

lemma psModel_trace_diag_gen (D : FieldData) (hq : 2 < D.q) (α β : D.Lab) :
    Matrix.trace (D.psModel α β !![D.gen, 0; 0, 1]) = D.chi α D.gen + D.chi β D.gen := by
  let M : Matrix (Fin 2) (Fin 2) D.Fq := !![D.gen, 0; 0, 1]
  have hgen_ne1 : D.gen ≠ 1 := by
    intro h1
    have hord := orderOf_gen D
    rw [h1, orderOf_one] at hord
    omega
  rw [Matrix.trace]
  dsimp only [Matrix.diag]
  rw [Fintype.sum_option]
  have hnone : D.psModel α β M none none = D.chi α D.gen := by
    rw [psModel_eq_ite]
    have hmob : mobius D M none = none := by simp [mobius, M]
    have hcoc : cocycle D α β M none = D.chi α D.gen := by
      simp [cocycle, bMat, M, chi_one]
    rw [hmob, if_pos rfl, hcoc]
  have hzero : D.psModel α β M (some 0) (some 0) = D.chi β D.gen := by
    rw [psModel_eq_ite]
    have hmob : mobius D M (some 0) = some 0 := by simp [mobius, M]
    have hcoc : cocycle D α β M (some 0) = D.chi β D.gen := by
      simp [cocycle, bMat, M, Matrix.det_fin_two, chi_one]
    rw [hmob, if_pos rfl, hcoc]
  have hrest : ∀ u : D.Fq, u ≠ 0 → D.psModel α β M (some u) (some u) = 0 := by
    intro u hu
    rw [psModel_eq_ite]
    have hmob : mobius D M (some u) = some (D.gen * u) := by simp [mobius, M]
    have hne : some u ≠ some (D.gen * u) := by
      intro h
      have heq : u = D.gen * u := Option.some.inj h
      have h1 : D.gen * u = 1 * u := by rw [← heq, one_mul]
      exact hgen_ne1 (mul_right_cancel₀ hu h1)
    rw [hmob, if_neg hne]
  rw [hnone, Finset.sum_eq_single (0 : D.Fq)]
  · rw [hzero]
  · intro u _ hu; exact hrest u hu
  · intro hmem; exact (hmem (Finset.mem_univ (0 : D.Fq))).elim

lemma det_trace_upper (D : FieldData) (α : D.Lab) {a d : D.Fq} (ha : a ≠ 0) (hd : d ≠ 0)
    (b : D.Fq) :
    Matrix.trace (D.R (.inl α) (glLift D !![a, b; 0, d] (by simp [Matrix.det_fin_two, ha, hd]))) =
      D.chi α (a * d) := by
  let M : Matrix (Fin 2) (Fin 2) D.Fq := !![a, b; 0, d]
  have hdet : M.det ≠ 0 := by simp [M, Matrix.det_fin_two, ha, hd]
  let g := glLift D M hdet
  have hsum : (∑ u : D.Bas (.inl α), D.R (.inl α) g u u) = D.R (.inl α) g () () := by
    change ∑ u : Unit, D.R (.inl α) g u u = _
    rw [Finset.univ_unique, Finset.sum_singleton]
  rw [Matrix.trace]
  dsimp only [Matrix.diag]
  rw [hsum]
  have hent : D.R (.inl α) g () () = matEntry (D.psModel α α M) (D.detVec α) (D.detVec α) := rfl
  rw [hent, matEntry_eq_dot_mulVec]
  have hmul : D.psModel α α M *ᵥ D.detVec α = D.chi α (a * d) • D.detVec α := by
    ext y
    rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    cases y with
    | none =>
      rw [Finset.sum_eq_single none]
      · rw [psModel_eq_ite]
        have hmob : mobius D M none = none := by simp [mobius, M]
        have hcoc : cocycle D α α M none = D.chi α (a * d) := by
          simp [cocycle, bMat, M, chi_mul D α ha hd]
        rw [hmob, if_pos rfl, hcoc, mul_comm]
      · intro x _ hx
        cases x with
        | none => exact (hx rfl).elim
        | some u =>
          rw [psModel_eq_ite]
          have hmob : mobius D M (some u) = some ((a * u + b) / d) := by simp [mobius, M, hd]
          rw [hmob, if_neg (by simp), zero_mul]
      · intro hmem; exact (hmem (Finset.mem_univ none)).elim
    | some v =>
      let u₀ : D.Fq := (d * v - b) / a
      rw [Finset.sum_eq_single (some u₀)]
      · rw [psModel_eq_ite]
        have hmob : mobius D M (some u₀) = some v := by
          have h10 : M 1 0 = 0 := rfl
          have h11 : M 1 1 = d := rfl
          have h00 : M 0 0 = a := rfl
          have h01 : M 0 1 = b := rfl
          dsimp only [mobius]
          rw [h10, h11, h00, h01, zero_mul, zero_add, if_pos hd]
          congr 1; dsimp only [u₀]; field_simp [ha, hd]; ring
        have hcoc : cocycle D α α M (some u₀) = D.chi α (a * d) := by
          have h10 : M 1 0 = 0 := rfl
          have h11 : M 1 1 = d := rfl
          have h00 : M 0 0 = a := rfl
          have h01 : M 0 1 = b := rfl
          have hb00 : (bMat D M (some u₀)) 0 0 = d := by
            dsimp only [bMat]
            rw [h10, h11, zero_mul, zero_add, if_pos hd]
            rfl
          have hb11 : (bMat D M (some u₀)) 1 1 = a := by
            dsimp only [bMat]
            rw [h10, h11, zero_mul, zero_add, if_pos hd, Matrix.det_fin_two, h00, h01, h10, h11,
              mul_zero, sub_zero]
            change a * d / d = a
            field_simp [hd]
          dsimp only [cocycle]
          rw [hb00, hb11, ← chi_mul D α hd ha, mul_comm d a]
        rw [hmob, if_pos rfl, hcoc]
        simp [FieldData.detVec, mul_comm]
      · intro x _ hx
        cases x with
        | none =>
          rw [psModel_eq_ite]
          have hmob : mobius D M none = none := by simp [mobius, M]
          rw [hmob, if_neg (by simp), zero_mul]
        | some u =>
          rw [psModel_eq_ite]
          have hmob : mobius D M (some u) = some ((a * u + b) / d) := by simp [mobius, M, hd]
          have hne : some v ≠ some ((a * u + b) / d) := by
            intro heq
            apply hx
            congr 1
            have hv : v = (a * u + b) / d := Option.some.inj heq
            dsimp only [u₀]; rw [hv]; field_simp [ha, hd]; ring
          rw [hmob, if_neg hne, zero_mul]
      · intro hmem; exact (hmem (Finset.mem_univ (some u₀))).elim
  have hdot : dotProduct (star (D.detVec α)) (D.chi α (a * d) • D.detVec α) = D.chi α (a * d) := by
    simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
    have h1 : (∑ x : Option D.Fq, star (D.detVec α x) * (D.chi α (a * d) * D.detVec α x)) =
        D.chi α (a * d) * dotProduct (star (D.detVec α)) (D.detVec α) := by
      simp only [dotProduct, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [h1, dot_conj_detVec_detVec, mul_one]
  rw [hmul, hdot]

lemma R_not_repEquiv (D : FieldData) :
    ∀ μ μ' : D.Irr, μ ≠ μ' → ¬ RepEquiv (D.R μ) (D.R μ') := by
  intro μ μ' hne h
  apply hne
  have hcard : Fintype.card (D.Bas μ) = Fintype.card (D.Bas μ') := repEquiv_card_eq h
  rcases bas_card_cases D μ with ⟨α, rfl, hc1⟩ | ⟨α, rfl, hc1⟩ | ⟨ab, rfl, hc1⟩ | ⟨k, rfl, hc1⟩ <;>
  rcases bas_card_cases D μ' with ⟨α', rfl, hc2⟩ | ⟨α', rfl, hc2⟩ | ⟨ab', rfl, hc2⟩ | ⟨k', rfl, hc2⟩
  · by_cases hq2 : D.q = 2
    · have : Fintype.card D.Lab = 1 := by rw [card_Lab, hq2]
      have hss : Subsingleton D.Lab := Fintype.card_le_one_iff_subsingleton.mp this.le
      rw [Subsingleton.elim α α']
    · let g := glLift D !![D.gen, 0; 0, 1] (by simp [Matrix.det_fin_two, gen_ne_zero D])
      have htr := repEquiv_trace h g
      rw [det_trace_upper D α (gen_ne_zero D) one_ne_zero 0,
        det_trace_upper D α' (gen_ne_zero D) one_ne_zero 0, mul_one] at htr
      by_contra hne_α
      exact chi_gen_ne D (fun heq => hne_α (congrArg Sum.inl heq)) htr
  · have := D.one_lt_q; omega
  · have := D.one_lt_q; omega
  · exfalso
    let g := glLift D !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])
    have htr := repEquiv_trace h g
    have htr2 := repEquiv_trace (cusp_isUnitary_irred_equiv D k').2.2 g
    rw [det_trace_upper D α one_ne_zero one_ne_zero 1, mul_one, chi_one] at htr
    rw [htr2, glLift_coe, piModel_trace_unipotent] at htr
    norm_num at htr
  · have := D.one_lt_q; omega
  · by_cases hq2 : D.q ≤ 2
    · have hq_eq : D.q = 2 := by have := D.one_lt_q; omega
      have : Fintype.card D.Lab = 1 := by rw [card_Lab, hq_eq]
      have hss : Subsingleton D.Lab := Fintype.card_le_one_iff_subsingleton.mp this.le
      rw [Subsingleton.elim α α']
    · have hq : 2 < D.q := by omega
      let g := glLift D !![D.gen, 0; 0, 1] (by simp [Matrix.det_fin_two, gen_ne_zero D])
      have htr := repEquiv_trace h g
      have hsum1 := det_add_st_trace D α g
      have hsum2 := det_add_st_trace D α' g
      rw [det_trace_upper D α (gen_ne_zero D) one_ne_zero 0, mul_one,
        glLift_coe, psModel_trace_diag_gen D hq α α] at hsum1
      rw [det_trace_upper D α' (gen_ne_zero D) one_ne_zero 0, mul_one,
        glLift_coe, psModel_trace_diag_gen D hq α' α'] at hsum2
      have hst1 : Matrix.trace (D.R (.inr (.inl α)) g) = D.chi α D.gen := by
        linear_combination hsum1
      have hst2 : Matrix.trace (D.R (.inr (.inl α')) g) = D.chi α' D.gen := by
        linear_combination hsum2
      rw [hst1, hst2] at htr
      by_contra hne_α
      exact chi_gen_ne D (fun heq => hne_α (by rw [heq])) htr
  · have := D.one_lt_q; omega
  · have := D.one_lt_q; omega
  · have := D.one_lt_q; omega
  · have := D.one_lt_q; omega
  · have hps := (GL2QFT.lemma_6_5 D).2.2 ab.1.1 ab.1.2 ab'.1.1 ab'.1.2
    have h1 := (ps_isUnitary_irred_equiv D ab).2.2
    have h2 := (ps_isUnitary_irred_equiv D ab').2.2
    have hps_eq : RepEquiv (fun g : D.G => D.psModel ab.1.1 ab.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq))
        (fun g : D.G => D.psModel ab'.1.1 ab'.1.2 (g : Matrix (Fin 2) (Fin 2) D.Fq)) :=
      repEquiv_trans (repEquiv_symm h1) (repEquiv_trans h h2)
    rcases hps.mp hps_eq with ⟨h11, h22⟩ | ⟨h12, h21⟩
    · congr 1; congr 1; congr 1; exact Subtype.ext (Prod.ext h11 h22)
    · exfalso
      have ha : ab.1.1.val < ab.1.2.val := ab.2
      have hb : ab'.1.1.val < ab'.1.2.val := ab'.2
      rw [h12, h21] at ha
      omega
  · have := D.one_lt_q; omega
  · exfalso
    let g := glLift D !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])
    have htr := repEquiv_trace h g
    have htr1 := repEquiv_trace (cusp_isUnitary_irred_equiv D k).2.2 g
    rw [htr1, glLift_coe, piModel_trace_unipotent] at htr
    rw [det_trace_upper D α' one_ne_zero one_ne_zero 1, mul_one, chi_one] at htr
    norm_num at htr
  · have := D.one_lt_q; omega
  · have := D.one_lt_q; omega
  · rw [cusp_repEquiv_iff D k k' h]

/-! ### Section 6: Schur orthogonality, completeness, and final Table 2 theorem -/

lemma R_isUnitary (D : FieldData) (μ : D.Irr) : IsUnitaryRep (D.R μ) := by
  rcases μ with α | α | ab | k
  · exact (det_st_isUnitary_and_irred D α).1
  · exact (det_st_isUnitary_and_irred D α).2.2.1
  · exact (ps_isUnitary_irred_equiv D ab).1
  · exact (cusp_isUnitary_irred_equiv D k).1

lemma R_isIrreducible (D : FieldData) (μ : D.Irr) : IsIrreducibleRep (D.R μ) := by
  rcases μ with α | α | ab | k
  · exact (det_st_isUnitary_and_irred D α).2.1
  · exact (det_st_isUnitary_and_irred D α).2.2.2
  · exact (ps_isUnitary_irred_equiv D ab).2.1
  · exact (cusp_isUnitary_irred_equiv D k).2.1

private lemma ker_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₁ (LinearMap.ker A.mulVecLin) := by
  intro g v hv
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

private lemma range_invariant {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    {A : Matrix ι₂ ι₁ ℂ} (hA : ∀ g : G, R₂ g * A = A * R₁ g) :
    IsInvariantSubspace R₂ (LinearMap.range A.mulVecLin) := by
  intro g w hw
  rcases hw with ⟨v, rfl⟩
  refine ⟨R₁ g *ᵥ v, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, ← hA g, ← Matrix.mulVec_mulVec]

private lemma mulVecLin_eq_zero_iff {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    (A : Matrix ι₂ ι₁ ℂ) : (∀ v, A *ᵥ v = 0) ↔ A = 0 := by
  constructor
  · intro h
    ext i j
    have := congr_fun (h (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · intro h v
    subst h
    simp

private lemma schur_zero_of_not_repEquiv {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (hi1 : IsIrreducibleRep R₁) (hi2 : IsIrreducibleRep R₂)
    (hne : ¬ RepEquiv R₁ R₂) {A : Matrix ι₂ ι₁ ℂ}
    (hA : ∀ g : G, A * R₁ g = R₂ g * A) : A = 0 := by
  have hA' : ∀ g : G, R₂ g * A = A * R₁ g := fun g => (hA g).symm
  by_contra hAne
  have hker_ne : LinearMap.ker A.mulVecLin ≠ ⊤ := by
    intro htop
    apply hAne
    rw [← mulVecLin_eq_zero_iff]
    intro v
    have hv : v ∈ LinearMap.ker A.mulVecLin := htop.symm ▸ Submodule.mem_top
    simpa [Matrix.mulVecLin_apply] using hv
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    (hi1.2 _ (ker_invariant hA')).resolve_right hker_ne
  have hinj : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp hker
  have hrange_ne : LinearMap.range A.mulVecLin ≠ ⊥ := by
    intro hbot
    apply hAne
    rw [← mulVecLin_eq_zero_iff]
    intro v
    have hv : A.mulVecLin v ∈ (⊥ : Submodule ℂ (ι₂ → ℂ)) := hbot ▸ LinearMap.mem_range_self _ v
    simpa [Matrix.mulVecLin_apply] using hv
  have hrange : LinearMap.range A.mulVecLin = ⊤ :=
    (hi2.2 _ (range_invariant hA')).resolve_left hrange_ne
  have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp hrange
  let e : (ι₁ → ℂ) ≃ₗ[ℂ] (ι₂ → ℂ) := LinearEquiv.ofBijective A.mulVecLin ⟨hinj, hsurj⟩
  let B : Matrix ι₁ ι₂ ℂ := LinearMap.toMatrix' e.symm.toLinearMap
  have hA_eq : LinearMap.toMatrix' A.mulVecLin = A := LinearMap.toMatrix'_toLin' A
  have hAB : A * B = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : A.mulVecLin.comp e.symm.toLinearMap = LinearMap.id :=
      LinearMap.ext fun v => e.apply_symm_apply v
    rw [hc, LinearMap.toMatrix'_id]
  have hBA : B * A = 1 := by
    rw [← hA_eq, ← LinearMap.toMatrix'_comp]
    have hc : e.symm.toLinearMap.comp A.mulVecLin = LinearMap.id :=
      LinearMap.ext fun v => e.symm_apply_apply v
    rw [hc, LinearMap.toMatrix'_id]
  exact hne ⟨A, B, hAB, hBA, fun g _ => hA g⟩

private lemma schur_eq_smul_one {G ι : Type} [Fintype ι] [DecidableEq ι]
    {R : G → Matrix ι ι ℂ} (hi : IsIrreducibleRep R)
    {A : Matrix ι ι ℂ} (hA : ∀ g : G, R g * A = A * R g) :
    ∃ c : ℂ, A = c • (1 : Matrix ι ι ℂ) := by
  have : Nonempty ι := hi.1
  have : Nontrivial (ι → ℂ) := Function.nontrivial
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A.mulVecLin
  have hker_ne : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin ≠ ⊥ := by
    rw [Module.End.hasEigenvalue_iff] at hc
    intro hbot
    apply hc
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro v hv
    apply hbot
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rw [Module.End.mem_eigenspace_iff] at hv
    simpa [Matrix.mulVecLin_apply, sub_eq_zero] using hv
  have hA' : ∀ g : G, R g * (A - c • (1 : Matrix ι ι ℂ)) =
      (A - c • (1 : Matrix ι ι ℂ)) * R g := by
    intro g
    simp [mul_sub, sub_mul, hA g]
  have hker_top : LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin = ⊤ :=
    (hi.2 _ (ker_invariant hA')).resolve_left hker_ne
  refine ⟨c, ?_⟩
  rw [← sub_eq_zero, ← mulVecLin_eq_zero_iff]
  intro v
  have hv : v ∈ LinearMap.ker (A - c • (1 : Matrix ι ι ℂ)).mulVecLin :=
    hker_top.symm ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  exact hv

private def unitMat {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂]
    (i₀ : ι₁) (j₀ : ι₂) : Matrix ι₁ ι₂ ℂ :=
  Matrix.of fun a b => if a = i₀ ∧ b = j₀ then 1 else 0

private lemma mul_unitMat_mul_apply {ι₁ ι₂ ι₃ ι₄ : Type}
    [Fintype ι₂] [Fintype ι₃] [DecidableEq ι₂] [DecidableEq ι₃]
    (M : Matrix ι₁ ι₂ ℂ) (i₀ : ι₂) (j₀ : ι₃) (N : Matrix ι₃ ι₄ ℂ) (i₁ : ι₁) (j₁ : ι₄) :
    (M * unitMat i₀ j₀ * N) i₁ j₁ = M i₁ i₀ * N j₀ j₁ := by
  simp only [Matrix.mul_apply, unitMat, Matrix.of_apply]
  rw [Finset.sum_eq_single j₀]
  · rw [Finset.sum_eq_single i₀]
    · simp
    · intro a _ ha; simp [ha]
    · intro h; exact (h (Finset.mem_univ i₀)).elim
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    · simp
    · intro a _; simp [hb]
  · intro h; exact (h (Finset.mem_univ j₀)).elim

private lemma trace_unitMat {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ j₀ : ι) :
    Matrix.trace (unitMat i₀ j₀) = if i₀ = j₀ then 1 else 0 := by
  rw [Matrix.trace]
  dsimp only [Matrix.diag, unitMat, Matrix.of_apply]
  by_cases h : i₀ = j₀
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i₀]
    · simp
    · intro a _ ha; simp [ha]
    · intro hmem; exact (hmem (Finset.mem_univ i₀)).elim
  · rw [if_neg h, Finset.sum_eq_zero]
    intro a _
    by_cases ha : a = i₀
    · subst ha; simp [h]
    · simp [ha]

private def avgOp {G ι₁ ι₂ : Type} [Group G] [Fintype G] [Fintype ι₁] [Fintype ι₂]
    (ρ₁ : G → Matrix ι₁ ι₁ ℂ) (ρ₂ : G → Matrix ι₂ ι₂ ℂ)
    (E : Matrix ι₂ ι₁ ℂ) : Matrix ι₂ ι₁ ℂ :=
  ∑ g : G, ρ₂ g * E * ρ₁ g⁻¹

private lemma avgOp_intertwines {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {ρ₁ : G → Matrix ι₁ ι₁ ℂ} {ρ₂ : G → Matrix ι₂ ι₂ ℂ}
    (h1 : IsMatRep ρ₁) (h2 : IsMatRep ρ₂) (E : Matrix ι₂ ι₁ ℂ) (h : G) :
    avgOp ρ₁ ρ₂ E * ρ₁ h = ρ₂ h * avgOp ρ₁ ρ₂ E := by
  rw [avgOp, Matrix.sum_mul, Matrix.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  dsimp only [Equiv.mulLeft]
  calc ρ₂ g * E * ρ₁ g⁻¹ * ρ₁ h
      = ρ₂ g * E * (ρ₁ g⁻¹ * ρ₁ h) := by simp only [Matrix.mul_assoc]
    _ = ρ₂ (h * (h⁻¹ * g)) * E * ρ₁ (g⁻¹ * h) := by
        rw [← h1.2 g⁻¹ h, mul_inv_cancel_left]
    _ = (ρ₂ h * ρ₂ (h⁻¹ * g)) * E * ρ₁ (h⁻¹ * g)⁻¹ := by
        rw [h2.2 h (h⁻¹ * g), mul_inv_rev, inv_inv]
    _ = ρ₂ h * (ρ₂ (h⁻¹ * g) * E * ρ₁ (h⁻¹ * g)⁻¹) := by
        simp only [Matrix.mul_assoc]

private lemma schur_ortho_ne {G ι₁ ι₂ : Type} [Group G] [Fintype G]
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {ρ₁ : G → Matrix ι₁ ι₁ ℂ} {ρ₂ : G → Matrix ι₂ ι₂ ℂ}
    (hm1 : IsMatRep ρ₁) (hm2 : IsMatRep ρ₂)
    (hi1 : IsIrreducibleRep ρ₁) (hi2 : IsIrreducibleRep ρ₂)
    (hne : ¬ RepEquiv ρ₁ ρ₂) (a₁ b₁ : ι₁) (a₂ b₂ : ι₂) :
    ∑ g : G, ρ₂ g a₂ b₂ * ρ₁ g⁻¹ b₁ a₁ = 0 := by
  have hzero : avgOp ρ₁ ρ₂ (unitMat b₂ b₁) = 0 :=
    schur_zero_of_not_repEquiv hi1 hi2 hne (avgOp_intertwines hm1 hm2 (unitMat b₂ b₁))
  have hentry := congrArg (fun M : Matrix ι₂ ι₁ ℂ => M a₂ a₁) hzero
  rw [avgOp, Matrix.sum_apply, Matrix.zero_apply] at hentry
  simp_rw [mul_unitMat_mul_apply] at hentry
  exact hentry

private lemma schur_ortho_self {G ι : Type} [Group G] [Fintype G] [Fintype ι] [DecidableEq ι]
    {ρ : G → Matrix ι ι ℂ} (hm : IsMatRep ρ) (hi : IsIrreducibleRep ρ)
    (a₁ b₁ a₂ b₂ : ι) :
    ∑ g : G, ρ g a₁ b₁ * ρ g⁻¹ b₂ a₂ =
      if a₁ = a₂ ∧ b₁ = b₂ then (Fintype.card G : ℂ) / (Fintype.card ι : ℂ) else 0 := by
  have hinter : ∀ g : G, ρ g * avgOp ρ ρ (unitMat b₁ b₂) = avgOp ρ ρ (unitMat b₁ b₂) * ρ g :=
    fun g => (avgOp_intertwines hm hm (unitMat b₁ b₂) g).symm
  obtain ⟨c, hc⟩ := schur_eq_smul_one hi hinter
  have htr_T : Matrix.trace (avgOp ρ ρ (unitMat b₁ b₂)) =
      (Fintype.card G : ℂ) * (if b₁ = b₂ then 1 else 0) := by
    rw [avgOp]
    have hsum_tr : Matrix.trace (∑ g : G, ρ g * unitMat b₁ b₂ * ρ g⁻¹) =
        ∑ g : G, Matrix.trace (ρ g * unitMat b₁ b₂ * ρ g⁻¹) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]
      exact Finset.sum_comm
    rw [hsum_tr]
    have hterm : ∀ g : G, Matrix.trace (ρ g * unitMat b₁ b₂ * ρ g⁻¹) = if b₁ = b₂ then 1 else 0 := by
      intro g
      rw [Matrix.trace_mul_comm (ρ g * unitMat b₁ b₂) (ρ g⁻¹), ← Matrix.mul_assoc,
        ← hm.2 g⁻¹ g, inv_mul_cancel, hm.1, Matrix.one_mul, trace_unitMat]
    simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htr_c : Matrix.trace (c • (1 : Matrix ι ι ℂ)) = c * (Fintype.card ι : ℂ) := by
    rw [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  have htr_eq : Matrix.trace (avgOp ρ ρ (unitMat b₁ b₂)) = Matrix.trace (c • (1 : Matrix ι ι ℂ)) :=
    congrArg Matrix.trace hc
  have hc_val : c = (Fintype.card G : ℂ) / (Fintype.card ι : ℂ) * (if b₁ = b₂ then 1 else 0) := by
    have : Nonempty ι := hi.1
    have hι_ne : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [htr_T, htr_c] at htr_eq
    calc c = (c * (Fintype.card ι : ℂ)) / (Fintype.card ι : ℂ) := by
            rw [mul_div_cancel_right₀ _ hι_ne]
      _ = ((Fintype.card G : ℂ) * (if b₁ = b₂ then 1 else 0)) / (Fintype.card ι : ℂ) := by
            rw [← htr_eq]
      _ = (Fintype.card G : ℂ) / (Fintype.card ι : ℂ) * (if b₁ = b₂ then 1 else 0) := by ring
  have hentry := congrArg (fun M : Matrix ι ι ℂ => M a₁ a₂) hc
  rw [avgOp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, hc_val] at hentry
  simp_rw [mul_unitMat_mul_apply] at hentry
  rw [hentry]
  by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂ <;> simp [ha, hb]

lemma completeness_of_sum_sq_eq_card (D : FieldData)
    (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : D.G → Matrix ι ι ℂ)
    (hm : IsMatRep ρ) (hi : IsIrreducibleRep ρ) :
    ∃ μ : D.Irr, RepEquiv (D.R μ) ρ := by
  by_contra hnone
  push Not at hnone
  let S := (Σ μ : D.Irr, D.Bas μ × D.Bas μ) ⊕ (ι × ι)
  let F : S → D.G → ℂ := fun s g => match s with
    | .inl ⟨μ, a, b⟩ => D.R μ g a b
    | .inr (a, b) => ρ g a b
  let Gd : S → D.G → ℂ := fun s g => match s with
    | .inl ⟨μ, a, b⟩ => D.R μ g⁻¹ b a
    | .inr (a, b) => ρ g⁻¹ b a
  let dim : S → ℂ := fun s => match s with
    | .inl ⟨μ, _⟩ => (Fintype.card (D.Bas μ) : ℂ)
    | .inr _ => (Fintype.card ι : ℂ)
  have hdim_ne : ∀ s : S, dim s ≠ 0 := by
    rintro (⟨μ, _, _⟩ | ⟨_, _⟩)
    · have : Nonempty (D.Bas μ) := (R_isIrreducible D μ).1
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    · have : Nonempty ι := hi.1
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdot : ∀ s₁ s₂ : S, ∑ g : D.G, F s₁ g * Gd s₂ g =
      if s₁ = s₂ then (Fintype.card D.G : ℂ) / dim s₁ else 0 := by
    rintro (⟨μ₁, a₁, b₁⟩ | ⟨a₁, b₁⟩) (⟨μ₂, a₂, b₂⟩ | ⟨a₂, b₂⟩)
    · by_cases hμ : μ₁ = μ₂
      · subst hμ
        have hself := schur_ortho_self (R_isUnitary D μ₁).1 (R_isIrreducible D μ₁) a₁ b₁ a₂ b₂
        by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂
        · subst ha; subst hb; simpa [F, Gd, dim] using hself
        · rw [if_neg (fun h => by cases h; exact hb rfl)]
          simpa [F, Gd, ha, hb] using hself
        · rw [if_neg (fun h => by cases h; exact ha rfl)]
          simpa [F, Gd, ha, hb] using hself
        · rw [if_neg (fun h => by cases h; exact ha rfl)]
          simpa [F, Gd, ha, hb] using hself
      · have hne := schur_ortho_ne (R_isUnitary D μ₂).1 (R_isUnitary D μ₁).1
          (R_isIrreducible D μ₂) (R_isIrreducible D μ₁)
          (R_not_repEquiv D μ₂ μ₁ (Ne.symm hμ)) a₂ b₂ a₁ b₁
        rw [if_neg (fun h => by cases h; exact hμ rfl)]
        simpa [F, Gd] using hne
    · have hne := schur_ortho_ne hm (R_isUnitary D μ₁).1 hi (R_isIrreducible D μ₁)
        (fun heq => hnone μ₁ (repEquiv_symm heq)) a₂ b₂ a₁ b₁
      rw [if_neg (by simp)]
      simpa [F, Gd] using hne
    · have hne := schur_ortho_ne (R_isUnitary D μ₂).1 hm (R_isIrreducible D μ₂) hi
        (hnone μ₂) a₂ b₂ a₁ b₁
      rw [if_neg (by simp)]
      simpa [F, Gd] using hne
    · have hself := schur_ortho_self hm hi a₁ b₁ a₂ b₂
      by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂
      · subst ha; subst hb; simpa [F, Gd, dim] using hself
      · rw [if_neg (fun h => by cases h; exact hb rfl)]
        simpa [F, Gd, ha, hb] using hself
      · rw [if_neg (fun h => by cases h; exact ha rfl)]
        simpa [F, Gd, ha, hb] using hself
      · rw [if_neg (fun h => by cases h; exact ha rfl)]
        simpa [F, Gd, ha, hb] using hself
  have hli : LinearIndependent ℂ F := by
    rw [Fintype.linearIndependent_iff]
    intro c hc s₀
    have h0 : ∑ g : D.G, (∑ s : S, c s • F s) g * Gd s₀ g = 0 := by
      rw [hc]; simp
    have h1 : ∑ g : D.G, (∑ s : S, c s • F s) g * Gd s₀ g =
        c s₀ * ((Fintype.card D.G : ℂ) / dim s₀) := by
      simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have hterm : ∀ s : S, (∑ g : D.G, c s * F s g * Gd s₀ g) =
          c s * (if s = s₀ then (Fintype.card D.G : ℂ) / dim s else 0) := by
        intro s
        simp_rw [mul_assoc, ← Finset.mul_sum, hdot s s₀]
      simp_rw [hterm]
      rw [Finset.sum_eq_single s₀]
      · simp
      · intro s _ hs; simp [hs]
      · intro hmem; exact (hmem (Finset.mem_univ s₀)).elim
    rw [h1] at h0
    have hG_ne : (Fintype.card D.G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hcoeff_ne : (Fintype.card D.G : ℂ) / dim s₀ ≠ 0 := div_ne_zero hG_ne (hdim_ne s₀)
    exact (mul_eq_zero.mp h0).resolve_right hcoeff_ne
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at hle
  have hcard_S : Fintype.card S = (∑ μ : D.Irr, Fintype.card (D.Bas μ) ^ 2) + Fintype.card ι ^ 2 := by
    simp [S, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, pow_two]
  rw [hcard_S, sum_bas_sq D] at hle
  have : Nonempty ι := hi.1
  have hpos : 0 < Fintype.card ι ^ 2 := sq_pos_of_pos Fintype.card_pos
  omega

end GL2QFT.Table2Aux

open GL2QFT in
theorem solution (D : FieldData) :
    (∀ μ : D.Irr, IsUnitaryRep (D.R μ)) ∧
    (∀ μ : D.Irr, IsIrreducibleRep (D.R μ)) ∧
    (∀ μ μ' : D.Irr, μ ≠ μ' → ¬ RepEquiv (D.R μ) (D.R μ')) ∧
    (Fintype.card {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} = (D.q - 1) * (D.q - 2) / 2 ∧
      Fintype.card {k : D.Lab2 // D.IsCuspLabel k} = D.q * (D.q - 1) / 2) ∧
    (∑ μ : D.Irr, Fintype.card (D.Bas μ) ^ 2 = Fintype.card D.G ∧
      Fintype.card D.G = (D.q ^ 2 - 1) * (D.q ^ 2 - D.q)) ∧
    (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : D.G → Matrix ι ι ℂ),
      IsMatRep ρ → IsIrreducibleRep ρ → ∃ μ : D.Irr, RepEquiv (D.R μ) ρ) :=
  ⟨GL2QFT.Table2Aux.R_isUnitary D,
   GL2QFT.Table2Aux.R_isIrreducible D,
   GL2QFT.Table2Aux.R_not_repEquiv D,
   ⟨GL2QFT.Table2Aux.card_ps_labels D, GL2QFT.Table2Aux.card_cusp_labels D⟩,
   ⟨GL2QFT.Table2Aux.sum_bas_sq D, GL2QFT.Table2Aux.card_G D⟩,
   fun ι _ _ ρ hm hi => GL2QFT.Table2Aux.completeness_of_sum_sq_eq_card D ι ρ hm hi⟩
