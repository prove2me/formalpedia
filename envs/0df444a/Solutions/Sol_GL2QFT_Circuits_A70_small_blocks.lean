-- Prove2me | solution 1 for GL2QFT.Circuits.A70_small_blocks
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:34:16.661005+00:00
-- url     : https://prove2.me/submissions/4c2e3396-3a81-4b0f-bad1-0f96c47a0ba9

import Definitions.Def_GL2QFT_Circuits_Combinators
import Definitions.Def_GL2QFT_Supplement_TotalA

noncomputable section

open Classical

namespace GL2QFT.A70SmallBlocksAux

open GL2QFT GL2QFT.FieldData GL2QFT.Supplement GL2QFT.Supplement.TotalA
open QAlgorithms QAlgorithms.Complexity
open scoped ComplexConjugate

local instance (D : FieldData) : Field D.Fq := AdjoinRoot.instField
local instance (D : FieldData) : Field D.Fq2 := AdjoinRoot.instField
local instance (D : FieldData) : IsDomain D.Fq2 := inferInstance
local instance (D : FieldData) : IsReduced D.Fq2 := inferInstance

/-! ### Section 1: Field cardinalities, generator, and character identities -/

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

lemma q_pos (D : FieldData) : (0 : ℝ) < D.q := by
  exact_mod_cast (by have := D.one_lt_q; omega : 0 < D.q)

lemma q_sub_one_pos (D : FieldData) : (0 : ℝ) < (D.q : ℝ) - 1 := by
  have : (1 : ℝ) < D.q := by exact_mod_cast D.one_lt_q
  linarith

lemma q_complex_ne (D : FieldData) : (D.q : ℂ) ≠ 0 := by
  exact_mod_cast (by have := D.one_lt_q; omega : D.q ≠ 0)

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

lemma chi_neg_one_sq (D : FieldData) (α : D.Lab) : D.chi α (-1) * D.chi α (-1) = 1 := by
  have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [← chi_mul D α hm1 hm1, neg_mul_neg, one_mul, chi_one]

lemma conj_chi_neg_one (D : FieldData) (α : D.Lab) :
    conj (D.chi α (-1)) = D.chi α (-1) := by
  have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [conj_chi, ← chi_inv D α hm1, inv_neg, inv_one]

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
  conv_lhs => rw [← h_pow_dlog2 D hz₁, ← h_pow_dlog2 D hz₂, ← pow_add]
  rw [theta_pow_h]
  simp only [FieldData.theta, if_neg hz₁, if_neg hz₂, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma theta_h_ne_one (D : FieldData) {k : D.Lab2} (hk : k ≠ 0) : D.theta k D.h ≠ 1 := by
  have h1 : D.h ^ 1 = D.h := pow_one D.h
  rw [← h1, theta_pow_h, mul_one]
  rw [Ne, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (NeZero.ne (D.q ^ 2 - 1))]
  have hk_pos : 0 < k.val := Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero k).mp hk)
  exact Nat.not_dvd_of_pos_of_lt hk_pos (ZMod.val_lt k)

lemma sum_theta_ne_zero (D : FieldData) {k : D.Lab2} (hk : k ≠ 0) :
    ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z = 0 := by
  let S := ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z
  have hshift : D.theta k D.h * S = S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun z _ => D.h * z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact mul_ne_zero (h_ne_zero D) hz
    · intro z₁ _ z₂ _ heq
      exact mul_left_cancel₀ (h_ne_zero D) heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨D.h⁻¹ * w, ?_, by rw [← mul_assoc, mul_inv_cancel₀ (h_ne_zero D), one_mul]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact mul_ne_zero (inv_ne_zero (h_ne_zero D)) hw
    · intro z _
      exact (theta_mul D k D.h z).symm
  have hmul0 : (D.theta k D.h - 1) * S = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr (theta_h_ne_one D hk))

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

lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by
  simp [FieldData.psi]

lemma psi_add (D : FieldData) (x y : D.Fq) : D.psi (x + y) = D.psi x * D.psi y := by
  simp only [FieldData.psi, map_add]
  rw [← Complex.exp_add]
  have hp : 0 < D.p := D.hp.pos
  have hmod : (Algebra.trace (ZMod D.p) D.Fq x + Algebra.trace (ZMod D.p) D.Fq y).val % D.p =
      ((Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val) % D.p := by
    rw [ZMod.val_add, Nat.mod_mod]
  have harg : 2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) /
        (D.p : ℂ) +
      2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq y).val : ℕ) : ℂ) /
        (D.p : ℂ) =
      2 * Real.pi * Complex.I *
        ((((Algebra.trace (ZMod D.p) D.Fq x).val +
          (Algebra.trace (ZMod D.p) D.Fq y).val : ℕ) : ℂ)) / (D.p : ℂ) := by
    push_cast; ring
  rw [harg]
  exact exp_two_pi_I_div_congr hp hmod

lemma conj_psi (D : FieldData) (x : D.Fq) : conj (D.psi x) = D.psi (-x) := by
  have hmul : D.psi (-x) * D.psi x = 1 := by
    rw [← psi_add, neg_add_cancel, psi_zero]
  have hnorm : conj (D.psi x) * D.psi x = 1 := by
    simp only [FieldData.psi]
    let r : ℝ := 2 * Real.pi * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℝ) / (D.p : ℝ)
    have hreal : (r : ℂ) * Complex.I =
        2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) /
          (D.p : ℂ) := by
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

lemma algebraMap_tr (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.tr z) = z + z ^ D.q := by
  have hfin : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  rw [FieldData.tr, FiniteField.algebraMap_trace_eq_sum_pow D.Fq D.Fq2 z, hfin,
    ← Fintype.card_eq_nat_card, card_Fq, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one, pow_one]

lemma algebraMap_nrm (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.nrm z) = z * z ^ D.q := by
  have hfin : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  rw [FieldData.nrm, FiniteField.algebraMap_norm_eq_prod_pow D.Fq D.Fq2 z, hfin,
    ← Fintype.card_eq_nat_card, card_Fq, Finset.prod_range_succ, Finset.prod_range_one,
    pow_zero, pow_one, pow_one]

lemma nrm_eq_zero (D : FieldData) (z : D.Fq2) : D.nrm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    have h1 : z * z ^ D.q = 0 := by rw [← algebraMap_nrm, hz, map_zero]
    rcases mul_eq_zero.mp h1 with rfl | hq
    · rfl
    · exact eq_zero_of_pow_eq_zero hq
  · rintro rfl
    apply (algebraMap D.Fq D.Fq2).injective
    rw [map_zero, algebraMap_nrm, zero_mul]

lemma sum_ne_zero_eq_sum_units {M : Type*} [AddCommMonoid M] (D : FieldData) (f : D.Fq → M) :
    ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), f t = ∑ t : D.Fqˣ, f (t : D.Fq) := by
  symm
  refine Finset.sum_bij (fun (t : D.Fqˣ) _ => (t : D.Fq))
    (fun t _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.ne_zero⟩)
    (fun _ _ _ _ h => Units.ext h)
    (fun t ht => ⟨Units.mk0 t (Finset.mem_filter.mp ht).2, Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

lemma gauss_eq_sum_units (D : FieldData) (α : D.Lab) :
    D.gauss α = ∑ u : D.Fqˣ, D.chi α (u : D.Fq) * D.psi (u : D.Fq) := by
  simp only [FieldData.gauss, FieldData.gaussG, one_mul]
  exact sum_ne_zero_eq_sum_units D (fun x => D.chi α x * D.psi x)

lemma gauss_zero (D : FieldData) : D.gauss 0 = -1 := by
  have htot := sum_psi D 1
  simp only [one_mul, one_ne_zero, ↓reduceIte] at htot
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset D.Fq) D.psi (Finset.mem_univ 0)
  rw [htot, psi_zero] at hsplit
  have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun x : D.Fq => x ≠ 0) := by
    ext x; simp
  have hgauss : D.gauss 0 = ∑ x ∈ Finset.univ.erase (0 : D.Fq), D.psi x := by
    rw [FieldData.gauss, FieldData.gaussG, hfilt]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [chi_zero_label D hx, one_mul, one_mul]
  rw [← hgauss] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit

/-! ### Section 2: Basis vectors, orthonormality, and `R μ 1` -/

lemma conj_isqrt (x : ℝ) : conj (isqrt x) = isqrt x := by simp [FieldData.isqrt]

lemma conj_isqrt_mul_isqrt {x : ℝ} (hx : 0 < x) :
    conj (isqrt x) * isqrt x = ((x : ℝ) : ℂ)⁻¹ := by
  rw [conj_isqrt]
  simp only [FieldData.isqrt, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hx.le, Complex.ofReal_inv]

lemma dot_star_smul_left {X : Type} [Fintype X] (c : ℂ) (u v : X → ℂ) :
    dotProduct (star (c • u)) v = conj c * dotProduct (star u) v := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul',
    Complex.star_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

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

lemma wVec_eq_smul_sum (D : FieldData) (β δ : D.Lab) :
    D.wVec β δ = isqrt (D.q - 1) • ∑ t : D.Fqˣ,
      (D.chi δ (t : D.Fq) * D.chi (-β) (t : D.Fq)) • D.vT (t : D.Fq) := by
  ext y
  simp only [FieldData.wVec, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  exact sum_ne_zero_eq_sum_units D (fun t => D.chi δ t * D.chi (-β) t * D.vT t y)

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

lemma dot_conj_multVec (D : FieldData) (i j : D.Lab) :
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
  calc conj (isqrt (D.q + 1)) * conj (D.chi α (-1)) * (isqrt (D.q + 1) * D.chi α (-1)) +
        ∑ _x : D.Fq, conj (isqrt (D.q + 1)) * isqrt (D.q + 1)
      = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) * (conj (D.chi α (-1)) * D.chi α (-1)) +
          (D.q : ℂ) * ((D.q : ℂ) + 1)⁻¹ := by
          rw [hsum]; ring
    _ = ((D.q : ℂ) + 1)⁻¹ * 1 + (D.q : ℂ) * ((D.q : ℂ) + 1)⁻¹ := by rw [hisqrt, h1]
    _ = ((D.q : ℂ) + 1)⁻¹ * ((D.q : ℂ) + 1) := by ring
    _ = 1 := inv_mul_cancel₀ (q_add_one_complex_ne D)

lemma dot_conj_stVec_none (D : FieldData) (α : D.Lab) :
    dotProduct (star (D.stVec α none)) (D.stVec α none) = 1 := by
  have h1 : conj (D.chi α (-1)) * D.chi α (-1) = 1 := by
    rw [conj_chi_neg_one, chi_neg_one_sq]
  have hisqrt1 : conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = ((D.q : ℂ) + 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (by linarith [q_pos D] : (0 : ℝ) < D.q + 1)
    simpa [Complex.ofReal_add, Complex.ofReal_one] using h
  have hisqrtq : conj (isqrt D.q) * isqrt D.q = (D.q : ℂ)⁻¹ := by
    simpa [Complex.ofReal_natCast] using conj_isqrt_mul_isqrt (q_pos D)
  have hsq : conj (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ) = (D.q : ℂ) := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (q_pos D).le,
      Complex.ofReal_natCast]
  simp only [dotProduct, FieldData.stVec, Fintype.sum_option, Pi.star_apply, Complex.star_def,
    map_mul, map_neg, neg_mul, mul_neg, neg_neg]
  have hsum : (∑ _x : D.Fq, conj (isqrt (D.q + 1)) * conj (isqrt D.q) * (isqrt (D.q + 1) * isqrt D.q)) =
      (D.q : ℂ) * (((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹) := by
    have hterm : conj (isqrt (D.q + 1)) * conj (isqrt D.q) * (isqrt (D.q + 1) * isqrt D.q) =
        ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹ := by
      calc conj (isqrt (D.q + 1)) * conj (isqrt D.q) * (isqrt (D.q + 1) * isqrt D.q)
          = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) * (conj (isqrt D.q) * isqrt D.q) := by ring
        _ = ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹ := by rw [hisqrt1, hisqrtq]
    simp [hterm, card_Fq]
  calc conj (isqrt (D.q + 1)) * (conj (Real.sqrt D.q : ℂ) * conj (D.chi α (-1))) *
          (isqrt (D.q + 1) * ((Real.sqrt D.q : ℂ) * D.chi α (-1))) +
        ∑ _x : D.Fq, conj (isqrt (D.q + 1)) * conj (isqrt D.q) * (isqrt (D.q + 1) * isqrt D.q)
      = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
          (conj (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ)) *
          (conj (D.chi α (-1)) * D.chi α (-1)) +
          (D.q : ℂ) * (((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹) := by
          rw [hsum]; ring
    _ = ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ) * 1 + (D.q : ℂ) * (((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹) := by
          rw [hisqrt1, hsq, h1]
    _ = ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ) + ((D.q : ℂ) + 1)⁻¹ * ((D.q : ℂ) * (D.q : ℂ)⁻¹) := by ring
    _ = ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ) + ((D.q : ℂ) + 1)⁻¹ * 1 := by
          rw [mul_inv_cancel₀ (q_complex_ne D)]
    _ = ((D.q : ℂ) + 1)⁻¹ * ((D.q : ℂ) + 1) := by ring
    _ = 1 := inv_mul_cancel₀ (q_add_one_complex_ne D)

lemma psModel_one (D : FieldData) (α β : D.Lab) :
    D.psModel α β (1 : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
  ext y x
  simp only [FieldData.psModel, Matrix.one_apply, Fin.isValue]
  cases x with
  | none => simp [chi_one, eq_comm]
  | some x' => simp [chi_one, eq_comm]

lemma borelModel_one (D : FieldData) (γ : D.Lab) :
    D.borelModel γ 1 0 1 = 1 := by
  ext y x
  simp only [FieldData.borelModel, Matrix.one_apply, div_one, one_mul, zero_mul,
    chi_one, psi_zero, mul_one]
  by_cases h : y = x
  · subst h; simp
  · have hne : (y : D.Fq) ≠ (x : D.Fq) := fun hval => h (Units.ext hval)
    simp [h, hne]

lemma piModel_one (D : FieldData) (k : D.Lab2) :
    D.piModel k (1 : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
  simp [FieldData.piModel, borelModel_one]

lemma matEntry_one {X : Type} [Fintype X] [DecidableEq X] (u v : X → ℂ) :
    matEntry (1 : Matrix X X ℂ) u v = dotProduct (star u) v := by
  simp only [matEntry, dotProduct, Pi.star_apply, Complex.star_def, Matrix.one_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [Ne.symm hy]
  · intro hm; exact (hm (Finset.mem_univ x)).elim

/-! ### Section 3: Matrix entries at `wGL D` -/

lemma matEntry_eq_sum_mulVec {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v : X → ℂ) :
    matEntry M u v = ∑ x, conj (u x) * M.mulVec v x := by
  simp only [matEntry, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma matEntry_smul_right {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v : X → ℂ) (c : ℂ) :
    matEntry M u (c • v) = c * matEntry M u v := by
  simp only [matEntry, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma matEntry_smul_left {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v : X → ℂ) (c : ℂ) :
    matEntry M (c • u) v = conj c * matEntry M u v := by
  simp only [matEntry, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

lemma matEntry_sum_right {X ι : Type} [Fintype X] (M : Matrix X X ℂ) (u : X → ℂ)
    (s : Finset ι) (f : ι → X → ℂ) :
    matEntry M u (∑ i ∈ s, f i) = ∑ i ∈ s, matEntry M u (f i) := by
  simp only [matEntry, Finset.sum_apply, Finset.mul_sum]
  calc ∑ x : X, ∑ y : X, ∑ i ∈ s, conj (u x) * M x y * f i y
      = ∑ x : X, ∑ i ∈ s, ∑ y : X, conj (u x) * M x y * f i y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ x : X, ∑ y : X, conj (u x) * M x y * f i y := Finset.sum_comm

lemma matEntry_sum_left {X ι : Type} [Fintype X] (M : Matrix X X ℂ)
    (s : Finset ι) (f : ι → X → ℂ) (v : X → ℂ) :
    matEntry M (∑ i ∈ s, f i) v = ∑ i ∈ s, matEntry M (f i) v := by
  simp only [matEntry, Finset.sum_apply, map_sum, Finset.sum_mul]
  calc ∑ x : X, ∑ y : X, ∑ i ∈ s, conj (f i x) * M x y * v y
      = ∑ x : X, ∑ i ∈ s, ∑ y : X, conj (f i x) * M x y * v y :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ x : X, ∑ y : X, conj (f i x) * M x y * v y := Finset.sum_comm

lemma psModel_wGL_apply (D : FieldData) (α₁ α₂ : D.Lab) (y x : Option D.Fq) :
    D.psModel α₁ α₂ ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) y x =
      match x with
      | none => if y = some 0 then 1 else 0
      | some x' =>
        if _hx : x' = 0 then (if y = none then 1 else 0)
        else if y = some x'⁻¹ then D.chi α₂ (-1) * D.chi (α₁ - α₂) x' else 0 := by
  have hw00 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = 0 := rfl
  have hw01 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 1 := rfl
  have hw10 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 1 := rfl
  have hw11 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = 0 := rfl
  dsimp only [FieldData.psModel]
  rw [hw00, hw01, hw10, hw11]
  cases x with
  | none =>
    simp [chi_one]
  | some x' =>
    dsimp only
    by_cases hx : x' = 0
    · subst hx
      simp [chi_one]
    · have hcond : (1 : D.Fq) * x' + 0 ≠ 0 := by simpa using hx
      have hloc : ((0 : D.Fq) * x' + 1) / ((1 : D.Fq) * x' + 0) = x'⁻¹ := by
        simp [one_div]
      have hdet : ((0 : D.Fq) * 0 - 1 * 1) / ((1 : D.Fq) * x' + 0) = -x'⁻¹ := by
        field_simp [hx]; ring
      rw [if_pos hcond, hloc, hdet, dif_neg hx]
      split_ifs with hy
      · have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
        rw [one_mul, add_zero, show (-x'⁻¹ : D.Fq) = (-1) * x'⁻¹ by ring,
          chi_mul D α₂ hm1 (inv_ne_zero hx), chi_inv D α₂ hx, sub_eq_add_neg, chi_add_label]
        ring
      · rfl

lemma matEntry_psModel_wGL_psVec_some_none_none (D : FieldData) (α β : D.Lab) :
    matEntry (D.psModel α β ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.psVec β (some none)) (D.psVec β none) = isqrt D.q := by
  rw [matEntry, Finset.sum_eq_single (some (0 : D.Fq))]
  · rw [Finset.sum_eq_single none]
    · simp [psModel_wGL_apply, FieldData.psVec, conj_isqrt]
    · intro x _ hx
      simp [FieldData.psVec, hx]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  · intro y _ hy
    rw [Finset.sum_eq_zero]
    intro x _
    cases x with
    | none => simp [psModel_wGL_apply, hy]
    | some x' => simp [FieldData.psVec]
  · intro hm; exact (hm (Finset.mem_univ _)).elim

lemma matEntry_psModel_wGL_detVec (D : FieldData) (α : D.Lab) :
    matEntry (D.psModel α α ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.detVec α) (D.detVec α) = D.chi α (-1) := by
  have hmul : (D.psModel α α ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (D.detVec α) =
      D.chi α (-1) • D.detVec α := by
    ext y
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    cases y with
    | none =>
      rw [Finset.sum_eq_single (some (0 : D.Fq))]
      · simp only [psModel_wGL_apply, ↓reduceDIte, ↓reduceIte, one_mul, FieldData.detVec]
        rw [← mul_assoc, mul_comm (D.chi α (-1)) (isqrt (D.q + 1)), mul_assoc,
          chi_neg_one_sq, mul_one]
      · intro x _ hx
        cases x with
        | none => simp [psModel_wGL_apply]
        | some x' =>
          have hx' : x' ≠ 0 := fun h0 => hx (congrArg some h0)
          simp [psModel_wGL_apply, hx']
      · intro hm; exact (hm (Finset.mem_univ _)).elim
    | some y' =>
      by_cases hy0 : y' = 0
      · subst hy0
        rw [Finset.sum_eq_single none]
        · simp [psModel_wGL_apply, FieldData.detVec, mul_comm]
        · intro x _ hx
          cases x with
          | none => exact absurd rfl hx
          | some x' =>
            by_cases hx' : x' = 0
            · simp [psModel_wGL_apply, hx']
            · have hne : (some (0 : D.Fq) : Option D.Fq) ≠ some x'⁻¹ :=
                fun h => hx' (inv_eq_zero.mp (Option.some.inj h).symm)
              simp [psModel_wGL_apply, hx', hne]
        · intro hm; exact (hm (Finset.mem_univ _)).elim
      · rw [Finset.sum_eq_single (some y'⁻¹)]
        · have hne0 : y'⁻¹ ≠ 0 := inv_ne_zero hy0
          simp only [psModel_wGL_apply, dif_neg hne0, inv_inv, ite_true, sub_self,
            chi_zero_label D hne0, mul_one, FieldData.detVec]
        · intro x _ hx
          cases x with
          | none => simp [psModel_wGL_apply, hy0]
          | some x' =>
            by_cases hx' : x' = 0
            · simp [psModel_wGL_apply, hx']
            · have hne : (some y' : Option D.Fq) ≠ some x'⁻¹ := by
                intro heq
                apply hx
                have h1 : y' = x'⁻¹ := Option.some.inj heq
                rw [h1, inv_inv]
              simp [psModel_wGL_apply, hx', hne]
        · intro hm; exact (hm (Finset.mem_univ _)).elim
  rw [matEntry_eq_sum_mulVec, hmul]
  have hpull : (∑ x : Option D.Fq, conj (D.detVec α x) * (D.chi α (-1) • D.detVec α) x) =
      D.chi α (-1) * dotProduct (star (D.detVec α)) (D.detVec α) := by
    rw [dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul, Pi.star_apply, Complex.star_def]; ring
  rw [hpull, dot_conj_detVec_detVec, mul_one]

lemma matEntry_psModel_wGL_stVec_none (D : FieldData) (α : D.Lab) :
    matEntry (D.psModel α α ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.stVec α none) (D.stVec α none) = -((D.q : ℂ)⁻¹) * D.chi α (-1) := by
  let M := D.psModel α α ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)
  let v := D.stVec α none
  have hMv_none : M.mulVec v none = isqrt (D.q + 1) * (-isqrt D.q) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (some (0 : D.Fq))]
    · simp [M, v, psModel_wGL_apply, FieldData.stVec]
    · intro x _ hx
      cases x with
      | none => simp [M, psModel_wGL_apply]
      | some x' =>
        have hx' : x' ≠ 0 := fun h0 => hx (congrArg some h0)
        simp [M, psModel_wGL_apply, hx']
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  have hMv_zero : M.mulVec v (some 0) = isqrt (D.q + 1) * ((Real.sqrt D.q : ℂ) * D.chi α (-1)) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single none]
    · simp [M, v, psModel_wGL_apply, FieldData.stVec]
    · intro x _ hx
      cases x with
      | none => exact absurd rfl hx
      | some x' =>
        by_cases hx' : x' = 0
        · simp [M, psModel_wGL_apply, hx']
        · have hne : (some (0 : D.Fq) : Option D.Fq) ≠ some x'⁻¹ :=
            fun h => hx' (inv_eq_zero.mp (Option.some.inj h).symm)
          simp [M, psModel_wGL_apply, hx', hne]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  have hMv_nz : ∀ y' : D.Fq, y' ≠ 0 →
      M.mulVec v (some y') = D.chi α (-1) * (isqrt (D.q + 1) * (-isqrt D.q)) := by
    intro y' hy0
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (some y'⁻¹)]
    · have hne0 : y'⁻¹ ≠ 0 := inv_ne_zero hy0
      simp [M, v, psModel_wGL_apply, FieldData.stVec, hne0, chi_zero_label D hne0]
    · intro x _ hx
      cases x with
      | none => simp [M, psModel_wGL_apply, hy0]
      | some x' =>
        by_cases hx' : x' = 0
        · simp [M, psModel_wGL_apply, hx']
        · have hne : (some y' : Option D.Fq) ≠ some x'⁻¹ := by
            intro heq
            apply hx
            have h1 : y' = x'⁻¹ := Option.some.inj heq
            rw [h1, inv_inv]
          simp [M, psModel_wGL_apply, hx', hne]
    · intro hm; exact (hm (Finset.mem_univ _)).elim
  have hisqrt1 : conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = ((D.q : ℂ) + 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (by linarith [q_pos D] : (0 : ℝ) < D.q + 1)
    simpa [Complex.ofReal_add, Complex.ofReal_one] using h
  have hisqrtq : conj (isqrt D.q) * isqrt D.q = (D.q : ℂ)⁻¹ := by
    simpa [Complex.ofReal_natCast] using conj_isqrt_mul_isqrt (q_pos D)
  have hsqrt_inv : (Real.sqrt D.q : ℂ) * isqrt D.q = 1 := by
    simp only [FieldData.isqrt, ← Complex.ofReal_mul,
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (q_pos D)), Complex.ofReal_one]
  have hconj_sqrt_inv : conj (Real.sqrt D.q : ℂ) * isqrt D.q = 1 := by
    rw [Complex.conj_ofReal, hsqrt_inv]
  have ht_none : conj (v none) * M.mulVec v none = -(((D.q : ℂ) + 1)⁻¹) * D.chi α (-1) := by
    rw [hMv_none]
    simp only [v, FieldData.stVec, map_mul, conj_chi_neg_one]
    calc conj (isqrt (D.q + 1)) * (conj (Real.sqrt D.q : ℂ) * D.chi α (-1)) *
          (isqrt (D.q + 1) * -isqrt D.q)
        = -((conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
            (conj (Real.sqrt D.q : ℂ) * isqrt D.q) * D.chi α (-1)) := by ring
      _ = -(((D.q : ℂ) + 1)⁻¹ * 1 * D.chi α (-1)) := by rw [hisqrt1, hconj_sqrt_inv]
      _ = -(((D.q : ℂ) + 1)⁻¹) * D.chi α (-1) := by ring
  have ht_zero : conj (v (some 0)) * M.mulVec v (some 0) = -(((D.q : ℂ) + 1)⁻¹) * D.chi α (-1) := by
    rw [hMv_zero]
    simp only [v, FieldData.stVec, map_mul, map_neg]
    have hsqrt_inv' : conj (isqrt D.q) * (Real.sqrt D.q : ℂ) = 1 := by
      rw [conj_isqrt, mul_comm, hsqrt_inv]
    calc conj (isqrt (D.q + 1)) * -conj (isqrt D.q) *
          (isqrt (D.q + 1) * ((Real.sqrt D.q : ℂ) * D.chi α (-1)))
        = -((conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
            (conj (isqrt D.q) * (Real.sqrt D.q : ℂ)) * D.chi α (-1)) := by
          ring
      _ = -(((D.q : ℂ) + 1)⁻¹ * 1 * D.chi α (-1)) := by rw [hisqrt1, hsqrt_inv']
      _ = -(((D.q : ℂ) + 1)⁻¹) * D.chi α (-1) := by ring
  have ht_nz : ∀ y' : D.Fq, y' ≠ 0 →
      conj (v (some y')) * M.mulVec v (some y') = ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α (-1) := by
    intro y' hy0
    rw [hMv_nz y' hy0]
    simp only [v, FieldData.stVec, map_mul, map_neg]
    calc conj (isqrt (D.q + 1)) * -conj (isqrt D.q) *
          (D.chi α (-1) * (isqrt (D.q + 1) * -isqrt D.q))
        = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) * (conj (isqrt D.q) * isqrt D.q) * D.chi α (-1) := by
          ring
      _ = ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α (-1) := by rw [hisqrt1, hisqrtq]
  rw [matEntry_eq_sum_mulVec, Fintype.sum_option]
  change conj (v none) * M.mulVec v none + ∑ y' : D.Fq, conj (v (some y')) * M.mulVec v (some y') = _
  rw [ht_none, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : D.Fq)), ht_zero]
  have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun y' : D.Fq => y' ≠ 0) := by
    ext y; simp
  have hsum_nz : (∑ y' ∈ Finset.univ.erase (0 : D.Fq), conj (v (some y')) * M.mulVec v (some y')) =
      ((D.q : ℂ) - 1) * (((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α (-1)) := by
    have hcongr : (∑ y' ∈ Finset.univ.erase (0 : D.Fq), conj (v (some y')) * M.mulVec v (some y')) =
        ∑ _y' ∈ Finset.univ.erase (0 : D.Fq), ((D.q : ℂ) + 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α (-1) := by
      refine Finset.sum_congr rfl fun y' hy' => ht_nz y' (Finset.mem_erase.mp hy').1
    rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      card_Fq, nsmul_eq_mul]
    have hq : 1 ≤ D.q := D.one_lt_q.le
    rw [Nat.cast_sub hq, Nat.cast_one]
  rw [hsum_nz]
  have hq0 : (D.q : ℂ) ≠ 0 := q_complex_ne D
  have hqp1 : (D.q : ℂ) + 1 ≠ 0 := q_add_one_complex_ne D
  field_simp [hq0, hqp1]
  ring

lemma matEntry_psModel_wGL_vT (D : FieldData) (α₁ α₂ : D.Lab) (s t : D.Fq) :
    matEntry (D.psModel α₁ α₂ ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)) (D.vT s) (D.vT t) =
      (D.q : ℂ)⁻¹ * D.chi α₂ (-1) *
        ∑ x : D.Fqˣ, D.chi (α₁ - α₂) (x : D.Fq) * D.psi (s * (x : D.Fq)⁻¹ - t * (x : D.Fq)) := by
  rw [matEntry, Fintype.sum_option]
  have hnone : (∑ x : Option D.Fq,
      conj (D.vT s none) * D.psModel α₁ α₂ ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) none x *
      D.vT t x) = 0 := by
    simp [FieldData.vT]
  rw [hnone, zero_add]
  have hcol : ∀ y' : D.Fq,
      (∑ x : Option D.Fq,
        conj (D.vT s (some y')) * D.psModel α₁ α₂ ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) (some y') x *
        D.vT t x) =
      if y' = 0 then 0
      else (D.q : ℂ)⁻¹ * D.chi α₂ (-1) * D.chi (α₁ - α₂) y'⁻¹ * D.psi (s * y' - t * y'⁻¹) := by
    intro y'
    rw [Fintype.sum_option]
    have hxnone : conj (D.vT s (some y')) *
        D.psModel α₁ α₂ ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) (some y') none * D.vT t none = 0 := by
      simp [FieldData.vT]
    rw [hxnone, zero_add]
    by_cases hy0 : y' = 0
    · subst hy0
      rw [if_pos rfl, Finset.sum_eq_zero]
      intro x' _
      rw [psModel_wGL_apply]
      dsimp only
      by_cases hx0 : x' = 0
      · simp [hx0]
      · simp [hx0, eq_comm]
    · rw [if_neg hy0, Finset.sum_eq_single y'⁻¹]
      · have hne0 : y'⁻¹ ≠ 0 := inv_ne_zero hy0
        simp only [psModel_wGL_apply, dif_neg hne0, inv_inv, FieldData.vT]
        rw [map_mul, starRingEnd_self_apply, conj_psi]
        have hisq : conj (isqrt D.q) * isqrt D.q = (D.q : ℂ)⁻¹ := by
          simpa [Complex.ofReal_natCast] using conj_isqrt_mul_isqrt (q_pos D)
        calc conj (isqrt D.q) * D.psi (s * y') * (D.chi α₂ (-1) * D.chi (α₁ - α₂) y'⁻¹) *
              (isqrt D.q * D.psi (-(t * y'⁻¹)))
            = (conj (isqrt D.q) * isqrt D.q) * D.chi α₂ (-1) * D.chi (α₁ - α₂) y'⁻¹ *
                (D.psi (s * y') * D.psi (-(t * y'⁻¹))) := by ring
          _ = (D.q : ℂ)⁻¹ * D.chi α₂ (-1) * D.chi (α₁ - α₂) y'⁻¹ *
                D.psi (s * y' - t * y'⁻¹) := by
              rw [hisq, ← psi_add, ← sub_eq_add_neg]
      · intro x' _ hx'
        rw [psModel_wGL_apply]
        dsimp only
        by_cases hx0 : x' = 0
        · simp [hx0]
        · have hne : (some y' : Option D.Fq) ≠ some x'⁻¹ := by
            intro heq
            apply hx'
            have h1 : y' = x'⁻¹ := Option.some.inj heq
            rw [h1, inv_inv]
          simp [hx0, hne]
      · intro hm; exact (hm (Finset.mem_univ y'⁻¹)).elim
  simp_rw [hcol]
  have hfilt : (∑ y' : D.Fq, if y' = 0 then (0 : ℂ)
        else (D.q : ℂ)⁻¹ * D.chi α₂ (-1) * D.chi (α₁ - α₂) y'⁻¹ * D.psi (s * y' - t * y'⁻¹)) =
      ∑ y' ∈ Finset.univ.filter (fun y' : D.Fq => y' ≠ 0),
        (D.q : ℂ)⁻¹ * D.chi α₂ (-1) * D.chi (α₁ - α₂) y'⁻¹ * D.psi (s * y' - t * y'⁻¹) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun y' _ => ?_
    by_cases hy0 : y' = 0 <;> simp [hy0]
  rw [hfilt, sum_ne_zero_eq_sum_units, Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.inv D.Fqˣ) _ _ fun x => ?_).symm
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  ring

lemma matEntry_psModel_wGL_wVec (D : FieldData) (α₁ α₂ ε η : D.Lab) (hsum : ε + η = α₁ + α₂) :
    matEntry (D.psModel α₁ α₂ ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.wVec α₂ ε) (D.wVec α₂ η) =
      (D.q : ℂ)⁻¹ * D.chi η (-1) * D.gauss (α₂ - ε) * D.gauss (η - α₂) := by
  rw [wVec_eq_smul_sum, wVec_eq_smul_sum, matEntry_smul_left, matEntry_smul_right,
    matEntry_sum_left]
  simp_rw [matEntry_sum_right, matEntry_smul_left, matEntry_smul_right,
    matEntry_psModel_wGL_vT D α₁ α₂]
  have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (q_sub_one_pos D)
    simpa [Complex.ofReal_sub, Complex.ofReal_one] using h
  have hL : conj (isqrt (D.q - 1)) * (isqrt (D.q - 1) *
      ∑ s : D.Fqˣ, ∑ t : D.Fqˣ,
        conj (D.chi ε (s : D.Fq) * D.chi (-α₂) (s : D.Fq)) *
          ((D.chi η (t : D.Fq) * D.chi (-α₂) (t : D.Fq)) *
            ((D.q : ℂ)⁻¹ * D.chi α₂ (-1) *
              ∑ x : D.Fqˣ, D.chi (α₁ - α₂) (x : D.Fq) *
                D.psi ((s : D.Fq) * (x : D.Fq)⁻¹ - (t : D.Fq) * (x : D.Fq))))) =
      ((D.q : ℂ) - 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α₂ (-1) *
        ∑ p : D.Fqˣ × D.Fqˣ × D.Fqˣ,
          D.chi (α₂ - ε) (p.1 : D.Fq) * D.chi (η - α₂) (p.2.1 : D.Fq) *
            D.chi (α₁ - α₂) (p.2.2 : D.Fq) *
            D.psi ((p.1 : D.Fq) * (p.2.2 : D.Fq)⁻¹ - (p.2.1 : D.Fq) * (p.2.2 : D.Fq)) := by
    rw [← mul_assoc, hisqrt]
    have hpull : (∑ s : D.Fqˣ, ∑ t : D.Fqˣ,
        conj (D.chi ε (s : D.Fq) * D.chi (-α₂) (s : D.Fq)) *
          ((D.chi η (t : D.Fq) * D.chi (-α₂) (t : D.Fq)) *
            ((D.q : ℂ)⁻¹ * D.chi α₂ (-1) *
              ∑ x : D.Fqˣ, D.chi (α₁ - α₂) (x : D.Fq) *
                D.psi ((s : D.Fq) * (x : D.Fq)⁻¹ - (t : D.Fq) * (x : D.Fq))))) =
        (D.q : ℂ)⁻¹ * D.chi α₂ (-1) *
          ∑ p : D.Fqˣ × D.Fqˣ × D.Fqˣ,
            D.chi (α₂ - ε) (p.1 : D.Fq) * D.chi (η - α₂) (p.2.1 : D.Fq) *
              D.chi (α₁ - α₂) (p.2.2 : D.Fq) *
              D.psi ((p.1 : D.Fq) * (p.2.2 : D.Fq)⁻¹ - (p.2.1 : D.Fq) * (p.2.2 : D.Fq)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, conj_chi, conj_chi, neg_neg, ← chi_add_label, ← chi_add_label,
        show -ε + α₂ = α₂ - ε by ring, show η + -α₂ = η - α₂ by ring]
      ring
    rw [hpull]
    ring
  rw [hL]
  let m1 : D.Fqˣ := Units.mk0 (-1 : D.Fq) (neg_ne_zero.mpr one_ne_zero)
  have hm1_sq : m1 * m1 = 1 := by ext; simp [m1]
  let e : D.Fqˣ × D.Fqˣ × D.Fqˣ ≃ D.Fqˣ × D.Fqˣ × D.Fqˣ :=
    { toFun := fun ⟨u, v, x⟩ => (u * x, m1 * v * x⁻¹, x)
      invFun := fun ⟨s, t, x⟩ => (s * x⁻¹, m1 * t * x, x)
      left_inv := fun ⟨u, v, x⟩ => by
        refine Prod.ext (by simp) (Prod.ext ?_ rfl)
        calc m1 * (m1 * v * x⁻¹) * x
            = (m1 * m1) * v * (x⁻¹ * x) := by group
          _ = v := by rw [hm1_sq, inv_mul_cancel, one_mul, mul_one]
      right_inv := fun ⟨s, t, x⟩ => by
        refine Prod.ext (by simp) (Prod.ext ?_ rfl)
        calc m1 * (m1 * t * x) * x⁻¹
            = (m1 * m1) * t * (x * x⁻¹) := by group
          _ = t := by rw [hm1_sq, mul_inv_cancel, one_mul, mul_one] }
  let f1 : D.Fqˣ × D.Fqˣ × D.Fqˣ → ℂ := fun p =>
    D.chi (α₂ - ε) (p.1 : D.Fq) * D.chi (η - α₂) (p.2.1 : D.Fq) *
      D.chi (α₁ - α₂) (p.2.2 : D.Fq) *
      D.psi ((p.1 : D.Fq) * (p.2.2 : D.Fq)⁻¹ - (p.2.1 : D.Fq) * (p.2.2 : D.Fq))
  let f2 : D.Fqˣ × D.Fqˣ × D.Fqˣ → ℂ := fun q =>
    D.chi (η - α₂) (-1) * (D.chi (α₂ - ε) (q.1 : D.Fq) * D.psi (q.1 : D.Fq)) *
      (D.chi (η - α₂) (q.2.1 : D.Fq) * D.psi (q.2.1 : D.Fq))
  have hbij : (∑ q : D.Fqˣ × D.Fqˣ × D.Fqˣ, f2 q) = ∑ p : D.Fqˣ × D.Fqˣ × D.Fqˣ, f1 p := by
    refine Fintype.sum_equiv e f2 f1 fun ⟨u, v, x⟩ => ?_
    simp only [e, f1, f2, Equiv.coe_fn_mk, Units.val_mul, Units.val_inv_eq_inv_val]
    have hm1_val : (m1 : D.Fq) = -1 := rfl
    have hpsi_arg : (u : D.Fq) * (x : D.Fq) * (x : D.Fq)⁻¹ -
        (m1 : D.Fq) * (v : D.Fq) * (x : D.Fq)⁻¹ * (x : D.Fq) = (u : D.Fq) + (v : D.Fq) := by
      rw [hm1_val]
      have hx : (x : D.Fq) ≠ 0 := x.ne_zero
      field_simp [hx]
      ring
    rw [hpsi_arg, psi_add, chi_mul D (α₂ - ε) u.ne_zero x.ne_zero]
    have hchi_v : D.chi (η - α₂) ((m1 : D.Fq) * (v : D.Fq) * (x : D.Fq)⁻¹) =
        D.chi (η - α₂) (-1) * D.chi (η - α₂) (v : D.Fq) * D.chi (α₂ - η) (x : D.Fq) := by
      rw [← Units.val_mul m1 v, chi_mul D (η - α₂) (m1 * v).ne_zero (inv_ne_zero x.ne_zero),
        Units.val_mul, chi_mul D (η - α₂) m1.ne_zero v.ne_zero, hm1_val,
        chi_inv D (η - α₂) x.ne_zero, show -(η - α₂) = α₂ - η by ring]
    rw [hchi_v]
    have hx_tot : D.chi (α₂ - ε) (x : D.Fq) * D.chi (α₂ - η) (x : D.Fq) *
        D.chi (α₁ - α₂) (x : D.Fq) = 1 := by
      rw [← chi_add_label, ← chi_add_label]
      have hexp : α₂ - ε + (α₂ - η) + (α₁ - α₂) = 0 := by
        calc α₂ - ε + (α₂ - η) + (α₁ - α₂)
            = (α₁ + α₂) - (ε + η) := by ring
          _ = 0 := by rw [hsum, sub_self]
      rw [hexp, chi_zero_label D x.ne_zero]
    calc D.chi (η - α₂) (-1) * (D.chi (α₂ - ε) (u : D.Fq) * D.psi (u : D.Fq)) *
          (D.chi (η - α₂) (v : D.Fq) * D.psi (v : D.Fq))
        = 1 * (D.chi (η - α₂) (-1) * (D.chi (α₂ - ε) (u : D.Fq) * D.psi (u : D.Fq)) *
            (D.chi (η - α₂) (v : D.Fq) * D.psi (v : D.Fq))) := (one_mul _).symm
      _ = (D.chi (α₂ - ε) (x : D.Fq) * D.chi (α₂ - η) (x : D.Fq) * D.chi (α₁ - α₂) (x : D.Fq)) *
            (D.chi (η - α₂) (-1) * (D.chi (α₂ - ε) (u : D.Fq) * D.psi (u : D.Fq)) *
              (D.chi (η - α₂) (v : D.Fq) * D.psi (v : D.Fq))) := by rw [hx_tot]
      _ = D.chi (α₂ - ε) (u : D.Fq) * D.chi (α₂ - ε) (x : D.Fq) *
            (D.chi (η - α₂) (-1) * D.chi (η - α₂) (v : D.Fq) * D.chi (α₂ - η) (x : D.Fq)) *
            D.chi (α₁ - α₂) (x : D.Fq) * (D.psi (u : D.Fq) * D.psi (v : D.Fq)) := by ring
  have hsum_eq : (∑ p : D.Fqˣ × D.Fqˣ × D.Fqˣ, f1 p) =
      ((D.q - 1 : ℕ) : ℂ) * D.chi (η - α₂) (-1) * D.gauss (α₂ - ε) * D.gauss (η - α₂) := by
    rw [← hbij]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ u : D.Fqˣ,
        (∑ q : D.Fqˣ × D.Fqˣ, f2 (u, q)) =
          ((D.q - 1 : ℕ) : ℂ) * D.chi (η - α₂) (-1) *
            (D.chi (α₂ - ε) (u : D.Fq) * D.psi (u : D.Fq)) * D.gauss (η - α₂) := by
      intro u
      rw [Fintype.sum_prod_type]
      simp only [f2, Finset.sum_const, Finset.card_univ, card_Fq_units, nsmul_eq_mul,
        ← Finset.mul_sum, gauss_eq_sum_units]
      ring
    simp_rw [hinner]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← gauss_eq_sum_units]
  change ((D.q : ℂ) - 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α₂ (-1) * (∑ p, f1 p) = _
  rw [hsum_eq]
  have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
    have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hchi_neg1 : D.chi α₂ (-1) * D.chi (η - α₂) (-1) = D.chi η (-1) := by
    rw [← chi_add_label, show α₂ + (η - α₂) = η by ring]
  rw [hcard]
  calc ((D.q : ℂ) - 1)⁻¹ * (D.q : ℂ)⁻¹ * D.chi α₂ (-1) *
        (((D.q : ℂ) - 1) * D.chi (η - α₂) (-1) * D.gauss (α₂ - ε) * D.gauss (η - α₂))
      = (((D.q : ℂ) - 1)⁻¹ * ((D.q : ℂ) - 1)) * (D.q : ℂ)⁻¹ *
          (D.chi α₂ (-1) * D.chi (η - α₂) (-1)) * D.gauss (α₂ - ε) * D.gauss (η - α₂) := by ring
    _ = (D.q : ℂ)⁻¹ * D.chi η (-1) * D.gauss (α₂ - ε) * D.gauss (η - α₂) := by
        rw [inv_mul_cancel₀ (q_sub_one_complex_ne D), one_mul, hchi_neg1]

lemma piModel_wGL (D : FieldData) (k : D.Lab2) :
    D.piModel k ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) =
      D.wprimeModel k * D.borelModel (D.restrLab k) (-1) 0 1 := by
  have hw00 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 = 0 := rfl
  have hw01 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 1 := rfl
  have hw10 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 1 := rfl
  have hw11 : ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = 0 := rfl
  simp only [FieldData.piModel, hw00, hw01, hw10, hw11, one_ne_zero, ↓reduceIte,
    neg_zero, mul_zero, one_mul, zero_sub, neg_neg, div_one]
  rw [borelModel_one, Matrix.one_mul]

lemma borelModel_neg_one_mulVec_multVec (D : FieldData) (γ η : D.Lab) :
    (D.borelModel γ (-1) 0 1).mulVec (D.multVec η) = D.chi η (-1) • D.multVec η := by
  ext y
  have hdiv : (1 : D.Fq) / (-1 : D.Fq) = -1 := by norm_num
  simp only [Matrix.mulVec, dotProduct, FieldData.borelModel, FieldData.multVec,
    Pi.smul_apply, smul_eq_mul, hdiv, zero_div, zero_mul, psi_zero, mul_one, chi_one]
  rw [Finset.sum_eq_single (-y)]
  · have hcond : (y : D.Fq) = -1 * ((-y : D.Fqˣ) : D.Fq) := by simp
    rw [if_pos hcond]
    have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    rw [Units.val_neg, show -(y : D.Fq) = (-1) * (y : D.Fq) by ring, chi_mul D η hm1 y.ne_zero]
    ring
  · intro x _ hx
    have hne : (y : D.Fq) ≠ -1 * (x : D.Fq) := by
      intro heq
      apply hx
      ext
      simp [heq]
    rw [if_neg hne, zero_mul]
  · intro hm; exact (hm (Finset.mem_univ (-y))).elim

lemma matEntry_wprimeModel_multVec (D : FieldData) (k : D.Lab2) (ε η : D.Lab)
    (hsum : ε + η = D.restrLab k) :
    matEntry (D.wprimeModel k) (D.multVec ε) (D.multVec η) =
      -((D.q : ℂ)⁻¹) * D.gaussQ2 (fun z => D.theta k z * D.chi (-ε) (D.nrm z)) := by
  let γ := D.restrLab k
  have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℂ) - 1)⁻¹ := by
    have h := conj_isqrt_mul_isqrt (q_sub_one_pos D)
    simpa [Complex.ofReal_sub, Complex.ofReal_one] using h
  have hmat : matEntry (D.wprimeModel k) (D.multVec ε) (D.multVec η) =
      ((D.q : ℂ) - 1)⁻¹ * ∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
        D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
          D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi η (x : D.Fq) := by
    simp only [matEntry, FieldData.multVec, FieldData.wprimeModel, map_mul, conj_chi]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    calc conj (isqrt (D.q - 1)) * D.chi (-ε) (y : D.Fq) *
          (D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq))) *
          (isqrt (D.q - 1) * D.chi η (x : D.Fq))
        = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) *
            (D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
              D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi η (x : D.Fq)) := by ring
      _ = ((D.q : ℂ) - 1)⁻¹ * _ := by rw [hisqrt]
  rw [hmat]
  have hreidx : (∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
        D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
          D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi η (x : D.Fq)) =
      (∑ u : D.Fqˣ, D.chi (-ε) (u : D.Fq) * D.besselJ k (u : D.Fq)) *
        (∑ x : D.Fqˣ, D.chi (ε + η - γ) (x : D.Fq)) := by
    let f1 : D.Fqˣ × D.Fqˣ → ℂ := fun p =>
      D.chi (-ε) (p.1 : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (p.2 : D.Fq)⁻¹) *
        D.besselJ k ((p.1 : D.Fq) * (p.2 : D.Fq)) * D.chi η (p.2 : D.Fq)
    let f2 : D.Fqˣ × D.Fqˣ → ℂ := fun q =>
      (D.chi (-ε) (q.1 : D.Fq) * D.besselJ k (q.1 : D.Fq)) * D.chi (ε + η - γ) (q.2 : D.Fq)
    have h1 : (∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
          D.chi (-ε) (y : D.Fq) * D.theta k (algebraMap D.Fq D.Fq2 (x : D.Fq)⁻¹) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq)) * D.chi η (x : D.Fq)) =
        ∑ p : D.Fqˣ × D.Fqˣ, f1 p := (Fintype.sum_prod_type f1).symm
    have h2 : (∑ u : D.Fqˣ, D.chi (-ε) (u : D.Fq) * D.besselJ k (u : D.Fq)) *
          (∑ x : D.Fqˣ, D.chi (ε + η - γ) (x : D.Fq)) =
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
    have hlab_x : D.chi (-ε) (x : D.Fq) * D.chi (ε + η - γ) (x : D.Fq) =
        D.chi (-γ) (x : D.Fq) * D.chi η (x : D.Fq) := by
      rw [← chi_add_label, ← chi_add_label]
      congr 1; ring
    rw [hθx, hmul_ε]
    calc D.chi (-ε) (y : D.Fq) * D.chi (-γ) (x : D.Fq) * D.besselJ k ((y : D.Fq) * (x : D.Fq)) *
          D.chi η (x : D.Fq)
        = D.chi (-ε) (y : D.Fq) * (D.chi (-γ) (x : D.Fq) * D.chi η (x : D.Fq)) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq)) := by ring
      _ = D.chi (-ε) (y : D.Fq) * (D.chi (-ε) (x : D.Fq) * D.chi (ε + η - γ) (x : D.Fq)) *
            D.besselJ k ((y : D.Fq) * (x : D.Fq)) := by rw [hlab_x]
      _ = (D.chi (-ε) (y : D.Fq) * D.chi (-ε) (x : D.Fq) *
            D.besselJ k (((y * x : D.Fqˣ) : D.Fq))) * D.chi (ε + η - γ) (x : D.Fq) := by
          push_cast; ring
  have hzero : ε + η - γ = 0 := sub_eq_zero.mpr hsum
  rw [hreidx, sum_chi_units, if_pos hzero]
  have hcard : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
    have := D.one_lt_q; rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hcard, mul_comm _ ((D.q : ℂ) - 1), ← mul_assoc,
    inv_mul_cancel₀ (q_sub_one_complex_ne D), one_mul]
  simp only [FieldData.besselJ]
  have hpull : (∑ u : D.Fqˣ, D.chi (-ε) (u : D.Fq) *
        (-((D.q : ℂ)⁻¹) * ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (u : D.Fq)),
          D.psi (D.tr v) * D.theta k v)) =
      -((D.q : ℂ)⁻¹) * ∑ u : D.Fqˣ,
        ∑ v ∈ Finset.univ.filter (fun v : D.Fq2 => v ≠ 0 ∧ D.nrm v = (u : D.Fq)),
          D.theta k v * D.chi (-ε) (D.nrm v) * D.psi (D.tr v) := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v hv => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [hv.2]
    ring
  rw [hpull]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  unfold FieldData.gaussQ2
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v = 0
  · simp [hv]
  · have hnrm_ne : D.nrm v ≠ 0 := mt (nrm_eq_zero D v).mp hv
    let u₀ : D.Fqˣ := Units.mk0 (D.nrm v) hnrm_ne
    rw [Finset.sum_eq_single u₀]
    · simp [hv, u₀]
    · intro u _ hu
      have hne : D.nrm v ≠ (u : D.Fq) := fun heq => hu (Units.ext heq.symm)
      simp [hv, hne]
    · intro hmem; exact (hmem (Finset.mem_univ u₀)).elim

lemma matEntry_piModel_wGL_multVec (D : FieldData) (k : D.Lab2) (ε η : D.Lab)
    (hsum : ε + η = D.restrLab k) :
    matEntry (D.piModel k ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
        (D.multVec ε) (D.multVec η) =
      -(D.chi η (-1) * (D.q : ℂ)⁻¹) * D.gaussQ2 (fun z => D.theta k z * D.chi (-ε) (D.nrm z)) := by
  rw [piModel_wGL, matEntry_eq_sum_mulVec, ← Matrix.mulVec_mulVec,
    borelModel_neg_one_mulVec_multVec, Matrix.mulVec_smul]
  have hpull : (∑ x : D.Fqˣ, conj (D.multVec ε x) *
        (D.chi η (-1) • (D.wprimeModel k).mulVec (D.multVec η)) x) =
      D.chi η (-1) * matEntry (D.wprimeModel k) (D.multVec ε) (D.multVec η) := by
    rw [matEntry_eq_sum_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hpull, matEntry_wprimeModel_multVec D k ε η hsum]
  ring

/-! ### Section 4: `q = 2` cuspidal Gauss sum evaluation -/

lemma q_eq_two_p_eq_two (D : FieldData) (hq2 : D.q = 2) : D.p = 2 := by
  have hpr : D.p ^ D.r = 2 := hq2
  have hp2 : 2 ≤ D.p := D.hp.two_le
  have hr1 : 1 ≤ D.r := D.hr
  have hle : D.p ≤ D.p ^ D.r := Nat.le_self_pow (by omega) D.p
  omega

lemma gaussQ2_q_eq_two (D : FieldData) (hq2 : D.q = 2)
    (k : {k : D.Lab2 // D.IsCuspLabel k}) :
    D.gaussQ2 (D.theta k.1) = 2 := by
  have hp2 : D.p = 2 := q_eq_two_p_eq_two D hq2
  have hcharFq : CharP D.Fq 2 := by
    have hcp := charP_of_injective_algebraMap (algebraMap (ZMod D.p) D.Fq).injective D.p
    exact Eq.mp (congrArg (fun n => CharP D.Fq n) hp2) hcp
  have hcharFq2 : CharP D.Fq2 2 := by
    have := charP_of_injective_algebraMap (algebraMap D.Fq D.Fq2).injective 2
    exact this
  have htwo_fq2 : (2 : D.Fq2) = 0 := CharP.cast_eq_zero D.Fq2 2
  have hfq_elem : ∀ x : D.Fq, x = 0 ∨ x = 1 := by
    intro x
    have hx2 : x ^ 2 = x := by
      have h := FiniteField.pow_card x
      rw [card_Fq, hq2] at h
      exact h
    have hmul : x * (x - 1) = 0 := by linear_combination hx2
    rcases mul_eq_zero.mp hmul with rfl | hsub
    · exact Or.inl rfl
    · exact Or.inr (sub_eq_zero.mp hsub)
  have hpsi1 : D.psi 1 = -1 := by
    have htot := sum_psi D 1
    simp only [one_mul, one_ne_zero, ↓reduceIte] at htot
    have huniv : (Finset.univ : Finset D.Fq) = {0, 1} := by
      ext x
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hfq_elem x
    rw [huniv, Finset.sum_pair zero_ne_one, psi_zero] at htot
    exact eq_neg_of_add_eq_zero_right htot
  have htr1 : D.tr (1 : D.Fq2) = 0 := by
    apply (algebraMap D.Fq D.Fq2).injective
    rw [map_zero, algebraMap_tr, hq2, one_pow]
    simpa [one_add_one_eq_two] using htwo_fq2
  have htr_nz : ∀ z : D.Fq2, z ≠ 0 → z ≠ 1 → D.tr z = 1 := by
    intro z hz0 hz1
    rcases hfq_elem (D.tr z) with h0 | h1
    · exfalso
      have halg : z + z ^ 2 = 0 := by
        have h := algebraMap_tr D z
        rw [h0, map_zero, hq2] at h
        exact h.symm
      have hmul : z * (z - 1) = 0 := by
        calc z * (z - 1) = (z + z ^ 2) - 2 * z := by ring
          _ = 0 - 0 * z := by rw [halg, htwo_fq2]
          _ = 0 := by ring
      rcases mul_eq_zero.mp hmul with h | h
      · exact hz0 h
      · exact hz1 (sub_eq_zero.mp h)
    · exact h1
  have hk_ne : k.1 ≠ 0 := by
    intro h0
    apply k.2.1
    rw [h0, ZMod.val_zero]
    exact dvd_zero _
  have hsum_theta := sum_theta_ne_zero D hk_ne
  let S := Finset.univ.filter (fun z : D.Fq2 => z ≠ 0)
  have h1S : (1 : D.Fq2) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_ne_zero⟩
  have hsum_erase : ∑ z ∈ S.erase (1 : D.Fq2), D.theta k.1 z = -1 := by
    have hsp := Finset.add_sum_erase S (D.theta k.1) h1S
    rw [hsum_theta, theta_one] at hsp
    exact eq_neg_of_add_eq_zero_right hsp
  unfold FieldData.gaussQ2
  rw [← Finset.add_sum_erase S (fun z => D.theta k.1 z * D.psi (D.tr z)) h1S]
  rw [theta_one, htr1, psi_zero, one_mul]
  have hcongr : (∑ z ∈ S.erase (1 : D.Fq2), D.theta k.1 z * D.psi (D.tr z)) =
      ∑ z ∈ S.erase (1 : D.Fq2), D.theta k.1 z * (-1) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz_ne1 : z ≠ 1 := (Finset.mem_erase.mp hz).1
    have hz_ne0 : z ≠ 0 := (Finset.mem_filter.mp (Finset.mem_erase.mp hz).2).2
    rw [htr_nz z hz_ne0 hz_ne1, hpsi1]
  rw [hcongr, ← Finset.sum_mul, hsum_erase]
  norm_num

end GL2QFT.A70SmallBlocksAux

open GL2QFT GL2QFT.FieldData GL2QFT.Supplement GL2QFT.Supplement.TotalA QAlgorithms QAlgorithms.Complexity
open GL2QFT.A70SmallBlocksAux
open scoped ComplexConjugate

theorem solution (D : FieldData) :
    (∀ (α β : D.Lab) (hlt : α.val < β.val),
      A70 D (.inl (α, β)) (.inl (α, β)) (.inl (α, β)) false (.inr (.inr (.inl ⟨(α, β), hlt⟩))) = 1 ∧
      A70 D (.inl (α, β)) (.inl (β, α)) (.inl (β, α)) true (.inr (.inr (.inl ⟨(α, β), hlt⟩))) = 1) ∧
    (∀ (α : D.Lab),
      A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) false (.inr (.inl α)) =
        (Real.sqrt (D.q / ((D.q : ℝ) + 1)) : ℂ) ∧
      A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) false (.inl α) =
        (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) ∧
      A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) true (.inr (.inl α)) =
        -(D.chi α (-1)) * (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) ∧
      A70 D (.inl (α, α)) (.inl (α, α)) (.inl (α, α)) true (.inl α) =
        D.chi α (-1) * (Real.sqrt (D.q / ((D.q : ℝ) + 1)) : ℂ)) ∧
    (D.q = 2 →
      A70 D (.inr 0) (.inr 0) (.inr 0) false (.inr (.inl 0)) = (Real.sqrt (2 / 3 : ℝ) : ℂ) ∧
      A70 D (.inr 0) (.inr 0) (.inl (0, 0)) true (.inr (.inl 0)) = (Real.sqrt (1 / 3 : ℝ) : ℂ) ∧
      ∀ k : {k : D.Lab2 // D.IsCuspLabel k},
        A70 D (.inr 0) (.inr 0) (.inr 0) false (.inr (.inr (.inr k))) =
          (Real.sqrt (1 / 3 : ℝ) : ℂ) ∧
        A70 D (.inr 0) (.inr 0) (.inl (0, 0)) true (.inr (.inr (.inr k))) =
          -(Real.sqrt (2 / 3 : ℝ) : ℂ)) := by
  have hq0 : (0 : ℝ) < D.q := q_pos D
  have hqp1 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith
  have hBBas_inl : ∀ ab : D.Lab × D.Lab, Fintype.card (D.BBas (.inl ab)) = 1 := fun _ => by
    change Fintype.card Unit = 1; simp
  have hUnit_unique : ∀ (ab : D.Lab × D.Lab) (f : D.BBas (.inl ab) → ℂ),
      (∑ P : D.BBas (.inl ab), f P) = f (() : D.BBas (.inl ab)) := fun ab f => by
    let p : D.BBas (.inl ab) := ()
    change (∑ P : D.BBas (.inl ab), f P) = f p
    rw [Finset.sum_eq_single p]
    · intro P _ hP; exact absurd (@Subsingleton.elim Unit _ P p) hP
    · intro hm; exact (hm (Finset.mem_univ p)).elim
  have hBas_det : ∀ α : D.Lab, Fintype.card (D.Bas (.inl α)) = 1 := fun _ => by
    change Fintype.card Unit = 1; simp
  have hBas_st : ∀ α : D.Lab, Fintype.card (D.Bas (.inr (.inl α))) = D.q := fun _ => by
    change Fintype.card (Option D.Lab) = D.q
    rw [Fintype.card_option, card_Lab]
    have := D.one_lt_q; omega
  have hBas_ps : ∀ ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val},
      Fintype.card (D.Bas (.inr (.inr (.inl ab)))) = D.q + 1 := fun _ => by
    change Fintype.card (Option (Option D.Lab)) = D.q + 1
    rw [Fintype.card_option, Fintype.card_option, card_Lab]
    have := D.one_lt_q; omega
  refine ⟨?part1, ?part2, ?part3⟩
  case part1 =>
    intro α β hlt
    let ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} := ⟨(α, β), hlt⟩
    let μ : D.Irr := .inr (.inr (.inl ab))
    constructor
    · rw [A70, if_neg Bool.false_ne_true, dif_pos ⟨rfl, rfl⟩]
      rw [hBas_ps ab, hBBas_inl (α, β)]
      have hlab : (labMu D) μ (.inl (α, β)) (() : D.BBas (.inl (α, β))) =
          some (none : Option (Option D.Lab)) := by
        simp [μ, ab, labMu]; rfl
      have hR1 : D.R μ 1 none none = 1 := by
        change matEntry (D.psModel α β (1 : Matrix (Fin 2) (Fin 2) D.Fq))
          (D.psVec β none) (D.psVec β none) = 1
        rw [psModel_one, matEntry_one]
        simp [dotProduct, FieldData.psVec]
      have hsum_u : (∑ P : D.BBas (.inl (α, β)), ∑ Pt : D.BBas (.inl (α, β)),
          (Rent D) μ 1 ((labMu D) μ (.inl (α, β)) (cast (congrArg D.BBas (rfl.trans rfl.symm)) Pt))
            ((labMu D) μ (.inl (α, β)) P) *
            conj (if cast (congrArg D.BBas rfl) Pt = P then (1 : ℂ) else 0)) = 1 := by
        simp only [cast_eq]
        rw [hUnit_unique, hUnit_unique]
        simp only [hlab, Rent]
        rw [hR1]
        simp; rfl
      rw [hsum_u, mul_one]
      have hsq : Real.sqrt (((D.q + 1 : ℕ) : ℝ) * 1 / ((1 : ℝ) * 1 * 1 * ((D.q : ℝ) + 1))) = 1 := by
        push_cast
        rw [mul_one, one_mul, one_mul, one_mul, div_self hqp1.ne', Real.sqrt_one]
      exact_mod_cast hsq
    · rw [A70, if_pos rfl]
      rw [hBas_ps ab, hBBas_inl (α, β), hBBas_inl (β, α)]
      have htLab : (tLab D) (.inl (β, α)) (β, α) = some (() : D.BBas (.inl (β, α))) := by
        simp [tLab]; rfl
      have hne_pair : (β, α) ≠ (α, β) := by
        intro h
        have hba : β = α := congrArg Prod.fst h
        rw [hba] at hlt
        exact lt_irrefl _ hlt
      have hlab1 : (labMu D) μ (.inl (β, α)) (() : D.BBas (.inl (β, α))) =
          some (some none : Option (Option D.Lab)) := by
        simp [μ, ab, labMu, hne_pair]; rfl
      have hlab2 : (labMu D) μ (.inl (α, β)) (() : D.BBas (.inl (α, β))) =
          some (none : Option (Option D.Lab)) := by
        simp [μ, ab, labMu]; rfl
      have hutw : conj ((utwW D) (.inl (α, β)) (β, α) (() : D.BBas (.inl (α, β)))) = 1 := by
        simp [utwW]
      rw [htLab]
      dsimp only
      have hsum_u : (∑ P : D.BBas (.inl (α, β)),
          (Rent D) μ (wGL D) ((labMu D) μ (.inl (β, α)) (() : D.BBas (.inl (β, α))))
            ((labMu D) μ (.inl (α, β)) P) * conj ((utwW D) (.inl (α, β)) (β, α) P)) =
          isqrt D.q := by
        rw [hUnit_unique]
        simp only [hlab1, hlab2, hutw, mul_one, Rent]
        exact matEntry_psModel_wGL_psVec_some_none_none D α β
      rw [hsum_u]
      simp only [Nat.cast_one]
      have hsq : Real.sqrt (((D.q + 1 : ℕ) : ℝ) * (D.q : ℝ) / (1 * 1 * 1 * ((D.q : ℝ) + 1))) =
          Real.sqrt (D.q : ℝ) := by
        push_cast
        congr 1
        field_simp [hqp1.ne']
      rw [hsq]
      simp only [FieldData.isqrt, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr hq0), Complex.ofReal_one]
  case part2 =>
    intro α
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- ω = false, st α
      rw [A70, if_neg Bool.false_ne_true, dif_pos ⟨rfl, rfl⟩]
      rw [hBas_st α, hBBas_inl (α, α)]
      have hlab : (labMu D) (.inr (.inl α)) (.inl (α, α)) (() : D.BBas (.inl (α, α))) =
          some (none : Option D.Lab) := by
        simp [labMu]; rfl
      have hR1 : D.R (.inr (.inl α)) 1 none none = 1 := by
        change matEntry (D.psModel α α (1 : Matrix (Fin 2) (Fin 2) D.Fq))
          (D.stVec α none) (D.stVec α none) = 1
        rw [psModel_one, matEntry_one, dot_conj_stVec_none]
      have hsum_u : (∑ P : D.BBas (.inl (α, α)), ∑ Pt : D.BBas (.inl (α, α)),
          (Rent D) (.inr (.inl α)) 1
            ((labMu D) (.inr (.inl α)) (.inl (α, α)) (cast (congrArg D.BBas (rfl.trans rfl.symm)) Pt))
            ((labMu D) (.inr (.inl α)) (.inl (α, α)) P) *
            conj (if cast (congrArg D.BBas rfl) Pt = P then (1 : ℂ) else 0)) = 1 := by
        simp only [cast_eq]
        rw [hUnit_unique, hUnit_unique]
        simp only [hlab, Rent]
        rw [hR1]
        simp; rfl
      rw [hsum_u, mul_one]
      simp [Nat.cast_one, mul_one, one_mul]
    · -- ω = false, det α
      rw [A70, if_neg Bool.false_ne_true, dif_pos ⟨rfl, rfl⟩]
      rw [hBas_det α, hBBas_inl (α, α)]
      have hlab : (labMu D) (.inl α) (.inl (α, α)) (() : D.BBas (.inl (α, α))) =
          some (() : Unit) := by
        simp [labMu]; rfl
      have hR1 : D.R (.inl α) 1 () () = 1 := by
        change matEntry (D.psModel α α (1 : Matrix (Fin 2) (Fin 2) D.Fq))
          (D.detVec α) (D.detVec α) = 1
        rw [psModel_one, matEntry_one, dot_conj_detVec_detVec]
      have hsum_u : (∑ P : D.BBas (.inl (α, α)), ∑ Pt : D.BBas (.inl (α, α)),
          (Rent D) (.inl α) 1
            ((labMu D) (.inl α) (.inl (α, α)) (cast (congrArg D.BBas (rfl.trans rfl.symm)) Pt))
            ((labMu D) (.inl α) (.inl (α, α)) P) *
            conj (if cast (congrArg D.BBas rfl) Pt = P then (1 : ℂ) else 0)) = 1 := by
        simp only [cast_eq]
        rw [hUnit_unique, hUnit_unique]
        simp only [hlab, Rent]
        rw [hR1]
        simp; rfl
      rw [hsum_u, mul_one]
      simp [Nat.cast_one, mul_one, one_mul]
    · -- ω = true, st α
      rw [A70, if_pos rfl]
      rw [hBas_st α, hBBas_inl (α, α)]
      have htLab : (tLab D) (.inl (α, α)) (α, α) = some (() : D.BBas (.inl (α, α))) := by
        simp [tLab]; rfl
      have hlab : (labMu D) (.inr (.inl α)) (.inl (α, α)) (() : D.BBas (.inl (α, α))) =
          some (none : Option D.Lab) := by
        simp [labMu]; rfl
      have hutw : conj ((utwW D) (.inl (α, α)) (α, α) (() : D.BBas (.inl (α, α)))) = 1 := by
        simp [utwW]
      rw [htLab]
      dsimp only
      have hsum_u : (∑ P : D.BBas (.inl (α, α)),
          (Rent D) (.inr (.inl α)) (wGL D)
            ((labMu D) (.inr (.inl α)) (.inl (α, α)) (() : D.BBas (.inl (α, α))))
            ((labMu D) (.inr (.inl α)) (.inl (α, α)) P) * conj ((utwW D) (.inl (α, α)) (α, α) P)) =
          -((D.q : ℂ)⁻¹) * D.chi α (-1) := by
        rw [hUnit_unique]
        simp only [hlab, hutw, mul_one, Rent]
        exact matEntry_psModel_wGL_stVec_none D α
      rw [hsum_u]
      simp only [Nat.cast_one]
      have hsq : Real.sqrt ((D.q : ℝ) * (D.q : ℝ) / (1 * 1 * 1 * ((D.q : ℝ) + 1))) * (D.q : ℝ)⁻¹ =
          Real.sqrt (1 / ((D.q : ℝ) + 1)) := by
        rw [← sq_eq_sq₀ (by positivity) (by positivity)]
        rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        field_simp [hq0.ne', hqp1.ne']
      calc (Real.sqrt ((D.q : ℝ) * (D.q : ℝ) / (1 * 1 * 1 * ((D.q : ℝ) + 1))) : ℂ) *
            (-((D.q : ℂ)⁻¹) * D.chi α (-1))
          = -(D.chi α (-1)) *
              ((Real.sqrt ((D.q : ℝ) * (D.q : ℝ) / (1 * 1 * 1 * ((D.q : ℝ) + 1))) * (D.q : ℝ)⁻¹ : ℝ) : ℂ) := by
              push_cast; ring
        _ = -(D.chi α (-1)) * (Real.sqrt (1 / ((D.q : ℝ) + 1)) : ℂ) := by rw [hsq]
    · -- ω = true, det α
      rw [A70, if_pos rfl]
      rw [hBas_det α, hBBas_inl (α, α)]
      have htLab : (tLab D) (.inl (α, α)) (α, α) = some (() : D.BBas (.inl (α, α))) := by
        simp [tLab]; rfl
      have hlab : (labMu D) (.inl α) (.inl (α, α)) (() : D.BBas (.inl (α, α))) =
          some (() : Unit) := by
        simp [labMu]; rfl
      have hutw : conj ((utwW D) (.inl (α, α)) (α, α) (() : D.BBas (.inl (α, α)))) = 1 := by
        simp [utwW]
      rw [htLab]
      dsimp only
      have hsum_u : (∑ P : D.BBas (.inl (α, α)),
          (Rent D) (.inl α) (wGL D)
            ((labMu D) (.inl α) (.inl (α, α)) (() : D.BBas (.inl (α, α))))
            ((labMu D) (.inl α) (.inl (α, α)) P) * conj ((utwW D) (.inl (α, α)) (α, α) P)) =
          D.chi α (-1) := by
        rw [hUnit_unique]
        simp only [hlab, hutw, mul_one, Rent]
        exact matEntry_psModel_wGL_detVec D α
      rw [hsum_u]
      simp [Nat.cast_one, one_mul, mul_comm]
  case part3 =>
    intro hq2
    have hq_real : (D.q : ℝ) = 2 := by exact_mod_cast hq2
    have hq_cplx : (D.q : ℂ) = 2 := by exact_mod_cast hq2
    have hlab_zero : ∀ a : D.Lab, a = 0 := fun a =>
      ZMod.val_injective (D.q - 1) (by have := ZMod.val_lt a; rw [ZMod.val_zero]; omega)
    have hBBas_inr0 : Fintype.card (D.BBas (.inr (0 : D.Lab))) = 1 := by
      rw [show Fintype.card (D.BBas (.inr (0 : D.Lab))) = Fintype.card D.Lab from rfl, card_Lab, hq2]
    have hst0 : Fintype.card (D.Bas (.inr (.inl (0 : D.Lab)))) = 2 := by
      rw [hBas_st 0, hq2]
    have hBBas_unique : ∀ f : D.BBas (.inr (0 : D.Lab)) → ℂ,
        (∑ P, f P) = f ((0 : D.Lab) : D.BBas (.inr (0 : D.Lab))) := by
      intro f
      let p0 : D.BBas (.inr (0 : D.Lab)) := (0 : D.Lab)
      change (∑ P, f P) = f p0
      rw [Finset.sum_eq_single p0]
      · intro P _ hP; exact absurd (hlab_zero P) hP
      · intro hm; exact (hm (Finset.mem_univ p0)).elim
    refine ⟨?_, ?_, ?_⟩
    · -- q = 2, ω = false, st 0
      rw [A70, if_neg Bool.false_ne_true, dif_pos ⟨rfl, rfl⟩]
      rw [hst0, hBBas_inr0, hq_real]
      have hlab : (labMu D) (.inr (.inl 0)) (.inr 0) ((0 : D.Lab) : D.BBas (.inr 0)) =
          some (some (0 : D.Lab)) := by
        simp [labMu]; rfl
      have hR1 : D.R (.inr (.inl 0)) 1 (some 0) (some 0) = 1 := by
        change matEntry (D.psModel 0 0 (1 : Matrix (Fin 2) (Fin 2) D.Fq))
          (D.wVec 0 0) (D.wVec 0 0) = 1
        rw [psModel_one, matEntry_one, dot_conj_wVec, if_pos rfl]
      have hsum : (∑ P : D.BBas (.inr (0 : D.Lab)), ∑ Pt : D.BBas (.inr (0 : D.Lab)),
          (Rent D) (.inr (.inl 0)) 1
            ((labMu D) (.inr (.inl 0)) (.inr 0) (cast (congrArg D.BBas (rfl.trans rfl.symm)) Pt))
            ((labMu D) (.inr (.inl 0)) (.inr 0) P) *
            conj (if cast (congrArg D.BBas rfl) Pt = P then (1 : ℂ) else 0)) = 1 := by
        simp only [cast_eq]
        rw [hBBas_unique, hBBas_unique]
        simp only [hlab, Rent]
        rw [hR1]
        simp; rfl
      rw [hsum, mul_one]
      simp only [Nat.cast_ofNat, Nat.cast_one]
      congr 2
      norm_num
    · -- q = 2, ω = true, st 0
      rw [A70, if_pos rfl]
      rw [hst0, hBBas_inr0, hq_real]
      have htLab : (tLab D) (.inr 0) (0, 0) = some ((0 : D.Lab) : D.BBas (.inr 0)) := by
        rw [tLab, if_pos (by ring)]
        rfl
      have hlab : (labMu D) (.inr (.inl 0)) (.inr 0) ((0 : D.Lab) : D.BBas (.inr 0)) =
          some (some (0 : D.Lab)) := by
        simp [labMu]; rfl
      have hutw : conj ((utwW D) (.inr 0) (0, 0) ((0 : D.Lab) : D.BBas (.inr 0))) = 1 := by
        simp [utwW]
      rw [htLab]
      dsimp only
      have hsum : (∑ P : D.BBas (.inr (0 : D.Lab)),
          (Rent D) (.inr (.inl 0)) (wGL D)
            ((labMu D) (.inr (.inl 0)) (.inr 0) ((0 : D.Lab) : D.BBas (.inr 0)))
            ((labMu D) (.inr (.inl 0)) (.inr 0) P) *
            conj ((utwW D) (.inr 0) (0, 0) P)) = (2 : ℂ)⁻¹ := by
        rw [hBBas_unique]
        simp only [hlab, hutw, mul_one, Rent]
        change matEntry (D.psModel 0 0 ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
          (D.wVec 0 0) (D.wVec 0 0) = (2 : ℂ)⁻¹
        rw [matEntry_psModel_wGL_wVec D 0 0 0 0 (by ring)]
        have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
        rw [sub_self, chi_zero_label D hm1, gauss_zero, hq_cplx]
        norm_num
      rw [hsum]
      simp only [Nat.cast_ofNat, Nat.cast_one]
      have hsq : Real.sqrt ((2 : ℝ) * 2 / (1 * 1 * 1 * (2 + 1))) * (2 : ℝ)⁻¹ =
          Real.sqrt (1 / 3 : ℝ) := by
        rw [← sq_eq_sq₀ (by positivity) (by positivity)]
        rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        norm_num
      calc (Real.sqrt ((2 : ℝ) * 2 / (1 * 1 * 1 * (2 + 1))) : ℂ) * (2 : ℂ)⁻¹
          = ((Real.sqrt ((2 : ℝ) * 2 / (1 * 1 * 1 * (2 + 1))) * (2 : ℝ)⁻¹ : ℝ) : ℂ) := by
              push_cast; rfl
        _ = (Real.sqrt (1 / 3 : ℝ) : ℂ) := by rw [hsq]
    · intro k
      have hcusp_card : Fintype.card (D.Bas (.inr (.inr (.inr k)))) = 1 := by
        change Fintype.card D.Lab = 1
        rw [card_Lab, hq2]
      have hres0 : D.restrLab k.1 = 0 := hlab_zero (D.restrLab k.1)
      have hres0' : (0 : D.Lab) = D.restrLab k.1 := hres0.symm
      refine ⟨?_, ?_⟩
      · -- q = 2, ω = false, cusp k
        rw [A70, if_neg Bool.false_ne_true, dif_pos ⟨rfl, rfl⟩]
        rw [hcusp_card, hBBas_inr0, hq_real]
        have hlab : (labMu D) (.inr (.inr (.inr k))) (.inr 0) ((0 : D.Lab) : D.BBas (.inr 0)) =
            some ((0 : D.Lab) : D.Bas (.inr (.inr (.inr k)))) := by
          simp [labMu, hres0']; rfl
        have hR1 : D.R (.inr (.inr (.inr k))) 1 (0 : D.Lab) (0 : D.Lab) = 1 := by
          change matEntry (D.piModel k.1 (1 : Matrix (Fin 2) (Fin 2) D.Fq))
            (D.multVec 0) (D.multVec 0) = 1
          rw [piModel_one, matEntry_one, dot_conj_multVec, if_pos rfl]
        have hsum : (∑ P : D.BBas (.inr (0 : D.Lab)), ∑ Pt : D.BBas (.inr (0 : D.Lab)),
            (Rent D) (.inr (.inr (.inr k))) 1
              ((labMu D) (.inr (.inr (.inr k))) (.inr 0)
                (cast (congrArg D.BBas (rfl.trans rfl.symm)) Pt))
              ((labMu D) (.inr (.inr (.inr k))) (.inr 0) P) *
              conj (if cast (congrArg D.BBas rfl) Pt = P then (1 : ℂ) else 0)) = 1 := by
          simp only [cast_eq]
          rw [hBBas_unique, hBBas_unique]
          simp only [hlab, Rent]
          rw [hR1]
          simp; rfl
        rw [hsum, mul_one]
        simp only [Nat.cast_one]
        congr 2
        norm_num
      · -- q = 2, ω = true, cusp k
        rw [A70, if_pos rfl]
        rw [hcusp_card, hBBas_inr0, hq_real]
        have htLab : (tLab D) (.inr 0) (0, 0) = some ((0 : D.Lab) : D.BBas (.inr 0)) := by
          rw [tLab, if_pos (by ring)]
          rfl
        have hlab : (labMu D) (.inr (.inr (.inr k))) (.inr 0) ((0 : D.Lab) : D.BBas (.inr 0)) =
            some ((0 : D.Lab) : D.Bas (.inr (.inr (.inr k)))) := by
          simp [labMu, hres0']; rfl
        have hutw : conj ((utwW D) (.inr 0) (0, 0) ((0 : D.Lab) : D.BBas (.inr 0))) = 1 := by
          simp [utwW]
        rw [htLab]
        dsimp only
        have hsum : (∑ P : D.BBas (.inr (0 : D.Lab)),
            (Rent D) (.inr (.inr (.inr k))) (wGL D)
              ((labMu D) (.inr (.inr (.inr k))) (.inr 0) ((0 : D.Lab) : D.BBas (.inr 0)))
              ((labMu D) (.inr (.inr (.inr k))) (.inr 0) P) *
              conj ((utwW D) (.inr 0) (0, 0) P)) = -1 := by
          rw [hBBas_unique]
          simp only [hlab, hutw, mul_one, Rent]
          change matEntry (D.piModel k.1 ((wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq))
            (D.multVec 0) (D.multVec 0) = -1
          rw [matEntry_piModel_wGL_multVec D k.1 0 0 (by rw [hres0, add_zero])]
          have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
          have hchi0 : ∀ z : D.Fq2, z ≠ 0 → D.chi (-0) (D.nrm z) = 1 := by
            intro z hz
            rw [neg_zero, chi_zero_label D (mt (nrm_eq_zero D z).mp hz)]
          have hgauss_eq : D.gaussQ2 (fun z => D.theta k.1 z * D.chi (-0) (D.nrm z)) =
              D.gaussQ2 (D.theta k.1) := by
            unfold FieldData.gaussQ2
            refine Finset.sum_congr rfl fun z hz => ?_
            dsimp only
            rw [hchi0 z (Finset.mem_filter.mp hz).2, mul_one]
          rw [hgauss_eq, gaussQ2_q_eq_two D hq2 k, chi_zero_label D hm1, hq_cplx]
          norm_num
        rw [hsum]
        simp only [Nat.cast_one]
        have hsq : Real.sqrt ((1 : ℝ) * 2 / (1 * 1 * 1 * (2 + 1))) = Real.sqrt (2 / 3 : ℝ) := by
          congr 1; norm_num
        rw [hsq]
        ring
