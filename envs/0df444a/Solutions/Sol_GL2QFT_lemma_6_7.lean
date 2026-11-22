-- Prove2me | solution 1 for GL2QFT.lemma_6_7
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:23:12.949414+00:00
-- url     : https://prove2.me/submissions/4c078d07-d61e-4617-be13-7753d39cf6fb

import Definitions.Def_GL2QFT_Irreps

open Classical

namespace GL2QFT.Lemma67

open GL2QFT GL2QFT.FieldData
open scoped ComplexConjugate

/-! ### Part 1: Cardinalities, generator, and discrete logarithm -/

lemma card_fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  have h1 : D.p ^ Module.finrank (ZMod D.p) D.Fq = Fintype.card D.Fq :=
    FiniteField.pow_finrank_eq_card D.p D.Fq
  have h2 : Module.finrank (ZMod D.p) D.Fq = D.r := by
    have hpb := (AdjoinRoot.powerBasis' D.f_monic).finrank
    simpa [FieldData.Fq, D.f_deg] using hpb
  rw [← h1, h2, FieldData.q]

lemma card_fq_units (D : FieldData) : Fintype.card D.Fqˣ = D.q - 1 := by
  rw [Fintype.card_units, card_fq]

lemma card_lab (D : FieldData) : Fintype.card D.Lab = D.q - 1 := by
  rw [ZMod.card]

lemma card_fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  have hfin : Module.finrank D.Fq D.Fq2 = 2 := by
    have hpb := (AdjoinRoot.powerBasis' D.F_monic).finrank
    simpa [FieldData.Fq2, D.F_deg] using hpb
  have hcard : Nat.card D.Fq2 = Nat.card D.Fq ^ Module.finrank D.Fq D.Fq2 :=
    Module.natCard_eq_pow_finrank (K := D.Fq) (V := D.Fq2)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_fq, hfin] at hcard
  exact hcard

lemma gen_order (D : FieldData) : orderOf D.gen = D.q - 1 := by
  have h_alg := FiniteField.algebraMap_norm_eq_pow (K := D.Fq) (K' := D.Fq2) (x := D.h)
  have hdiv : (Nat.card D.Fq2 - 1) / (Nat.card D.Fq - 1) = D.q + 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_fq2, card_fq]
    have hq : 1 < D.q := D.one_lt_q
    have hmul : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
      zify [Nat.one_le_pow 2 D.q (by omega), hq.le]
      ring
    rw [hmul, Nat.mul_div_cancel_left _ (by omega)]
  rw [hdiv] at h_alg
  change (algebraMap D.Fq D.Fq2).toMonoidHom D.gen = D.h ^ (D.q + 1) at h_alg
  have hinj : Function.Injective ((algebraMap D.Fq D.Fq2).toMonoidHom) :=
    RingHom.injective (algebraMap D.Fq D.Fq2)
  rw [← orderOf_injective (algebraMap D.Fq D.Fq2).toMonoidHom hinj D.gen, h_alg,
    orderOf_pow' (x := D.h) (Nat.succ_ne_zero D.q)]
  have hord : orderOf D.h = (D.q - 1) * (D.q + 1) := by
    rw [D.h_order]
    change (D.q) ^ 2 - 1 = (D.q - 1) * (D.q + 1)
    have hq : 1 < D.q := D.one_lt_q
    zify [Nat.one_le_pow 2 D.q (by omega), hq.le]
    ring
  rw [hord]
  change (D.q - 1) * (D.q + 1) / Nat.gcd ((D.q - 1) * (D.q + 1)) (D.q + 1) = D.q - 1
  rw [Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h0
  have hord := gen_order D
  rw [h0, orderOf_zero] at hord
  have hq : 1 < D.q := D.one_lt_q
  omega

lemma exists_gen_pow (D : FieldData) {x : D.Fq} (hx : x ≠ 0) :
    ∃ n : ℕ, n < D.q - 1 ∧ D.gen ^ n = x := by
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu_ord : orderOf u = D.q - 1 := by
    rw [← orderOf_units (y := u)]
    exact gen_order D
  let f : Fin (D.q - 1) → D.Fqˣ := fun i => u ^ (i : ℕ)
  have hfinj : Function.Injective f := by
    intro i j hij
    have hmod : (i : ℕ) ≡ (j : ℕ) [MOD orderOf u] := pow_eq_pow_iff_modEq.mp hij
    rw [hu_ord] at hmod
    ext
    exact Nat.ModEq.eq_of_lt_of_lt hmod i.isLt j.isLt
  have hfsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, by simp [card_fq_units]⟩ |>.2
  obtain ⟨i, hi⟩ := hfsurj (Units.mk0 x hx)
  refine ⟨i.val, i.isLt, ?_⟩
  have hval := congrArg (fun z : D.Fqˣ => (z : D.Fq)) hi
  simpa [f, u] using hval

lemma dlog_lt (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.dlog x < D.q - 1 := by
  obtain ⟨n, hn, hpow⟩ := exists_gen_pow D hx
  have hex : ∃ m : ℕ, D.gen ^ m = x := ⟨n, hpow⟩
  simp only [FieldData.dlog, hex, ↓reduceDIte]
  exact lt_of_le_of_lt (Nat.find_min' hex hpow) hn

lemma gen_pow_dlog (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  obtain ⟨n, _, hpow⟩ := exists_gen_pow D hx
  have hex : ∃ m : ℕ, D.gen ^ m = x := ⟨n, hpow⟩
  simp only [FieldData.dlog, hex, ↓reduceDIte]
  exact Nat.find_spec hex

lemma dlog_one (D : FieldData) : D.dlog 1 = 0 := by
  have hex : ∃ m : ℕ, D.gen ^ m = (1 : D.Fq) := ⟨0, pow_zero _⟩
  simp only [FieldData.dlog, hex, ↓reduceDIte]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' hex (pow_zero _))

lemma dlog_gen (D : FieldData) (hq : 2 < D.q) : D.dlog D.gen = 1 := by
  have hex : ∃ m : ℕ, D.gen ^ m = D.gen := ⟨1, pow_one _⟩
  simp only [FieldData.dlog, hex, ↓reduceDIte]
  have hle : Nat.find hex ≤ 1 := Nat.find_min' hex (pow_one _)
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    have hsp := Nat.find_spec hex
    rw [h0, pow_zero] at hsp
    have hord := gen_order D
    rw [← hsp, orderOf_one] at hord
    omega
  omega

lemma dlog_mul_mod (D : FieldData) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.dlog (x * y) % (D.q - 1) = (D.dlog x + D.dlog y) % (D.q - 1) := by
  let u : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)
  have hu_ord : orderOf u = D.q - 1 := by
    rw [← orderOf_units (y := u)]
    exact gen_order D
  have hpow : u ^ D.dlog (x * y) = u ^ (D.dlog x + D.dlog y) := by
    ext
    simp only [Units.val_pow_eq_pow_val, u, Units.val_mk0]
    rw [pow_add, gen_pow_dlog D (mul_ne_zero hx hy), gen_pow_dlog D hx, gen_pow_dlog D hy]
  have hmod := pow_eq_pow_iff_modEq.mp hpow
  simpa [hu_ord, Nat.ModEq] using hmod

/-! ### Part 2: Complex exponentials, `chi`, and `psi` -/

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

lemma chi_one (D : FieldData) (α : D.Lab) : D.chi α 1 = 1 := by
  simp [FieldData.chi, dlog_one]

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
    push_cast
    ring
  rw [harg]
  exact exp_two_pi_I_div_congr hq hmod

lemma chi_add (D : FieldData) (α β : D.Lab) (x : D.Fq) :
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
      push_cast
      ring
    rw [harg]
    exact exp_two_pi_I_div_congr hq hmod

lemma chi_zero_lab (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.chi 0 x = 1 := by
  simp [FieldData.chi, hx]

lemma conj_chi (D : FieldData) (α : D.Lab) (x : D.Fq) :
    conj (D.chi α x) = D.chi (-α) x := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero]
  · have hmul : D.chi (-α) x * D.chi α x = 1 := by
      rw [← chi_add, neg_add_cancel, chi_zero_lab D hx]
    have hnorm : conj (D.chi α x) * D.chi α x = 1 := by
      simp only [FieldData.chi, hx, ↓reduceIte]
      let r : ℝ := 2 * Real.pi * ((α.val * D.dlog x : ℕ) : ℝ) / ((D.q - 1 : ℕ) : ℝ)
      have hreal : (r : ℂ) * Complex.I =
          2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) := by
        simp only [r]
        push_cast
        ring
      rw [← hreal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hne : D.chi α x ≠ 0 := by simp [FieldData.chi, hx, Complex.exp_ne_zero]
    exact mul_right_cancel₀ hne (hnorm.trans hmul.symm)

lemma chi_inv (D : FieldData) (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    D.chi α x⁻¹ = D.chi (-α) x := by
  have h1 : D.chi α x⁻¹ * D.chi α x = 1 := by
    rw [← chi_mul D α (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, chi_one]
  have h2 : D.chi (-α) x * D.chi α x = 1 := by
    rw [← chi_add, neg_add_cancel, chi_zero_lab D hx]
  have hne : D.chi α x ≠ 0 := by simp [FieldData.chi, hx, Complex.exp_ne_zero]
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

lemma chi_div (D : FieldData) (α : D.Lab) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.chi α (x / y) = D.chi α x * D.chi (-α) y := by
  rw [div_eq_mul_inv, chi_mul D α hx (inv_ne_zero hy), chi_inv D α hy]

lemma chi_gen_ne (D : FieldData) {α β : D.Lab} (h : α ≠ β) :
    D.chi α D.gen ≠ D.chi β D.gen := by
  have hq2 : 2 < D.q := by
    by_contra hle
    have hq : 1 < D.q := D.one_lt_q
    have hqeq : D.q - 1 = 1 := by omega
    have hsub : Subsingleton D.Lab := by
      change Subsingleton (ZMod (D.q - 1))
      rw [hqeq]
      infer_instance
    exact h (Subsingleton.elim α β)
  have hdlog : D.dlog D.gen = 1 := dlog_gen D hq2
  have hgen : D.gen ≠ 0 := gen_ne_zero D
  intro heq
  simp only [FieldData.chi, hgen, ↓reduceIte, hdlog, mul_one] at heq
  rw [Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨k, hk⟩ := heq
  have hq1 : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by
    have : 1 < D.q := D.one_lt_q
    exact Nat.cast_ne_zero.mpr (by omega)
  have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
  have hk' : ((α.val : ℂ) - (β.val : ℂ)) / ((D.q - 1 : ℕ) : ℂ) = k := by
    have h1 : 2 * Real.pi * Complex.I * (((α.val : ℂ) - (β.val : ℂ)) / ((D.q - 1 : ℕ) : ℂ)) =
        2 * Real.pi * Complex.I * (k : ℂ) := by
      calc 2 * Real.pi * Complex.I * (((α.val : ℂ) - (β.val : ℂ)) / ((D.q - 1 : ℕ) : ℂ))
          = 2 * Real.pi * Complex.I * (α.val : ℂ) / ((D.q - 1 : ℕ) : ℂ) -
            2 * Real.pi * Complex.I * (β.val : ℂ) / ((D.q - 1 : ℕ) : ℂ) := by ring
        _ = (k : ℂ) * (2 * Real.pi * Complex.I) := by rw [hk]; ring
        _ = 2 * Real.pi * Complex.I * (k : ℂ) := by ring
    exact mul_left_cancel₀ h2pi h1
  have hk'' : ((α.val : ℤ) - (β.val : ℤ)) = k * ((D.q - 1 : ℕ) : ℤ) := by
    have hc : ((α.val : ℂ) - (β.val : ℂ)) = (k : ℂ) * ((D.q - 1 : ℕ) : ℂ) :=
      (div_eq_iff hq1).mp hk'
    exact_mod_cast hc
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
    have hterm : ∀ x : D.Fqˣ, D.chi 0 (x : D.Fq) = 1 := fun x => chi_zero_lab D x.ne_zero
    simp [hterm, card_fq_units]
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
      rw [← chi_zero_lab D (gen_ne_zero D)]
      exact sub_ne_zero.mpr (chi_gen_ne D h0)
    have hmul0 : (D.chi α D.gen - 1) * ∑ x : D.Fqˣ, D.chi α (x : D.Fq) = 0 := by
      have heq := hreidx.trans hfac
      linear_combination -heq
    exact mul_eq_zero.mp hmul0 |>.resolve_left hdiff

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
    push_cast
    ring
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
      simp only [r]
      push_cast
      ring
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
  have hval_lt : (Algebra.trace (ZMod D.p) D.Fq x₀).val < D.p := ZMod.val_lt _
  exact absurd (Nat.le_of_dvd hval_pos heq) (not_le_of_gt hval_lt)

lemma sum_psi (D : FieldData) (u : D.Fq) :
    ∑ x : D.Fq, D.psi (u * x) = if u = 0 then (D.q : ℂ) else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp [psi_zero, card_fq]
  · simp only [hu, ↓reduceIte]
    obtain ⟨x₀, hx₀⟩ := psi_nontrivial D
    let x₁ : D.Fq := x₀ / u
    have hreidx : ∑ x : D.Fq, D.psi (u * x) = ∑ x : D.Fq, D.psi (u * (x₁ + x)) :=
      (Fintype.sum_equiv (Equiv.addLeft x₁) _ _ fun _ => rfl).symm
    have hfac : ∑ x : D.Fq, D.psi (u * (x₁ + x)) = D.psi x₀ * ∑ x : D.Fq, D.psi (u * x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hmul : u * (x₁ + x) = x₀ + u * x := by
        simp [x₁, mul_add, mul_div_cancel₀ _ hu]
      rw [hmul, psi_add]
    have hmul0 : (D.psi x₀ - 1) * ∑ x : D.Fq, D.psi (u * x) = 0 := by
      have heq := hreidx.trans hfac
      linear_combination -heq
    exact mul_eq_zero.mp hmul0 |>.resolve_left (sub_ne_zero.mpr hx₀)

/-! ### Part 3: Basis vectors, `psModel` on `B`, `RB`, `R`, and trace obstruction -/

lemma conj_isqrt (x : ℝ) : conj (isqrt x) = isqrt x := by
  simp [FieldData.isqrt]

lemma conj_isqrt_mul_isqrt {x : ℝ} (hx : 0 < x) :
    conj (isqrt x) * isqrt x = ((x : ℝ) : ℂ)⁻¹ := by
  rw [conj_isqrt]
  simp only [FieldData.isqrt, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hx.le, Complex.ofReal_inv]

lemma q_pos (D : FieldData) : (0 : ℝ) < D.q := by
  exact_mod_cast (by have := D.one_lt_q; omega : 0 < D.q)

lemma q_sub_one_pos (D : FieldData) : (0 : ℝ) < ((D.q - 1 : ℕ) : ℝ) := by
  have := D.one_lt_q
  exact_mod_cast (by omega : 0 < D.q - 1)

lemma q_sub_one_real (D : FieldData) : ((D.q - 1 : ℕ) : ℝ) = (D.q : ℝ) - 1 := by
  have := D.one_lt_q
  rw [Nat.cast_sub (by omega), Nat.cast_one]

lemma q_sub_one_complex_ne (D : FieldData) : ((D.q : ℂ) - 1) ≠ 0 := by
  have h1 : (1 : ℝ) < D.q := by exact_mod_cast D.one_lt_q
  intro h
  have : ((D.q : ℝ) - 1 : ℝ) = 0 := by exact_mod_cast h
  linarith

lemma q_complex_ne (D : FieldData) : (D.q : ℂ) ≠ 0 := by
  have := D.one_lt_q
  exact Nat.cast_ne_zero.mpr (by omega)

lemma q_add_one_complex_ne (D : FieldData) : ((D.q : ℂ) + 1) ≠ 0 := by
  have h1 : (1 : ℝ) < D.q := by exact_mod_cast D.one_lt_q
  intro h
  have : ((D.q : ℝ) + 1 : ℝ) = 0 := by exact_mod_cast h
  linarith

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

lemma matEntry_sub_right {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v w : X → ℂ) :
    matEntry M u (v - w) = matEntry M u v - matEntry M u w := by
  simp only [matEntry, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma matEntry_sub_left {X : Type} [Fintype X] (M : Matrix X X ℂ) (u v w : X → ℂ) :
    matEntry M (u - v) w = matEntry M u w - matEntry M v w := by
  simp only [matEntry, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

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

lemma borel_diag_ne_zero (D : FieldData) (g : D.G)
    (hc : (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 ≠ 0 ∧ (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 ≠ 0 := by
  have hmul : (g : Matrix (Fin 2) (Fin 2) D.Fq) * ((g⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdet1 : (g : Matrix (Fin 2) (Fin 2) D.Fq).det *
      ((g⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq).det = 1 := by
    rw [← Matrix.det_mul, hmul, Matrix.det_one]
  have hdet : (g : Matrix (Fin 2) (Fin 2) D.Fq).det ≠ 0 := left_ne_zero_of_mul_eq_one hdet1
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  exact mul_ne_zero_iff.mp hdet

lemma sum_ne_zero_eq_sum_units {M : Type*} [AddCommMonoid M] (D : FieldData) (f : D.Fq → M) :
    ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), f t = ∑ t : D.Fqˣ, f (t : D.Fq) := by
  symm
  refine Finset.sum_bij (fun (t : D.Fqˣ) _ => (t : D.Fq))
    (fun t _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.ne_zero⟩)
    (fun _ _ _ _ h => Units.ext h)
    (fun t ht => ⟨Units.mk0 t (Finset.mem_filter.mp ht).2, Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

lemma vT_none (D : FieldData) (t : D.Fq) : D.vT t none = 0 := rfl

lemma vT_zero (D : FieldData) (β : D.Lab) : D.vT 0 = D.psVec β (some none) := by
  ext y
  cases y <;> simp [FieldData.vT, FieldData.psVec, psi_zero]

lemma dot_conj_vT (D : FieldData) (s t : D.Fq) :
    (∑ y : Option D.Fq, conj (D.vT s y) * D.vT t y) = if s = t then 1 else 0 := by
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
      _ = (D.q : ℂ)⁻¹ * D.psi ((s - t) * x) := by
          congr 2; ring
  simp_rw [hterm, ← Finset.mul_sum, sum_psi]
  by_cases hst : s = t
  · simp [hst, inv_mul_cancel₀ (q_complex_ne D)]
  · simp [hst, sub_eq_zero]

lemma psModel_mulVec_infty (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) :
    (D.psModel α β M).mulVec (D.psVec β none) =
      (D.chi α (M 0 0) * D.chi β (M 1 1)) • D.psVec β none := by
  ext y
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, FieldData.psModel, FieldData.psVec,
    hc, ne_eq, not_true_eq_false, ↓reduceIte, Pi.smul_apply, smul_eq_mul]
  cases y <;> simp

lemma psModel_mulVec_vT (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (t : D.Fq) :
    (D.psModel α β M).mulVec (D.vT t) =
      (D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * t)) •
        D.vT (M 1 1 / M 0 0 * t) := by
  ext y
  cases y with
  | none =>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_option, FieldData.psModel, FieldData.vT,
      hc, hd]
  | some y' =>
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, FieldData.psModel, FieldData.vT,
      hc, zero_mul, zero_add, mul_zero, sub_zero, hd, ne_eq, not_false_eq_true, ↓reduceIte,
      zero_add, Option.some.injEq, Pi.smul_apply, smul_eq_mul]
    let x₀ : D.Fq := (M 1 1 * y' - M 0 1) / M 0 0
    have hiff : ∀ x : D.Fq, y' = (M 0 0 * x + M 0 1) / M 1 1 ↔ x = x₀ := by
      intro x
      constructor
      · intro h
        have h1 : M 1 1 * y' = M 0 0 * x + M 0 1 := by
          rw [h, mul_div_cancel₀ _ hd]
        dsimp [x₀]
        rw [eq_div_iff ha]
        linear_combination -h1
      · intro h
        rw [h]
        dsimp [x₀]
        field_simp [ha, hd]
        ring
    rw [Finset.sum_eq_single x₀]
    · have hy0 : (M 0 0 * x₀ + M 0 1) / M 1 1 = y' := ((hiff x₀).mpr rfl).symm
      rw [hy0]
      simp only [↓reduceIte]
      have hdet : D.chi β (M 0 0 * M 1 1 / M 1 1) = D.chi β (M 0 0) := by
        rw [mul_div_cancel_right₀ _ hd]
      rw [hdet]
      have harg : t * x₀ = (M 1 1 / M 0 0 * t) * y' + -(M 0 1 / M 0 0 * t) := by
        dsimp [x₀]
        field_simp [ha]
        ring
      simp only [harg, psi_add, map_mul, conj_psi, neg_neg]
      ring
    · intro x _ hx
      have hne : ¬ (y' = (M 0 0 * x + M 0 1) / M 1 1) := fun h => hx ((hiff x).mp h)
      simp [hne]
    · intro hx
      exact absurd (Finset.mem_univ x₀) hx

lemma matEntry_psModel_vT (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (s t : D.Fq) :
    matEntry (D.psModel α β M) (D.vT s) (D.vT t) =
      if s = M 1 1 / M 0 0 * t then
        D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * t)
      else 0 := by
  rw [matEntry_eq_sum_mulVec, psModel_mulVec_vT D α β M hc ha hd t]
  have hsum : (∑ x : Option D.Fq, conj (D.vT s x) *
      ((D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * t)) •
        D.vT (M 1 1 / M 0 0 * t)) x) =
      (D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * t)) *
        ∑ x : Option D.Fq, conj (D.vT s x) * D.vT (M 1 1 / M 0 0 * t) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [hsum, dot_conj_vT]
  split_ifs <;> simp

lemma matEntry_psModel_infty_infty (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) :
    matEntry (D.psModel α β M) (D.psVec β none) (D.psVec β none) =
      D.chi α (M 0 0) * D.chi β (M 1 1) := by
  rw [matEntry_eq_sum_mulVec, psModel_mulVec_infty D α β M hc]
  simp [FieldData.psVec]

lemma matEntry_psModel_infty_vT (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (t : D.Fq) :
    matEntry (D.psModel α β M) (D.psVec β none) (D.vT t) = 0 := by
  rw [matEntry_eq_sum_mulVec, psModel_mulVec_vT D α β M hc ha hd t]
  simp [FieldData.psVec, vT_none]

lemma matEntry_psModel_vT_infty (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (t : D.Fq) :
    matEntry (D.psModel α β M) (D.vT t) (D.psVec β none) = 0 := by
  rw [matEntry_eq_sum_mulVec, psModel_mulVec_infty D α β M hc]
  simp [FieldData.psVec, vT_none]

lemma wVec_eq_sum (D : FieldData) (β δ : D.Lab) :
    D.wVec β δ = isqrt (D.q - 1) •
      ∑ t : D.Fqˣ, (D.chi δ (t : D.Fq) * D.chi (-β) (t : D.Fq)) • D.vT (t : D.Fq) := by
  ext y
  simp only [FieldData.wVec, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  congr 1
  exact sum_ne_zero_eq_sum_units D (fun t => D.chi δ t * D.chi (-β) t * D.vT t y)

lemma matEntry_psModel_wVec_wVec (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (δ δ' : D.Lab) :
    matEntry (D.psModel α β M) (D.wVec β δ) (D.wVec β δ') =
      D.RB (.inr (α + β)) M δ δ' := by
  rw [wVec_eq_sum, wVec_eq_sum, matEntry_smul_left, matEntry_smul_right,
    matEntry_sum_left]
  simp_rw [matEntry_sum_right, matEntry_smul_left, matEntry_smul_right, matEntry_psModel_vT D α β M hc ha hd]
  have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℝ) - 1 : ℂ)⁻¹ := by
    have h1 := conj_isqrt_mul_isqrt (q_sub_one_pos D)
    rw [q_sub_one_real] at h1
    simpa [Complex.ofReal_sub, Complex.ofReal_one] using h1
  have hL : conj (isqrt (D.q - 1)) * (isqrt (D.q - 1) *
      ∑ s : D.Fqˣ, ∑ t : D.Fqˣ,
        conj (D.chi δ (s : D.Fq) * D.chi (-β) (s : D.Fq)) *
          ((D.chi δ' (t : D.Fq) * D.chi (-β) (t : D.Fq)) *
            if (s : D.Fq) = M 1 1 / M 0 0 * (t : D.Fq) then
              D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))
            else 0)) =
      ((D.q : ℝ) - 1 : ℂ)⁻¹ * ∑ s : D.Fqˣ, ∑ t : D.Fqˣ,
        if (s : D.Fq) = M 1 1 / M 0 0 * (t : D.Fq) then
          conj (D.chi δ (s : D.Fq)) * (D.chi (α + β) (M 1 1) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))) *
            D.chi δ' (t : D.Fq)
        else 0 := by
    rw [← mul_assoc, hisqrt]
    congr 1
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    split_ifs with hst
    · simp only [map_mul, conj_chi, neg_neg]
      have hcb : D.chi β (s : D.Fq) =
          D.chi β (M 1 1) * D.chi (-β) (M 0 0) * D.chi β (t : D.Fq) := by
        rw [hst, chi_mul D β (div_ne_zero hd ha) t.ne_zero, chi_div D β hd ha]
      have ha1 : D.chi (-β) (M 0 0) * D.chi β (M 0 0) = 1 := by
        rw [← chi_add, neg_add_cancel, chi_zero_lab D ha]
      have ht1 : D.chi β (t : D.Fq) * D.chi (-β) (t : D.Fq) = 1 := by
        rw [← chi_add, add_neg_cancel, chi_zero_lab D t.ne_zero]
      have hd1 : D.chi β (M 1 1) * D.chi α (M 1 1) = D.chi (α + β) (M 1 1) := by
        rw [← chi_add, add_comm]
      calc D.chi (-δ) (s : D.Fq) * D.chi β (s : D.Fq) *
            ((D.chi δ' (t : D.Fq) * D.chi (-β) (t : D.Fq)) *
              (D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))))
          = D.chi (-δ) (s : D.Fq) *
              ((D.chi β (M 1 1) * D.chi α (M 1 1)) *
                (D.chi (-β) (M 0 0) * D.chi β (M 0 0)) *
                (D.chi β (t : D.Fq) * D.chi (-β) (t : D.Fq)) *
                D.psi (M 0 1 / M 0 0 * (t : D.Fq))) * D.chi δ' (t : D.Fq) := by
            rw [hcb]; ring
        _ = D.chi (-δ) (s : D.Fq) *
              (D.chi (α + β) (M 1 1) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))) *
              D.chi δ' (t : D.Fq) := by
            rw [hd1, ha1, ht1]; ring
    · ring
  rw [hL]
  symm
  simp only [FieldData.RB, matEntry, FieldData.borelModel, FieldData.multVec, map_mul]
  have hR : ∑ s : D.Fqˣ, ∑ t : D.Fqˣ,
      conj (isqrt (D.q - 1)) * conj (D.chi δ (s : D.Fq)) *
        (if (s : D.Fq) = M 1 1 / M 0 0 * (t : D.Fq) then
          D.chi (α + β) (M 1 1) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))
        else 0) * (isqrt (D.q - 1) * D.chi δ' (t : D.Fq)) =
      ((D.q : ℝ) - 1 : ℂ)⁻¹ * ∑ s : D.Fqˣ, ∑ t : D.Fqˣ,
        if (s : D.Fq) = M 1 1 / M 0 0 * (t : D.Fq) then
          conj (D.chi δ (s : D.Fq)) * (D.chi (α + β) (M 1 1) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))) *
            D.chi δ' (t : D.Fq)
        else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · calc conj (isqrt (D.q - 1)) * conj (D.chi δ (s : D.Fq)) *
            (D.chi (α + β) (M 1 1) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))) *
            (isqrt (D.q - 1) * D.chi δ' (t : D.Fq))
          = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) *
              (conj (D.chi δ (s : D.Fq)) *
                (D.chi (α + β) (M 1 1) * D.psi (M 0 1 / M 0 0 * (t : D.Fq))) *
                D.chi δ' (t : D.Fq)) := by ring
        _ = ((D.q : ℝ) - 1 : ℂ)⁻¹ * _ := by rw [hisqrt]
    · simp
  exact hR

lemma matEntry_psModel_infty_wVec (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (δ : D.Lab) :
    matEntry (D.psModel α β M) (D.psVec β none) (D.wVec β δ) = 0 := by
  rw [wVec_eq_sum, matEntry_smul_right, matEntry_sum_right]
  simp_rw [matEntry_smul_right, matEntry_psModel_infty_vT D α β M hc ha hd]
  simp

lemma matEntry_psModel_wVec_infty (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (δ : D.Lab) :
    matEntry (D.psModel α β M) (D.wVec β δ) (D.psVec β none) = 0 := by
  rw [wVec_eq_sum, matEntry_smul_left, matEntry_sum_left]
  simp_rw [matEntry_smul_left, matEntry_psModel_vT_infty D α β M hc]
  simp

lemma matEntry_psModel_v0_wVec (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (δ : D.Lab) :
    matEntry (D.psModel α β M) (D.vT 0) (D.wVec β δ) = 0 := by
  rw [wVec_eq_sum, matEntry_smul_right, matEntry_sum_right]
  simp_rw [matEntry_smul_right, matEntry_psModel_vT D α β M hc ha hd]
  have hterm : ∀ t : D.Fqˣ, (if (0 : D.Fq) = M 1 1 / M 0 0 * (t : D.Fq) then
      D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * (t : D.Fq)) else 0) = 0 := by
    intro t
    have hne : (0 : D.Fq) ≠ M 1 1 / M 0 0 * (t : D.Fq) :=
      (mul_ne_zero (div_ne_zero hd ha) t.ne_zero).symm
    simp [hne]
  simp only [hterm, mul_zero, Finset.sum_const_zero]

lemma matEntry_psModel_wVec_v0 (D : FieldData) (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq)
    (hc : M 1 0 = 0) (ha : M 0 0 ≠ 0) (hd : M 1 1 ≠ 0) (δ : D.Lab) :
    matEntry (D.psModel α β M) (D.wVec β δ) (D.vT 0) = 0 := by
  rw [wVec_eq_sum, matEntry_smul_left, matEntry_sum_left]
  simp_rw [matEntry_smul_left, matEntry_psModel_vT D α β M hc ha hd]
  have hterm : ∀ s : D.Fqˣ, (if (s : D.Fq) = M 1 1 / M 0 0 * (0 : D.Fq) then
      D.chi α (M 1 1) * D.chi β (M 0 0) * D.psi (M 0 1 / M 0 0 * (0 : D.Fq)) else 0) = 0 := by
    intro s
    simp [s.ne_zero]
  simp_rw [hterm]
  simp

lemma stVec_none_eq (D : FieldData) (α : D.Lab) :
    D.stVec α none =
      (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) • D.psVec α none -
        isqrt (D.q + 1) • D.vT 0 := by
  ext y
  cases y <;> simp [FieldData.stVec, FieldData.psVec, FieldData.vT, psi_zero, mul_assoc]

/-! ### Clauses 1–7 helpers -/

lemma trace_eq_of_repEquivOn {G ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {S : Set G} {R : G → Matrix ι ι ℂ} {R' : G → Matrix κ κ ℂ}
    (h : RepEquivOn S R R') {g : G} (hg : g ∈ S) :
    Matrix.trace (R g) = Matrix.trace (R' g) := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  have h1 : R' g = A * R g * B := by
    calc R' g = R' g * 1 := (Matrix.mul_one _).symm
      _ = R' g * (A * B) := by rw [hAB]
      _ = (R' g * A) * B := (Matrix.mul_assoc _ _ _).symm
      _ = (A * R g) * B := by rw [hinter g hg]
  rw [h1, Matrix.trace_mul_cycle, hBA, Matrix.one_mul]

lemma not_repEquivOn_inl_inr (D : FieldData) (u v w : D.Lab) :
    ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
        (fun g : D.G => D.RB (.inl (u, v)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
        (fun g : D.G => D.RB (.inr w) (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  intro heq
  let M : Matrix (Fin 2) (Fin 2) D.Fq := !![1, 1; 0, 1]
  let Minv : Matrix (Fin 2) (Fin 2) D.Fq := !![1, -1; 0, 1]
  let g : D.G := ⟨M, Minv,
    by ext i j; fin_cases i <;> fin_cases j <;> simp [M, Minv],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [M, Minv]⟩
  have hg : g ∈ {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0} := by
    simp [g, M]
  have htr := trace_eq_of_repEquivOn heq hg
  have htr1 : Matrix.trace (D.RB (.inl (u, v)) (g : Matrix (Fin 2) (Fin 2) D.Fq)) = 1 := by
    change ∑ _ : Unit, D.RB (.inl (u, v)) M () () = 1
    simp [FieldData.RB, M, chi_one]
  have htr2 : Matrix.trace (D.RB (.inr w) (g : Matrix (Fin 2) (Fin 2) D.Fq)) = -1 := by
    change ∑ δ : D.Lab, matEntry (D.borelModel w (M 0 0) (M 0 1) (M 1 1)) (D.multVec δ) (D.multVec δ) = -1
    have hdiag : ∀ δ : D.Lab,
        matEntry (D.borelModel w (M 0 0) (M 0 1) (M 1 1)) (D.multVec δ) (D.multVec δ) =
          ((D.q : ℝ) - 1 : ℂ)⁻¹ * ∑ x : D.Fqˣ, D.psi (x : D.Fq) := by
      intro δ
      simp only [matEntry, FieldData.borelModel, FieldData.multVec, M, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, div_one, one_mul,
        chi_one]
      have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℝ) - 1 : ℂ)⁻¹ := by
        have h1 := conj_isqrt_mul_isqrt (q_sub_one_pos D)
        rw [q_sub_one_real] at h1
        simpa [Complex.ofReal_sub, Complex.ofReal_one] using h1
      calc ∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
            conj (isqrt (D.q - 1) * D.chi δ (y : D.Fq)) *
              (if (y : D.Fq) = (x : D.Fq) then D.psi (x : D.Fq) else 0) *
              (isqrt (D.q - 1) * D.chi δ (x : D.Fq))
          = ∑ x : D.Fqˣ, ∑ y : D.Fqˣ,
              if y = x then
                (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) *
                  (conj (D.chi δ (x : D.Fq)) * D.chi δ (x : D.Fq)) * D.psi (x : D.Fq)
              else 0 := by
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
                by_cases hyx : y = x
                · subst hyx; simp [mul_comm, mul_left_comm, mul_assoc]
                · have hne : (y : D.Fq) ≠ (x : D.Fq) := fun h => hyx (Units.ext h)
                  simp [hyx, hne]
        _ = ∑ x : D.Fqˣ, ((D.q : ℝ) - 1 : ℂ)⁻¹ * D.psi (x : D.Fq) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_eq_single x (fun y _ hy => by simp [hy])
            (fun hx => absurd (Finset.mem_univ x) hx)]
          simp only [↓reduceIte, hisqrt, conj_chi]
          have h1 : D.chi (-δ) (x : D.Fq) * D.chi δ (x : D.Fq) = 1 := by
            rw [← chi_add, neg_add_cancel, chi_zero_lab D x.ne_zero]
          rw [h1, mul_one]
        _ = ((D.q : ℝ) - 1 : ℂ)⁻¹ * ∑ x : D.Fqˣ, D.psi (x : D.Fq) := by
          rw [← Finset.mul_sum]
    simp_rw [hdiag, Finset.sum_const, Finset.card_univ, card_lab, nsmul_eq_mul]
    have hcard : ((D.q - 1 : ℕ) : ℂ) = ((D.q : ℝ) - 1 : ℂ) := by
      have := D.one_lt_q
      rw [Nat.cast_sub (by omega)]
      simp
    have hmul : ((D.q : ℝ) - 1 : ℂ) * ((D.q : ℝ) - 1 : ℂ)⁻¹ = 1 := by
      have hne : ((D.q : ℝ) - 1 : ℂ) ≠ 0 := by simpa using q_sub_one_complex_ne D
      exact mul_inv_cancel₀ hne
    rw [hcard, ← mul_assoc, hmul, one_mul]
    rw [← sum_ne_zero_eq_sum_units]
    have hsplit : (∑ x : D.Fq, D.psi x) =
        (∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.psi x) +
          (∑ x ∈ Finset.univ.filter (fun x : D.Fq => ¬ (x ≠ 0)), D.psi x) :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : D.Fq => x ≠ 0) D.psi).symm
    have h0 : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => ¬ (x ≠ 0)), D.psi x = 1 := by
      have hf : Finset.univ.filter (fun x : D.Fq => ¬ (x ≠ 0)) = {0} := by
        ext x; simp
      rw [hf, Finset.sum_singleton, psi_zero]
    have hall : ∑ x : D.Fq, D.psi x = 0 := by
      simpa using sum_psi D 1
    linear_combination hsplit.symm + hall - h0
  rw [htr1, htr2] at htr
  norm_num at htr

end GL2QFT.Lemma67

open GL2QFT GL2QFT.FieldData GL2QFT.Lemma67
open scoped ComplexConjugate

theorem solution (D : FieldData) :
    (∀ (α β : D.Lab) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 →
      D.RB (.inl (α, β)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () () =
        D.chi α ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) * D.chi β ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) ∧
    (∀ (γ : D.Lab) (g : D.G) (δ δ' : D.Lab), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 →
      D.RB (.inr γ) (g : Matrix (Fin 2) (Fin 2) D.Fq) δ δ' =
        if δ = δ' then D.chi δ ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
          D.chi (γ - δ) ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) else 0) ∧
    (∀ (α : D.Lab) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      D.R (.inl α) g () () = D.RB (.inl (α, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()) ∧
    (∀ (α : D.Lab) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      ∀ i j : Option D.Lab, D.R (.inr (.inl α)) g i j =
        match i, j with
        | none, none => D.RB (.inl (α, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()
        | some δ, some δ' => D.RB (.inr (2 * α)) (g : Matrix (Fin 2) (Fin 2) D.Fq) δ δ'
        | _, _ => 0) ∧
    (∀ (ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val}) (g : D.G),
      (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      ∀ i j : Option (Option D.Lab), D.R (.inr (.inr (.inl ab))) g i j =
        match i, j with
        | none, none => D.RB (.inl (ab.1.1, ab.1.2)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()
        | some none, some none => D.RB (.inl (ab.1.2, ab.1.1)) (g : Matrix (Fin 2) (Fin 2) D.Fq) () ()
        | some (some δ), some (some δ') =>
            D.RB (.inr (ab.1.1 + ab.1.2)) (g : Matrix (Fin 2) (Fin 2) D.Fq) δ δ'
        | _, _ => 0) ∧
    (∀ (k : {k : D.Lab2 // D.IsCuspLabel k}) (g : D.G), (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 →
      ∀ i j : D.Lab, D.R (.inr (.inr (.inr k))) g i j =
        D.RB (.inr (D.restrLab k.1)) (g : Matrix (Fin 2) (Fin 2) D.Fq) i j) ∧
    ((∀ γ δ δ' : D.Lab, δ ≠ δ' → ∃ g : D.G, (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 ∧
        D.chi δ ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) * D.chi (γ - δ) ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) ≠
          D.chi δ' ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
            D.chi (γ - δ') ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) ∧
      (∀ α : D.Lab, ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
          (fun g : D.G => D.RB (.inl (α, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
          (fun g : D.G => D.RB (.inr (2 * α)) (g : Matrix (Fin 2) (Fin 2) D.Fq))) ∧
      (∀ α β : D.Lab, α ≠ β →
        ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
            (fun g : D.G => D.RB (.inl (α, β)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
            (fun g : D.G => D.RB (.inl (β, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq)) ∧
        ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
            (fun g : D.G => D.RB (.inl (α, β)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
            (fun g : D.G => D.RB (.inr (α + β)) (g : Matrix (Fin 2) (Fin 2) D.Fq)) ∧
        ¬ RepEquivOn {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
            (fun g : D.G => D.RB (.inl (β, α)) (g : Matrix (Fin 2) (Fin 2) D.Fq))
            (fun g : D.G => D.RB (.inr (α + β)) (g : Matrix (Fin 2) (Fin 2) D.Fq)))) := by
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7⟩
  case c1 =>
    intro α β g _ _
    rfl
  case c2 =>
    intro γ g δ δ' hc hb
    obtain ⟨ha, hd⟩ := borel_diag_ne_zero D g hc
    set M : Matrix (Fin 2) (Fin 2) D.Fq := ↑g
    change matEntry (D.borelModel γ (M 0 0) (M 0 1) (M 1 1)) (D.multVec δ) (D.multVec δ') = _
    simp only [matEntry, FieldData.borelModel, FieldData.multVec, hb, zero_div, zero_mul, psi_zero,
      mul_one]
    let u_da : D.Fqˣ := Units.mk0 (M 1 1 / M 0 0) (div_ne_zero hd ha)
    have hisqrt : conj (isqrt (D.q - 1)) * isqrt (D.q - 1) = ((D.q : ℝ) - 1 : ℂ)⁻¹ := by
      have h1 := conj_isqrt_mul_isqrt (q_sub_one_pos D)
      rw [q_sub_one_real] at h1
      simpa [Complex.ofReal_sub, Complex.ofReal_one] using h1
    have hsum : ∑ y : D.Fqˣ, ∑ x : D.Fqˣ,
        conj (isqrt (D.q - 1) * D.chi δ (y : D.Fq)) *
          (if (y : D.Fq) = M 1 1 / M 0 0 * (x : D.Fq) then D.chi γ (M 1 1) else 0) *
          (isqrt (D.q - 1) * D.chi δ' (x : D.Fq)) =
        ((D.q : ℝ) - 1 : ℂ)⁻¹ * D.chi δ (M 0 0) * D.chi (γ - δ) (M 1 1) *
          ∑ x : D.Fqˣ, D.chi (δ' - δ) (x : D.Fq) := by
      rw [Finset.sum_comm]
      have hinner : ∀ x : D.Fqˣ,
          (∑ y : D.Fqˣ, conj (isqrt (D.q - 1) * D.chi δ (y : D.Fq)) *
            (if (y : D.Fq) = M 1 1 / M 0 0 * (x : D.Fq) then D.chi γ (M 1 1) else 0) *
            (isqrt (D.q - 1) * D.chi δ' (x : D.Fq))) =
          ((D.q : ℝ) - 1 : ℂ)⁻¹ * D.chi δ (M 0 0) * D.chi (γ - δ) (M 1 1) *
            D.chi (δ' - δ) (x : D.Fq) := by
        intro x
        rw [Finset.sum_eq_single (u_da * x)]
        · have hy : ((u_da * x : D.Fqˣ) : D.Fq) = M 1 1 / M 0 0 * (x : D.Fq) := by
            simp [u_da]
          simp only [hy, ↓reduceIte, map_mul, conj_chi]
          have hcd : D.chi (-δ) (M 1 1 / M 0 0 * (x : D.Fq)) =
              D.chi (-δ) (M 1 1) * D.chi δ (M 0 0) * D.chi (-δ) (x : D.Fq) := by
            rw [chi_mul D (-δ) (div_ne_zero hd ha) x.ne_zero, chi_div D (-δ) hd ha, neg_neg]
          rw [hcd]
          have hgd : D.chi (-δ) (M 1 1) * D.chi γ (M 1 1) = D.chi (γ - δ) (M 1 1) := by
            rw [← chi_add, add_comm, sub_eq_add_neg]
          have hdx : D.chi (-δ) (x : D.Fq) * D.chi δ' (x : D.Fq) = D.chi (δ' - δ) (x : D.Fq) := by
            rw [← chi_add, add_comm, sub_eq_add_neg]
          calc conj (isqrt (D.q - 1)) * (D.chi (-δ) (M 1 1) * D.chi δ (M 0 0) * D.chi (-δ) (x : D.Fq)) *
                D.chi γ (M 1 1) * (isqrt (D.q - 1) * D.chi δ' (x : D.Fq))
              = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) * D.chi δ (M 0 0) *
                  (D.chi (-δ) (M 1 1) * D.chi γ (M 1 1)) *
                  (D.chi (-δ) (x : D.Fq) * D.chi δ' (x : D.Fq)) := by ring
            _ = ((D.q : ℝ) - 1 : ℂ)⁻¹ * D.chi δ (M 0 0) * D.chi (γ - δ) (M 1 1) *
                  D.chi (δ' - δ) (x : D.Fq) := by rw [hisqrt, hgd, hdx]
        · intro y _ hyne
          have hne : (y : D.Fq) ≠ M 1 1 / M 0 0 * (x : D.Fq) := by
            intro heq
            apply hyne
            ext
            simpa [u_da] using heq
          simp [hne]
        · intro hmem
          exact absurd (Finset.mem_univ (u_da * x)) hmem
      simp_rw [hinner, ← Finset.mul_sum]
    rw [hsum, sum_chi_units]
    by_cases hdd : δ = δ'
    · subst hdd
      simp only [sub_self, ↓reduceIte]
      have hcard : ((D.q - 1 : ℕ) : ℂ) = ((D.q : ℝ) - 1 : ℂ) := by
        have := D.one_lt_q
        rw [Nat.cast_sub (by omega)]
        simp
      have hmul : ((D.q : ℝ) - 1 : ℂ)⁻¹ * ((D.q : ℝ) - 1 : ℂ) = 1 :=
        inv_mul_cancel₀ (by simpa using q_sub_one_complex_ne D)
      rw [hcard]
      calc ((D.q : ℝ) - 1 : ℂ)⁻¹ * D.chi δ (M 0 0) * D.chi (γ - δ) (M 1 1) * ((D.q : ℝ) - 1 : ℂ)
          = (((D.q : ℝ) - 1 : ℂ)⁻¹ * ((D.q : ℝ) - 1 : ℂ)) *
              (D.chi δ (M 0 0) * D.chi (γ - δ) (M 1 1)) := by ring
        _ = D.chi δ (M 0 0) * D.chi (γ - δ) (M 1 1) := by rw [hmul, one_mul]
    · have hsub : δ' - δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hdd)
      simp [hdd, hsub]
  case c3 =>
    intro α g hc
    obtain ⟨ha, hd⟩ := borel_diag_ne_zero D g hc
    set M : Matrix (Fin 2) (Fin 2) D.Fq := ↑g
    change matEntry (D.psModel α α M) (D.detVec α) (D.detVec α) =
      D.chi α (M 0 0) * D.chi α (M 1 1)
    have hq1 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith [q_pos D]
    have hisqrt : conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = ((D.q : ℝ) + 1 : ℂ)⁻¹ := by
      have h1 := conj_isqrt_mul_isqrt hq1
      simpa [Complex.ofReal_add, Complex.ofReal_one] using h1
    have hsum : (∑ y : Option D.Fq, ∑ x : Option D.Fq,
        conj (D.detVec α y) * D.psModel α α M y x * D.detVec α x) =
        ∑ x : Option D.Fq, (((D.q : ℝ) + 1 : ℂ)⁻¹ * (D.chi α (M 0 0) * D.chi α (M 1 1))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      cases x with
      | none =>
        rw [Fintype.sum_option]
        simp only [FieldData.psModel, FieldData.detVec, hc, ne_eq, not_true_eq_false, ↓reduceIte,
          Option.some_ne_none, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, map_mul,
          conj_chi]
        have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
        have h1 : D.chi (-α) (-1) * D.chi α (-1) = 1 := by
          rw [← chi_add, neg_add_cancel, chi_zero_lab D hm1]
        calc conj (isqrt (D.q + 1)) * D.chi (-α) (-1) * (D.chi α (M 0 0) * D.chi α (M 1 1)) *
              (isqrt (D.q + 1) * D.chi α (-1))
            = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) * (D.chi (-α) (-1) * D.chi α (-1)) *
                (D.chi α (M 0 0) * D.chi α (M 1 1)) := by ring
          _ = ((D.q : ℝ) + 1 : ℂ)⁻¹ * (D.chi α (M 0 0) * D.chi α (M 1 1)) := by
              rw [hisqrt, h1, mul_one]
      | some x' =>
        let y₀ : Option D.Fq := some ((M 0 0 * x' + M 0 1) / M 1 1)
        rw [Finset.sum_eq_single y₀]
        · simp only [y₀, FieldData.psModel, FieldData.detVec, hc, zero_mul, zero_add, mul_zero,
            sub_zero, hd, ne_eq, not_false_eq_true, ↓reduceIte, conj_isqrt, mul_one]
          rw [mul_div_cancel_right₀ _ hd]
          calc isqrt (D.q + 1) * (D.chi α (M 1 1) * D.chi α (M 0 0)) * isqrt (D.q + 1)
              = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
                  (D.chi α (M 0 0) * D.chi α (M 1 1)) := by rw [conj_isqrt]; ring
            _ = ((D.q : ℝ) + 1 : ℂ)⁻¹ * (D.chi α (M 0 0) * D.chi α (M 1 1)) := by rw [hisqrt]
        · intro y _ hyne
          simp only [FieldData.psModel, hc, zero_mul, zero_add, hd, ne_eq, not_false_eq_true,
            ↓reduceIte]
          have hne : y ≠ some ((M 0 0 * x' + M 0 1) / M 1 1) := hyne
          simp [hne]
        · intro hmem
          exact absurd (Finset.mem_univ y₀) hmem
    change (∑ y : Option D.Fq, ∑ x : Option D.Fq,
      conj (D.detVec α y) * D.psModel α α M y x * D.detVec α x) = _
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_option, card_fq, nsmul_eq_mul]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ (by simpa using q_add_one_complex_ne D), one_mul]
  case c4 =>
    intro α g hc i j
    obtain ⟨ha, hd⟩ := borel_diag_ne_zero D g hc
    set M : Matrix (Fin 2) (Fin 2) D.Fq := ↑g
    change matEntry (D.psModel α α M) (D.stVec α i) (D.stVec α j) = _
    cases i <;> cases j
    · -- (none, none)
      have hst : D.stVec α none =
          (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) • D.psVec α none -
            isqrt (D.q + 1) • D.vT 0 := stVec_none_eq D α
      rw [hst]
      simp only [matEntry_sub_left, matEntry_sub_right, matEntry_smul_left, matEntry_smul_right,
        matEntry_psModel_infty_infty D α α M hc,
        matEntry_psModel_infty_vT D α α M hc ha hd 0,
        matEntry_psModel_vT_infty D α α M hc 0]
      have hv0 : matEntry (D.psModel α α M) (D.vT 0) (D.vT 0) =
          D.chi α (M 0 0) * D.chi α (M 1 1) := by
        rw [matEntry_psModel_vT D α α M hc ha hd 0 0]
        simp [psi_zero, mul_comm]
      rw [hv0]
      have hq1 : (0 : ℝ) < (D.q : ℝ) + 1 := by linarith [q_pos D]
      have hisqrt1 : conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = ((D.q : ℝ) + 1 : ℂ)⁻¹ := by
        have h1 := conj_isqrt_mul_isqrt hq1
        simpa [Complex.ofReal_add, Complex.ofReal_one] using h1
      have hsq : conj (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ) = (D.q : ℂ) := by
        rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (q_pos D).le]
        simp
      have hm1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
      have hchi1 : conj (D.chi α (-1)) * D.chi α (-1) = 1 := by
        rw [conj_chi, ← chi_add, neg_add_cancel, chi_zero_lab D hm1]
      have hcoef : conj (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) *
            (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) +
            conj (isqrt (D.q + 1)) * isqrt (D.q + 1) = 1 := by
        calc conj (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) *
              (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) +
              conj (isqrt (D.q + 1)) * isqrt (D.q + 1)
            = (conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
                ((conj (Real.sqrt D.q : ℂ) * (Real.sqrt D.q : ℂ)) *
                  (conj (D.chi α (-1)) * D.chi α (-1))) +
                conj (isqrt (D.q + 1)) * isqrt (D.q + 1) := by
              simp only [map_mul]; ring
          _ = ((D.q : ℝ) + 1 : ℂ)⁻¹ * ((D.q : ℂ) * 1) + ((D.q : ℝ) + 1 : ℂ)⁻¹ := by
              rw [hisqrt1, hsq, hchi1]
          _ = ((D.q : ℂ) + 1)⁻¹ * ((D.q : ℂ) + 1) := by push_cast; ring
          _ = 1 := inv_mul_cancel₀ (q_add_one_complex_ne D)
      change _ = D.chi α (M 0 0) * D.chi α (M 1 1)
      calc _ = (conj (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) *
                (isqrt (D.q + 1) * (Real.sqrt D.q : ℂ) * D.chi α (-1)) +
                conj (isqrt (D.q + 1)) * isqrt (D.q + 1)) *
                (D.chi α (M 0 0) * D.chi α (M 1 1)) := by ring
        _ = D.chi α (M 0 0) * D.chi α (M 1 1) := by rw [hcoef, one_mul]
    · -- (none, some δ)
      rw [stVec_none_eq]
      simp only [FieldData.stVec, matEntry_sub_left, matEntry_smul_left,
        matEntry_psModel_infty_wVec D α α M hc ha hd,
        matEntry_psModel_v0_wVec D α α M hc ha hd,
        mul_zero, sub_self]
    · -- (some δ, none)
      rw [stVec_none_eq]
      simp only [FieldData.stVec, matEntry_sub_right, matEntry_smul_right,
        matEntry_psModel_wVec_infty D α α M hc,
        matEntry_psModel_wVec_v0 D α α M hc ha hd,
        mul_zero, sub_self]
    · -- (some δ, some δ')
      simp only [FieldData.stVec]
      rw [matEntry_psModel_wVec_wVec D α α M hc ha hd, two_mul]
  case c5 =>
    intro ab g hc i j
    obtain ⟨ha, hd⟩ := borel_diag_ne_zero D g hc
    set M : Matrix (Fin 2) (Fin 2) D.Fq := ↑g
    change matEntry (D.psModel ab.1.1 ab.1.2 M) (D.psVec ab.1.2 i) (D.psVec ab.1.2 j) = _
    rcases i with _ | (_ | δ) <;> rcases j with _ | (_ | δ')
    · exact matEntry_psModel_infty_infty D ab.1.1 ab.1.2 M hc
    · rw [← vT_zero D ab.1.2]
      exact matEntry_psModel_infty_vT D ab.1.1 ab.1.2 M hc ha hd 0
    · exact matEntry_psModel_infty_wVec D ab.1.1 ab.1.2 M hc ha hd δ'
    · rw [← vT_zero D ab.1.2]
      exact matEntry_psModel_vT_infty D ab.1.1 ab.1.2 M hc 0
    · rw [← vT_zero D ab.1.2, matEntry_psModel_vT D ab.1.1 ab.1.2 M hc ha hd 0 0]
      simp [psi_zero, FieldData.RB, mul_comm]
    · rw [← vT_zero D ab.1.2]
      exact matEntry_psModel_v0_wVec D ab.1.1 ab.1.2 M hc ha hd δ'
    · exact matEntry_psModel_wVec_infty D ab.1.1 ab.1.2 M hc δ
    · rw [← vT_zero D ab.1.2]
      exact matEntry_psModel_wVec_v0 D ab.1.1 ab.1.2 M hc ha hd δ
    · exact matEntry_psModel_wVec_wVec D ab.1.1 ab.1.2 M hc ha hd δ δ'
  case c6 =>
    intro k g hc i j
    simp [FieldData.R, FieldData.piModel, FieldData.RB, hc]
  case c7 =>
    refine ⟨?c7a, ?c7b, ?c7c⟩
    case c7a =>
      intro γ δ δ' hne
      let M : Matrix (Fin 2) (Fin 2) D.Fq := !![D.gen, 0; 0, 1]
      let Minv : Matrix (Fin 2) (Fin 2) D.Fq := !![D.gen⁻¹, 0; 0, 1]
      have hg0 : D.gen ≠ 0 := gen_ne_zero D
      let g : D.G := ⟨M, Minv,
        by ext i j; fin_cases i <;> fin_cases j <;> simp [M, Minv, mul_inv_cancel₀ hg0],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [M, Minv, inv_mul_cancel₀ hg0]⟩
      refine ⟨g, by simp [g, M], by simp [g, M], ?_⟩
      simp only [g, M, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, chi_one, mul_one]
      exact chi_gen_ne D hne
    case c7b =>
      intro α
      exact not_repEquivOn_inl_inr D α α (2 * α)
    case c7c =>
      intro α β hab
      refine ⟨?_, not_repEquivOn_inl_inr D α β (α + β), not_repEquivOn_inl_inr D β α (α + β)⟩
      intro heq
      let M : Matrix (Fin 2) (Fin 2) D.Fq := !![D.gen, 0; 0, 1]
      let Minv : Matrix (Fin 2) (Fin 2) D.Fq := !![D.gen⁻¹, 0; 0, 1]
      have hg0 : D.gen ≠ 0 := gen_ne_zero D
      let g : D.G := ⟨M, Minv,
        by ext i j; fin_cases i <;> fin_cases j <;> simp [M, Minv, mul_inv_cancel₀ hg0],
        by ext i j; fin_cases i <;> fin_cases j <;> simp [M, Minv, inv_mul_cancel₀ hg0]⟩
      have hg : g ∈ {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0} := by
        simp [g, M]
      have htr := trace_eq_of_repEquivOn heq hg
      change (∑ _ : Unit, D.RB (.inl (α, β)) M () ()) = ∑ _ : Unit, D.RB (.inl (β, α)) M () () at htr
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul,
        FieldData.RB, M, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, chi_one, mul_one] at htr
      exact chi_gen_ne D hab htr
