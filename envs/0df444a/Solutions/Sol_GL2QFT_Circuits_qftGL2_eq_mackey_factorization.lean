-- Prove2me | solution 1 for GL2QFT.Circuits.qftGL2_eq_mackey_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T08:45:14.080424+00:00
-- url     : https://prove2.me/submissions/180cb1e1-3a38-40a6-b141-824b4d42bd19

import Definitions.Def_GL2QFT_Circuits_Leaves
import Definitions.Def_GL2QFT_Supplement_Mackey
import Theorems.Thm_GL2QFT_Supplement_theorem_5_4
import Theorems.Thm_GL2QFT_lemma_3_5
import Theorems.Thm_GL2QFT_lemma_6_7
import Theorems.Thm_GL2QFT_table_2_completeness
import Theorems.Thm_GL2QFT_Circuits_qftB_algebraic_factorization
import Theorems.Thm_GL2QFT_Circuits_phi_isometries

noncomputable section

open Classical
open scoped Matrix ComplexConjugate

namespace GL2QFT_MackeyFactorization_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData GL2QFT.Induction GL2QFT.Supplement
open GL2QFT.Supplement.TotalA GL2QFT.Supplement.Mackey

/-! ### Part 1: Finite field, character, and basic matrix/isometry lemmas -/

lemma card_Fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  have hdim : Module.finrank (ZMod D.p) D.Fq = D.r := by
    rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]
  have hc := Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq)
  rw [hdim, ZMod.card] at hc
  exact hc

lemma card_Fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  have hdim : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  have hc := Module.card_eq_pow_finrank (K := D.Fq) (V := D.Fq2)
  rw [hdim, card_Fq] at hc
  exact hc

lemma card_Fq_units (D : FieldData) : Fintype.card D.Fqˣ = D.q - 1 := by
  rw [Fintype.card_units, card_Fq]

lemma card_Lab (D : FieldData) : Fintype.card D.Lab = D.q - 1 := by
  rw [ZMod.card]

lemma algebraMap_gen (D : FieldData) : algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  unfold FieldData.gen
  have hnorm := @FiniteField.algebraMap_norm_eq_pow D.Fq D.Fq2 _ _ _ _ D.h
  rw [hnorm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_Fq2, card_Fq]
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]; ring
  rw [hsq, Nat.mul_div_cancel _ (by omega)]

lemma orderOf_gen (D : FieldData) : orderOf D.gen = D.q - 1 := by
  let f : D.Fq →* D.Fq2 := (algebraMap D.Fq D.Fq2).toMonoidHom
  have hf : Function.Injective f := (algebraMap D.Fq D.Fq2).injective
  rw [← orderOf_injective f hf D.gen]
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = D.q - 1
  rw [algebraMap_gen, orderOf_pow' D.h (by omega), D.h_order]
  change (D.q ^ 2 - 1) / ((D.q ^ 2 - 1).gcd (D.q + 1)) = D.q - 1
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]; ring
  rw [hsq, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h
  have ho := orderOf_gen D
  rw [h, orderOf_zero] at ho
  have := D.one_lt_q
  omega

def uGen (D : FieldData) : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)

lemma orderOf_uGen (D : FieldData) : orderOf (uGen D) = D.q - 1 := by
  rw [← orderOf_injective (Units.coeHom D.Fq) Units.val_injective (uGen D)]
  exact orderOf_gen D

lemma exists_pow_gen (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : ∃ n : ℕ, D.gen ^ n = x := by
  let u := uGen D
  let φ : Fin (D.q - 1) → D.Fqˣ := fun k => u ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have heq : u ^ i.val = u ^ j.val := hij
    rw [pow_eq_pow_iff_modEq, orderOf_uGen] at heq
    change i.val % (D.q - 1) = j.val % (D.q - 1) at heq
    ext
    rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at heq
  have hcard : Fintype.card (Fin (D.q - 1)) = Fintype.card D.Fqˣ := by
    rw [Fintype.card_fin, card_Fq_units]
  have hbij := (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩
  obtain ⟨k, hk⟩ := hbij.2 (Units.mk0 x hx)
  exact ⟨k.val, by simpa [φ, u, uGen] using congrArg Units.val hk⟩

lemma gen_pow_dlog (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  unfold FieldData.dlog
  rw [dif_pos (exists_pow_gen D hx)]
  exact Nat.find_spec (exists_pow_gen D hx)

lemma dlog_one (D : FieldData) : D.dlog 1 = 0 := by
  unfold FieldData.dlog
  have h : ∃ n : ℕ, D.gen ^ n = 1 := ⟨0, pow_zero _⟩
  rw [dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h (pow_zero _))

lemma dlog_gen (D : FieldData) (hq : 2 < D.q) : D.dlog D.gen = 1 := by
  have hex : ∃ m : ℕ, D.gen ^ m = D.gen := ⟨1, pow_one _⟩
  simp only [FieldData.dlog, hex, ↓reduceDIte]
  have hle : Nat.find hex ≤ 1 := Nat.find_min' hex (pow_one _)
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    have hsp := Nat.find_spec hex
    rw [h0, pow_zero] at hsp
    have hord := orderOf_gen D
    rw [← hsp, orderOf_one] at hord
    omega
  omega

lemma dlog_mul_mod (D : FieldData) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.dlog (x * y) % (D.q - 1) = (D.dlog x + D.dlog y) % (D.q - 1) := by
  have hpow : (uGen D) ^ D.dlog (x * y) = (uGen D) ^ (D.dlog x + D.dlog y) := by
    ext
    simp only [Units.val_pow_eq_pow_val, uGen, Units.val_mk0]
    rw [pow_add, gen_pow_dlog D (mul_ne_zero hx hy), gen_pow_dlog D hx, gen_pow_dlog D hy]
  have hmod := pow_eq_pow_iff_modEq.mp hpow
  simpa [orderOf_uGen D, Nat.ModEq] using hmod

lemma dlogLab_injective (D : FieldData) :
    Function.Injective (fun x : D.Fqˣ => D.dlogLab (x : D.Fq)) := by
  intro x y hxy
  have hmod : D.dlog (x : D.Fq) ≡ D.dlog (y : D.Fq) [MOD (D.q - 1)] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hxy
  rw [← orderOf_uGen D, ← pow_eq_pow_iff_modEq] at hmod
  have hval := congrArg Units.val hmod
  change D.gen ^ D.dlog (x : D.Fq) = D.gen ^ D.dlog (y : D.Fq) at hval
  rw [gen_pow_dlog D x.ne_zero, gen_pow_dlog D y.ne_zero] at hval
  exact Units.val_injective hval

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
        simp only [r]; push_cast; ring
      rw [← hreal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have hne : D.chi α x ≠ 0 := by simp [FieldData.chi, hx, Complex.exp_ne_zero]
    exact mul_right_cancel₀ hne (hnorm.trans hmul.symm)

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
  have hval_lt : (Algebra.trace (ZMod D.p) D.Fq x₀).val < D.p := ZMod.val_lt _
  exact absurd (Nat.le_of_dvd hval_pos heq) (not_le_of_gt hval_lt)

lemma sum_psi (D : FieldData) (u : D.Fq) :
    ∑ x : D.Fq, D.psi (u * x) = if u = 0 then (D.q : ℂ) else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp [psi_zero, card_Fq]
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

lemma sum_psi_units (D : FieldData) (u : D.Fq) :
    ∑ x : D.Fqˣ, D.psi (u * (x : D.Fq)) = if u = 0 then ((D.q - 1 : ℕ) : ℂ) else -1 := by
  have hsplit : ∑ x : D.Fq, D.psi (u * x) = D.psi (u * 0) + ∑ x : D.Fqˣ, D.psi (u * (x : D.Fq)) := by
    have h1 : (∑ x : D.Fq, D.psi (u * x)) =
        D.psi (u * 0) + ∑ x ∈ Finset.univ.erase (0 : D.Fq), D.psi (u * x) :=
      (Finset.add_sum_erase Finset.univ (fun x : D.Fq => D.psi (u * x)) (Finset.mem_univ 0)).symm
    rw [h1]
    congr 1
    symm
    refine Finset.sum_bij (fun (x : D.Fqˣ) _ => (x : D.Fq))
      (fun x _ => Finset.mem_erase.mpr ⟨x.ne_zero, Finset.mem_univ _⟩)
      (fun _ _ _ _ h => Units.ext h)
      (fun y hy => ⟨Units.mk0 y (Finset.mem_erase.mp hy).1, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  rw [sum_psi, mul_zero, psi_zero] at hsplit
  have hq : 1 ≤ D.q := D.one_lt_q.le
  by_cases hu : u = 0
  · subst hu
    simp only [↓reduceIte] at hsplit ⊢
    have hcast : ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) - 1 := by
      rw [Nat.cast_sub hq, Nat.cast_one]
    rw [hcast]
    linear_combination -hsplit
  · simp only [hu, ↓reduceIte] at hsplit ⊢
    linear_combination -hsplit

lemma conj_isqrt (x : ℝ) : conj (isqrt x) = isqrt x := by
  simp [FieldData.isqrt]

lemma conj_isqrt_mul_isqrt {x : ℝ} (hx : 0 < x) :
    conj (isqrt x) * isqrt x = ((x : ℝ) : ℂ)⁻¹ := by
  rw [conj_isqrt]
  simp only [FieldData.isqrt, ← Complex.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hx.le, Complex.ofReal_inv]

lemma isqrt_mul_isqrt {x : ℝ} (hx : 0 < x) :
    isqrt x * isqrt x = ((x : ℝ) : ℂ)⁻¹ := by
  simpa [conj_isqrt] using conj_isqrt_mul_isqrt hx

lemma isometry_mul {X M Y : Type} [Fintype X] [DecidableEq X] [Fintype M] [DecidableEq M] [Fintype Y]
    {A : Matrix M X ℂ} {B : Matrix Y M ℂ}
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (B * A).conjTranspose * (B * A) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B.conjTranspose B A, hB,
    Matrix.one_mul, hA]

lemma permMat_iso {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (hf : Function.Injective f) :
    (permMat f).conjTranspose * permMat f = 1 := by
  ext x₁ x₂
  simp only [permMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (f x₁)]
  · simp [hf.eq_iff]
  · intro y _ hy
    rw [if_neg hy, star_zero, zero_mul]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma frameMatRight_iso {X Y B : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype B] [DecidableEq B]
    {M : Matrix Y X ℂ} (hM : M.conjTranspose * M = 1) :
    (frameMatRight (B := B) M).conjTranspose * frameMatRight (B := B) M = 1 := by
  ext i j
  simp only [frameMatRight, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  by_cases hij : i.2 = j.2
  · have hsum : (∑ y : Y, ∑ b : B, star (if b = i.2 then M y i.1 else 0) *
        (if b = j.2 then M y j.1 else 0)) = ∑ y : Y, star (M y i.1) * M y j.1 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_eq_single i.2]
      · simp [hij]
      · intro b _ hb; simp [hb]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hsum]
    have hm := congrFun (congrFun hM i.1) j.1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
    rw [hm]
    simp [hij, Prod.ext_iff]
  · rw [Finset.sum_eq_zero]
    · simp [Prod.ext_iff, hij]
    · intro y _; rw [Finset.sum_eq_zero]; intro b _
      by_cases hb : b = i.2
      · subst hb; simp [hij]
      · simp [hb]

lemma frameMat_iso {A X Y : Type} [Fintype A] [DecidableEq A] [Fintype X] [DecidableEq X] [Fintype Y]
    {M : Matrix Y X ℂ} (hM : M.conjTranspose * M = 1) :
    (frameMat (A := A) M).conjTranspose * frameMat (A := A) M = 1 := by
  ext i j
  simp only [frameMat, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  dsimp only
  by_cases hij : i.1 = j.1
  · have hsum : (∑ a : A, ∑ y : Y, star (if a = i.1 then M y i.2 else 0) *
        (if a = j.1 then M y j.2 else 0)) = ∑ y : Y, star (M y i.2) * M y j.2 := by
      rw [Finset.sum_eq_single i.1]
      · simp [hij]
      · intro a _ ha; simp [ha]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hsum]
    have hm := congrFun (congrFun hM i.2) j.2
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
    rw [hm]
    simp [hij, Prod.ext_iff]
  · rw [Finset.sum_eq_zero]
    · simp [Prod.ext_iff, hij]
    · intro a _; rw [Finset.sum_eq_zero]; intro y _
      by_cases ha : a = i.1
      · subst ha; simp [hij]
      · simp [ha]

lemma submatrix_iso {X Y X' Y' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype X'] [DecidableEq X'] [Fintype Y']
    (M : Matrix Y X ℂ) (hM : M.conjTranspose * M = 1)
    (ιX : X' → X) (ιY : Y' → Y)
    (hιX : Function.Injective ιX) (hιY : Function.Injective ιY)
    (hinv : ∀ x' y, (∀ y', ιY y' ≠ y) → M y (ιX x') = 0) :
    (M.submatrix ιY ιX).conjTranspose * (M.submatrix ιY ιX) = 1 := by
  ext x₁' x₂'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.one_apply]
  have himg : (∑ y' : Y', star (M (ιY y') (ιX x₁')) * M (ιY y') (ιX x₂')) =
      ∑ y ∈ Finset.univ.image ιY, star (M y (ιX x₁')) * M y (ιX x₂') := by
    rw [Finset.sum_image]
    intro a _ b _ hab; exact hιY hab
  have hfull : (∑ y ∈ Finset.univ.image ιY, star (M y (ιX x₁')) * M y (ιX x₂')) =
      ∑ y : Y, star (M y (ιX x₁')) * M y (ιX x₂') := by
    refine Finset.sum_subset (Finset.subset_univ _) fun y _ hy => ?_
    have hnot : ∀ y', ιY y' ≠ y := fun y' h => hy (Finset.mem_image.mpr ⟨y', Finset.mem_univ y', h⟩)
    rw [hinv x₁' y hnot, star_zero, zero_mul]
  rw [himg, hfull]
  have hm := congrFun (congrFun hM (ιX x₁')) (ιX x₂')
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hm
  rw [hm]
  simp [hιX.eq_iff]

/-! ### Part 2: Subgroup `B`, Bruhat decomposition, `mackeyEncMat`, `qftB` iso, `mackeyMid`/`Out` -/

def BSub (D : FieldData) : Subgroup D.G where
  carrier := {g : D.G | (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ((a : Matrix (Fin 2) (Fin 2) D.Fq) * (b : Matrix (Fin 2) (Fin 2) D.Fq)) 1 0 = 0
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    change (a : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 at ha
    change (b : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 at hb
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    change (a : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 at ha
    change ((a⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0
    have hmul : (a : Matrix (Fin 2) (Fin 2) D.Fq) * ((a⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
      simp
    have h11 : ((a : Matrix (Fin 2) (Fin 2) D.Fq) * ((a⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)) 1 1 = 1 := by
      rw [hmul]; simp
    have h10 : ((a : Matrix (Fin 2) (Fin 2) D.Fq) * ((a⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)) 1 0 = 0 := by
      rw [hmul]; simp
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h11 h10
    have ha11_ne : (a : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 ≠ 0 := by
      intro hz
      simp [ha, hz] at h11
    rw [ha, zero_mul, zero_add] at h10
    exact (mul_eq_zero.mp h10).resolve_left ha11_ne

lemma BSub_diag_ne_zero (D : FieldData) (b : BSub D) :
    (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 ≠ 0 ∧ (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 ≠ 0 := by
  have hb10 : (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := b.2
  have hbi10 : ((b.1⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := (BSub D).inv_mem b.2
  have hmul : (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) * ((b.1⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
    simp
  have h00 : ((b.1 : Matrix (Fin 2) (Fin 2) D.Fq) * ((b.1⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)) 0 0 = 1 := by
    rw [hmul]; simp
  have h11 : ((b.1 : Matrix (Fin 2) (Fin 2) D.Fq) * ((b.1⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq)) 1 1 = 1 := by
    rw [hmul]; simp
  rw [Matrix.mul_apply, Fin.sum_univ_two] at h00 h11
  constructor
  · intro hz
    simp [hz, hbi10] at h00
  · intro hz
    simp [hb10, hz] at h11

def bmatG (D : FieldData) (x : D.BElt) : D.G :=
  ⟨D.bmat x, !![((x.1⁻¹ : D.Fqˣ) : D.Fq), -x.2.2 * ((x.1⁻¹ : D.Fqˣ) : D.Fq);
      0, ((x.2.1⁻¹ : D.Fqˣ) : D.Fq)],
    by
      ext i j; fin_cases i <;> fin_cases j <;> simp [FieldData.bmat]
      · field_simp [x.1.ne_zero]; ring
    ,
    by
      ext i j; fin_cases i <;> fin_cases j <;> simp [FieldData.bmat]
      · ring⟩

def bEltEquivB (D : FieldData) : D.BElt ≃ BSub D where
  toFun x := ⟨bmatG D x, by change (D.bmat x) 1 0 = 0; simp [FieldData.bmat]⟩
  invFun b :=
    let M : Matrix (Fin 2) (Fin 2) D.Fq := b.1
    ⟨Units.mk0 (M 0 0) (BSub_diag_ne_zero D b).1,
     Units.mk0 (M 1 1) (BSub_diag_ne_zero D b).2,
     M 0 1 / M 1 1⟩
  left_inv x := by
    rcases x with ⟨a, d, b⟩
    ext <;> simp [bmatG, FieldData.bmat, div_eq_mul_inv]
  right_inv b := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [bmatG, FieldData.bmat]
    · simp [bmatG, FieldData.bmat, div_mul_cancel₀ _ (BSub_diag_ne_zero D b).2]
    · simpa [bmatG, FieldData.bmat] using b.2.symm
    · simp [bmatG, FieldData.bmat]

lemma bEltEquivB_coe_mat (D : FieldData) (x : D.BElt) :
    ((bEltEquivB D x : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) = D.bmat x := rfl

lemma card_BSub (D : FieldData) : Fintype.card (BSub D) = D.q * (D.q - 1) ^ 2 := by
  rw [← Fintype.card_congr (bEltEquivB D)]
  simp only [FieldData.BElt, Fintype.card_prod, card_Fq_units, card_Fq]
  ring

def bruhatEquiv (D : FieldData) : CosetT D × D.BElt ≃ D.G where
  toFun tb := cosetRep D tb.1 * (bEltEquivB D tb.2 : BSub D).1
  invFun g :=
    let M : Matrix (Fin 2) (Fin 2) D.Fq := g
    if h : M 1 0 = 0 then (.inl (), (bEltEquivB D).symm ⟨g, h⟩)
    else
      let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
      let det : D.Fq := a * d - b * c
      have hdet : det ≠ 0 := by
        have hg : IsUnit ((g : Matrix (Fin 2) (Fin 2) D.Fq).det) :=
          (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
        simpa [det, a, b, c, d, M, Matrix.det_fin_two] using hg.ne_zero
      let d' : D.Fq := b - (a / c) * d
      have hd' : d' ≠ 0 := by
        intro hd0
        apply hdet
        have hc_eq : c * d' = -det := by
          calc c * d' = c * b - (c * c⁻¹) * (a * d) := by dsimp [d']; rw [div_eq_mul_inv]; ring
            _ = c * b - 1 * (a * d) := by rw [mul_inv_cancel₀ h]
            _ = -det := by dsimp [det]; ring
        rw [hd0, mul_zero] at hc_eq
        exact neg_eq_zero.mp hc_eq.symm
      (.inr (a / c), ⟨Units.mk0 c h, Units.mk0 d' hd', d / d'⟩)
  left_inv tb := by
    rcases tb with ⟨⟨⟩ | x, ⟨a, d, b⟩⟩
    · have h10 : ((cosetRep D (.inl ()) * (bEltEquivB D (a, d, b)).1 : D.G) :
          Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := by
        simp [cosetRep, bEltEquivB, bmatG, FieldData.bmat]
      dsimp only
      rw [dif_pos h10]
      apply Prod.ext
      · rfl
      · simp [cosetRep]
    · have hprod : ((cosetRep D (.inr x) * (bEltEquivB D (a, d, b)).1 : D.G) :
          Matrix (Fin 2) (Fin 2) D.Fq) =
          !![x * (a : D.Fq), x * (b * (d : D.Fq)) + (d : D.Fq); (a : D.Fq), b * (d : D.Fq)] := by
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [cosetRep, bEltEquivB, bmatG, FieldData.bmat, Matrix.mul_apply, Fin.sum_univ_two]
      have h10 : ((cosetRep D (.inr x) * (bEltEquivB D (a, d, b)).1 : D.G) :
          Matrix (Fin 2) (Fin 2) D.Fq) 1 0 ≠ 0 := by
        rw [hprod]; simp [a.ne_zero]
      dsimp only
      rw [dif_neg h10]
      simp only [hprod, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have ha : (a : D.Fq) ≠ 0 := a.ne_zero
      have hd : (d : D.Fq) ≠ 0 := d.ne_zero
      have hx_eq : x * (a : D.Fq) / (a : D.Fq) = x := mul_div_cancel_right₀ x ha
      have hd_eq : x * (b * (d : D.Fq)) + (d : D.Fq) - x * (a : D.Fq) / (a : D.Fq) * (b * (d : D.Fq)) =
          (d : D.Fq) := by
        rw [hx_eq]; ring
      apply Prod.ext
      · exact congrArg Sum.inr hx_eq
      · apply Prod.ext
        · ext; rfl
        · apply Prod.ext
          · ext; exact hd_eq
          · dsimp only; rw [hd_eq, mul_div_cancel_right₀ b hd]
  right_inv g := by
    dsimp only
    by_cases h : (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0
    · rw [dif_pos h]
      simp only [cosetRep, one_mul]
      exact congrArg Subtype.val ((bEltEquivB D).apply_symm_apply ⟨g, h⟩)
    · rw [dif_neg h]
      ext i j
      simp only [cosetRep, bEltEquivB, bmatG, FieldData.bmat]
      have hd' : (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 -
          (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 / (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 *
          (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 ≠ 0 := by
        intro hd0
        have hdet : ((g : Matrix (Fin 2) (Fin 2) D.Fq).det) ≠ 0 :=
          ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
        rw [Matrix.det_fin_two] at hdet
        apply hdet
        have hc_eq : (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 *
            ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 -
            (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 / (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 *
            (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) =
            -((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 * (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 -
            (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 * (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0) := by
          calc (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 *
                ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 -
                (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 / (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 *
                (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)
              = (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 * (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 -
                ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 * ((g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0)⁻¹) *
                ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 * (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) := by
                  rw [div_eq_mul_inv]; ring
            _ = (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 * (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 -
                1 * ((g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 * (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) := by
                  rw [mul_inv_cancel₀ h]
            _ = _ := by ring
        rw [hd0, mul_zero] at hc_eq
        exact neg_eq_zero.mp hc_eq.symm
      fin_cases i <;> fin_cases j <;> simp [div_mul_cancel₀ _ h, div_mul_cancel₀ _ hd']

lemma mackeyEncMat_eq_if (D : FieldData) (tb : CosetT D × D.BElt) (g : D.G) :
    mackeyEncMat D tb g = if g = bruhatEquiv D tb then 1 else 0 := by
  simp only [mackeyEncMat, Matrix.of_apply, bruhatEquiv, Equiv.coe_fn_mk]
  congr 1
  rw [eq_iff_iff]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [bEltEquivB_coe_mat] using this
  · intro h
    subst h
    simp [bEltEquivB_coe_mat]

lemma mackeyEncMat_iso (D : FieldData) :
    (mackeyEncMat D).conjTranspose * mackeyEncMat D = 1 := by
  ext g₁ g₂
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, mackeyEncMat_eq_if, Matrix.one_apply]
  rw [Finset.sum_eq_single ((bruhatEquiv D).symm g₁)]
  · simp [(bruhatEquiv D).apply_symm_apply g₁, eq_comm]
  · intro tb _ htb
    have hne : g₁ ≠ bruhatEquiv D tb := fun h =>
      htb (by rw [h, (bruhatEquiv D).symm_apply_apply])
    simp [hne]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma bInEmb_injective (D : FieldData) : Function.Injective (bInEmb D) := by
  rintro ⟨a₁, d₁, b₁⟩ ⟨a₂, d₂, b₂⟩ h
  simp only [bInEmb, Prod.mk.injEq, Option.some.injEq] at h
  have ha := dlogLab_injective D h.1.1
  have hd := dlogLab_injective D h.1.2
  subst ha hd
  simp only [h.2]

lemma bMidInj_injective (D : FieldData) : Function.Injective (bMidInj D) := by
  rintro ⟨a₁, d₁, η₁⟩ ⟨a₂, d₂, η₂⟩ h
  simp only [bMidInj, Prod.mk.injEq, Option.some.injEq] at h
  rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
  rfl

def fbOutPermInv (D : FieldData) : D.BOutLabel → D.Lab × D.Lab × Option D.Lab
  | ⟨.inl ab, _, _⟩ => (ab.1, ab.2, none)
  | ⟨.inr γ, δ, δ'⟩ =>
    let δ₀ : D.Lab := δ
    let δ₀' : D.Lab := δ'
    (δ₀', γ - δ₀', some (δ₀' - δ₀))

lemma fbOutPerm_left_inv (D : FieldData) (p : D.Lab × D.Lab × Option D.Lab) :
    fbOutPermInv D (fbOutPerm D p) = p := by
  rcases p with ⟨α, β, _ | η⟩ <;> simp [fbOutPerm, fbOutPermInv]

lemma fbOutPerm_injective (D : FieldData) : Function.Injective (fbOutPerm D) :=
  Function.LeftInverse.injective (fbOutPerm_left_inv D)

lemma qftB_iso (D : FieldData) : D.qftB.conjTranspose * D.qftB = 1 := by
  rw [qftB_algebraic_factorization D]
  have hperm : (permMat (fbOutPerm D)).conjTranspose * permMat (fbOutPerm D) = 1 :=
    permMat_iso _ (fbOutPerm_injective D)
  have h3_iso : (phiFmult D * phiLog D * phiFplus D).conjTranspose *
      (phiFmult D * phiLog D * phiFplus D) = 1 := by
    have := isometry_mul (isometry_mul (phi_isometries D).1.1 (phi_isometries D).2.2.2.1)
      (phi_isometries D).2.1.1
    simpa only [Matrix.mul_assoc] using this
  have h12_iso :
      (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
        frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D))).conjTranspose *
      (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
        frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D))) = 1 :=
    isometry_mul (frameMatRight_iso (frameMat_iso (phi_isometries D).2.1.1))
      (frameMatRight_iso (frameMatRight_iso (phi_isometries D).2.1.1))
  let M : Matrix ((Option D.Lab × Option D.Lab) × Option D.Lab)
      ((Option D.Lab × Option D.Lab) × D.Fq) ℂ :=
    frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
      frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) *
      frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D)
  have hM_iso : M.conjTranspose * M = 1 :=
    isometry_mul (frameMat_iso h3_iso) h12_iso
  have hinv : ∀ (x' : D.BElt) (y : (Option D.Lab × Option D.Lab) × Option D.Lab),
      (∀ y' : D.Lab × D.Lab × Option D.Lab, bMidInj D y' ≠ y) → M y (bInEmb D x') = 0 := by
    intro x' y hy
    rcases y with ⟨⟨a', d'⟩, η?⟩
    have hnone : a' = none ∨ d' = none := by
      cases a' with
      | none => exact Or.inl rfl
      | some a => cases d' with
        | none => exact Or.inr rfl
        | some d => exact absurd rfl (hy (a, d, η?))
    have h12_apply : ∀ (u v w x y z : Option D.Lab),
        (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
          frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)))
          ((u, v), w) ((x, y), z) =
        if w = z then phiFmult D u x * phiFmult D v y else 0 := by
      intro u v w x y z
      simp only [Matrix.mul_apply, Fintype.sum_prod_type, frameMatRight, frameMat, Matrix.of_apply]
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single v]
        · rw [Finset.sum_eq_single z]
          · by_cases hw : w = z <;> simp [hw]
          · intro c _ hc; simp [hc]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · intro b _ hb; rw [Finset.sum_eq_zero]; intro c _; simp [Ne.symm hb]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro a _ ha; rw [Finset.sum_eq_zero]; intro b _; rw [Finset.sum_eq_zero]; intro c _; simp [ha]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    have hM_apply : M ((a', d'), η?) (bInEmb D x') =
        phiFmult D a' (some (D.dlogLab (x'.1 : D.Fq))) *
          phiFmult D d' (some (D.dlogLab (x'.2.1 : D.Fq))) *
          (phiFmult D * phiLog D * phiFplus D) η? x'.2.2 := by
      dsimp [M, bInEmb]
      rw [Matrix.mul_apply, Finset.sum_eq_single ((some (D.dlogLab (x'.1 : D.Fq)),
          some (D.dlogLab (x'.2.1 : D.Fq))), η?)]
      · rw [h12_apply, if_pos rfl]; simp [frameMat]
      · rintro ⟨⟨x₀, y₀⟩, z₀⟩ _ hne
        by_cases hxy : (x₀, y₀) = (some (D.dlogLab (x'.1 : D.Fq)), some (D.dlogLab (x'.2.1 : D.Fq)))
        · by_cases hz : η? = z₀
          · rcases Prod.mk.inj hxy with ⟨rfl, rfl⟩
            exact absurd (by subst hz; rfl) hne
          · rw [h12_apply, if_neg hz, zero_mul]
        · simp [frameMat, hxy]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hM_apply]
    rcases hnone with rfl | rfl <;> simp [phiFmult]
  have hsub_iso : (M.submatrix (bMidInj D) (bInEmb D)).conjTranspose *
      M.submatrix (bMidInj D) (bInEmb D) = 1 :=
    submatrix_iso M hM_iso (bInEmb D) (bMidInj D) (bInEmb_injective D) (bMidInj_injective D) hinv
  exact isometry_mul hsub_iso hperm

lemma bbasLab_injective (D : FieldData) (l : D.BIrr) : Function.Injective (bbasLab D l) := by
  intro a b h
  cases l with
  | inl _ => rcases a, b with ⟨⟨⟩, ⟨⟩⟩; rfl
  | inr _ => exact h

lemma mackeyMidEmb_injective (D : FieldData) : Function.Injective (mackeyMidEmb D) := by
  rintro ⟨x₁, q₁, r₁⟩ ⟨x₂, q₂, r₂⟩ h
  simp only [mackeyMidEmb, Prod.mk.injEq] at h
  rcases h with ⟨⟨hq, hr⟩, hx⟩
  subst hx
  have hq' := bbasLab_injective D _ hq
  have hr' := bbasLab_injective D _ hr
  subst hq' hr'
  rfl

lemma mackeyOutEmb_injective (D : FieldData) : Function.Injective (mackeyOutEmb D) := by
  rintro ⟨⟨y₁, q₁, r₁⟩, h₁a, h₁b⟩ ⟨⟨y₂, q₂, r₂⟩, h₂a, h₂b⟩ h
  simp only [mackeyOutEmb, Prod.mk.injEq] at h
  rcases h with ⟨⟨hq, hr⟩, hy⟩
  subst hy
  have hq' := bbasLab_injective D _ hq
  have hr' := bbasLab_injective D _ hr
  subst hq' hr'
  rfl

lemma labMu_isSome_indep (D : FieldData) (μ : D.Irr) (ν : D.BIrr) (P Q : D.BBas ν) :
    (labMu D μ ν P).isSome = (labMu D μ ν Q).isSome := by
  rcases μ with α | α | ⟨ab, hab⟩ | ⟨k, hk⟩ <;> rcases ν with ab' | γ <;>
    simp [labMu] <;> split_ifs <;> rfl

lemma frameMat_totalA_off_out (D : FieldData) (m : MackeyMid D) (y : (D.Lab × D.Lab) × OutReg D)
    (hy : ∀ m' : MackeyOut D, mackeyOutEmb D m' ≠ y) :
    frameMat (A := D.Lab × D.Lab) (totalA D) y (mackeyMidEmb D m) = 0 := by
  by_contra hne
  rcases m with ⟨⟨⟨l, κ, ω, lt⟩, hval⟩, Q, R⟩
  rcases y with ⟨⟨a₁, a₂⟩, ⟨l', μ, lt'⟩⟩
  simp only [frameMat, mackeyMidEmb, Matrix.of_apply] at hne
  split_ifs at hne with ha
  · simp only [totalA, Matrix.of_apply] at hne
    split_ifs at hne with hl
    · rcases hl with ⟨hl1, hl2⟩
      subst hl1; subst hl2
      have hsome : (labMu D μ lt' Q).isSome ∧ (labMu D μ l' R).isSome := by
        cases ω
        · simp only [A70, Bool.false_eq_true, ↓reduceIte] at hne
          split_ifs at hne with hk
          · have hsum_ne : ∑ P : D.BBas l', ∑ Pt : D.BBas κ,
                Rent D μ 1 (labMu D μ lt' (cast (congrArg D.BBas (hk.1.trans hk.2.symm)) Pt))
                  (labMu D μ l' P) *
                conj (if cast (congrArg D.BBas hk.1) Pt = P then (1 : ℂ) else 0) ≠ 0 :=
              fun hz => hne (mul_eq_zero.mpr (Or.inr hz))
            obtain ⟨P, -, hP⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
            obtain ⟨Pt, -, hPt⟩ := Finset.exists_ne_zero_of_sum_ne_zero hP
            have hrent : Rent D μ 1 (labMu D μ lt' (cast (congrArg D.BBas (hk.1.trans hk.2.symm)) Pt))
                (labMu D μ l' P) ≠ 0 := fun hz => hPt (by rw [hz, zero_mul])
            cases h1 : labMu D μ lt' (cast (congrArg D.BBas (hk.1.trans hk.2.symm)) Pt) with
            | none => simp [Rent, h1] at hrent
            | some v₁ => cases h2 : labMu D μ l' P with
              | none => simp [Rent, h1, h2] at hrent
              | some v₂ =>
                rw [labMu_isSome_indep D μ lt' Q (cast (congrArg D.BBas (hk.1.trans hk.2.symm)) Pt), h1]
                rw [labMu_isSome_indep D μ l' R P, h2]
                exact ⟨rfl, rfl⟩
          · exact absurd rfl hne
        · cases κ with
          | inr _ => simp [A70] at hne
          | inl ab =>
            simp only [A70, ↓reduceIte] at hne
            have hsum_ne : ∑ P : D.BBas l',
                (match tLab D lt' ab with
                  | some Pt => Rent D μ (wGL D) (labMu D μ lt' Pt) (labMu D μ l' P)
                  | none => 0) * conj (utwW D l' ab P) ≠ 0 :=
              fun hz => hne (mul_eq_zero.mpr (Or.inr hz))
            obtain ⟨P, -, hP⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
            cases ht : tLab D lt' ab with
            | none => simp [ht] at hP
            | some Pt =>
              rw [ht] at hP
              dsimp only at hP
              have hrent : Rent D μ (wGL D) (labMu D μ lt' Pt) (labMu D μ l' P) ≠ 0 :=
                fun hz => hP (by simp [hz])
              cases h1 : labMu D μ lt' Pt with
              | none => simp [Rent, h1] at hrent
              | some v₁ => cases h2 : labMu D μ l' P with
                | none => simp [Rent, h1, h2] at hrent
                | some v₂ =>
                  rw [labMu_isSome_indep D μ lt' Q Pt, h1]
                  rw [labMu_isSome_indep D μ l' R P, h2]
                  exact ⟨rfl, rfl⟩
      let m' : MackeyOut D := ⟨⟨(l', μ, lt'), (Q, R)⟩, hsome.1, hsome.2⟩
      apply hy m'
      simp only [mackeyOutEmb, m', ha]
    · exact hne rfl
  · exact hne rfl

/-! ### Part 3: Generic Schur/Completeness and Irrep Systems for `B` and `G` -/

section GenericCompleteness

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
  · intro h v; subst h; simp

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
    intro g; simp [mul_sub, sub_mul, hA g]
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

lemma repEquiv_symm {K ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : RepEquiv R₂ R₁ := by
  obtain ⟨A, B, hAB, hBA, hint⟩ := h
  refine ⟨B, A, hBA, hAB, fun g _ => ?_⟩
  calc B * R₂ g = B * R₂ g * (A * B) := by rw [hAB, Matrix.mul_one]
    _ = B * (R₂ g * A) * B := by simp only [Matrix.mul_assoc]
    _ = B * (A * R₁ g) * B := by rw [hint g (Set.mem_univ _)]
    _ = R₁ g * B := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]

lemma repEquiv_trace {K ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) (g : K) : Matrix.trace (R₁ g) = Matrix.trace (R₂ g) := by
  obtain ⟨A, B, hAB, hBA, hint⟩ := h
  calc Matrix.trace (R₁ g) = Matrix.trace ((B * A) * R₁ g) := by rw [hBA, Matrix.one_mul]
    _ = Matrix.trace (B * (A * R₁ g)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace (B * (R₂ g * A)) := by rw [hint g (Set.mem_univ _)]
    _ = Matrix.trace ((B * R₂ g) * A) := by rw [← Matrix.mul_assoc]
    _ = Matrix.trace (A * (B * R₂ g)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((A * B) * R₂ g) := by rw [← Matrix.mul_assoc]
    _ = Matrix.trace (R₂ g) := by rw [hAB, Matrix.one_mul]

lemma completeness_of_irrep_sum_sq_eq_card {K Λ : Type} [Group K] [Fintype K] [Fintype Λ]
    (B : Λ → Type) [∀ l, Fintype (B l)] [∀ l, DecidableEq (B l)]
    (R : ∀ l, K → Matrix (B l) (B l) ℂ)
    (hU : ∀ l, IsUnitaryRep (R l)) (hI : ∀ l, IsIrreducibleRep (R l))
    (hNe : ∀ l₁ l₂, l₁ ≠ l₂ → ¬ RepEquiv (R l₁) (R l₂))
    (hSum : ∑ l : Λ, Fintype.card (B l) ^ 2 = Fintype.card K)
    (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : K → Matrix ι ι ℂ)
    (hm : IsMatRep ρ) (hi : IsIrreducibleRep ρ) :
    ∃ l : Λ, RepEquiv (R l) ρ := by
  by_contra hnone
  push Not at hnone
  let S := (Σ l : Λ, B l × B l) ⊕ (ι × ι)
  let F : S → K → ℂ := fun s g => match s with
    | .inl ⟨l, a, b⟩ => R l g a b
    | .inr (a, b) => ρ g a b
  let Gd : S → K → ℂ := fun s g => match s with
    | .inl ⟨l, a, b⟩ => R l g⁻¹ b a
    | .inr (a, b) => ρ g⁻¹ b a
  let dim : S → ℂ := fun s => match s with
    | .inl ⟨l, _⟩ => (Fintype.card (B l) : ℂ)
    | .inr _ => (Fintype.card ι : ℂ)
  have hdim_ne : ∀ s : S, dim s ≠ 0 := by
    rintro (⟨l, _, _⟩ | ⟨_, _⟩)
    · have : Nonempty (B l) := (hI l).1
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    · have : Nonempty ι := hi.1
      exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hdot : ∀ s₁ s₂ : S, ∑ g : K, F s₁ g * Gd s₂ g =
      if s₁ = s₂ then (Fintype.card K : ℂ) / dim s₁ else 0 := by
    rintro (⟨l₁, a₁, b₁⟩ | ⟨a₁, b₁⟩) (⟨l₂, a₂, b₂⟩ | ⟨a₂, b₂⟩)
    · by_cases hl : l₁ = l₂
      · subst hl
        have hself := schur_ortho_self (hU l₁).1 (hI l₁) a₁ b₁ a₂ b₂
        by_cases ha : a₁ = a₂ <;> by_cases hb : b₁ = b₂
        · subst ha; subst hb; simpa [F, Gd, dim] using hself
        · rw [if_neg (fun h => by cases h; exact hb rfl)]
          simpa [F, Gd, ha, hb] using hself
        · rw [if_neg (fun h => by cases h; exact ha rfl)]
          simpa [F, Gd, ha, hb] using hself
        · rw [if_neg (fun h => by cases h; exact ha rfl)]
          simpa [F, Gd, ha, hb] using hself
      · have hne := schur_ortho_ne (hU l₂).1 (hU l₁).1 (hI l₂) (hI l₁)
          (hNe l₂ l₁ (Ne.symm hl)) a₂ b₂ a₁ b₁
        rw [if_neg (fun h => by cases h; exact hl rfl)]
        simpa [F, Gd] using hne
    · have hne := schur_ortho_ne hm (hU l₁).1 hi (hI l₁)
        (fun heq => hnone l₁ (repEquiv_symm heq)) a₂ b₂ a₁ b₁
      rw [if_neg (by simp)]
      simpa [F, Gd] using hne
    · have hne := schur_ortho_ne (hU l₂).1 hm (hI l₂) hi (hnone l₂) a₂ b₂ a₁ b₁
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
    have h0 : ∑ g : K, (∑ s : S, c s • F s) g * Gd s₀ g = 0 := by
      rw [hc]; simp
    have h1 : ∑ g : K, (∑ s : S, c s • F s) g * Gd s₀ g =
        c s₀ * ((Fintype.card K : ℂ) / dim s₀) := by
      simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have hterm : ∀ s : S, (∑ g : K, c s * F s g * Gd s₀ g) =
          c s * (if s = s₀ then (Fintype.card K : ℂ) / dim s else 0) := by
        intro s
        simp_rw [mul_assoc, ← Finset.mul_sum, hdot s s₀]
      simp_rw [hterm]
      rw [Finset.sum_eq_single s₀]
      · simp
      · intro s _ hs; simp [hs]
      · intro hmem; exact (hmem (Finset.mem_univ s₀)).elim
    rw [h1] at h0
    have hK_ne : (Fintype.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hcoeff_ne : (Fintype.card K : ℂ) / dim s₀ ≠ 0 := div_ne_zero hK_ne (hdim_ne s₀)
    exact (mul_eq_zero.mp h0).resolve_right hcoeff_ne
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at hle
  have hcard_S : Fintype.card S = (∑ l : Λ, Fintype.card (B l) ^ 2) + Fintype.card ι ^ 2 := by
    simp [S, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, pow_two]
  rw [hcard_S, hSum] at hle
  have : Nonempty ι := hi.1
  have hpos : 0 < Fintype.card ι ^ 2 := sq_pos_of_pos Fintype.card_pos
  omega

end GenericCompleteness

lemma isUnitaryRep_of_equiv {K ι ι' : Type} [Monoid K] [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι)
    {R : K → Matrix ι ι ℂ} (hR : IsUnitaryRep R) :
    IsUnitaryRep (fun g => (R g).submatrix e e) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext i j
    simp [hR.1.1, Matrix.one_apply, e.injective.eq_iff]
  · intro g₁ g₂
    ext i j
    simp only [Matrix.submatrix_apply, hR.1.2 g₁ g₂, Matrix.mul_apply]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  · intro g
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    have hm := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp (hR.2 g)) (e i)) (e j)
    simp only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      Matrix.submatrix_apply, Matrix.one_apply] at hm ⊢
    rw [← Fintype.sum_equiv e (fun j_1 => R g (e i) (e j_1) * star (R g (e j) (e j_1)))
      (fun j_1 => R g (e i) j_1 * star (R g (e j) j_1)) fun _ => rfl] at hm
    simpa [e.injective.eq_iff] using hm

lemma isIrreducibleRep_of_equiv {K ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι' ≃ ι) {R : K → Matrix ι ι ℂ} (hR : IsIrreducibleRep R) :
    IsIrreducibleRep (fun g => (R g).submatrix e e) := by
  refine ⟨⟨e.symm hR.1.some⟩, fun W' hW' => ?_⟩
  let L : (ι' → ℂ) ≃ₗ[ℂ] (ι → ℂ) := LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) e
  let W : Submodule ℂ (ι → ℂ) := W'.map L.toLinearMap
  have hL_apply : ∀ (v : ι' → ℂ) (x : ι), L v x = v (e.symm x) := fun _ _ => rfl
  have hmulVec : ∀ (g : K) (v : ι' → ℂ), L (((R g).submatrix e e).mulVec v) = (R g).mulVec (L v) := by
    intro g v
    ext x
    simp only [hL_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, e.apply_symm_apply]
    exact Fintype.sum_equiv e (fun y' => R g x (e y') * v y')
      (fun y => R g x y * v (e.symm y)) fun y' => by simp
  have hW_inv : IsInvariantSubspace R W := by
    rintro g w ⟨v, hv, rfl⟩
    refine ⟨((R g).submatrix e e).mulVec v, hW' g v hv, hmulVec g v⟩
  rcases hR.2 W hW_inv with hbot | htop
  · left
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro v hv
    have h0 : L v = 0 := hbot (L v) (Submodule.mem_map_of_mem hv)
    exact L.injective (h0.trans (map_zero L).symm)
  · right
    rw [Submodule.eq_top_iff'] at htop ⊢
    intro v
    have hmem : L v ∈ W := htop (L v)
    rcases hmem with ⟨v', hv', heq⟩
    have hv_eq : v' = v := L.injective heq
    rwa [← hv_eq]

lemma repEquiv_of_submatrix_left {K ι₁ ι₁' ι₂ : Type} [Fintype ι₁] [Fintype ι₁'] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₁'] [DecidableEq ι₂]
    (e : ι₁' ≃ ι₁) {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : RepEquiv (fun g => (R₁ g).submatrix e e) R₂ := by
  obtain ⟨A, B, hAB, hBA, hint⟩ := h
  refine ⟨A.submatrix id e, B.submatrix e id, ?_, ?_, fun g _ => ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
    rw [Fintype.sum_equiv e (fun j_1 => A i (e j_1) * B (e j_1) j) (fun j_1 => A i j_1 * B j_1 j)
      fun _ => rfl]
    exact congrFun (congrFun hAB i) j
  · ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, Matrix.one_apply]
    have hm := congrFun (congrFun hBA (e i)) (e j)
    simpa [Matrix.mul_apply, Matrix.one_apply, e.injective.eq_iff] using hm
  · ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
    rw [Fintype.sum_equiv e (fun j_1 => A i (e j_1) * R₁ g (e j_1) (e j))
      (fun j_1 => A i j_1 * R₁ g j_1 (e j)) fun _ => rfl]
    exact congrFun (congrFun (hint g (Set.mem_univ _)) i) (e j)

lemma repEquiv_of_submatrix_right {K ι₁ ι₂ ι₂' : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₂']
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₂']
    (e : ι₂' ≃ ι₂) {R₁ : K → Matrix ι₁ ι₁ ℂ} {R₂ : K → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : RepEquiv R₁ (fun g => (R₂ g).submatrix e e) := by
  exact repEquiv_symm (repEquiv_of_submatrix_left e (repEquiv_symm h))

lemma isIrreducibleRep_of_unitary_conj {K ι ι' : Type} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι']
    (U : Matrix ι ι' ℂ) (hU1 : U.conjTranspose * U = 1) (hU2 : U * U.conjTranspose = 1)
    {R : K → Matrix ι ι ℂ} (hR : IsIrreducibleRep R) :
    IsIrreducibleRep (fun g => U.conjTranspose * R g * U) := by
  have he : Fintype.card ι' = Fintype.card ι := by
    have ht1 : (U.conjTranspose * U).trace = Fintype.card ι' := by rw [hU1]; simp
    have ht2 : (U * U.conjTranspose).trace = Fintype.card ι := by rw [hU2]; simp
    rw [Matrix.trace_mul_comm] at ht1
    exact Nat.cast_injective (ht1.symm.trans ht2)
  have hne : Nonempty ι' := Fintype.card_pos_iff.mp (he.symm ▸ Fintype.card_pos_iff.mpr hR.1)
  refine ⟨hne, fun W' hW' => ?_⟩
  let W : Submodule ℂ (ι → ℂ) := W'.map U.mulVecLin
  have hW_inv : IsInvariantSubspace R W := by
    rintro g w ⟨v, hv, rfl⟩
    refine ⟨(U.conjTranspose * R g * U).mulVec v, hW' g v hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    have hassoc : U * (U.conjTranspose * R g * U) = R g * U := by
      calc U * (U.conjTranspose * R g * U) = (U * U.conjTranspose) * (R g * U) := by
            simp only [Matrix.mul_assoc]
        _ = R g * U := by rw [hU2, Matrix.one_mul]
    rw [hassoc]
  rcases hR.2 W hW_inv with hbot | htop
  · left
    rw [Submodule.eq_bot_iff] at hbot ⊢
    intro v hv
    have hUv : U.mulVec v = 0 := hbot (U.mulVec v) (Submodule.mem_map_of_mem hv)
    calc v = (1 : Matrix ι' ι' ℂ).mulVec v := (Matrix.one_mulVec v).symm
      _ = (U.conjTranspose * U).mulVec v := by rw [hU1]
      _ = U.conjTranspose.mulVec (U.mulVec v) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hUv, Matrix.mulVec_zero]
  · right
    rw [Submodule.eq_top_iff'] at htop ⊢
    intro v
    have hmem : U.mulVec v ∈ W := htop (U.mulVec v)
    rcases hmem with ⟨v', hv', heq⟩
    have hv_eq : v' = v := by
      change U.mulVec v' = U.mulVec v at heq
      calc v' = (1 : Matrix ι' ι' ℂ).mulVec v' := (Matrix.one_mulVec v').symm
        _ = (U.conjTranspose * U).mulVec v' := by rw [hU1]
        _ = U.conjTranspose.mulVec (U.mulVec v') := (Matrix.mulVec_mulVec _ _ _).symm
        _ = U.conjTranspose.mulVec (U.mulVec v) := by rw [heq]
        _ = (U.conjTranspose * U).mulVec v := Matrix.mulVec_mulVec _ _ _
        _ = (1 : Matrix ι' ι' ℂ).mulVec v := by rw [hU1]
        _ = v := Matrix.one_mulVec v
    rwa [← hv_eq]

def RH (D : FieldData) (l : D.BIrr) (h : BSub D) : Matrix (D.BBas l) (D.BBas l) ℂ :=
  D.RB l (h.1 : Matrix (Fin 2) (Fin 2) D.Fq)

lemma RH_isUnitaryRep (D : FieldData) (l : D.BIrr) : IsUnitaryRep (RH D l) := by
  cases l with
  | inl ab =>
    rcases ab with ⟨α, β⟩
    have hsub : ∀ i j : D.BBas (.inl (α, β)), i = j := fun i j =>
      Subsingleton.elim (α := Unit) i j
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext i j
      rw [Matrix.one_apply, if_pos (hsub i j)]
      simp [RH, FieldData.RB, chi_one]
    · intro h₁ h₂
      ext i j
      have h10_1 : (h₁.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := h₁.2
      have h10_2 : (h₂.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := h₂.2
      have h00 : ((h₁ * h₂).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 =
          (h₁.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 * (h₂.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 := by
        change ((h₁.1 : Matrix (Fin 2) (Fin 2) D.Fq) * (h₂.1 : Matrix (Fin 2) (Fin 2) D.Fq)) 0 0 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two, h10_2, mul_zero, add_zero]
      have h11 : ((h₁ * h₂).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 =
          (h₁.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 * (h₂.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 := by
        change ((h₁.1 : Matrix (Fin 2) (Fin 2) D.Fq) * (h₂.1 : Matrix (Fin 2) (Fin 2) D.Fq)) 1 1 = _
        rw [Matrix.mul_apply, Fin.sum_univ_two, h10_1, zero_mul, zero_add]
      rw [Matrix.mul_apply, Finset.sum_eq_single i
        (fun k _ hk => absurd (hsub k i) hk) (fun hm => absurd (Finset.mem_univ _) hm)]
      simp only [RH, FieldData.RB]
      rw [h00, h11, chi_mul D α (BSub_diag_ne_zero D h₁).1 (BSub_diag_ne_zero D h₂).1,
        chi_mul D β (BSub_diag_ne_zero D h₁).2 (BSub_diag_ne_zero D h₂).2]
      ring
    · intro h
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
      ext i j
      rw [Matrix.mul_apply, Finset.sum_eq_single i
        (fun k _ hk => absurd (hsub k i) hk) (fun hm => absurd (Finset.mem_univ _) hm),
        Matrix.one_apply, if_pos (hsub i j), Matrix.conjTranspose_apply]
      simp only [RH, FieldData.RB]
      have ha : D.chi α ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
          star (D.chi α ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)) = 1 := by
        rw [RCLike.star_def, conj_chi, ← chi_add, add_neg_cancel,
          chi_zero_lab D (BSub_diag_ne_zero D h).1]
      have hd : D.chi β ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
          star (D.chi β ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) = 1 := by
        rw [RCLike.star_def, conj_chi, ← chi_add, add_neg_cancel,
          chi_zero_lab D (BSub_diag_ne_zero D h).2]
      calc D.chi α ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
            D.chi β ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
            star (D.chi α ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
              D.chi β ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1))
          = (D.chi α ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
              star (D.chi α ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0))) *
            (D.chi β ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
              star (D.chi β ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1))) := by
              rw [star_mul']; ring
        _ = 1 := by rw [ha, hd, mul_one]
  | inr γ =>
    have h67 := lemma_6_7 D
    have htab := (table_2_completeness D).1
    let M : BSub D → Matrix D.Lab D.Lab ℂ := fun h δ δ' => RH D (.inr γ) h δ δ'
    by_cases hγ : γ = 0
    · subst hγ
      have hSt := htab (.inr (.inl 0))
      let eBas : Option D.Lab ≃ D.Bas (.inr (.inl 0)) := Equiv.refl (Option D.Lab)
      have hblock : ∀ (h : BSub D) (δ δ' : D.Lab),
          D.R (.inr (.inl 0)) h.1 (eBas (some δ)) (eBas (some δ')) = M h δ δ' := fun h δ δ' => by
        have heq := h67.2.2.2.1 0 h.1 h.2 (some δ) (some δ')
        rw [mul_zero] at heq
        exact heq.trans rfl
      have hoff1 : ∀ (h : BSub D) (δ : D.Lab),
          D.R (.inr (.inl 0)) h.1 (eBas (some δ)) (eBas none) = 0 := fun h δ =>
        h67.2.2.2.1 0 h.1 h.2 (some δ) none
      have hoff2 : ∀ (h : BSub D) (δ' : D.Lab),
          D.R (.inr (.inl 0)) h.1 (eBas none) (eBas (some δ')) = 0 := fun h δ' =>
        h67.2.2.2.1 0 h.1 h.2 none (some δ')
      have h1 : M 1 = 1 := by
        ext δ δ'
        rw [← hblock 1 δ δ', Subgroup.coe_one, hSt.1.1, Matrix.one_apply, Matrix.one_apply]
        simp [eBas.injective.eq_iff]
      have hmul : ∀ h₁ h₂, M (h₁ * h₂) = M h₁ * M h₂ := by
        intro h₁ h₂
        ext δ δ'
        rw [← hblock (h₁ * h₂) δ δ', Subgroup.coe_mul, hSt.1.2 h₁.1 h₂.1, Matrix.mul_apply]
        rw [← Fintype.sum_equiv eBas
          (fun k => D.R (.inr (.inl 0)) h₁.1 (eBas (some δ)) (eBas k) *
            D.R (.inr (.inl 0)) h₂.1 (eBas k) (eBas (some δ')))
          (fun k => D.R (.inr (.inl 0)) h₁.1 (eBas (some δ)) k *
            D.R (.inr (.inl 0)) h₂.1 k (eBas (some δ')))
          fun _ => rfl]
        rw [Fintype.sum_option, hoff1 h₁ δ, hoff2 h₂ δ', mul_zero, zero_add, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hblock h₁ δ k, hblock h₂ k δ']
      have hunit : ∀ h, M h * (M h)ᴴ = 1 := by
        intro h
        ext δ δ'
        have hm := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp (hSt.2 h.1))
          (eBas (some δ))) (eBas (some δ'))
        rw [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.one_apply] at hm
        rw [← Fintype.sum_equiv eBas
          (fun k => D.R (.inr (.inl 0)) h.1 (eBas (some δ)) (eBas k) *
            star (D.R (.inr (.inl 0)) h.1 (eBas (some δ')) (eBas k)))
          (fun k => D.R (.inr (.inl 0)) h.1 (eBas (some δ)) k *
            (D.R (.inr (.inl 0)) h.1)ᴴ k (eBas (some δ')))
          fun _ => by simp [Matrix.conjTranspose_apply]] at hm
        rw [Fintype.sum_option, hoff1 h δ, hoff1 h δ', star_zero, mul_zero, zero_add] at hm
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eBas.injective.eq_iff,
          Option.some.injEq] at hm ⊢
        simpa [hblock] using hm
      exact isUnitaryRep_of_equiv (Equiv.refl D.Lab : D.BBas (.inr 0) ≃ D.Lab)
        ⟨⟨h1, hmul⟩, fun h => Matrix.mem_unitaryGroup_iff.mpr (hunit h)⟩
    · have hpos : (0 : D.Lab).val < γ.val := by
        rw [ZMod.val_zero, Nat.pos_iff_ne_zero]
        intro hz
        apply hγ
        have := ZMod.natCast_zmod_val γ
        rw [hz, Nat.cast_zero] at this
        exact this.symm
      let ab : {ab : D.Lab × D.Lab // ab.1.val < ab.2.val} := ⟨(0, γ), hpos⟩
      have hPs := htab (.inr (.inr (.inl ab)))
      let eBas : Option (Option D.Lab) ≃ D.Bas (.inr (.inr (.inl ab))) :=
        Equiv.refl (Option (Option D.Lab))
      have hblock : ∀ (h : BSub D) (δ δ' : D.Lab),
          D.R (.inr (.inr (.inl ab))) h.1 (eBas (some (some δ))) (eBas (some (some δ'))) = M h δ δ' :=
        fun h δ δ' => by
          have heq := h67.2.2.2.2.1 ab h.1 h.2 (some (some δ)) (some (some δ'))
          have hab0 : ab.1.1 + ab.1.2 = γ := zero_add γ
          rw [hab0] at heq
          exact heq.trans rfl
      have hoff1 : ∀ (h : BSub D) (δ : D.Lab),
          D.R (.inr (.inr (.inl ab))) h.1 (eBas (some (some δ))) (eBas none) = 0 := fun h δ =>
        h67.2.2.2.2.1 ab h.1 h.2 (some (some δ)) none
      have hoff2 : ∀ (h : BSub D) (δ : D.Lab),
          D.R (.inr (.inr (.inl ab))) h.1 (eBas (some (some δ))) (eBas (some none)) = 0 := fun h δ =>
        h67.2.2.2.2.1 ab h.1 h.2 (some (some δ)) (some none)
      have hoff3 : ∀ (h : BSub D) (δ' : D.Lab),
          D.R (.inr (.inr (.inl ab))) h.1 (eBas none) (eBas (some (some δ'))) = 0 := fun h δ' =>
        h67.2.2.2.2.1 ab h.1 h.2 none (some (some δ'))
      have hoff4 : ∀ (h : BSub D) (δ' : D.Lab),
          D.R (.inr (.inr (.inl ab))) h.1 (eBas (some none)) (eBas (some (some δ'))) = 0 := fun h δ' =>
        h67.2.2.2.2.1 ab h.1 h.2 (some none) (some (some δ'))
      have h1 : M 1 = 1 := by
        ext δ δ'
        rw [← hblock 1 δ δ', Subgroup.coe_one, hPs.1.1, Matrix.one_apply, Matrix.one_apply]
        simp [eBas.injective.eq_iff]
      have hmul : ∀ h₁ h₂, M (h₁ * h₂) = M h₁ * M h₂ := by
        intro h₁ h₂
        ext δ δ'
        rw [← hblock (h₁ * h₂) δ δ', Subgroup.coe_mul, hPs.1.2 h₁.1 h₂.1, Matrix.mul_apply]
        rw [← Fintype.sum_equiv eBas
          (fun k => D.R (.inr (.inr (.inl ab))) h₁.1 (eBas (some (some δ))) (eBas k) *
            D.R (.inr (.inr (.inl ab))) h₂.1 (eBas k) (eBas (some (some δ'))))
          (fun k => D.R (.inr (.inr (.inl ab))) h₁.1 (eBas (some (some δ))) k *
            D.R (.inr (.inr (.inl ab))) h₂.1 k (eBas (some (some δ'))))
          fun _ => rfl]
        rw [Fintype.sum_option, hoff1 h₁ δ, hoff3 h₂ δ', mul_zero, zero_add,
          Fintype.sum_option, hoff2 h₁ δ, hoff4 h₂ δ', mul_zero, zero_add, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hblock h₁ δ k, hblock h₂ k δ']
      have hunit : ∀ h, M h * (M h)ᴴ = 1 := by
        intro h
        ext δ δ'
        have hm := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp (hPs.2 h.1))
          (eBas (some (some δ)))) (eBas (some (some δ')))
        rw [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.one_apply] at hm
        rw [← Fintype.sum_equiv eBas
          (fun k => D.R (.inr (.inr (.inl ab))) h.1 (eBas (some (some δ))) (eBas k) *
            star (D.R (.inr (.inr (.inl ab))) h.1 (eBas (some (some δ'))) (eBas k)))
          (fun k => D.R (.inr (.inr (.inl ab))) h.1 (eBas (some (some δ))) k *
            (D.R (.inr (.inr (.inl ab))) h.1)ᴴ k (eBas (some (some δ'))))
          fun _ => by simp [Matrix.conjTranspose_apply]] at hm
        rw [Fintype.sum_option, hoff1 h δ, hoff1 h δ', star_zero, mul_zero, zero_add,
          Fintype.sum_option, hoff2 h δ, hoff2 h δ', star_zero, mul_zero, zero_add] at hm
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eBas.injective.eq_iff,
          Option.some.injEq] at hm ⊢
        simpa [hblock] using hm
      exact isUnitaryRep_of_equiv (Equiv.refl D.Lab : D.BBas (.inr γ) ≃ D.Lab)
        ⟨⟨h1, hmul⟩, fun h => Matrix.mem_unitaryGroup_iff.mpr (hunit h)⟩

def labEquivUnits (D : FieldData) : D.Lab ≃ D.Fqˣ :=
  let φ : D.Lab → D.Fqˣ := fun k => (uGen D) ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have hmod : i.val ≡ j.val [MOD orderOf (uGen D)] := pow_eq_pow_iff_modEq.mp hij
    rw [orderOf_uGen D] at hmod
    exact ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt i) (ZMod.val_lt j))
  have hcard : Fintype.card D.Lab = Fintype.card D.Fqˣ := by rw [card_Lab, card_Fq_units]
  Equiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

def multMat (D : FieldData) : Matrix D.Fqˣ D.Lab ℂ :=
  Matrix.of fun x i => D.multVec i x

lemma matrix_mul_eq_one_symm {X : Type} [Fintype X] [DecidableEq X]
    {A B : Matrix X X ℂ} (h : A * B = 1) : B * A = 1 := by
  have hdet : IsUnit B.det := isUnit_iff_exists_inv.mpr ⟨A.det, by
    rw [mul_comm, ← Matrix.det_mul, h, Matrix.det_one]⟩
  have hAB : A = B⁻¹ := by
    calc A = A * (B * B⁻¹) := by rw [Matrix.mul_nonsing_inv B hdet, Matrix.mul_one]
      _ = (A * B) * B⁻¹ := by rw [Matrix.mul_assoc]
      _ = B⁻¹ := by rw [h, Matrix.one_mul]
  rw [hAB, Matrix.mul_nonsing_inv B hdet]

lemma multMat_conjTranspose_mul (D : FieldData) :
    (multMat D).conjTranspose * multMat D = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, multMat, Matrix.of_apply,
    FieldData.multVec, Matrix.one_apply]
  have hq : (0 : ℝ) < (D.q - 1 : ℕ) := by have := D.one_lt_q; exact_mod_cast (by omega : 0 < D.q - 1)
  have hq' : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by
    have := D.one_lt_q; exact Nat.cast_ne_zero.mpr (by omega)
  have hcast : ((D.q : ℝ) - 1) = ((D.q - 1 : ℕ) : ℝ) := by
    have := D.one_lt_q; rw [Nat.cast_sub this.le, Nat.cast_one]
  have hstep1 : ∑ x : D.Fqˣ, star (isqrt (D.q - 1) * D.chi i (x : D.Fq)) *
        (isqrt (D.q - 1) * D.chi j (x : D.Fq)) =
      (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) *
        ∑ x : D.Fqˣ, D.chi (j - i) (x : D.Fq) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_mul', RCLike.star_def, conj_chi]
    have hchi : D.chi (-i) (x : D.Fq) * D.chi j (x : D.Fq) = D.chi (j - i) (x : D.Fq) := by
      rw [mul_comm, ← chi_add, sub_eq_add_neg]
    calc starRingEnd ℂ (isqrt (D.q - 1)) * D.chi (-i) (x : D.Fq) *
          (isqrt (D.q - 1) * D.chi j (x : D.Fq))
        = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) *
            (D.chi (-i) (x : D.Fq) * D.chi j (x : D.Fq)) := by ring
      _ = _ := by rw [hchi]
  rw [hstep1, hcast, conj_isqrt_mul_isqrt hq, sum_chi_units]
  by_cases hij : i = j
  · subst hij; simp [hq']
  · have hne : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
    simp [hij, hne]

lemma multMat_mul_conjTranspose (D : FieldData) :
    multMat D * (multMat D).conjTranspose = 1 := by
  let M : Matrix D.Fqˣ D.Fqˣ ℂ := (multMat D).submatrix id (labEquivUnits D).symm
  have hM1 : M.conjTranspose * M = 1 := by
    ext x y
    simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.one_apply]
    have hm := congrFun (congrFun (multMat_conjTranspose_mul D) ((labEquivUnits D).symm x))
      ((labEquivUnits D).symm y)
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      (labEquivUnits D).symm.injective.eq_iff] using hm
  have hM2 : M * M.conjTranspose = 1 := matrix_mul_eq_one_symm hM1
  ext x y
  have hm := congrFun (congrFun hM2 x) y
  simp only [M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
    Matrix.one_apply] at hm ⊢
  rw [← Fintype.sum_equiv (labEquivUnits D).symm
    (fun j => multMat D x ((labEquivUnits D).symm j) * star (multMat D y ((labEquivUnits D).symm j)))
    (fun j => multMat D x j * star (multMat D y j)) fun _ => rfl]
  exact hm

lemma RH_inr_eq (D : FieldData) (γ : D.Lab) (h : BSub D) :
    RH D (.inr γ) h =
      (multMat D).conjTranspose *
        D.borelModel γ ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
          ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
          ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
        multMat D := by
  ext i j
  change D.Lab at i j
  simp only [RH, FieldData.RB, matEntry]
  symm
  calc ((multMat D).conjTranspose *
          D.borelModel γ ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
            ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
            ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
          multMat D) i j
      = ∑ y : D.Fqˣ, (∑ x : D.Fqˣ, star (D.multVec i x) *
          D.borelModel γ ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
            ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
            ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) x y) * D.multVec j y := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, multMat, Matrix.of_apply]
    _ = ∑ x : D.Fqˣ, ∑ y : D.Fqˣ, star (D.multVec i x) *
          D.borelModel γ ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
            ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
            ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) x y * D.multVec j y := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm

def diagB (D : FieldData) (a d : D.Fqˣ) : BSub D := bEltEquivB D (a, d, 0)
def uB (D : FieldData) (x : D.Fq) : BSub D := bEltEquivB D (1, 1, x)

lemma diagB_mat (D : FieldData) (a d : D.Fqˣ) :
    ((diagB D a d).1 : Matrix (Fin 2) (Fin 2) D.Fq) = !![(a : D.Fq), 0; 0, (d : D.Fq)] := by
  simp [diagB, bEltEquivB, bmatG, FieldData.bmat]

lemma uB_mat (D : FieldData) (x : D.Fq) :
    ((uB D x).1 : Matrix (Fin 2) (Fin 2) D.Fq) = !![1, x; 0, 1] := by
  simp [uB, bEltEquivB, bmatG, FieldData.bmat]

lemma borelModel_isIrreducibleRep (D : FieldData) (γ : D.Lab) :
    IsIrreducibleRep (fun h : BSub D => D.borelModel γ
      ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
      ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
      ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) := by
  refine ⟨⟨1⟩, fun W hW => ?_⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    rw [Submodule.eq_top_iff']
    have hne : ∃ v ∈ W, v ≠ 0 := by
      by_contra! hall
      apply hbot
      rw [Submodule.eq_bot_iff]
      exact hall
    obtain ⟨v, hvW, hv0⟩ := hne
    have hv_pt : ∃ x₀ : D.Fqˣ, v x₀ ≠ 0 := by
      by_contra! hall
      exact hv0 (funext hall)
    obtain ⟨x₀, hx₀⟩ := hv_pt
    let projVec : D.Fqˣ → ℂ :=
      ∑ b : D.Fq, conj (D.psi (b * (x₀ : D.Fq))) •
        (D.borelModel γ (((uB D b).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
          (((uB D b).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
          (((uB D b).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)).mulVec v
    have hproj_mem : projVec ∈ W :=
      Submodule.sum_mem W fun b _ => W.smul_mem _ (hW (uB D b) v hvW)
    have hproj_eq : projVec = ((D.q : ℂ) * v x₀) • Pi.single x₀ (1 : ℂ) := by
      ext y
      simp only [projVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hterm : ∀ b : D.Fq,
          conj (D.psi (b * (x₀ : D.Fq))) *
            (D.borelModel γ (((uB D b).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
              (((uB D b).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
              (((uB D b).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)).mulVec v y =
          D.psi (b * ((y : D.Fq) - (x₀ : D.Fq))) * v y := by
        intro b
        simp only [uB_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Matrix.mulVec, dotProduct, FieldData.borelModel]
        rw [Finset.sum_eq_single y]
        · simp only [div_one, one_mul, ↓reduceIte, chi_one, conj_psi]
          calc D.psi (-(b * (x₀ : D.Fq))) * (D.psi (b * (y : D.Fq)) * v y)
              = (D.psi (-(b * (x₀ : D.Fq))) * D.psi (b * (y : D.Fq))) * v y := by ring
            _ = D.psi (-(b * (x₀ : D.Fq)) + b * (y : D.Fq)) * v y := by rw [← psi_add]
            _ = D.psi (b * ((y : D.Fq) - (x₀ : D.Fq))) * v y := by
                congr 2; ring
        · intro z _ hz
          have hne : (y : D.Fq) ≠ (z : D.Fq) := fun h => hz (Units.ext h).symm
          simp [hne]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      simp_rw [hterm, ← Finset.sum_mul]
      have hcomm : ∑ b : D.Fq, D.psi (b * ((y : D.Fq) - (x₀ : D.Fq))) =
          ∑ b : D.Fq, D.psi (((y : D.Fq) - (x₀ : D.Fq)) * b) :=
        Finset.sum_congr rfl fun b _ => by rw [mul_comm]
      rw [hcomm, sum_psi]
      by_cases hy : y = x₀
      · subst hy; simp
      · have hne : (y : D.Fq) - (x₀ : D.Fq) ≠ 0 := sub_ne_zero.mpr fun h => hy (Units.ext h)
        simp [hy, hne]
    have hcoeff_ne : (D.q : ℂ) * v x₀ ≠ 0 := by
      have hq : (D.q : ℂ) ≠ 0 := by
        have := D.one_lt_q; exact Nat.cast_ne_zero.mpr (by omega)
      exact mul_ne_zero hq hx₀
    have hsingle_x₀ : Pi.single x₀ (1 : ℂ) ∈ W := by
      have hmem : ((D.q : ℂ) * v x₀)⁻¹ • projVec ∈ W := W.smul_mem _ hproj_mem
      rwa [hproj_eq, smul_smul, inv_mul_cancel₀ hcoeff_ne, one_smul] at hmem
    have hsingle_all : ∀ y : D.Fqˣ, Pi.single y (1 : ℂ) ∈ W := by
      intro y
      let d := diagB D (x₀ * y⁻¹) 1
      have hmv := hW d (Pi.single x₀ (1 : ℂ)) hsingle_x₀
      have hmv_eq : (D.borelModel γ ((d.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
          ((d.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
          ((d.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)).mulVec (Pi.single x₀ (1 : ℂ)) =
          Pi.single y (1 : ℂ) := by
        ext z
        simp only [d, diagB_mat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Matrix.mulVec, dotProduct,
          FieldData.borelModel, chi_one, Units.val_one, Units.val_mul,
          Units.val_inv_eq_inv_val]
        rw [Finset.sum_eq_single x₀]
        · rw [Pi.single_eq_same, mul_one]
          have heq : 1 / ((x₀ : D.Fq) * (y : D.Fq)⁻¹) * (x₀ : D.Fq) = (y : D.Fq) := by
            field_simp [x₀.ne_zero, y.ne_zero]
          rw [heq]
          by_cases hz : z = y
          · subst hz; simp [psi_zero]
          · have hne : (z : D.Fq) ≠ (y : D.Fq) := fun h => hz (Units.ext h)
            simp [hne, hz]
        · intro w _ hw; rw [Pi.single_eq_of_ne hw, mul_zero]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      rwa [hmv_eq] at hmv
    intro w
    have hw_eq : w = ∑ y : D.Fqˣ, w y • Pi.single y (1 : ℂ) := by
      ext z; simp [Pi.single_apply]
    rw [hw_eq]
    exact Submodule.sum_mem W fun y _ => W.smul_mem _ (hsingle_all y)

lemma RH_isIrreducibleRep (D : FieldData) (l : D.BIrr) : IsIrreducibleRep (RH D l) := by
  cases l with
  | inl ab =>
    refine ⟨⟨()⟩, fun W hW => ?_⟩
    by_cases hbot : W = ⊥
    · exact Or.inl hbot
    · right
      rw [Submodule.eq_top_iff']
      have hne : ∃ v ∈ W, v ≠ 0 := by
        by_contra! hall; apply hbot; rw [Submodule.eq_bot_iff]; exact hall
      obtain ⟨v, hvW, hv0⟩ := hne
      let u₀ : D.BBas (.inl ab) := (PUnit.unit : Unit)
      have hu : ∀ u : D.BBas (.inl ab), u = u₀ := fun u =>
        @Subsingleton.elim (D.BBas (.inl ab)) (inferInstanceAs (Subsingleton Unit)) u u₀
      have hv_ne : v u₀ ≠ 0 := fun h => hv0 (funext fun u => by rw [hu u]; exact h)
      intro w
      have hw_eq : w = (w u₀ * (v u₀)⁻¹) • v := by
        funext u
        rw [hu u]
        simp [mul_assoc, inv_mul_cancel₀ hv_ne]
      rw [hw_eq]
      exact W.smul_mem _ hvW
  | inr γ =>
    have heq : RH D (.inr γ) = fun h => (multMat D).conjTranspose *
        D.borelModel γ ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)
          ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1)
          ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
        multMat D := funext (RH_inr_eq D γ)
    rw [heq]
    exact isIrreducibleRep_of_unitary_conj (multMat D) (multMat_conjTranspose_mul D)
      (multMat_mul_conjTranspose D) (borelModel_isIrreducibleRep D γ)

lemma RH_not_repEquiv_inl_inr (D : FieldData) (ab₁ : D.Lab × D.Lab) (γ : D.Lab) :
    ¬ RepEquiv (RH D (.inl ab₁)) (RH D (.inr γ)) := by
  intro heq
  have htr := repEquiv_trace heq (uB D 1)
  have h1 : Matrix.trace (RH D (.inl ab₁) (uB D 1)) = 1 := by
    rw [Matrix.trace]
    change ∑ i : Unit, RH D (.inl ab₁) (uB D 1) i i = 1
    rw [Fintype.sum_unique]
    simp [RH, FieldData.RB, uB_mat, chi_one]
  have h2 : Matrix.trace (RH D (.inr γ) (uB D 1)) = -1 := by
    let e : D.Lab ≃ D.BBas (.inr γ) := Equiv.refl D.Lab
    have hmat : (RH D (.inr γ) (uB D 1)).submatrix e e =
        (multMat D).conjTranspose * D.borelModel γ 1 1 1 * multMat D := by
      ext i j
      change RH D (.inr γ) (uB D 1) i j = _
      rw [RH_inr_eq, uB_mat]
      simp
    have htr_sub : Matrix.trace (RH D (.inr γ) (uB D 1)) =
        Matrix.trace ((RH D (.inr γ) (uB D 1)).submatrix e e) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
    rw [htr_sub, hmat, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
      multMat_mul_conjTranspose, Matrix.mul_one]
    simp only [Matrix.trace, Matrix.diag, FieldData.borelModel, div_one, one_mul, ↓reduceIte, chi_one]
    simpa using sum_psi_units D 1
  rw [h1, h2] at htr
  norm_num at htr

lemma RH_not_repEquiv (D : FieldData) (l₁ l₂ : D.BIrr) (hne : l₁ ≠ l₂) :
    ¬ RepEquiv (RH D l₁) (RH D l₂) := by
  cases l₁ with
  | inl ab₁ =>
    cases l₂ with
    | inl ab₂ =>
      intro heq
      rcases ab₁ with ⟨α₁, β₁⟩
      rcases ab₂ with ⟨α₂, β₂⟩
      have htr1 := repEquiv_trace heq (diagB D (uGen D) 1)
      have htr2 := repEquiv_trace heq (diagB D 1 (uGen D))
      simp only [Matrix.trace, Matrix.diag] at htr1 htr2
      have hsum1a : (∑ i : D.BBas (.inl (α₁, β₁)), RH D (.inl (α₁, β₁)) (diagB D (uGen D) 1) i i) =
          D.chi α₁ D.gen := by
        change ∑ i : Unit, RH D (.inl (α₁, β₁)) (diagB D (uGen D) 1) i i = _
        rw [Fintype.sum_unique]
        simp [RH, FieldData.RB, diagB_mat, chi_one, uGen]
      have hsum1b : (∑ i : D.BBas (.inl (α₂, β₂)), RH D (.inl (α₂, β₂)) (diagB D (uGen D) 1) i i) =
          D.chi α₂ D.gen := by
        change ∑ i : Unit, RH D (.inl (α₂, β₂)) (diagB D (uGen D) 1) i i = _
        rw [Fintype.sum_unique]
        simp [RH, FieldData.RB, diagB_mat, chi_one, uGen]
      have hsum2a : (∑ i : D.BBas (.inl (α₁, β₁)), RH D (.inl (α₁, β₁)) (diagB D 1 (uGen D)) i i) =
          D.chi β₁ D.gen := by
        change ∑ i : Unit, RH D (.inl (α₁, β₁)) (diagB D 1 (uGen D)) i i = _
        rw [Fintype.sum_unique]
        simp [RH, FieldData.RB, diagB_mat, chi_one, uGen]
      have hsum2b : (∑ i : D.BBas (.inl (α₂, β₂)), RH D (.inl (α₂, β₂)) (diagB D 1 (uGen D)) i i) =
          D.chi β₂ D.gen := by
        change ∑ i : Unit, RH D (.inl (α₂, β₂)) (diagB D 1 (uGen D)) i i = _
        rw [Fintype.sum_unique]
        simp [RH, FieldData.RB, diagB_mat, chi_one, uGen]
      rw [hsum1a, hsum1b] at htr1
      rw [hsum2a, hsum2b] at htr2
      have hα : α₁ = α₂ := by by_contra h; exact chi_gen_ne D h htr1
      have hβ : β₁ = β₂ := by by_contra h; exact chi_gen_ne D h htr2
      exact hne (by rw [hα, hβ])
    | inr γ => exact RH_not_repEquiv_inl_inr D ab₁ γ
  | inr γ =>
    cases l₂ with
    | inl ab₂ => exact fun heq => RH_not_repEquiv_inl_inr D ab₂ γ (repEquiv_symm heq)
    | inr γ' =>
      intro heq
      have htr := repEquiv_trace heq (diagB D (uGen D) (uGen D))
      have htrace_eq : ∀ δ : D.Lab,
          Matrix.trace (RH D (.inr δ) (diagB D (uGen D) (uGen D))) =
            ((D.q - 1 : ℕ) : ℂ) * D.chi δ D.gen := by
        intro δ
        let e : D.Lab ≃ D.BBas (.inr δ) := Equiv.refl D.Lab
        have hmat : (RH D (.inr δ) (diagB D (uGen D) (uGen D))).submatrix e e =
            (multMat D).conjTranspose * D.borelModel δ (D.gen) 0 (D.gen) * multMat D := by
          ext i j
          change RH D (.inr δ) (diagB D (uGen D) (uGen D)) i j = _
          rw [RH_inr_eq, diagB_mat]
          simp [uGen]
        have htr_sub : Matrix.trace (RH D (.inr δ) (diagB D (uGen D) (uGen D))) =
            Matrix.trace ((RH D (.inr δ) (diagB D (uGen D) (uGen D))).submatrix e e) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
          exact Fintype.sum_equiv e.symm _ _ fun _ => rfl
        rw [htr_sub, hmat, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
          multMat_mul_conjTranspose, Matrix.mul_one]
        simp only [Matrix.trace, Matrix.diag, FieldData.borelModel,
          div_self (gen_ne_zero D), one_mul, ↓reduceIte, zero_div, zero_mul, psi_zero, mul_one,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_Fq_units]
      rw [htrace_eq γ, htrace_eq γ'] at htr
      have hq : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by
        have := D.one_lt_q; exact Nat.cast_ne_zero.mpr (by omega)
      have hchi := mul_left_cancel₀ hq htr
      have hγ : γ = γ' := by by_contra h; exact chi_gen_ne D h hchi
      exact hne (congrArg Sum.inr hγ)

lemma RH_isIrrepSystem (D : FieldData) : IsIrrepSystem (RH D) := by
  refine ⟨RH_isUnitaryRep D, RH_isIrreducibleRep D, RH_not_repEquiv D, ?_⟩
  have hsum : ∑ l : D.BIrr, Fintype.card (D.BBas l) ^ 2 = Fintype.card (BSub D) := by
    rw [Fintype.sum_sum_type]
    have h1 : ∑ ab : D.Lab × D.Lab, Fintype.card (D.BBas (.inl ab)) ^ 2 = (D.q - 1) ^ 2 := by
      have hterm : ∀ ab : D.Lab × D.Lab, Fintype.card (D.BBas (.inl ab)) ^ 2 = 1 := fun _ => by
        change Fintype.card Unit ^ 2 = 1; simp
      simp [hterm, pow_two]
    have h2 : ∑ γ : D.Lab, Fintype.card (D.BBas (.inr γ)) ^ 2 = (D.q - 1) * (D.q - 1) ^ 2 := by
      have hterm : ∀ γ : D.Lab, Fintype.card (D.BBas (.inr γ)) ^ 2 = (D.q - 1) ^ 2 := fun _ => by
        change Fintype.card D.Lab ^ 2 = (D.q - 1) ^ 2; rw [card_Lab]
      simp [hterm]
    rw [h1, h2, card_BSub]
    have hq := D.one_lt_q
    zify [hq.le]
    ring
  exact completeness_of_irrep_sum_sq_eq_card D.BBas (RH D)
    (RH_isUnitaryRep D) (RH_isIrreducibleRep D) (RH_not_repEquiv D) hsum

def Nminus (D : FieldData) : D.Irr → Finset D.BIrr
  | .inl α => {.inl (α, α)}
  | .inr (.inl α) => {.inl (α, α), .inr (2 * α)}
  | .inr (.inr (.inl ab)) => {.inl ab.1, .inl (ab.1.2, ab.1.1), .inr (ab.1.1 + ab.1.2)}
  | .inr (.inr (.inr k)) => {.inr (D.restrLab k.1)}

def labMuEquiv (D : FieldData) : (μ : D.Irr) → AdBas D.BBas (Nminus D) μ ≃ D.Bas μ
  | .inl α =>
      { toFun := fun _ => ()
        invFun := fun _ => ⟨⟨.inl (α, α), by simp [Nminus]⟩, ()⟩
        left_inv := fun ⟨⟨l, hl⟩, P⟩ => by
          simp only [Nminus, Finset.mem_singleton] at hl
          subst hl; rfl
        right_inv := fun ⟨⟩ => rfl }
  | .inr (.inl α) =>
      { toFun := fun x => match x with
          | ⟨⟨.inl _, _⟩, _⟩ => none
          | ⟨⟨.inr _, _⟩, δ⟩ => some δ
        invFun := fun i => match i with
          | none => ⟨⟨.inl (α, α), by simp [Nminus]⟩, ()⟩
          | some δ => ⟨⟨.inr (2 * α), by simp [Nminus]⟩, δ⟩
        left_inv := fun ⟨⟨l, hl⟩, P⟩ => by
          simp only [Nminus, Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl <;> rfl
        right_inv := fun i => by rcases i with _ | δ <;> rfl }
  | .inr (.inr (.inl ⟨(α, β), hab⟩)) =>
      { toFun := fun x => match x with
          | ⟨⟨.inl ab', _⟩, _⟩ => if ab' = (α, β) then none else some none
          | ⟨⟨.inr _, _⟩, δ⟩ => some (some δ)
        invFun := fun i => match i with
          | none => ⟨⟨.inl (α, β), by simp [Nminus]⟩, ()⟩
          | some none => ⟨⟨.inl (β, α), by simp [Nminus]⟩, ()⟩
          | some (some δ) => ⟨⟨.inr (α + β), by simp [Nminus]⟩, δ⟩
        left_inv := fun ⟨⟨l, hl⟩, P⟩ => by
          have hab' : α.val < β.val := hab
          have hne : (β, α) ≠ (α, β) := fun h => by
            have := congrArg (fun p : D.Lab × D.Lab => p.1.val) h
            dsimp at this; omega
          simp only [Nminus, Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl | rfl
          · have hP : (() : D.BBas (.inl (α, β))) = P := Subsingleton.elim (α := Unit) () P
            dsimp only [FieldData.Bas]; rw [if_pos rfl, hP]
          · have hP : (() : D.BBas (.inl (β, α))) = P := Subsingleton.elim (α := Unit) () P
            dsimp only [FieldData.Bas]; rw [if_neg hne, hP]
          · rfl
        right_inv := fun i => by
          have hab' : α.val < β.val := hab
          have hne : (β, α) ≠ (α, β) := fun h => by
            have := congrArg (fun p : D.Lab × D.Lab => p.1.val) h
            dsimp at this; omega
          change Option (Option D.Lab) at i
          cases i with
          | none => dsimp only [Equiv.coe_fn_mk, FieldData.Bas]; rw [if_pos rfl]
          | some j =>
            cases j with
            | none => dsimp only [Equiv.coe_fn_mk, FieldData.Bas]; rw [if_neg hne]
            | some δ => rfl }
  | .inr (.inr (.inr k)) =>
      { toFun := fun x =>
          match x with
          | ⟨⟨.inr _, _⟩, δ⟩ => δ
          | ⟨⟨.inl _, hl⟩, _⟩ => False.elim (by simp [Nminus] at hl)
        invFun := fun δ => ⟨⟨.inr (D.restrLab k.1), by simp [Nminus]⟩, δ⟩
        left_inv := fun ⟨⟨l, hl⟩, P⟩ => by
          simp only [Nminus, Finset.mem_singleton] at hl
          subst hl; rfl
        right_inv := fun _ => rfl }

lemma labMu_eq_some_iff (D : FieldData) (μ : D.Irr) (l : D.BIrr) (P : D.BBas l) (i : D.Bas μ) :
    labMu D μ l P = some i ↔ ∃ hl : l ∈ Nminus D μ, labMuEquiv D μ ⟨⟨l, hl⟩, P⟩ = i := by
  rcases μ with α | α | ⟨⟨α, β⟩, hab⟩ | ⟨k, hk⟩
  · constructor
    · intro h
      rcases l with ab' | γ
      · simp only [labMu] at h
        split_ifs at h with h1
        subst h1
        refine ⟨by simp [Nminus], ?_⟩
        exact Subsingleton.elim (α := Unit) _ _
      · simp [labMu] at h
    · rintro ⟨hl, rfl⟩
      simp only [Nminus, Finset.mem_singleton] at hl
      subst hl; simp [labMu, labMuEquiv]; rfl
  · constructor
    · intro h
      rcases l with ab' | γ
      · simp only [labMu] at h
        split_ifs at h with h1
        subst h1
        refine ⟨by simp [Nminus], ?_⟩
        have hi := (Option.some.inj h).symm
        simp [labMuEquiv, hi]; rfl
      · simp only [labMu] at h
        split_ifs at h with h1
        subst h1
        refine ⟨by simp [Nminus], ?_⟩
        have hi := (Option.some.inj h).symm
        simp [labMuEquiv, hi]; rfl
    · rintro ⟨hl, rfl⟩
      simp only [Nminus, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> simp [labMu, labMuEquiv]
  · have hab' : α.val < β.val := hab
    have hne : (β, α) ≠ (α, β) := fun h => by
      have := congrArg (fun p : D.Lab × D.Lab => p.1.val) h
      dsimp at this; omega
    constructor
    · intro h
      rcases l with ab' | γ
      · by_cases h1 : ab' = (α, β)
        · subst h1
          simp only [labMu, ↓reduceIte] at h
          have hi := (Option.some.inj h).symm
          refine ⟨by simp [Nminus], ?_⟩
          simp [labMuEquiv, hi]; rfl
        · by_cases h2 : ab' = (β, α)
          · subst h2
            simp only [labMu, if_neg h1, ↓reduceIte] at h
            have hi := (Option.some.inj h).symm
            refine ⟨by simp [Nminus], ?_⟩
            simp [labMuEquiv, hne, hi]; rfl
          · simp [labMu, h1, h2] at h
      · simp only [labMu] at h
        split_ifs at h with h1
        subst h1
        have hi := (Option.some.inj h).symm
        refine ⟨by simp [Nminus], ?_⟩
        simp [labMuEquiv, hi]; rfl
    · rintro ⟨hl, rfl⟩
      simp only [Nminus, Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl <;> simp [labMu, labMuEquiv, hne]
  · constructor
    · intro h
      rcases l with ab' | γ
      · simp [labMu] at h
      · simp only [labMu] at h
        split_ifs at h with h1
        subst h1
        have hi := (Option.some.inj h).symm
        refine ⟨by simp [Nminus], ?_⟩
        simp [labMuEquiv, hi]; rfl
    · rintro ⟨hl, rfl⟩
      simp only [Nminus, Finset.mem_singleton] at hl
      subst hl; simp [labMu, labMuEquiv]

def RG (D : FieldData) (μ : D.Irr) (g : D.G) :
    Matrix (AdBas D.BBas (Nminus D) μ) (AdBas D.BBas (Nminus D) μ) ℂ :=
  (D.R μ g).submatrix (labMuEquiv D μ) (labMuEquiv D μ)

lemma RG_isIrrepSystem (D : FieldData) : IsIrrepSystem (RG D) := by
  have htab := table_2_completeness D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro μ; exact isUnitaryRep_of_equiv (labMuEquiv D μ) (htab.1 μ)
  · intro μ; exact isIrreducibleRep_of_equiv (labMuEquiv D μ) (htab.2.1 μ)
  · intro μ₁ μ₂ hne heq
    apply htab.2.2.1 μ₁ μ₂ hne
    have heq' := repEquiv_of_submatrix_left (labMuEquiv D μ₁).symm
      (repEquiv_of_submatrix_right (labMuEquiv D μ₂).symm heq)
    have h1 : (fun g => (RG D μ₁ g).submatrix (labMuEquiv D μ₁).symm (labMuEquiv D μ₁).symm) = D.R μ₁ := by
      ext g i j; simp [RG]
    have h2 : (fun g => (RG D μ₂ g).submatrix (labMuEquiv D μ₂).symm (labMuEquiv D μ₂).symm) = D.R μ₂ := by
      ext g i j; simp [RG]
    rwa [h1, h2] at heq'
  · intro ι _ _ ρ hm hi
    obtain ⟨μ, hμ⟩ := htab.2.2.2.2.2 ι ρ hm hi
    exact ⟨μ, repEquiv_of_submatrix_left (labMuEquiv D μ) hμ⟩

lemma RG_isSubgroupAdapted (D : FieldData) :
    IsSubgroupAdapted (BSub D) D.BBas (Nminus D) (RH D) (RG D) := by
  have h67 := lemma_6_7 D
  intro μ h Q P
  rcases Q with ⟨⟨l₁, hl₁⟩, q⟩
  rcases P with ⟨⟨l₂, hl₂⟩, p⟩
  rcases μ with α | α | ⟨⟨α, β⟩, hab⟩ | ⟨k, hk⟩
  · simp only [Nminus, Finset.mem_singleton] at hl₁ hl₂
    subst hl₁; subst hl₂
    simp only [RG, Matrix.submatrix_apply, labMuEquiv, RH, ↓reduceDIte]
    exact h67.2.2.1 α h.1 h.2
  · simp only [Nminus, Finset.mem_insert, Finset.mem_singleton] at hl₁ hl₂
    rcases hl₁ with rfl | rfl <;> rcases hl₂ with rfl | rfl
    · simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, RH, ↓reduceDIte]
      exact h67.2.2.2.1 α h.1 h.2 none none
    · have hne : (⟨.inl (α, α), hl₁⟩ : Nminus D (.inr (.inl α))) ≠ ⟨.inr (2 * α), hl₂⟩ := by simp
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne]
      exact h67.2.2.2.1 α h.1 h.2 none (some p)
    · have hne : (⟨.inr (2 * α), hl₁⟩ : Nminus D (.inr (.inl α))) ≠ ⟨.inl (α, α), hl₂⟩ := by simp
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne]
      exact h67.2.2.2.1 α h.1 h.2 (some q) none
    · simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, RH, ↓reduceDIte, cast_eq]
      exact h67.2.2.2.1 α h.1 h.2 (some q) (some p)
  · simp only [Nminus, Finset.mem_insert, Finset.mem_singleton] at hl₁ hl₂
    have hab' : α.val < β.val := hab
    have hab_ne : (β, α) ≠ (α, β) := fun h => by
      have := congrArg (fun x : D.Lab × D.Lab => x.1.val) h
      dsimp at this; omega
    rcases hl₁ with rfl | rfl | rfl <;> rcases hl₂ with rfl | rfl | rfl
    · simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, RH, ↓reduceDIte, ↓reduceIte]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 none none
    · have hne : (⟨.inl (α, β), hl₁⟩ : Nminus D (.inr (.inr (.inl ⟨(α, β), hab⟩)))) ≠
          ⟨.inl (β, α), hl₂⟩ := fun h => hab_ne (Sum.inl.inj (congrArg Subtype.val h)).symm
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne, ↓reduceIte]
      dsimp only [FieldData.Bas]
      rw [if_neg hab_ne]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 none (some none)
    · have hne : (⟨.inl (α, β), hl₁⟩ : Nminus D (.inr (.inr (.inl ⟨(α, β), hab⟩)))) ≠
          ⟨.inr (α + β), hl₂⟩ := by simp
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne, ↓reduceIte]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 none (some (some p))
    · have hne : (⟨.inl (β, α), hl₁⟩ : Nminus D (.inr (.inr (.inl ⟨(α, β), hab⟩)))) ≠
          ⟨.inl (α, β), hl₂⟩ := fun h => hab_ne (Sum.inl.inj (congrArg Subtype.val h))
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne, ↓reduceIte]
      dsimp only [FieldData.Bas]
      rw [if_neg hab_ne]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 (some none) none
    · simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, RH, ↓reduceDIte, cast_eq]
      dsimp only [FieldData.Bas]
      rw [if_neg hab_ne]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 (some none) (some none)
    · have hne : (⟨.inl (β, α), hl₁⟩ : Nminus D (.inr (.inr (.inl ⟨(α, β), hab⟩)))) ≠
          ⟨.inr (α + β), hl₂⟩ := by simp
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne]
      dsimp only [FieldData.Bas]
      rw [if_neg hab_ne]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 (some none) (some (some p))
    · have hne : (⟨.inr (α + β), hl₁⟩ : Nminus D (.inr (.inr (.inl ⟨(α, β), hab⟩)))) ≠
          ⟨.inl (α, β), hl₂⟩ := by simp
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne, ↓reduceIte]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 (some (some q)) none
    · have hne : (⟨.inr (α + β), hl₁⟩ : Nminus D (.inr (.inr (.inl ⟨(α, β), hab⟩)))) ≠
          ⟨.inl (β, α), hl₂⟩ := by simp
      simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, dif_neg hne]
      dsimp only [FieldData.Bas]
      rw [if_neg hab_ne]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 (some (some q)) (some none)
    · simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, RH, ↓reduceDIte, cast_eq]
      exact h67.2.2.2.2.1 ⟨(α, β), hab⟩ h.1 h.2 (some (some q)) (some (some p))
  · simp only [Nminus, Finset.mem_singleton] at hl₁ hl₂
    subst hl₁; subst hl₂
    simp only [RG, Matrix.submatrix_apply, labMuEquiv, Equiv.coe_fn_mk, RH, ↓reduceDIte, cast_eq]
    exact h67.2.2.2.2.2.1 ⟨k, hk⟩ h.1 h.2 q p

/-! ### Part 4a: Unitarity / Isometry of `mackeyNopMat` (Conjunct 4) -/

def abOf (D : FieldData) : ∀ l : D.BIrr, D.BBas l → D.Lab × D.Lab
  | .inl αβ, _ => (αβ.2, αβ.1)
  | .inr γ, δ => (γ - (show D.Lab from δ), (show D.Lab from δ))

lemma utwW_eq_ite (D : FieldData) (l : D.BIrr) (ab : D.Lab × D.Lab) (P : D.BBas l) :
    utwW D l ab P = if ab = abOf D l P then 1 else 0 := by
  cases l with
  | inl αβ => rfl
  | inr γ => rfl

lemma abOf_inj (D : FieldData) : ∀ l : D.BIrr, Function.Injective (abOf D l)
  | .inl αβ => fun P₁ P₂ _ =>
      @Subsingleton.elim (D.BBas (.inl αβ)) (inferInstanceAs (Subsingleton Unit)) P₁ P₂
  | .inr _ => fun _ _ h => congrArg Prod.snd h

lemma uB_sum_RB (D : FieldData) (γ' δ₀ : D.Lab) (x₁ x₂ : D.Fq) :
    ∑ δ : D.Lab,
      star (D.RB (.inr γ') !![1, x₁; 0, 1] δ δ₀) *
        D.RB (.inr γ') !![1, x₂; 0, 1] δ δ₀ =
      ((D.q - 1 : ℕ) : ℂ)⁻¹ * ∑ y : D.Fqˣ, D.psi ((x₂ - x₁) * (y : D.Fq)) := by
  have h2 : uB D x₁ * uB D (x₂ - x₁) = uB D x₂ := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, uB_mat]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hmul : RH D (.inr γ') (uB D x₂) =
      RH D (.inr γ') (uB D x₁) * RH D (.inr γ') (uB D (x₂ - x₁)) := by
    rw [← (RH_isUnitaryRep D (.inr γ')).1.2, h2]
  have hu1 : RH D (.inr γ') (uB D x₁) * (RH D (.inr γ') (uB D x₁))ᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp ((RH_isUnitaryRep D (.inr γ')).2 (uB D x₁))
  have hu2 : (RH D (.inr γ') (uB D x₁))ᴴ * RH D (.inr γ') (uB D x₁) = 1 :=
    matrix_mul_eq_one_symm hu1
  have hprod : (RH D (.inr γ') (uB D x₁))ᴴ * RH D (.inr γ') (uB D x₂) =
      RH D (.inr γ') (uB D (x₂ - x₁)) := by
    rw [hmul, ← Matrix.mul_assoc, hu2, Matrix.one_mul]
  let e : D.Lab ≃ D.BBas (.inr γ') := Equiv.refl D.Lab
  have hsum : ∑ δ : D.Lab,
      star (D.RB (.inr γ') !![1, x₁; 0, 1] δ δ₀) *
        D.RB (.inr γ') !![1, x₂; 0, 1] δ δ₀ =
      ((RH D (.inr γ') (uB D x₁))ᴴ * RH D (.inr γ') (uB D x₂)) (e δ₀) (e δ₀) := by
    rw [Matrix.mul_apply]
    rw [← Fintype.sum_equiv e
      (fun δ : D.Lab => (RH D (.inr γ') (uB D x₁))ᴴ (e δ₀) (e δ) *
        RH D (.inr γ') (uB D x₂) (e δ) (e δ₀))
      (fun δ : D.BBas (.inr γ') => (RH D (.inr γ') (uB D x₁))ᴴ (e δ₀) δ *
        RH D (.inr γ') (uB D x₂) δ (e δ₀))
      fun _ => rfl]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [Matrix.conjTranspose_apply]
    have h1 : D.RB (.inr γ') !![1, x₁; 0, 1] δ δ₀ = RH D (.inr γ') (uB D x₁) (e δ) (e δ₀) := by
      change D.RB (.inr γ') !![1, x₁; 0, 1] δ δ₀ = D.RB (.inr γ') ((uB D x₁).1 : Matrix (Fin 2) (Fin 2) D.Fq) δ δ₀
      rw [uB_mat]
    have h2' : D.RB (.inr γ') !![1, x₂; 0, 1] δ δ₀ = RH D (.inr γ') (uB D x₂) (e δ) (e δ₀) := by
      change D.RB (.inr γ') !![1, x₂; 0, 1] δ δ₀ = D.RB (.inr γ') ((uB D x₂).1 : Matrix (Fin 2) (Fin 2) D.Fq) δ δ₀
      rw [uB_mat]
    rw [h1, h2']
  rw [hsum, hprod]
  have hentry : RH D (.inr γ') (uB D (x₂ - x₁)) (e δ₀) (e δ₀) =
      ((multMat D).conjTranspose * D.borelModel γ' 1 (x₂ - x₁) 1 * multMat D) δ₀ δ₀ := by
    change RH D (.inr γ') (uB D (x₂ - x₁)) δ₀ δ₀ = _
    rw [RH_inr_eq, uB_mat]
    simp
  rw [hentry]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, multMat, Matrix.of_apply,
    FieldData.multVec]
  have hinner : ∀ y : D.Fqˣ,
      (∑ x : D.Fqˣ, star (isqrt (D.q - 1) * D.chi δ₀ (x : D.Fq)) *
        D.borelModel γ' 1 (x₂ - x₁) 1 x y) *
        (isqrt (D.q - 1) * D.chi δ₀ (y : D.Fq)) =
      (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) * D.psi ((x₂ - x₁) * (y : D.Fq)) := by
    intro y
    simp only [FieldData.borelModel, div_one, one_mul, chi_one]
    rw [Finset.sum_eq_single y]
    · simp only [↓reduceIte]
      rw [star_mul', RCLike.star_def, conj_chi]
      have hchi : D.chi (-δ₀) (y : D.Fq) * D.chi δ₀ (y : D.Fq) = 1 := by
        rw [← chi_add, neg_add_cancel, chi_zero_lab D y.ne_zero]
      calc _
          = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) *
              (D.chi (-δ₀) (y : D.Fq) * D.chi δ₀ (y : D.Fq)) *
              D.psi ((x₂ - x₁) * (y : D.Fq)) := by ring
        _ = (conj (isqrt (D.q - 1)) * isqrt (D.q - 1)) * D.psi ((x₂ - x₁) * (y : D.Fq)) := by
              rw [hchi, mul_one]
    · intro x _ hx
      have hne : (x : D.Fq) ≠ (y : D.Fq) := fun h => hx (Units.ext h)
      simp [hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  simp_rw [hinner, ← Finset.mul_sum]
  have hq : (0 : ℝ) < (D.q - 1 : ℕ) := by have := D.one_lt_q; exact_mod_cast (by omega : 0 < D.q - 1)
  have hcast : ((D.q : ℝ) - 1) = ((D.q - 1 : ℕ) : ℝ) := by
    have := D.one_lt_q; rw [Nat.cast_sub this.le, Nat.cast_one]
  rw [hcast, conj_isqrt_mul_isqrt hq]
  push_cast
  rfl

lemma cast_BBas_inj (D : FieldData) {a b : D.BIrr} (h : a = b) {x y : D.BBas a}
    (hxy : cast (congrArg D.BBas h) x = cast (congrArg D.BBas h) y) : x = y := by
  subst h; exact hxy

lemma mackeyNopMat_iso (D : FieldData) :
    (mackeyNopMat D).conjTranspose * mackeyNopMat D = 1 := by
  ext tb₁ tb₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.conjTranspose_apply]
  rcases tb₁ with ⟨t₁, ⟨l₁, P₁, Q₁⟩⟩
  rcases tb₂ with ⟨t₂, ⟨l₂, P₂, Q₂⟩⟩
  by_cases hl12 : l₁ = l₂
  swap
  · have hzero : ∀ m : MackeyMid D,
        star (mackeyNopMat D m (t₁, ⟨l₁, P₁, Q₁⟩)) * mackeyNopMat D m (t₂, ⟨l₂, P₂, Q₂⟩) = 0 := by
      intro m
      by_cases h1 : l₁ = m.1.1.1
      · have h2 : l₂ ≠ m.1.1.1 := fun h => hl12 (h1.trans h.symm)
        simp [mackeyNopMat, h2]
      · simp [mackeyNopMat, h1]
    rw [Finset.sum_eq_zero fun m _ => hzero m, if_neg]
    intro h; exact hl12 (congrArg (fun x => x.2.1) h)
  subst hl12
  by_cases hQ : Q₁ = Q₂
  swap
  · have hzero : ∀ m : MackeyMid D,
        star (mackeyNopMat D m (t₁, ⟨l₁, P₁, Q₁⟩)) * mackeyNopMat D m (t₂, ⟨l₁, P₂, Q₂⟩) = 0 := by
      intro m
      by_cases hl : l₁ = m.1.1.1
      · by_cases hm2 : m.2.2 = cast (congrArg D.BBas hl) Q₁
        · have hne : m.2.2 ≠ cast (congrArg D.BBas hl) Q₂ := fun h =>
            hQ (cast_BBas_inj D hl (hm2.symm.trans h))
          simp [mackeyNopMat, hl, hne]
        · simp [mackeyNopMat, hl, hm2]
      · simp [mackeyNopMat, hl]
    rw [Finset.sum_eq_zero fun m _ => hzero m, if_neg]
    intro h
    have h2 : (⟨l₁, P₁, Q₁⟩ : D.BOutLabel) = ⟨l₁, P₂, Q₂⟩ := congrArg Prod.snd h
    have h2' := (Sigma.ext_iff.mp h2).2
    simp only [heq_eq_eq, Prod.mk.injEq] at h2'
    exact hQ h2'.2
  subst hQ
  rcases t₁ with ⟨⟩ | x₁ <;> rcases t₂ with ⟨⟩ | x₂
  · by_cases hP : P₁ = P₂
    · subst hP
      simp only [↓reduceIte]
      let m₀ : MackeyMid D := ⟨⟨(l₁, l₁, false, l₁), ⟨rfl, rfl⟩⟩, (P₁, Q₁)⟩
      rw [Finset.sum_eq_single m₀]
      · simp [m₀, mackeyNopMat]
      · intro m _ hm
        rcases m with ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, ⟨pt, q⟩⟩
        by_contra hnz
        have h1 : mackeyNopMat D ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, ⟨pt, q⟩⟩ (.inl (), ⟨l₁, P₁, Q₁⟩) ≠ 0 := by
          intro hz; apply hnz; rw [hz, star_zero, zero_mul]
        simp only [mackeyNopMat, Matrix.of_apply] at h1
        split_ifs at h1 with hl hq hω hlt hpt
        · subst hl; subst hω; subst hlt
          dsimp only [ValidIn, ↓reduceIte] at hv
          rcases hv with ⟨rfl, _⟩
          dsimp only [cast_eq] at hq hpt
          subst hq; subst hpt
          exact hm rfl
        all_goals exact h1 rfl
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · have hzero : ∀ m : MackeyMid D,
          star (mackeyNopMat D m (.inl (), ⟨l₁, P₁, Q₁⟩)) *
            mackeyNopMat D m (.inl (), ⟨l₁, P₂, Q₁⟩) = 0 := by
        intro m
        rcases m with ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, ⟨pt, q⟩⟩
        by_cases hl : l₁ = l
        swap; · simp [mackeyNopMat, hl]
        subst hl
        by_cases hq : q = Q₁
        swap; · simp [mackeyNopMat, hq]
        subst hq
        by_cases hω : ω = false
        swap; · simp [mackeyNopMat, hω]
        subst hω
        by_cases hlt : lt = l₁
        swap; · simp [mackeyNopMat, hlt]
        subst hlt
        simp only [mackeyNopMat, Matrix.of_apply, ↓reduceDIte, ↓reduceIte, cast_eq]
        split_ifs with h1 h2
        · exact absurd (h1.symm.trans h2) hP
        · simp
        · simp
        · simp
      rw [Finset.sum_eq_zero fun m _ => hzero m, if_neg]
      intro h
      have h2 : (⟨l₁, P₁, Q₁⟩ : D.BOutLabel) = ⟨l₁, P₂, Q₁⟩ := congrArg Prod.snd h
      have h2' := (Sigma.ext_iff.mp h2).2
      simp only [heq_eq_eq, Prod.mk.injEq] at h2'
      exact hP h2'.1
  · have hzero : ∀ m : MackeyMid D,
        star (mackeyNopMat D m (.inl (), ⟨l₁, P₁, Q₁⟩)) *
          mackeyNopMat D m (.inr x₂, ⟨l₁, P₂, Q₁⟩) = 0 := by
      intro m
      rcases m with ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, ⟨pt, q⟩⟩
      cases ω <;> simp [mackeyNopMat]
    rw [Finset.sum_eq_zero fun m _ => hzero m, if_neg]
    intro h; cases congrArg Prod.fst h
  · have hzero : ∀ m : MackeyMid D,
        star (mackeyNopMat D m (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
          mackeyNopMat D m (.inl (), ⟨l₁, P₂, Q₁⟩) = 0 := by
      intro m
      rcases m with ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, ⟨pt, q⟩⟩
      cases ω <;> simp [mackeyNopMat]
    rw [Finset.sum_eq_zero fun m _ => hzero m, if_neg]
    intro h; cases congrArg Prod.fst h
  · by_cases hP : P₁ = P₂
    swap
    · have hzero : ∀ m : MackeyMid D,
          star (mackeyNopMat D m (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
            mackeyNopMat D m (.inr x₂, ⟨l₁, P₂, Q₁⟩) = 0 := by
        intro m
        rcases m with ⟨⟨⟨l, κ, ω, lt⟩, hv⟩, ⟨pt, q⟩⟩
        by_cases hl : l₁ = l
        swap; · simp [mackeyNopMat, hl]
        subst hl
        by_cases hq : q = Q₁
        swap; · simp [mackeyNopMat, hq]
        subst hq
        by_cases hω : ω = true
        swap; · simp [mackeyNopMat, hω]
        subst hω
        rcases κ with ab | γ
        swap; · simp [mackeyNopMat]
        simp only [mackeyNopMat, Matrix.of_apply, ↓reduceDIte, ↓reduceIte, cast_eq,
          utwW_eq_ite]
        cases tLab D lt ab with
        | none => simp
        | some Pt =>
          by_cases hab1 : ab = abOf D l₁ P₁
          · have hab2 : abOf D l₁ P₁ ≠ abOf D l₁ P₂ := fun h => hP (abOf_inj D l₁ h)
            simp [hab1, hab2]
          · simp [hab1]
      rw [Finset.sum_eq_zero fun m _ => hzero m, if_neg]
      intro h
      have h2 : (⟨l₁, P₁, Q₁⟩ : D.BOutLabel) = ⟨l₁, P₂, Q₁⟩ := congrArg Prod.snd h
      have h2' := (Sigma.ext_iff.mp h2).2
      simp only [heq_eq_eq, Prod.mk.injEq] at h2'
      exact hP h2'.1
    subst hP
    let ab₀ : D.Lab × D.Lab := abOf D l₁ P₁
    have hval1 : ValidIn D l₁ (.inl ab₀) true (.inl ab₀) :=
      ⟨ab₀, rfl, by cases l₁ with | inl _ => rfl | inr _ => exact sub_add_cancel _ (show D.Lab from P₁), rfl⟩
    have hval2 : ValidIn D l₁ (.inl ab₀) true (.inr (ab₀.1 + ab₀.2)) :=
      ⟨ab₀, rfl, by cases l₁ with | inl _ => rfl | inr _ => exact sub_add_cancel _ (show D.Lab from P₁), rfl⟩
    let ir₁ : InReg D := ⟨(l₁, .inl ab₀, true, .inl ab₀), hval1⟩
    let ir₂ : InReg D := ⟨(l₁, .inl ab₀, true, .inr (ab₀.1 + ab₀.2)), hval2⟩
    have hir_ne : ir₁ ≠ ir₂ := by
      intro h
      have h4 := congrArg (fun x : InReg D => x.1.2.2.2) h
      cases h4
    rw [Fintype.sum_sigma]
    have hsplit : (∑ x : InReg D, ∑ pq : D.BBas x.1.2.2.2 × D.BBas x.1.1,
        star (mackeyNopMat D ⟨x, pq⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
          mackeyNopMat D ⟨x, pq⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) =
        (∑ pq : D.BBas ir₁.1.2.2.2 × D.BBas ir₁.1.1,
          star (mackeyNopMat D ⟨ir₁, pq⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
            mackeyNopMat D ⟨ir₁, pq⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) +
        (∑ pq : D.BBas ir₂.1.2.2.2 × D.BBas ir₂.1.1,
          star (mackeyNopMat D ⟨ir₂, pq⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
            mackeyNopMat D ⟨ir₂, pq⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) := by
      rw [Finset.sum_eq_add ir₁ ir₂ hir_ne]
      · intro x _ hx
        rcases hx with ⟨hx1, hx2⟩
        rw [Finset.sum_eq_zero]
        intro pq _
        rcases x with ⟨⟨l, κ, ω, lt⟩, hv⟩
        rcases pq with ⟨pt, q⟩
        by_cases hl : l₁ = l
        swap; · simp [mackeyNopMat, hl]
        subst hl
        by_cases hq : q = Q₁
        swap; · simp [mackeyNopMat, hq]
        subst hq
        by_cases hω : ω = true
        swap; · simp [mackeyNopMat, hω]
        subst hω
        rcases κ with ab | γ
        swap; · simp [mackeyNopMat]
        by_cases hab : ab = ab₀
        swap
        · simp only [mackeyNopMat, Matrix.of_apply, ↓reduceDIte, ↓reduceIte, cast_eq,
            utwW_eq_ite]
          cases tLab D lt ab with
          | none => simp
          | some Pt => simp [hab, ab₀]
        subst hab
        dsimp only [ValidIn, ↓reduceIte] at hv
        rcases hv with ⟨ab', hκeq, _, hlt⟩
        have hab' : ab' = ab₀ := (Sum.inl.inj hκeq).symm
        subst hab'
        rcases lt with αβ | γ
        · have heq : αβ = ab₀ := hlt.symm
          subst heq
          exact absurd rfl hx1
        · have heq : ab₀.1 + ab₀.2 = γ := hlt
          subst heq
          exact absurd rfl hx2
      · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hsplit]
    have hterm1 : (∑ pq : D.BBas ir₁.1.2.2.2 × D.BBas ir₁.1.1,
        star (mackeyNopMat D ⟨ir₁, pq⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
          mackeyNopMat D ⟨ir₁, pq⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) =
        conj (isqrt D.q) * isqrt D.q := by
      rw [Fintype.sum_prod_type]
      have hinner : ∀ pt : D.BBas ir₁.1.2.2.2,
          (∑ q : D.BBas l₁,
            star (mackeyNopMat D ⟨ir₁, (pt, q)⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
              mackeyNopMat D ⟨ir₁, (pt, q)⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) =
          conj (isqrt D.q) * isqrt D.q := by
        intro pt
        rw [Finset.sum_eq_single Q₁]
        · have hcard : Fintype.card (D.BBas (.inl ab₀)) = 1 := by
            change Fintype.card Unit = 1; simp
          simp only [ir₁, mackeyNopMat, Matrix.of_apply, ↓reduceDIte, ↓reduceIte, cast_eq,
            tLab, utwW_eq_ite, ab₀, FieldData.RB, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one]
          rw [chi_one, chi_one, hcard]
          simp [RCLike.star_def]
        · intro q _ hq
          simp [ir₁, mackeyNopMat, hq]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      let pt₀ : D.BBas ir₁.1.2.2.2 := (() : D.BBas (.inl ab₀))
      have hsub : ∀ pt : D.BBas ir₁.1.2.2.2, pt = pt₀ := fun pt =>
        @Subsingleton.elim (D.BBas (.inl ab₀)) (inferInstanceAs (Subsingleton Unit)) pt pt₀
      rw [Finset.sum_eq_single pt₀
        (fun pt _ hpt => absurd (hsub pt) hpt)
        (fun hm => absurd (Finset.mem_univ _) hm)]
      exact hinner pt₀
    have hterm2 : (∑ pq : D.BBas ir₂.1.2.2.2 × D.BBas ir₂.1.1,
        star (mackeyNopMat D ⟨ir₂, pq⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
          mackeyNopMat D ⟨ir₂, pq⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) =
        (conj (isqrt D.q) * isqrt D.q) *
          ∑ y : D.Fqˣ, D.psi ((x₂ - x₁) * (y : D.Fq)) := by
      let eD : D.Lab ≃ D.BBas ir₂.1.2.2.2 := Equiv.refl D.Lab
      have hinner : ∀ δ : D.Lab,
          (∑ q : D.BBas l₁,
            star (mackeyNopMat D ⟨ir₂, (eD δ, q)⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
              mackeyNopMat D ⟨ir₂, (eD δ, q)⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩)) =
          (conj (isqrt D.q) * isqrt D.q) * ((D.q - 1 : ℕ) : ℂ) *
            (star (D.RB (.inr (ab₀.1 + ab₀.2)) !![1, x₁; 0, 1] δ ab₀.1) *
              D.RB (.inr (ab₀.1 + ab₀.2)) !![1, x₂; 0, 1] δ ab₀.1) := by
        intro δ
        rw [Finset.sum_eq_single Q₁]
        · have hcard : (Fintype.card (D.BBas (.inr (ab₀.1 + ab₀.2))) : ℝ) = ((D.q - 1 : ℕ) : ℝ) := by
            change (Fintype.card D.Lab : ℝ) = _; rw [card_Lab]
          have hq1_nonneg : (0 : ℝ) ≤ (D.q - 1 : ℕ) := Nat.cast_nonneg _
          have hsqrt : (Real.sqrt ((D.q - 1 : ℕ) : ℝ) : ℂ) *
              (Real.sqrt ((D.q - 1 : ℕ) : ℝ) : ℂ) = ((D.q - 1 : ℕ) : ℂ) := by
            rw [← Complex.ofReal_mul, Real.mul_self_sqrt hq1_nonneg]
            norm_cast
          simp only [ir₂, mackeyNopMat, Matrix.of_apply, ↓reduceDIte, ↓reduceIte, cast_eq,
            tLab, utwW_eq_ite, ab₀]
          rw [hcard, ← hsqrt]
          have heq :
              star (isqrt D.q * (Real.sqrt ((D.q - 1 : ℕ) : ℝ) : ℂ) *
                  D.RB (.inr ((abOf D l₁ P₁).1 + (abOf D l₁ P₁).2)) !![1, x₁; 0, 1] (eD δ)
                    (abOf D l₁ P₁).1 * 1) *
                (isqrt D.q * (Real.sqrt ((D.q - 1 : ℕ) : ℝ) : ℂ) *
                  D.RB (.inr ((abOf D l₁ P₁).1 + (abOf D l₁ P₁).2)) !![1, x₂; 0, 1] (eD δ)
                    (abOf D l₁ P₁).1 * 1) =
              conj (isqrt D.q) * isqrt D.q *
                  ((Real.sqrt ((D.q - 1 : ℕ) : ℝ) : ℂ) *
                    (Real.sqrt ((D.q - 1 : ℕ) : ℝ) : ℂ)) *
                (star (D.RB (.inr ((abOf D l₁ P₁).1 + (abOf D l₁ P₁).2)) !![1, x₁; 0, 1] (eD δ)
                    (abOf D l₁ P₁).1) *
                  D.RB (.inr ((abOf D l₁ P₁).1 + (abOf D l₁ P₁).2)) !![1, x₂; 0, 1] (eD δ)
                    (abOf D l₁ P₁).1) := by
            simp only [star_mul', mul_one, RCLike.star_def, Complex.conj_ofReal]
            ring
          exact heq
        · intro q _ hq
          simp [ir₂, mackeyNopMat, hq]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      rw [Fintype.sum_prod_type, ← Fintype.sum_equiv eD
        (fun δ : D.Lab => ∑ q : D.BBas l₁,
          star (mackeyNopMat D ⟨ir₂, (eD δ, q)⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
            mackeyNopMat D ⟨ir₂, (eD δ, q)⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩))
        (fun δ : D.BBas ir₂.1.2.2.2 => ∑ q : D.BBas l₁,
          star (mackeyNopMat D ⟨ir₂, (δ, q)⟩ (.inr x₁, ⟨l₁, P₁, Q₁⟩)) *
            mackeyNopMat D ⟨ir₂, (δ, q)⟩ (.inr x₂, ⟨l₁, P₁, Q₁⟩))
        fun _ => rfl]
      simp_rw [hinner, ← Finset.mul_sum]
      rw [uB_sum_RB]
      have hq1_ne : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by
        have := D.one_lt_q; exact Nat.cast_ne_zero.mpr (by omega)
      rw [mul_assoc, ← mul_assoc ((D.q - 1 : ℕ) : ℂ), mul_inv_cancel₀ hq1_ne, one_mul]
    rw [hterm1, hterm2, ← mul_one_add]
    have hq_pos : (0 : ℝ) < D.q := by have := D.one_lt_q; exact_mod_cast (by omega : 0 < D.q)
    have hq_ne : (D.q : ℂ) ≠ 0 := by have := D.one_lt_q; exact_mod_cast (by omega : D.q ≠ 0)
    rw [conj_isqrt_mul_isqrt hq_pos, sum_psi_units]
    have hcast : (1 : ℂ) + ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) := by
      have hq := D.one_lt_q
      rw [Nat.cast_sub hq.le, Nat.cast_one]
      ring
    by_cases hx : x₁ = x₂
    · subst hx
      simp [sub_self, hcast, inv_mul_cancel₀ hq_ne]
    · have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      have heq_pairs : ¬ ((Sum.inr x₁ : CosetT D), (⟨l₁, P₁, Q₁⟩ : D.BOutLabel)) =
          (.inr x₂, ⟨l₁, P₁, Q₁⟩) := fun h => hx (Sum.inr.inj (congrArg Prod.fst h))
      simp [hne, heq_pairs]

/-! ### Part 4b: Mackey instantiation for `BSub D < D.G` -/

def omegaSet (D : FieldData) : Set D.G := {1, wGL D}

lemma wGL_ne_one (D : FieldData) : wGL D ≠ 1 := by
  intro h
  have h01 := congrFun (congrFun (congrArg (fun x : D.G => (x : Matrix (Fin 2) (Fin 2) D.Fq)) h) 0) 1
  simp [wGL] at h01

lemma wGL_mul_self (D : FieldData) : wGL D * wGL D = 1 := by
  apply Units.ext
  rw [Units.val_mul, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wGL]

lemma wGL_inv (D : FieldData) : (wGL D)⁻¹ = wGL D :=
  inv_eq_of_mul_eq_one_right (wGL_mul_self D)

lemma uB_mul_wGL (D : FieldData) (x : D.Fq) :
    ((uB D x : BSub D) : D.G) * wGL D = cosetRep D (.inr x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uB_mat, wGL, cosetRep]

def tOmega (D : FieldData) : D.G → Set (BSub D) :=
  fun ω => if ω = 1 then {1} else {b : BSub D | ∃ x : D.Fq, b = uB D x}

lemma BSub_double_coset_one_10 (D : FieldData) (h k : BSub D) :
    ((h.1 * (1 : D.G) * k.1 : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := by
  have hhk : ((h * k : BSub D) : D.G) = h.1 * k.1 := rfl
  rw [mul_one, ← hhk]
  exact (h * k).2

lemma BSub_double_coset_wGL_10 (D : FieldData) (h k : BSub D) :
    ((h.1 * wGL D * k.1 : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 =
      ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) * ((k.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) := by
  have hh : (h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := h.2
  have hk : (k.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := k.2
  simp only [Units.val_mul, wGL, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
  change ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 * 0 +
      (h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 * 1) *
      (k.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 +
    ((h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 * 1 +
      (h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 * 0) *
      (k.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = _
  rw [hh, hk]
  simp

lemma hOmega (D : FieldData) : IsDoubleCosetTransversal (BSub D) (BSub D) (omegaSet D) := by
  intro g
  by_cases hg10 : (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0
  · refine ⟨⟨1, Or.inl rfl⟩, ⟨g, hg10, 1, (1 : BSub D).2, by simp⟩, ?_⟩
    rintro ⟨ω, hω⟩ ⟨h, hh, k, hk, hghk⟩
    rcases hω with rfl | rfl
    · rfl
    · exfalso
      have h10 := congrFun (congrFun (congrArg (fun x : D.G => (x : Matrix (Fin 2) (Fin 2) D.Fq)) hghk) 1) 0
      rw [hg10, BSub_double_coset_wGL_10 D ⟨h, hh⟩ ⟨k, hk⟩] at h10
      exact mul_ne_zero (BSub_diag_ne_zero D ⟨h, hh⟩).2 (BSub_diag_ne_zero D ⟨k, hk⟩).1 h10.symm
  · obtain ⟨tb, htb⟩ := (bruhatEquiv D).surjective g
    rcases tb with ⟨⟨⟩ | x, b⟩
    · exfalso
      apply hg10
      rw [← htb]
      have h10 : ((bruhatEquiv D (.inl (), b) : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := by
        simp only [bruhatEquiv, Equiv.coe_fn_mk, cosetRep, one_mul]
        exact (bEltEquivB D b).2
      exact h10
    · refine ⟨⟨wGL D, Or.inr rfl⟩,
          ⟨(uB D x : D.G), (uB D x).2, ((bEltEquivB D b : BSub D) : D.G), (bEltEquivB D b).2, ?_⟩, ?_⟩
      · rw [← htb]
        dsimp only [bruhatEquiv, Equiv.coe_fn_mk]
        rw [← uB_mul_wGL D x, mul_assoc]
      · rintro ⟨ω, hω⟩ ⟨h, hh, k, hk, hghk⟩
        rcases hω with rfl | rfl
        · exfalso
          apply hg10
          have h10 := congrFun (congrFun (congrArg (fun x : D.G => (x : Matrix (Fin 2) (Fin 2) D.Fq)) hghk) 1) 0
          simpa using h10.trans (BSub_double_coset_one_10 D ⟨h, hh⟩ ⟨k, hk⟩)
        · rfl

lemma interSub_one_eq_top (D : FieldData) : interSub (BSub D) 1 = ⊤ := by
  rw [eq_top_iff]
  intro h _
  change (h : D.G) ∈ (BSub D).map (MulAut.conj (1 : D.G)).toMonoidHom
  exact Subgroup.mem_map.mpr ⟨h, h.2, by simp⟩

lemma interSub_wGL_mem_iff (D : FieldData) (h : BSub D) :
    h ∈ interSub (BSub D) (wGL D) ↔ (h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 := by
  change ((h : D.G) ∈ (BSub D).map (MulAut.conj (wGL D)).toMonoidHom) ↔ _
  have hconj : (((wGL D)⁻¹ * h.1 * wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 =
      (h.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 := by
    rw [wGL_inv]
    simp only [Units.val_mul, wGL, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
    simp
  constructor
  · rintro ⟨y, hy, hyh⟩
    have hy' : y = (wGL D)⁻¹ * h.1 * wGL D := by
      have := congrArg (fun z : D.G => (wGL D)⁻¹ * z * wGL D) hyh
      dsimp only [MulAut.conj, MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulEquiv.coe_mk,
        Equiv.coe_fn_mk] at this
      simpa [mul_assoc] using this
    rw [← hconj, ← hy']
    exact hy
  · intro h01
    refine ⟨(wGL D)⁻¹ * h.1 * wGL D, ?_, ?_⟩
    · change (((wGL D)⁻¹ * h.1 * wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0
      rw [hconj, h01]
    · dsimp [MulAut.conj]
      simp [mul_assoc]

lemma hTOmega (D : FieldData) :
    ∀ ω ∈ omegaSet D, Subgroup.IsComplement (tOmega D ω) (interSub (BSub D) ω : Set (BSub D)) := by
  intro ω hω
  rcases hω with rfl | rfl
  · unfold Subgroup.IsComplement
    have htop : interSub (BSub D) 1 = ⊤ := interSub_one_eq_top D
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ heq
      simp only [tOmega, ↓reduceIte, Set.mem_singleton_iff] at ha ha'
      subst ha; subst ha'
      simp only [one_mul] at heq
      have hbb' : b = b' := Subtype.ext (congrArg Subtype.val heq)
      subst hbb'; rfl
    · intro b
      refine ⟨⟨⟨1, by simp [tOmega]⟩, ⟨b, htop ▸ trivial⟩⟩, one_mul b⟩
  · have hne : wGL D ≠ 1 := wGL_ne_one D
    unfold Subgroup.IsComplement
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ heq
      simp only [tOmega, if_neg hne] at ha ha'
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨x', rfl⟩ := ha'
      have hb01 : (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 :=
        (interSub_wGL_mem_iff D b).mp hb
      have hb'01 : (b'.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 :=
        (interSub_wGL_mem_iff D b').mp hb'
      have heqM : ((uB D x).1 : Matrix (Fin 2) (Fin 2) D.Fq) * (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) =
          ((uB D x').1 : Matrix (Fin 2) (Fin 2) D.Fq) * (b'.1 : Matrix (Fin 2) (Fin 2) D.Fq) := by
        simpa [Subgroup.coe_mul, Units.val_mul] using congrArg (fun z : BSub D => (z.1 : Matrix (Fin 2) (Fin 2) D.Fq)) heq
      have h11 : (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 = (b'.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 := by
        have := congrFun (congrFun heqM 1) 1
        simpa [uB_mat, Matrix.mul_apply, Fin.sum_univ_two, b.2, b'.2] using this
      have h01 : x * (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 =
          x' * (b'.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 := by
        have := congrFun (congrFun heqM 0) 1
        simpa [uB_mat, Matrix.mul_apply, Fin.sum_univ_two, hb01, hb'01] using this
      rw [h11] at h01
      have hx : x = x' := mul_right_cancel₀ (BSub_diag_ne_zero D b').2 h01
      subst hx
      have hbb' : b = b' := mul_left_cancel heq
      subst hbb'; rfl
    · intro b
      let x : D.Fq := (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 / (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1
      let t : BSub D := (uB D x)⁻¹ * b
      have ht01 : (t.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 := by
        have hu_inv : ((uB D x)⁻¹ : BSub D) = uB D (-x) := by
          apply inv_eq_of_mul_eq_one_right
          apply Subtype.ext; apply Units.ext
          rw [Subgroup.coe_mul, Subgroup.coe_one, Units.val_mul, Units.val_one]
          ext i j; fin_cases i <;> fin_cases j <;> simp [uB_mat]
        have htM : (t.1 : Matrix (Fin 2) (Fin 2) D.Fq) =
            ((uB D (-x)).1 : Matrix (Fin 2) (Fin 2) D.Fq) * (b.1 : Matrix (Fin 2) (Fin 2) D.Fq) := by
          simp [t, hu_inv, Subgroup.coe_mul, Units.val_mul]
        rw [htM, Matrix.mul_apply, Fin.sum_univ_two, uB_mat]
        simp [x, div_mul_cancel₀ _ (BSub_diag_ne_zero D b).2]
      refine ⟨⟨⟨uB D x, by simp [tOmega, hne]⟩, ⟨t, (interSub_wGL_mem_iff D t).mpr ht01⟩⟩, ?_⟩
      dsimp
      exact mul_inv_cancel_left (uB D x) b

lemma mackeyT_eq_range (D : FieldData) :
    mackeyT (BSub D) (omegaSet D) (tOmega D) = Set.range (cosetRep D) := by
  ext g
  simp only [mackeyT, omegaSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range]
  constructor
  · rintro ⟨ω, rfl | rfl, a, ha, rfl⟩
    · simp only [tOmega, ↓reduceIte, Set.mem_singleton_iff] at ha
      subst ha
      exact ⟨.inl (), by simp [cosetRep]⟩
    · simp only [tOmega, if_neg (wGL_ne_one D)] at ha
      obtain ⟨x, rfl⟩ := ha
      exact ⟨.inr x, (uB_mul_wGL D x).symm⟩
  · rintro ⟨⟨⟩ | x, rfl⟩
    · exact ⟨1, Or.inl rfl, 1, by simp [tOmega], by simp [cosetRep]⟩
    · exact ⟨wGL D, Or.inr rfl, uB D x, by simp [tOmega, wGL_ne_one D], (uB_mul_wGL D x).symm⟩

lemma cosetRep_injective (D : FieldData) : Function.Injective (cosetRep D) := by
  intro t₁ t₂ h
  have heq : bruhatEquiv D (t₁, (1, 1, 0)) = bruhatEquiv D (t₂, (1, 1, 0)) := by
    simp only [bruhatEquiv, Equiv.coe_fn_mk, h]
  exact congrArg Prod.fst ((bruhatEquiv D).injective heq)

def mackeyT_equiv (D : FieldData) :
    CosetT D ≃ mackeyT (BSub D) (omegaSet D) (tOmega D) where
  toFun t := ⟨cosetRep D t, (mackeyT_eq_range D).symm.subset (Set.mem_range_self t)⟩
  invFun g := Classical.choose ((mackeyT_eq_range D).subset g.2)
  left_inv t := cosetRep_injective D (Classical.choose_spec ((mackeyT_eq_range D).subset
    ((mackeyT_eq_range D).symm.subset (Set.mem_range_self t))))
  right_inv g := Subtype.ext (Classical.choose_spec ((mackeyT_eq_range D).subset g.2))

lemma mackeyT_isComplement (D : FieldData) :
    Subgroup.IsComplement (mackeyT (BSub D) (omegaSet D) (tOmega D)) (BSub D : Set D.G) := by
  unfold Subgroup.IsComplement
  let e := (mackeyT_equiv D).symm.prodCongr (bEltEquivB D).symm
  have hcomp : (fun p : mackeyT (BSub D) (omegaSet D) (tOmega D) × BSub D =>
        (p.1 : D.G) * (p.2 : D.G)) = (bruhatEquiv D) ∘ e := by
    funext ⟨⟨g, hg⟩, b⟩
    dsimp only [Function.comp_apply, e]
    rw [Equiv.prodCongr_apply, Prod.map_apply]
    dsimp only [bruhatEquiv, Equiv.coe_fn_mk]
    have ht : cosetRep D ((mackeyT_equiv D).symm ⟨g, hg⟩) = g :=
      congrArg Subtype.val ((mackeyT_equiv D).apply_symm_apply ⟨g, hg⟩)
    have hb : ((bEltEquivB D ((bEltEquivB D).symm b) : BSub D) : D.G) = (b : D.G) :=
      congrArg Subtype.val ((bEltEquivB D).apply_symm_apply b)
    rw [ht, hb]
  change Function.Bijective (fun p : mackeyT (BSub D) (omegaSet D) (tOmega D) × BSub D =>
    (p.1 : D.G) * (p.2 : D.G))
  rw [hcomp]
  exact (bruhatEquiv D).bijective.comp e.bijective

lemma BSub_index_eq (D : FieldData) : (BSub D).index = D.q + 1 := by
  have hcard1 : Fintype.card (mackeyT (BSub D) (omegaSet D) (tOmega D)) * Fintype.card (BSub D) =
      Fintype.card D.G := by
    have hbij : Function.Bijective (fun p : mackeyT (BSub D) (omegaSet D) (tOmega D) × BSub D =>
        (p.1 : D.G) * (p.2 : D.G)) := mackeyT_isComplement D
    rw [← Fintype.card_prod]
    exact Fintype.card_of_bijective hbij
  have hcard2 : (BSub D).index * Fintype.card (BSub D) = Fintype.card D.G := by
    simpa [Nat.card_eq_fintype_card] using Subgroup.index_mul_card (BSub D)
  have hpos : 0 < Fintype.card (BSub D) := Fintype.card_pos
  have heq : (BSub D).index = Fintype.card (mackeyT (BSub D) (omegaSet D) (tOmega D)) :=
    Nat.eq_of_mul_eq_mul_right hpos (hcard2.trans hcard1.symm)
  rw [heq, ← Fintype.card_congr (mackeyT_equiv D)]
  simp [CosetT, card_Fq, add_comm]

lemma interSub_one_index_eq (D : FieldData) : (interSub (BSub D) 1).index = 1 := by
  rw [interSub_one_eq_top, Subgroup.index_top]

lemma interSub_wGL_index_eq (D : FieldData) : (interSub (BSub D) (wGL D)).index = D.q := by
  have hne := wGL_ne_one D
  have he : D.Fq ≃ tOmega D (wGL D) :=
    { toFun := fun x => ⟨uB D x, by simp [tOmega, hne]⟩
      invFun := fun b => (b.1.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1
      left_inv := fun x => by simp [uB_mat]
      right_inv := fun ⟨b, hb⟩ => by
        simp only [tOmega, if_neg hne] at hb
        obtain ⟨x, rfl⟩ := hb
        simp [uB_mat] }
  have hcard1 : Fintype.card (tOmega D (wGL D)) * Fintype.card (interSub (BSub D) (wGL D)) =
      Fintype.card (BSub D) := by
    have hbij : Function.Bijective (fun p : tOmega D (wGL D) × interSub (BSub D) (wGL D) =>
        (p.1 : BSub D) * (p.2 : BSub D)) := hTOmega D (wGL D) (Or.inr rfl)
    rw [← Fintype.card_prod]
    exact Fintype.card_of_bijective hbij
  have hcard2 : (interSub (BSub D) (wGL D)).index * Fintype.card (interSub (BSub D) (wGL D)) =
      Fintype.card (BSub D) := by
    simpa [Nat.card_eq_fintype_card] using Subgroup.index_mul_card (interSub (BSub D) (wGL D))
  have hpos : 0 < Fintype.card (interSub (BSub D) (wGL D)) := Fintype.card_pos
  have heq : (interSub (BSub D) (wGL D)).index = Fintype.card (tOmega D (wGL D)) :=
    Nat.eq_of_mul_eq_mul_right hpos (hcard2.trans hcard1.symm)
  rw [heq, ← Fintype.card_congr he, card_Fq]

abbrev LambdaW (D : FieldData) (ω : D.G) : Type :=
  {_x : D.BIrr // ω = 1} ⊕ {_x : D.Lab × D.Lab // ω ≠ 1}

def BW (D : FieldData) (ω : D.G) : LambdaW D ω → Type
  | .inl l => D.BBas l.1
  | .inr _ => Unit

instance instFintypeBW (D : FieldData) (ω : D.G) (κ : LambdaW D ω) : Fintype (BW D ω κ) :=
  match κ with
  | .inl l => inferInstanceAs (Fintype (D.BBas l.1))
  | .inr _ => inferInstanceAs (Fintype Unit)

instance instDecEqBW (D : FieldData) (ω : D.G) (κ : LambdaW D ω) : DecidableEq (BW D ω κ) :=
  match κ with
  | .inl l => inferInstanceAs (DecidableEq (D.BBas l.1))
  | .inr _ => inferInstanceAs (DecidableEq Unit)

def RW (D : FieldData) (ω : D.G) :
    ∀ κ : LambdaW D ω, interSub (BSub D) ω → Matrix (BW D ω κ) (BW D ω κ) ℂ
  | .inl l => fun h => RH D l.1 h.1
  | .inr ab => fun h _ _ =>
      D.chi ab.1.1 (((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
        D.chi ab.1.2 (((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)

lemma RW_isIrrepSystem (D : FieldData) :
    ∀ ω ∈ omegaSet D, IsIrrepSystem (RW D ω) := by
  intro ω hω
  rcases hω with rfl | rfl
  · have hH := RH_isIrrepSystem D
    let eG : BSub D ≃* interSub (BSub D) 1 :=
      { toFun := fun h => ⟨h, interSub_one_eq_top D ▸ trivial⟩
        invFun := fun h => h.1
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro (⟨l, _⟩ | ⟨_, hne⟩)
      · exact ⟨⟨(hH.1 l).1.1, fun h₁ h₂ => (hH.1 l).1.2 h₁.1 h₂.1⟩, fun h => (hH.1 l).2 h.1⟩
      · exact absurd rfl hne
    · rintro (⟨l, _⟩ | ⟨_, hne⟩)
      · refine ⟨(hH.2.1 l).1, fun W hW => ?_⟩
        exact (hH.2.1 l).2 W fun g v hv => hW (eG g) v hv
      · exact absurd rfl hne
    · rintro (⟨l₁, _⟩ | ⟨_, hne⟩) (⟨l₂, _⟩ | ⟨_, hne2⟩) hne12 heq
      · apply hH.2.2.1 l₁ l₂ (fun h => hne12 (by subst h; rfl))
        rcases heq with ⟨A, B, hAB, hBA, hint⟩
        exact ⟨A, B, hAB, hBA, fun g _ => hint (eG g) (Set.mem_univ _)⟩
      · exact absurd rfl hne2
      · exact absurd rfl hne
      · exact absurd rfl hne
    · intro ι _ _ ρ hm hi
      let ρ' : BSub D → Matrix ι ι ℂ := fun h => ρ (eG h)
      have hm' : IsMatRep ρ' := ⟨hm.1, fun h₁ h₂ => hm.2 (eG h₁) (eG h₂)⟩
      have hi' : IsIrreducibleRep ρ' := ⟨hi.1, fun W hW => hi.2 W fun g v hv => hW (eG.symm g) v hv⟩
      obtain ⟨l, A, B, hAB, hBA, hint⟩ := hH.2.2.2 ι ρ' hm' hi'
      exact ⟨.inl ⟨l, rfl⟩, A, B, hAB, hBA, fun g _ => hint (eG.symm g) (Set.mem_univ _)⟩
  · have hne : wGL D ≠ 1 := wGL_ne_one D
    have hUn : ∀ κ : LambdaW D (wGL D), IsUnitaryRep (RW D (wGL D) κ) := by
      rintro (⟨_, h1⟩ | ⟨⟨α, β⟩, _⟩)
      · exact absurd h1 hne
      · have hsub : ∀ i j : BW D (wGL D) (.inr ⟨(α, β), ‹_›⟩), i = j := fun i j =>
          Subsingleton.elim (α := Unit) i j
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · ext i j
          rw [Matrix.one_apply, if_pos (hsub i j)]
          simp [RW, chi_one]
        · intro h₁ h₂
          ext i j
          have h10_1 : ((h₁.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := h₁.1.2
          have h10_2 : ((h₂.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := h₂.1.2
          have h00 : (((h₁ * h₂).1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 =
              ((h₁.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 *
                ((h₂.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 := by
            change ((h₁.1.1 : Matrix (Fin 2) (Fin 2) D.Fq) *
              (h₂.1.1 : Matrix (Fin 2) (Fin 2) D.Fq)) 0 0 = _
            rw [Matrix.mul_apply, Fin.sum_univ_two, h10_2, mul_zero, add_zero]
          have h11 : (((h₁ * h₂).1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 =
              ((h₁.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 *
                ((h₂.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 := by
            change ((h₁.1.1 : Matrix (Fin 2) (Fin 2) D.Fq) *
              (h₂.1.1 : Matrix (Fin 2) (Fin 2) D.Fq)) 1 1 = _
            rw [Matrix.mul_apply, Fin.sum_univ_two, h10_1, zero_mul, zero_add]
          rw [Matrix.mul_apply, Finset.sum_eq_single i
            (fun k _ hk => absurd (hsub k i) hk)
            (fun hm => absurd (Finset.mem_univ _) hm)]
          simp only [RW]
          rw [h00, h11, chi_mul D α (BSub_diag_ne_zero D h₁.1).1 (BSub_diag_ne_zero D h₂.1).1,
            chi_mul D β (BSub_diag_ne_zero D h₁.1).2 (BSub_diag_ne_zero D h₂.1).2]
          ring
        · intro h
          rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
          ext i j
          rw [Matrix.mul_apply, Finset.sum_eq_single i
            (fun k _ hk => absurd (hsub k i) hk)
            (fun hm => absurd (Finset.mem_univ _) hm),
            Matrix.one_apply, if_pos (hsub i j), Matrix.conjTranspose_apply]
          simp only [RW]
          have ha : D.chi α (((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
              star (D.chi α (((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0)) = 1 := by
            rw [RCLike.star_def, conj_chi, ← chi_add, add_neg_cancel,
              chi_zero_lab D (BSub_diag_ne_zero D h.1).1]
          have hd : D.chi β (((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) *
              star (D.chi β (((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1)) = 1 := by
            rw [RCLike.star_def, conj_chi, ← chi_add, add_neg_cancel,
              chi_zero_lab D (BSub_diag_ne_zero D h.1).2]
          calc D.chi α _ * D.chi β _ * star (D.chi α _ * D.chi β _)
              = (D.chi α _ * star (D.chi α _)) * (D.chi β _ * star (D.chi β _)) := by
                  rw [star_mul']; ring
            _ = 1 := by rw [ha, hd, mul_one]
    have hIrr : ∀ κ : LambdaW D (wGL D), IsIrreducibleRep (RW D (wGL D) κ) := by
      rintro (⟨_, h1⟩ | ab)
      · exact absurd h1 hne
      · refine ⟨⟨()⟩, fun W hW => ?_⟩
        by_cases hbot : W = ⊥
        · exact Or.inl hbot
        · right
          rw [Submodule.eq_top_iff']
          obtain ⟨v, hvW, hv0⟩ : ∃ v ∈ W, v ≠ 0 := by
            by_contra! hall; apply hbot; rw [Submodule.eq_bot_iff]; exact hall
          let u₀ : BW D (wGL D) (.inr ab) := (PUnit.unit : Unit)
          have hu : ∀ u : BW D (wGL D) (.inr ab), u = u₀ := fun u =>
            @Subsingleton.elim (BW D (wGL D) (.inr ab)) (inferInstanceAs (Subsingleton Unit)) u u₀
          have hv_ne : v u₀ ≠ 0 := fun h => hv0 (funext fun u => by rw [hu u]; exact h)
          intro w
          have hw : w = (w u₀ * (v u₀)⁻¹) • v := by
            funext u
            rw [hu u]
            simp [Pi.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv_ne]
          rw [hw]
          exact W.smul_mem _ hvW
    have hDist : ∀ κ₁ κ₂ : LambdaW D (wGL D), κ₁ ≠ κ₂ →
        ¬ RepEquiv (RW D (wGL D) κ₁) (RW D (wGL D) κ₂) := by
      have htr_eval : ∀ (ab' : D.Lab × D.Lab) (h' : wGL D ≠ 1) (g : interSub (BSub D) (wGL D)),
          Matrix.trace (RW D (wGL D) (.inr ⟨ab', h'⟩) g) =
            D.chi ab'.1 (((g.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) *
              D.chi ab'.2 (((g.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) := by
        intro ab' h' g
        let u₀ : BW D (wGL D) (.inr ⟨ab', h'⟩) := (PUnit.unit : Unit)
        rw [Matrix.trace, Finset.sum_eq_single u₀
          (fun k _ hk => absurd (@Subsingleton.elim (BW D (wGL D) (.inr ⟨ab', h'⟩))
            (inferInstanceAs (Subsingleton Unit)) k u₀) hk)
          (fun hm => absurd (Finset.mem_univ _) hm)]
        rfl
      rintro (⟨_, h1⟩ | ⟨⟨α₁, β₁⟩, hne1⟩) (⟨_, h2⟩ | ⟨⟨α₂, β₂⟩, hne2⟩) hne12 heq
      · exact absurd h1 hne
      · exact absurd h1 hne
      · exact absurd h2 hne
      · let d₁ : interSub (BSub D) (wGL D) :=
          ⟨diagB D (uGen D) 1, (interSub_wGL_mem_iff D _).mpr (by simp [diagB_mat])⟩
        let d₂ : interSub (BSub D) (wGL D) :=
          ⟨diagB D 1 (uGen D), (interSub_wGL_mem_iff D _).mpr (by simp [diagB_mat])⟩
        have htr1 := repEquiv_trace heq d₁
        have htr2 := repEquiv_trace heq d₂
        rw [htr_eval (α₁, β₁) hne1 d₁, htr_eval (α₂, β₂) hne2 d₁] at htr1
        rw [htr_eval (α₁, β₁) hne1 d₂, htr_eval (α₂, β₂) hne2 d₂] at htr2
        simp only [d₁, d₂, diagB_mat, chi_one, uGen, Units.val_mk0, Units.val_one,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          mul_one, one_mul] at htr1 htr2
        have hα : α₁ = α₂ := by by_contra h; exact chi_gen_ne D h htr1
        have hβ : β₁ = β₂ := by by_contra h; exact chi_gen_ne D h htr2
        exact hne12 (by subst hα; subst hβ; rfl)
    refine ⟨hUn, hIrr, hDist, ?_⟩
    have he_card : (D.Fqˣ × D.Fqˣ) ≃ interSub (BSub D) (wGL D) :=
      { toFun := fun ad =>
          ⟨diagB D ad.1 ad.2, (interSub_wGL_mem_iff D _).mpr (by simp [diagB_mat])⟩
        invFun := fun h =>
          (Units.mk0 ((h.1.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0) (BSub_diag_ne_zero D h.1).1,
           Units.mk0 ((h.1.1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1) (BSub_diag_ne_zero D h.1).2)
        left_inv := fun ⟨a, d⟩ => by ext <;> simp [diagB_mat]
        right_inv := fun ⟨h, hh⟩ => by
          apply Subtype.ext; apply Subtype.ext; apply Units.ext
          ext i j; fin_cases i <;> fin_cases j
          · simp [diagB_mat]
          · simpa [diagB_mat] using ((interSub_wGL_mem_iff D h).mp hh).symm
          · simpa [diagB_mat] using h.2.symm
          · simp [diagB_mat] }
    have hcard_inter : Fintype.card (interSub (BSub D) (wGL D)) = (D.q - 1) ^ 2 := by
      rw [← Fintype.card_congr he_card, Fintype.card_prod, card_Fq_units, pow_two]
    have hsum : ∑ κ : LambdaW D (wGL D), Fintype.card (BW D (wGL D) κ) ^ 2 =
        Fintype.card (interSub (BSub D) (wGL D)) := by
      rw [Fintype.sum_sum_type]
      have h0 : ∑ x : {_x : D.BIrr // wGL D = 1}, Fintype.card (BW D (wGL D) (.inl x)) ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun x _ => absurd x.2 hne
      have h1 : ∑ x : {_x : D.Lab × D.Lab // wGL D ≠ 1},
          Fintype.card (BW D (wGL D) (.inr x)) ^ 2 = (D.q - 1) ^ 2 := by
        have ht : ∀ x : {_x : D.Lab × D.Lab // wGL D ≠ 1},
            Fintype.card (BW D (wGL D) (.inr x)) ^ 2 = 1 := fun _ => by
          change Fintype.card Unit ^ 2 = 1; simp
        simp only [ht, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
        have he_l : (D.Lab × D.Lab) ≃ {_x : D.Lab × D.Lab // wGL D ≠ 1} :=
          { toFun := fun ab => ⟨ab, hne⟩
            invFun := Subtype.val
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← Fintype.card_congr he_l, Fintype.card_prod, card_Lab, pow_two]
      rw [h0, zero_add, h1, hcard_inter]
    exact completeness_of_irrep_sum_sq_eq_card (BW D (wGL D)) (RW D (wGL D)) hUn hIrr hDist hsum

def NmW (D : FieldData) (ω : D.G) (l : D.BIrr) : Finset (LambdaW D ω) :=
  if hω : ω = 1 then ({(Sum.inl ⟨l, hω⟩ : LambdaW D ω)} : Finset (LambdaW D ω))
  else
    match l with
    | .inl αβ => ({(Sum.inr ⟨αβ, hω⟩ : LambdaW D ω)} : Finset (LambdaW D ω))
    | .inr γ => Finset.univ.image (fun δ : D.Lab => (Sum.inr ⟨(δ, γ - δ), hω⟩ : LambdaW D ω))

def adaptW (D : FieldData) (ω : D.G) (l : D.BIrr) :
    D.BBas l ≃ AdBas (BW D ω) (NmW D ω) l :=
  if hω : ω = 1 then
    { toFun := fun P => ⟨⟨Sum.inl ⟨l, hω⟩, by simp [NmW, hω]⟩, P⟩
      invFun := fun x =>
        match x with
        | ⟨⟨.inl l', hl⟩, P⟩ => by
            have heq : l'.1 = l := by
              have hm : (Sum.inl l' : LambdaW D ω) ∈ NmW D ω l := hl
              simp only [NmW, dif_pos hω, Finset.mem_singleton] at hm
              exact congrArg Subtype.val (Sum.inl.inj hm)
            exact cast (congrArg D.BBas heq) P
        | ⟨⟨.inr ab, _⟩, _⟩ => False.elim (ab.2 hω)
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨κ, hl⟩, P⟩ => by
        simp only [NmW, dif_pos hω, Finset.mem_singleton] at hl
        subst hl
        rfl }
  else
    match l with
    | .inl αβ =>
        { toFun := fun _ => ⟨⟨Sum.inr ⟨αβ, hω⟩, by simp [NmW, dif_neg hω]⟩, ()⟩
          invFun := fun _ => (() : D.BBas (.inl αβ))
          left_inv := fun P => Subsingleton.elim (α := Unit) () P
          right_inv := fun ⟨⟨κ, hl⟩, P⟩ => by
            simp only [NmW, dif_neg hω, Finset.mem_singleton] at hl
            subst hl
            have hP : (() : Unit) = P := Subsingleton.elim () P
            simp [hP] }
    | .inr γ =>
        { toFun := fun δ =>
            ⟨⟨Sum.inr ⟨(show D.Lab from δ, γ - show D.Lab from δ), hω⟩, by
              simp only [NmW, dif_neg hω, Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨show D.Lab from δ, rfl⟩⟩, ()⟩
          invFun := fun x =>
            match x with
            | ⟨⟨.inl l', _⟩, _⟩ => False.elim (hω l'.2)
            | ⟨⟨.inr ab, _⟩, _⟩ => ab.1.1
          left_inv := fun _ => rfl
          right_inv := fun ⟨⟨κ, hl⟩, P⟩ => by
            simp only [NmW, dif_neg hω, Finset.mem_image, Finset.mem_univ, true_and] at hl
            obtain ⟨δ, rfl⟩ := hl
            have hP : (() : Unit) = P := Subsingleton.elim () P
            simp [hP] }

lemma hAdW (D : FieldData) :
    ∀ ω ∈ omegaSet D, IsAdaptedToInter (BSub D) D.BBas (RH D) (BW D) (RW D) (NmW D) (adaptW D) ω := by
  have h67 := lemma_6_7 D
  intro ω hω l h Q P
  rcases hω with rfl | rfl
  · rcases Q with ⟨⟨qκ, hqκ⟩, q⟩
    rcases P with ⟨⟨pκ, hpκ⟩, p⟩
    simp only [NmW, ↓reduceDIte, Finset.mem_singleton] at hqκ hpκ
    subst hqκ; subst hpκ
    rw [RHad, Matrix.submatrix_apply]
    simp only [adaptW, ↓reduceDIte, Equiv.coe_fn_symm_mk, RW, cast_eq]
    rfl
  · have hne : wGL D ≠ 1 := wGL_ne_one D
    have h01 : ((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 :=
      (interSub_wGL_mem_iff D h.1).mp h.2
    rcases l with ⟨α, β⟩ | γ
    · rcases Q with ⟨⟨qκ, hqκ⟩, q⟩
      rcases P with ⟨⟨pκ, hpκ⟩, p⟩
      simp only [NmW, dif_neg hne, Finset.mem_singleton] at hqκ hpκ
      subst hqκ; subst hpκ
      rw [RHad, Matrix.submatrix_apply]
      simp only [↓reduceDIte, RW, RH, FieldData.RB]
    · rcases Q with ⟨⟨qκ, hqκ⟩, q⟩
      rcases P with ⟨⟨pκ, hpκ⟩, p⟩
      simp only [NmW, dif_neg hne, Finset.mem_image, Finset.mem_univ, true_and] at hqκ hpκ
      obtain ⟨δ₁, rfl⟩ := hqκ
      obtain ⟨δ₂, rfl⟩ := hpκ
      rw [RHad, Matrix.submatrix_apply]
      simp only [adaptW, dif_neg hne, Equiv.coe_fn_symm_mk, RH]
      rw [h67.2.1 γ h.1.1 δ₁ δ₂ h.1.2 h01]
      by_cases he : δ₁ = δ₂
      · subst he
        simp [RW]
      · have hne' : (⟨Sum.inr ⟨(δ₁, γ - δ₁), hne⟩, hqκ⟩ : NmW D (wGL D) (.inr γ)) ≠
            ⟨Sum.inr ⟨(δ₂, γ - δ₂), hne⟩, hpκ⟩ := fun h => by
          have := congrArg (fun x : NmW D (wGL D) (.inr γ) => x.1) h
          dsimp at this
          have := congrArg (fun ab : {_x : D.Lab × D.Lab // wGL D ≠ 1} => ab.1.1) (Sum.inr.inj this)
          exact he this
        simp [he, hne']

def Ntw (D : FieldData) (ω : D.G) (l : D.BIrr) : Finset (LambdaW D ω) :=
  if hω : ω = 1 then ({(Sum.inl ⟨l, hω⟩ : LambdaW D ω)} : Finset (LambdaW D ω))
  else
    match l with
    | .inl αβ => ({(Sum.inr ⟨(αβ.2, αβ.1), hω⟩ : LambdaW D ω)} : Finset (LambdaW D ω))
    | .inr γ => Finset.univ.image (fun δ : D.Lab => (Sum.inr ⟨(γ - δ, δ), hω⟩ : LambdaW D ω))

def Utw (D : FieldData) (ω : D.G) (l : D.BIrr) :
    Matrix (Σ κ : Ntw D ω l, BW D ω κ.1) (D.BBas l) ℂ :=
  Matrix.of fun x P =>
    match x with
    | ⟨⟨.inl l', _⟩, P'⟩ =>
        if h : l'.1 = l then
          if cast (congrArg D.BBas h) P' = P then 1 else 0
        else 0
    | ⟨⟨.inr ab, _⟩, _⟩ => utwW D l ab.1 P

lemma hUtw (D : FieldData) :
    ∀ ω ∈ omegaSet D, ∀ l : D.BIrr,
      IsUntwisting (BSub D) D.BBas (RH D) (BW D) (RW D) (Ntw D) (Utw D) ω l := by
  have h67 := lemma_6_7 D
  intro ω hω l
  rcases hω with rfl | rfl
  · let e : D.BBas l ≃ Σ κ : Ntw D 1 l, BW D 1 κ.1 :=
      { toFun := fun P => ⟨⟨.inl ⟨l, rfl⟩, by simp [Ntw]⟩, P⟩
        invFun := fun x =>
          match x with
          | ⟨⟨.inl l', hl⟩, P⟩ => by
              have heq : l'.1 = l := by
                have hm : (Sum.inl l' : LambdaW D 1) ∈ Ntw D 1 l := hl
                simp only [Ntw, ↓reduceDIte, Finset.mem_singleton] at hm
                exact congrArg Subtype.val (Sum.inl.inj hm)
              exact cast (congrArg D.BBas heq) P
          | ⟨⟨.inr ab, _⟩, _⟩ => False.elim (ab.2 rfl)
        left_inv := fun _ => rfl
        right_inv := fun ⟨⟨κ, hl⟩, P⟩ => by
          simp only [Ntw, ↓reduceDIte, Finset.mem_singleton] at hl
          subst hl; rfl }
    have hU_eq : ∀ x (P : D.BBas l), Utw D 1 l x P = if x = e P then 1 else 0 := by
      intro ⟨⟨κ, hκ⟩, Q⟩ P
      simp only [Ntw, ↓reduceDIte, Finset.mem_singleton] at hκ
      subst hκ
      simp only [Utw, Matrix.of_apply, ↓reduceDIte, e, Equiv.coe_fn_mk]
      split_ifs
      · rfl
      · exfalso
        rename_i h1 h2
        exact h2 (Sigma.ext rfl (cast_eq_iff_heq.mp h1))
      · exfalso
        rename_i h1 h2
        exact h1 (cast_eq_iff_heq.mpr (Sigma.ext_iff.mp h2).2)
      · rfl
    refine ⟨?_, ?_, fun h => ?_⟩
    · ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single (e.symm x)]
      · simp [(e.apply_symm_apply x), eq_comm]
      · intro P _ hP
        have hne : x ≠ e P := fun h => hP (by rw [h, e.symm_apply_apply])
        simp [hne]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · ext P₁ P₂
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single (e P₁)]
      · simp [e.injective.eq_iff]
      · intro x _ hx
        simp [hx]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      have hleft : ∀ P : D.BBas l,
          (∑ P' : D.BBas l, Utw D 1 l x P' * twistRep (BSub D) 1 (RH D l) h P' P) =
          twistRep (BSub D) 1 (RH D l) h (e.symm x) P := by
        intro P
        rw [Finset.sum_eq_single (e.symm x)]
        · rw [hU_eq, if_pos (e.apply_symm_apply x).symm, one_mul]
        · intro P' _ hP'
          have hne : x ≠ e P' := fun heq => hP' (by rw [heq, e.symm_apply_apply])
          rw [hU_eq, if_neg hne, zero_mul]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      simp_rw [hleft]
      rw [Finset.sum_eq_single (e.symm y)]
      · rw [hU_eq, if_pos (e.apply_symm_apply y).symm, star_one, mul_one]
        rcases x with ⟨⟨qx, hqx⟩, px⟩
        rcases y with ⟨⟨qy, hqy⟩, py⟩
        simp only [Ntw, ↓reduceDIte, Finset.mem_singleton] at hqx hqy
        subst hqx; subst hqy
        simp only [↓reduceDIte, e, twistRep, RW, mul_one, one_mul, inv_one]
        rfl
      · intro P _ hP
        have hne : y ≠ e P := fun heq => hP (by rw [heq, e.symm_apply_apply])
        rw [hU_eq, if_neg hne, star_zero, mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm
  · have hne : wGL D ≠ 1 := wGL_ne_one D
    let e : D.BBas l ≃ Σ κ : Ntw D (wGL D) l, BW D (wGL D) κ.1 :=
      { toFun := fun P => ⟨⟨.inr ⟨abOf D l P, hne⟩, by
          cases l with
          | inl αβ => simp [Ntw, dif_neg hne, abOf]
          | inr γ =>
              simp only [Ntw, dif_neg hne, Finset.mem_image, Finset.mem_univ, true_and]
              exact ⟨P, by simp [abOf]⟩⟩, ()⟩
        invFun := fun x =>
          match x with
          | ⟨⟨.inl l', _⟩, _⟩ => False.elim (hne l'.2)
          | ⟨⟨.inr ab, hmem⟩, _⟩ =>
              match l with
              | .inl αβ => (() : D.BBas (.inl αβ))
              | .inr γ => ab.1.2
        left_inv := fun P => by
          cases l with
          | inl αβ => exact @Subsingleton.elim (D.BBas (.inl αβ)) (inferInstanceAs (Subsingleton Unit)) _ P
          | inr γ => rfl
        right_inv := fun ⟨⟨κ, hκ⟩, u⟩ => by
          rcases κ with ⟨l', h1⟩ | ab
          · exact absurd h1 hne
          · have hu : (() : Unit) = u := Subsingleton.elim () u
            cases l with
            | inl αβ =>
                simp only [Ntw, dif_neg hne, Finset.mem_singleton] at hκ
                have hab : ab.1 = (αβ.2, αβ.1) := congrArg Subtype.val (Sum.inr.inj hκ)
                subst hu
                apply Sigma.ext
                · apply Subtype.ext; exact congrArg Sum.inr (Subtype.ext hab.symm)
                · rfl
            | inr γ =>
                simp only [Ntw, dif_neg hne, Finset.mem_image, Finset.mem_univ, true_and] at hκ
                obtain ⟨δ, hδ⟩ := hκ
                have hab : ab.1 = (γ - δ, δ) := (congrArg Subtype.val (Sum.inr.inj hδ)).symm
                subst hu
                apply Sigma.ext
                · apply Subtype.ext; apply congrArg Sum.inr; apply Subtype.ext
                  change abOf D (.inr γ) ab.1.2 = ab.1
                  rw [hab]
                  rfl
                · rfl }
    have hU_eq : ∀ x (P : D.BBas l), Utw D (wGL D) l x P = if x = e P then 1 else 0 := by
      intro ⟨⟨κ, hκ⟩, u⟩ P
      rcases κ with ⟨l', h1⟩ | ab
      · exact absurd h1 hne
      · simp only [Utw, Matrix.of_apply, utwW_eq_ite]
        let u₀ : BW D (wGL D) (.inr ab) := ()
        have hu : u = u₀ := @Subsingleton.elim (BW D (wGL D) (.inr ab))
          (inferInstanceAs (Subsingleton Unit)) u u₀
        by_cases h1 : ab.1 = abOf D l P
        · have heq : (⟨⟨Sum.inr ab, hκ⟩, u⟩ : Σ κ : Ntw D (wGL D) l, BW D (wGL D) κ.1) = e P := by
            apply Sigma.ext
            · apply Subtype.ext; exact congrArg Sum.inr (Subtype.ext h1)
            · rw [hu]; rfl
          simp [h1, heq]
        · have hne' : (⟨⟨Sum.inr ab, hκ⟩, u⟩ : Σ κ : Ntw D (wGL D) l, BW D (wGL D) κ.1) ≠ e P := by
            intro heq
            have heq1 := congrArg (fun z : Σ κ : Ntw D (wGL D) l, BW D (wGL D) κ.1 => z.1.1) heq
            dsimp [e] at heq1
            exact h1 (congrArg Subtype.val (Sum.inr.inj heq1))
          simp [h1, hne']
    refine ⟨?_, ?_, fun h => ?_⟩
    · ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single (e.symm x)]
      · simp [(e.apply_symm_apply x), eq_comm]
      · intro P _ hP
        have hne' : x ≠ e P := fun heq => hP (by rw [heq, e.symm_apply_apply])
        simp [hne']
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · ext P₁ P₂
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hU_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single (e P₁)]
      · simp [e.injective.eq_iff]
      · intro x _ hx
        simp [hx]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · ext x y
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      have hleft : ∀ P : D.BBas l,
          (∑ P' : D.BBas l, Utw D (wGL D) l x P' * twistRep (BSub D) (wGL D) (RH D l) h P' P) =
          twistRep (BSub D) (wGL D) (RH D l) h (e.symm x) P := by
        intro P
        rw [Finset.sum_eq_single (e.symm x)]
        · rw [hU_eq, if_pos (e.apply_symm_apply x).symm, one_mul]
        · intro P' _ hP'
          have hne' : x ≠ e P' := fun heq => hP' (by rw [heq, e.symm_apply_apply])
          rw [hU_eq, if_neg hne', zero_mul]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      simp_rw [hleft]
      rw [Finset.sum_eq_single (e.symm y)]
      · rw [hU_eq, if_pos (e.apply_symm_apply y).symm, star_one, mul_one]
        have h10 : ((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 0 := h.1.2
        have hdiag_00 : (((wGL D)⁻¹ * ((h.1 : BSub D) : D.G) * wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 =
            ((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 := by
          rw [wGL_inv]
          simp only [Units.val_mul, wGL, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
          simp
        have hdiag_11 : (((wGL D)⁻¹ * ((h.1 : BSub D) : D.G) * wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 1 1 =
            ((h.1 : BSub D).1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 0 := by
          rw [wGL_inv]
          simp only [Units.val_mul, wGL, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
          simp
        have hdiag_01 : (((wGL D)⁻¹ * ((h.1 : BSub D) : D.G) * wGL D : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) 0 1 = 0 := by
          rw [wGL_inv]
          simp only [Units.val_mul, wGL, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue]
          simp [h10]
        rcases x with ⟨⟨qx, hqx⟩, ux⟩
        rcases y with ⟨⟨qy, hqy⟩, uy⟩
        rcases qx with ⟨lx, hlx⟩ | ⟨abx, hnex⟩
        · exact absurd hlx hne
        · rcases qy with ⟨ly, hly⟩ | ⟨aby, hney⟩
          · exact absurd hly hne
          · cases l with
            | inl αβ =>
                have habx : abx = (αβ.2, αβ.1) := by
                  simpa [Ntw, dif_neg hne] using hqx
                have haby : aby = (αβ.2, αβ.1) := by
                  simpa [Ntw, dif_neg hne] using hqy
                have he_xy : (⟨Sum.inr ⟨abx, hnex⟩, hqx⟩ : Ntw D (wGL D) (.inl αβ)) =
                    ⟨Sum.inr ⟨aby, hney⟩, hqy⟩ := by
                  apply Subtype.ext; exact congrArg Sum.inr (Subtype.ext (habx.trans haby.symm))
                rw [dif_pos he_xy]
                have he_inv_x : e.symm ⟨⟨.inr ⟨abx, hnex⟩, hqx⟩, ux⟩ = () := rfl
                have he_inv_y : e.symm ⟨⟨.inr ⟨aby, hney⟩, hqy⟩, uy⟩ = () := rfl
                rw [he_inv_x, he_inv_y]
                simp only [twistRep, RH]
                rw [h67.1 αβ.1 αβ.2 _ (interSub_conj_mem (BSub D) (wGL D) h) hdiag_01,
                  hdiag_00, hdiag_11]
                simp only [RW]
                rw [congrArg Prod.fst haby, congrArg Prod.snd haby, mul_comm]
            | inr γ =>
                obtain ⟨δ₁, hδ₁⟩ := by
                  simpa only [Ntw, dif_neg hne, Finset.mem_image, Finset.mem_univ, true_and] using hqx
                obtain ⟨δ₂, hδ₂⟩ := by
                  simpa only [Ntw, dif_neg hne, Finset.mem_image, Finset.mem_univ, true_and] using hqy
                have habx : abx = (γ - δ₁, δ₁) := (congrArg Subtype.val (Sum.inr.inj hδ₁)).symm
                have haby : aby = (γ - δ₂, δ₂) := (congrArg Subtype.val (Sum.inr.inj hδ₂)).symm
                have he_inv_x : e.symm ⟨⟨.inr ⟨abx, hnex⟩, hqx⟩, ux⟩ = abx.2 := rfl
                have he_inv_y : e.symm ⟨⟨.inr ⟨aby, hney⟩, hqy⟩, uy⟩ = aby.2 := rfl
                rw [he_inv_x, he_inv_y]
                simp only [twistRep, RH]
                rw [h67.2.1 γ _ abx.2 aby.2 (interSub_conj_mem (BSub D) (wGL D) h) hdiag_01,
                  hdiag_00, hdiag_11]
                by_cases hδ : abx.2 = aby.2
                · have hab_eq : abx = aby := by
                    rw [habx, haby]
                    have h12 : δ₁ = δ₂ := by
                      have := hδ
                      rw [habx, haby] at this
                      exact this
                    subst h12; rfl
                  have hsub_eq : (⟨Sum.inr ⟨abx, hnex⟩, hqx⟩ : Ntw D (wGL D) (.inr γ)) =
                      ⟨Sum.inr ⟨aby, hney⟩, hqy⟩ := by
                    apply Subtype.ext; exact congrArg Sum.inr (Subtype.ext hab_eq)
                  rw [if_pos hδ, dif_pos hsub_eq]
                  simp only [RW]
                  have hsub : γ - abx.2 = aby.1 := by rw [hδ, haby]
                  rw [hsub, hδ, mul_comm]
                · have hsub_ne : (⟨Sum.inr ⟨abx, hnex⟩, hqx⟩ : Ntw D (wGL D) (.inr γ)) ≠
                      ⟨Sum.inr ⟨aby, hney⟩, hqy⟩ := fun heq => hδ (by
                    have := congrArg (fun z : Ntw D (wGL D) (.inr γ) => z.1) heq
                    exact congrArg (fun w : {_x : D.Lab × D.Lab // wGL D ≠ 1} => w.1.2)
                      (Sum.inr.inj this))
                  rw [if_neg hδ, dif_neg hsub_ne]
      · intro P _ hP
        have hne' : y ≠ e P := fun heq => hP (by rw [heq, e.symm_apply_apply])
        rw [hU_eq, if_neg hne', star_zero, mul_zero]
      · intro hm; exact absurd (Finset.mem_univ _) hm

lemma tLab_eq_some_adaptW_symm (D : FieldData) (lt : D.BIrr) (ab : D.Lab × D.Lab)
    (hlt : match lt with | .inl αβ => ab = αβ | .inr γ => ab.1 + ab.2 = γ)
    (hmem : (Sum.inr ⟨ab, wGL_ne_one D⟩ : LambdaW D (wGL D)) ∈ NmW D (wGL D) lt) :
    tLab D lt ab =
      some ((adaptW D (wGL D) lt).symm ⟨⟨Sum.inr ⟨ab, wGL_ne_one D⟩, hmem⟩, ()⟩) := by
  cases lt with
  | inl αβ =>
      simp [tLab, hlt]
      exact congrArg some (Subsingleton.elim (α := Unit) _ _)
  | inr γ => simp [tLab, hlt, adaptW, dif_neg (wGL_ne_one D)]

def validInEquivKSet (D : FieldData) (l lt : D.BIrr) :
    {x : D.BIrr × Bool // ValidIn D l x.1 x.2 lt} ≃
      KSet (omegaSet D) (NmW D) (Ntw D) l lt where
  toFun x :=
    match x with
    | ⟨(κ, false), hv⟩ =>
        ⟨⟨1, Or.inl rfl⟩, ⟨Sum.inl ⟨l, rfl⟩, by simp [Ntw],
          by dsimp [ValidIn] at hv; rw [hv.2]; simp [NmW]⟩⟩
    | ⟨(.inr _, true), hv⟩ =>
        False.elim (by dsimp [ValidIn] at hv; rcases hv with ⟨ab, h, _⟩; cases h)
    | ⟨(.inl ab, true), hv⟩ =>
        ⟨⟨wGL D, Or.inr rfl⟩, ⟨Sum.inr ⟨ab, wGL_ne_one D⟩,
          by
            dsimp [ValidIn] at hv
            rcases hv with ⟨ab', hab', hnl, _⟩
            obtain rfl := Sum.inl.inj hab'
            cases l with
            | inl αβ => simp [Ntw, dif_neg (wGL_ne_one D), hnl]
            | inr γ =>
                simp only [Ntw, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and]
                exact ⟨ab.2, by congr 1; apply Subtype.ext; exact Prod.ext (eq_sub_of_add_eq hnl).symm rfl⟩,
          by
            dsimp [ValidIn] at hv
            rcases hv with ⟨ab', hab', _, hnlt⟩
            obtain rfl := Sum.inl.inj hab'
            cases lt with
            | inl αβ => simp [NmW, dif_neg (wGL_ne_one D), hnlt]
            | inr γ =>
                simp only [NmW, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and]
                exact ⟨ab.1, by
                  congr 1; apply Subtype.ext; exact Prod.ext rfl (eq_sub_of_add_eq' hnlt).symm⟩⟩⟩
  invFun y :=
    match y with
    | ⟨⟨ω, hω⟩, ⟨κ, hntw, hnmw⟩⟩ =>
        if h1 : ω = 1 then
          ⟨(l, false), ⟨rfl, by
            simp only [Ntw, dif_pos h1, Finset.mem_singleton] at hntw
            simp only [NmW, dif_pos h1, Finset.mem_singleton] at hnmw
            exact (congrArg Subtype.val (Sum.inl.inj (hntw.symm.trans hnmw))).symm⟩⟩
        else
          match κ, hntw, hnmw with
          | .inl l', _, _ => False.elim (h1 l'.2)
          | .inr ab, hntw, hnmw =>
              ⟨(.inl ab.1, true), by
                have hωw : ω = wGL D := hω.resolve_left h1
                subst hωw
                refine ⟨ab.1, rfl, ?_, ?_⟩
                · cases l with
                  | inl αβ =>
                      simp only [Ntw, dif_neg (wGL_ne_one D), Finset.mem_singleton] at hntw
                      exact congrArg Subtype.val (Sum.inr.inj hntw)
                  | inr γ =>
                      simp only [Ntw, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and] at hntw
                      obtain ⟨δ, hδ⟩ := hntw
                      have heq := congrArg Subtype.val (Sum.inr.inj hδ)
                      rw [← heq]
                      exact sub_add_cancel γ δ
                · cases lt with
                  | inl αβ =>
                      simp only [NmW, dif_neg (wGL_ne_one D), Finset.mem_singleton] at hnmw
                      exact congrArg Subtype.val (Sum.inr.inj hnmw)
                  | inr γ =>
                      simp only [NmW, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and] at hnmw
                      obtain ⟨δ, hδ⟩ := hnmw
                      have heq := congrArg Subtype.val (Sum.inr.inj hδ)
                      rw [← heq]
                      exact add_sub_cancel δ γ⟩
  left_inv x := by
    rcases x with ⟨⟨κ, ω⟩, hv⟩
    cases ω
    · dsimp [ValidIn] at hv
      dsimp only
      rw [dif_pos rfl]
      exact Subtype.ext (Prod.ext hv.1.symm rfl)
    · rcases κ with ab | γ
      · simp [dif_neg (wGL_ne_one D)]
      · exfalso; dsimp [ValidIn] at hv; rcases hv with ⟨ab, h, _⟩; cases h
  right_inv y := by
    rcases y with ⟨⟨ω, hω⟩, ⟨κ, hntw, hnmw⟩⟩
    by_cases h1 : ω = 1
    · subst h1
      have hκ : κ = Sum.inl ⟨l, rfl⟩ := by simpa [Ntw] using hntw
      subst hκ
      simp
    · have hωw : ω = wGL D := hω.resolve_left h1
      subst hωw
      rcases κ with l' | ab
      · exact absurd l'.2 (wGL_ne_one D)
      · simp [dif_neg (wGL_ne_one D)]

lemma A70_eq_zero_of_not_mem (D : FieldData) (l lt κ : D.BIrr) (ω : Bool) (μ : D.Irr)
    (h : ¬(l ∈ Nminus D μ ∧ lt ∈ Nminus D μ)) : A70 D l lt κ ω μ = 0 := by
  have hnone : (∀ P : D.BBas l, labMu D μ l P = none) ∨
      (∀ Pt : D.BBas lt, labMu D μ lt Pt = none) := by
    by_cases hl : l ∈ Nminus D μ
    · right
      intro Pt
      by_contra hne
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
      exact h ⟨hl, ((labMu_eq_some_iff D μ lt Pt i).mp hi).1⟩
    · left
      intro P
      by_contra hne
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hne
      exact hl ((labMu_eq_some_iff D μ l P i).mp hi).1
  cases ω
  · simp only [A70, Bool.false_eq_true, ↓reduceIte]
    split_ifs with hk
    · suffices hsum : (∑ P : D.BBas l, ∑ Pt : D.BBas κ,
          Rent D μ 1 (labMu D μ lt (cast (congrArg D.BBas (hk.1.trans hk.2.symm)) Pt))
              (labMu D μ l P) *
            conj (if cast (congrArg D.BBas hk.1) Pt = P then (1 : ℂ) else 0)) = 0 by
        rw [hsum, mul_zero]
      apply Finset.sum_eq_zero
      intro P _
      apply Finset.sum_eq_zero
      intro Pt _
      rcases hnone with hl0 | hlt0
      · rw [hl0 P]
        cases labMu D μ lt (cast (congrArg D.BBas (hk.1.trans hk.2.symm)) Pt) <;> simp [Rent]
      · rw [hlt0 _]
        simp [Rent]
    · rfl
  · simp only [A70, ↓reduceIte]
    cases κ with
    | inl ab =>
        dsimp only
        rw [mul_eq_zero]
        right
        apply Finset.sum_eq_zero
        intro P _
        rcases hnone with hl0 | hlt0
        · rw [hl0 P]
          cases tLab D lt ab with
          | none => simp
          | some Pt => dsimp only; cases labMu D μ lt Pt <;> simp [Rent]
        · cases tLab D lt ab with
          | none => simp
          | some Pt => dsimp only; rw [hlt0 Pt]; simp [Rent]
    | inr _ => rfl

lemma A70_eq_Ablock (D : FieldData) (l lt : D.BIrr)
    (μ : MSet (Nminus D) l lt)
    (x : {x : D.BIrr × Bool // ValidIn D l x.1 x.2 lt}) :
    A70 D l lt x.1.1 x.1.2 μ.1 =
      Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D)
        l lt μ (validInEquivKSet D l lt x) := by
  rcases x with ⟨⟨κ, ω⟩, hv⟩
  cases ω
  · dsimp [ValidIn] at hv
    have hκ : κ = l := hv.1
    have hlt : lt = l := hv.2
    revert μ hv
    subst κ; subst lt
    intro μ hv
    have hlab : ∀ (ν : D.BIrr) (hν : ν ∈ Nminus D μ.1) (P : D.BBas ν),
        labMu D μ.1 ν P = some (labMuEquiv D μ.1 ⟨⟨ν, hν⟩, P⟩) :=
      fun ν hν P => (labMu_eq_some_iff D μ.1 ν P _).mpr ⟨hν, rfl⟩
    have hcard_mu : Fintype.card (AdBas D.BBas (Nminus D) μ.1) = Fintype.card (D.Bas μ.1) :=
      Fintype.card_congr (labMuEquiv D μ.1)
    have hidx_B : (BSub D).index = D.q + 1 := BSub_index_eq D
    let k0 : KSet (omegaSet D) (NmW D) (Ntw D) l l :=
      ⟨⟨1, Or.inl rfl⟩, ⟨Sum.inl ⟨l, rfl⟩, by simp [Ntw], by simp [NmW]⟩⟩
    have hK : validInEquivKSet D l l ⟨(l, false), hv⟩ = k0 := rfl
    rw [hK]
    dsimp only [A70]
    rw [if_neg Bool.false_ne_true, dif_pos (⟨rfl, rfl⟩ : l = l ∧ l = l)]
    simp only [Ablock, Matrix.of_apply, k0, hcard_mu, interSub_one_index_eq D, hidx_B]
    have hcard_bw : Fintype.card (BW D 1 (.inl ⟨l, rfl⟩)) = Fintype.card (D.BBas l) :=
      Fintype.card_congr (Equiv.refl (D.BBas l))
    rw [hcard_bw]
    simp only [Nat.cast_one, Nat.cast_add]
    congr 1
    apply Finset.sum_congr rfl
    intro P _
    rw [← Fintype.sum_equiv (Equiv.refl (D.BBas l)) _ _ (fun _ => rfl)]
    apply Finset.sum_congr rfl
    intro Pt _
    simp only [cast_eq, hlab l μ.2.1 P, hlab l μ.2.2 Pt, Rent, RG,
      Matrix.submatrix_apply, adaptW, ↓reduceDIte, Equiv.coe_fn_symm_mk, Utw, Matrix.of_apply]
  · rcases κ with ab | γ
    · have hv' := hv
      dsimp [ValidIn] at hv'
      rcases hv' with ⟨ab', hab', hnl, hnlt⟩
      obtain rfl := Sum.inl.inj hab'
      have hlab : ∀ (ν : D.BIrr) (hν : ν ∈ Nminus D μ.1) (P : D.BBas ν),
          labMu D μ.1 ν P = some (labMuEquiv D μ.1 ⟨⟨ν, hν⟩, P⟩) :=
        fun ν hν P => (labMu_eq_some_iff D μ.1 ν P _).mpr ⟨hν, rfl⟩
      have hcard_mu : Fintype.card (AdBas D.BBas (Nminus D) μ.1) = Fintype.card (D.Bas μ.1) :=
        Fintype.card_congr (labMuEquiv D μ.1)
      have hidx_B : (BSub D).index = D.q + 1 := BSub_index_eq D
      have hmem_ntw : (Sum.inr ⟨ab, wGL_ne_one D⟩ : LambdaW D (wGL D)) ∈ Ntw D (wGL D) l := by
        cases l with
        | inl αβ => simp [Ntw, dif_neg (wGL_ne_one D), hnl]
        | inr γ =>
            simp only [Ntw, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨ab.2, by congr 1; apply Subtype.ext; exact Prod.ext (eq_sub_of_add_eq hnl).symm rfl⟩
      have hmem_nmw : (Sum.inr ⟨ab, wGL_ne_one D⟩ : LambdaW D (wGL D)) ∈ NmW D (wGL D) lt := by
        cases lt with
        | inl αβ => simp [NmW, dif_neg (wGL_ne_one D), hnlt]
        | inr γ =>
            simp only [NmW, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨ab.1, by congr 1; apply Subtype.ext; exact Prod.ext rfl (eq_sub_of_add_eq' hnlt).symm⟩
      have htlab := tLab_eq_some_adaptW_symm D lt ab hnlt hmem_nmw
      let k1 : KSet (omegaSet D) (NmW D) (Ntw D) l lt :=
        ⟨⟨wGL D, Or.inr rfl⟩, ⟨Sum.inr ⟨ab, wGL_ne_one D⟩, hmem_ntw, hmem_nmw⟩⟩
      have hK : validInEquivKSet D l lt ⟨(Sum.inl ab, true), hv⟩ = k1 := rfl
      rw [hK]
      simp only [A70, ↓reduceIte, Ablock, Matrix.of_apply, k1, hcard_mu,
        interSub_wGL_index_eq D, hidx_B]
      have hcard_bw : Fintype.card (BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩)) = 1 :=
        Fintype.card_congr (Equiv.refl Unit) |>.trans Fintype.card_unit
      rw [hcard_bw]
      simp only [Nat.cast_one, Nat.cast_add]
      congr 1
      apply Finset.sum_congr rfl
      intro P _
      have hsum_pt : (∑ Pt : BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩),
          RG D μ.1 (wGL D) ⟨⟨lt, μ.2.2⟩, (adaptW D (wGL D) lt).symm
              ⟨⟨.inr ⟨ab, wGL_ne_one D⟩, hmem_nmw⟩, Pt⟩⟩ ⟨⟨l, μ.2.1⟩, P⟩ *
            conj (Utw D (wGL D) l ⟨⟨.inr ⟨ab, wGL_ne_one D⟩, hmem_ntw⟩, Pt⟩ P)) =
          RG D μ.1 (wGL D) ⟨⟨lt, μ.2.2⟩, (adaptW D (wGL D) lt).symm
              ⟨⟨.inr ⟨ab, wGL_ne_one D⟩, hmem_nmw⟩, ()⟩⟩ ⟨⟨l, μ.2.1⟩, P⟩ *
            conj (Utw D (wGL D) l ⟨⟨.inr ⟨ab, wGL_ne_one D⟩, hmem_ntw⟩, ()⟩ P) := by
        let : Unique (BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩)) :=
          ⟨⟨()⟩, fun x => Subsingleton.elim (α := Unit) x ()⟩
        exact Fintype.sum_unique _
      rw [hsum_pt, htlab]
      simp only [hlab l μ.2.1 P, hlab lt μ.2.2 _, Rent, RG, Matrix.submatrix_apply,
        Utw, Matrix.of_apply]
    · exfalso; dsimp [ValidIn] at hv; rcases hv with ⟨ab, h, _⟩; cases h

local instance instFintypeNOutAux (D : FieldData) (ω : omegaSet D) (l : D.BIrr) :
    Fintype (Σ κ : Ntw D ω.1 l, Σ lt : {lt : D.BIrr // κ.1 ∈ NmW D ω.1 lt}, D.BBas lt.1) :=
  Sigma.instFintype

local instance instFintypeNOut (D : FieldData) (l : D.BIrr) :
    Fintype (NOut (omegaSet D) D.BBas (NmW D) (Ntw D) l) :=
  Sigma.instFintype

lemma theorem_5_4_inst (D : FieldData) (l : D.BIrr) :
    Aop (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D) l *
        Nop (BSub D) (omegaSet D) (tOmega D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D) l =
      UIndLam (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D) l ∧
    ∀ lt : D.BIrr,
      Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D) l lt *
          (Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D) l lt)ᴴ = 1 ∧
        (Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D) l lt)ᴴ *
          Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D) l lt = 1 := by
  convert theorem_5_4 (BSub D) (omegaSet D) (hOmega D) (tOmega D) (hTOmega D)
    D.BBas (Nminus D) (RH D) (RH_isIrrepSystem D) (RG D)
    (by convert RG_isIrrepSystem D; all_goals rfl)
    (RG_isSubgroupAdapted D) (BW D) (RW D) (RW_isIrrepSystem D) (NmW D) (adaptW D)
    (hAdW D) (Ntw D) (Utw D) (hUtw D) l

lemma totalA_iso (D : FieldData) : (totalA D).conjTranspose * totalA D = 1 := by
  ext x₁ x₂
  rcases x₁ with ⟨⟨l₁, κ₁, ω₁, lt₁⟩, hv₁⟩
  rcases x₂ with ⟨⟨l₂, κ₂, ω₂, lt₂⟩, hv₂⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, totalA, Matrix.of_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  by_cases hll : l₁ = l₂ ∧ lt₁ = lt₂
  · rcases hll with ⟨rfl, rfl⟩
    rw [Finset.sum_eq_single l₁]
    · trans ∑ μ : D.Irr, starRingEnd ℂ (A70 D l₁ lt₁ κ₁ ω₁ μ) * A70 D l₁ lt₁ κ₂ ω₂ μ
      · apply Finset.sum_congr rfl; intro μ _
        rw [Finset.sum_eq_single lt₁]
        · simp
        · intro lt' _ hlt'; simp [hlt']
        · intro hm; exact absurd (Finset.mem_univ _) hm
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset D.Irr)
        (fun μ => l₁ ∈ Nminus D μ ∧ lt₁ ∈ Nminus D μ)]
      have hzero : ∑ μ ∈ Finset.univ.filter (fun μ => ¬(l₁ ∈ Nminus D μ ∧ lt₁ ∈ Nminus D μ)),
          starRingEnd ℂ (A70 D l₁ lt₁ κ₁ ω₁ μ) * A70 D l₁ lt₁ κ₂ ω₂ μ = 0 :=
        Finset.sum_eq_zero fun μ hμ => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hμ
          simp [A70_eq_zero_of_not_mem D l₁ lt₁ κ₁ ω₁ μ hμ]
      rw [hzero, add_zero, ← Finset.sum_coe_sort]
      have hsum_m : (∑ μ : {μ : D.Irr // μ ∈ Finset.univ.filter (fun μ =>
            l₁ ∈ Nminus D μ ∧ lt₁ ∈ Nminus D μ)},
          starRingEnd ℂ (A70 D l₁ lt₁ κ₁ ω₁ μ.1) * A70 D l₁ lt₁ κ₂ ω₂ μ.1) =
          ∑ μ : MSet (Nminus D) l₁ lt₁,
            starRingEnd ℂ (Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D)
              (adaptW D) (Ntw D) (Utw D) l₁ lt₁ μ (validInEquivKSet D l₁ lt₁ ⟨(κ₁, ω₁), hv₁⟩)) *
            Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D)
              (adaptW D) (Ntw D) (Utw D) l₁ lt₁ μ (validInEquivKSet D l₁ lt₁ ⟨(κ₂, ω₂), hv₂⟩) := by
        refine Fintype.sum_equiv (Equiv.subtypeEquivRight (by simp)) _ _ fun μ => ?_
        let μ' : MSet (Nminus D) l₁ lt₁ := (Equiv.subtypeEquivRight (by simp)) μ
        have h1 := A70_eq_Ablock D l₁ lt₁ μ' ⟨(κ₁, ω₁), hv₁⟩
        have h2 := A70_eq_Ablock D l₁ lt₁ μ' ⟨(κ₂, ω₂), hv₂⟩
        exact congrArg₂ (· * ·) (congrArg (starRingEnd ℂ) h1) h2
      rw [hsum_m]
      have h54 := ((theorem_5_4_inst D l₁).2 lt₁).2
      have hentry : (∑ μ : MSet (Nminus D) l₁ lt₁,
          starRingEnd ℂ (Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D)
            (adaptW D) (Ntw D) (Utw D) l₁ lt₁ μ (validInEquivKSet D l₁ lt₁ ⟨(κ₁, ω₁), hv₁⟩)) *
          Ablock (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D)
            (adaptW D) (Ntw D) (Utw D) l₁ lt₁ μ (validInEquivKSet D l₁ lt₁ ⟨(κ₂, ω₂), hv₂⟩)) =
          if validInEquivKSet D l₁ lt₁ ⟨(κ₁, ω₁), hv₁⟩ =
              validInEquivKSet D l₁ lt₁ ⟨(κ₂, ω₂), hv₂⟩ then 1 else 0 := by
        simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
          congrFun (congrFun h54 (validInEquivKSet D l₁ lt₁ ⟨(κ₁, ω₁), hv₁⟩))
            (validInEquivKSet D l₁ lt₁ ⟨(κ₂, ω₂), hv₂⟩)
      rw [hentry]
      have hiff : validInEquivKSet D l₁ lt₁ ⟨(κ₁, ω₁), hv₁⟩ =
            validInEquivKSet D l₁ lt₁ ⟨(κ₂, ω₂), hv₂⟩ ↔
          (⟨(l₁, κ₁, ω₁, lt₁), hv₁⟩ : InReg D) = ⟨(l₁, κ₂, ω₂, lt₁), hv₂⟩ := by
        rw [(validInEquivKSet D l₁ lt₁).injective.eq_iff]
        constructor
        · intro h
          rcases Prod.mk.inj (Subtype.mk.inj h) with ⟨rfl, rfl⟩
          rfl
        · intro h
          have hv := congrArg Subtype.val h
          exact Subtype.ext (Prod.ext (congrArg (fun p => p.2.1) hv) (congrArg (fun p => p.2.2.1) hv))
      simp [hiff]
    · intro l' _ hl'
      apply Finset.sum_eq_zero; intro μ _
      apply Finset.sum_eq_zero; intro lt' _
      simp [hl']
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · have hne : (⟨(l₁, κ₁, ω₁, lt₁), hv₁⟩ : InReg D) ≠ ⟨(l₂, κ₂, ω₂, lt₂), hv₂⟩ := by
      intro h; apply hll
      have := congrArg Subtype.val h
      exact ⟨congrArg Prod.fst this, congrArg (fun p => p.2.2.2) this⟩
    rw [if_neg hne]
    apply Finset.sum_eq_zero; intro l' _
    apply Finset.sum_eq_zero; intro μ _
    apply Finset.sum_eq_zero; intro lt' _
    by_cases h1 : l' = l₁ ∧ lt' = lt₁
    · rcases h1 with ⟨rfl, rfl⟩
      have h2 : ¬(l' = l₂ ∧ lt' = lt₂) := fun h => hll h
      simp [h2]
    · simp [h1]

/-! ### Part 5b: Mackey factorization theorem (`D.qftGL2 = ...`) and final `solution` -/

lemma sum_eq_sum_of_inj_vanish {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (g : β → ℂ)
    (h0 : ∀ b, (∀ a, f a ≠ b) → g b = 0) :
    ∑ b : β, g b = ∑ a : α, g (f a) := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
  · exact Finset.sum_image (fun a₁ _ a₂ _ h => hf h)
  · intro b _ hb
    apply h0 b
    intro a ha
    exact hb (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ha⟩)

private lemma mackeyOut_sigma_eq (D : FieldData) (μ : D.Irr) (l lt : D.BIrr)
    (hl : l ∈ Nminus D μ) (hlt : lt ∈ Nminus D μ) (Q : D.BBas lt) (R : D.BBas l)
    (a b : AdBas D.BBas (Nminus D) μ)
    (ha : a = ⟨⟨lt, hlt⟩, Q⟩) (hb : b = ⟨⟨l, hl⟩, R⟩) :
    (⟨(b.1.1, μ, a.1.1), (a.2, b.2)⟩ : Σ y : OutReg D, D.BBas y.2.2 × D.BBas y.1) =
      ⟨(l, μ, lt), (Q, R)⟩ := by
  subst ha; subst hb; rfl

private def mackeyOutInvFun (D : FieldData) (o : D.OutLabel) : MackeyOut D :=
  let ltQ := (labMuEquiv D o.1).symm o.2.1
  let lR := (labMuEquiv D o.1).symm o.2.2
  ⟨⟨(lR.1.1, o.1, ltQ.1.1), (ltQ.2, lR.2)⟩,
    by simp [(labMu_eq_some_iff D o.1 ltQ.1.1 ltQ.2 o.2.1).mpr ⟨ltQ.1.2, by simp [ltQ]⟩],
    by simp [(labMu_eq_some_iff D o.1 lR.1.1 lR.2 o.2.2).mpr ⟨lR.1.2, by simp [lR]⟩]⟩

def mackeyOutEquiv (D : FieldData) : MackeyOut D ≃ D.OutLabel where
  toFun := mackeyReindexFun D
  invFun := mackeyOutInvFun D
  left_inv m := by
    rcases m with ⟨⟨⟨l, μ, lt⟩, ⟨Q, R⟩⟩, hm1, hm2⟩
    obtain ⟨hlt, hQ⟩ := (labMu_eq_some_iff D μ lt Q _).mp (Option.some_get hm1).symm
    obtain ⟨hl, hR⟩ := (labMu_eq_some_iff D μ l R _).mp (Option.some_get hm2).symm
    have hsym1 : (labMuEquiv D μ).symm (Option.get (labMu D μ lt Q) hm1) = ⟨⟨lt, hlt⟩, Q⟩ :=
      (labMuEquiv D μ).symm_apply_eq.mpr hQ.symm
    have hsym2 : (labMuEquiv D μ).symm (Option.get (labMu D μ l R) hm2) = ⟨⟨l, hl⟩, R⟩ :=
      (labMuEquiv D μ).symm_apply_eq.mpr hR.symm
    apply Subtype.ext
    dsimp only [mackeyOutInvFun, mackeyReindexFun]
    exact mackeyOut_sigma_eq D μ l lt hl hlt Q R
      ((labMuEquiv D μ).symm (Option.get (labMu D μ lt Q) hm1))
      ((labMuEquiv D μ).symm (Option.get (labMu D μ l R) hm2))
      hsym1 hsym2
  right_inv o := by
    rcases o with ⟨μ, ⟨i, j⟩⟩
    dsimp only [mackeyReindexFun, mackeyOutInvFun]
    have h1 : labMu D μ ((labMuEquiv D μ).symm i).1.1 ((labMuEquiv D μ).symm i).2 = some i :=
      (labMu_eq_some_iff D μ _ _ i).mpr ⟨((labMuEquiv D μ).symm i).1.2, by simp⟩
    have h2 : labMu D μ ((labMuEquiv D μ).symm j).1.1 ((labMuEquiv D μ).symm j).2 = some j :=
      (labMu_eq_some_iff D μ _ _ j).mpr ⟨((labMuEquiv D μ).symm j).1.2, by simp⟩
    refine Sigma.ext rfl (heq_of_eq (Prod.ext ?_ ?_))
    · exact Option.some.inj ((Option.some_get _).trans h1)
    · exact Option.some.inj ((Option.some_get _).trans h2)

lemma circuit_entry_eq (D : FieldData) (μ : D.Irr) (i j : D.Bas μ) (g : D.G) :
    let ltQ := (labMuEquiv D μ).symm i
    let lR := (labMuEquiv D μ).symm j
    let l := lR.1.1
    let lt := ltQ.1.1
    let Q := ltQ.2
    let R := lR.2
    let t₀ := ((bruhatEquiv D).symm g).1
    let b₀ := ((bruhatEquiv D).symm g).2
    (mackeyReindexMat D *
      Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
      mackeyNopMat D * frameMat (A := CosetT D) D.qftB * mackeyEncMat D) ⟨μ, (i, j)⟩ g =
      ∑ x : {p : D.BIrr × Bool // ValidIn D l p.1 p.2 lt},
        A70 D l lt x.1.1 x.1.2 μ *
        ∑ P : D.BBas l,
          mackeyNopMat D ⟨⟨(l, x.1.1, x.1.2, lt), x.2⟩, (Q, R)⟩ (t₀, ⟨l, (P, R)⟩) *
          D.qftB ⟨l, (P, R)⟩ b₀ := by
  intro ltQ lR l lt Q R t₀ b₀
  have htb_pair : (bruhatEquiv D).symm g = (t₀, b₀) := rfl
  -- Step 1: peel `mackeyEncMat D`
  rw [Matrix.mul_apply]
  have hstep1 : (∑ tb : CosetT D × D.BElt,
      (mackeyReindexMat D *
        Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
        mackeyNopMat D * frameMat (A := CosetT D) D.qftB) ⟨μ, (i, j)⟩ tb * mackeyEncMat D tb g) =
      (mackeyReindexMat D *
        Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
        mackeyNopMat D * frameMat (A := CosetT D) D.qftB) ⟨μ, (i, j)⟩ (t₀, b₀) := by
    rw [Finset.sum_eq_single ((bruhatEquiv D).symm g)]
    · have hbr : g = bruhatEquiv D (t₀, b₀) := by
        simpa [htb_pair] using ((bruhatEquiv D).apply_symm_apply g).symm
      simp [mackeyEncMat_eq_if, hbr]
    · intro tb _ htb
      have hne : g ≠ bruhatEquiv D tb := fun h =>
        htb (by rw [h, (bruhatEquiv D).symm_apply_apply])
      simp [mackeyEncMat_eq_if, hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hstep1]
  -- Step 2: peel `frameMat (A := CosetT D) D.qftB`
  rw [Matrix.mul_apply]
  have hstep2 : (∑ tb' : CosetT D × D.BOutLabel,
      (mackeyReindexMat D *
        Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
        mackeyNopMat D) ⟨μ, (i, j)⟩ tb' *
        frameMat (A := CosetT D) D.qftB tb' (t₀, b₀)) =
      ∑ bo : D.BOutLabel,
        (mackeyReindexMat D *
          Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
          mackeyNopMat D) ⟨μ, (i, j)⟩ (t₀, bo) * D.qftB bo b₀ := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single t₀]
    · simp [frameMat]
    · intro t _ ht
      apply Finset.sum_eq_zero; intro bo _
      simp [frameMat, ht]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hstep2]
  -- Step 3: peel `mackeyReindexMat D`
  have h1m : (labMu D μ lt Q).isSome = true := by
    have heq := (labMu_eq_some_iff D μ lt Q i).mpr ⟨ltQ.1.2, (labMuEquiv D μ).apply_symm_apply i⟩
    rw [heq]; rfl
  have h2m : (labMu D μ l R).isSome = true := by
    have heq := (labMu_eq_some_iff D μ l R j).mpr ⟨lR.1.2, (labMuEquiv D μ).apply_symm_apply j⟩
    rw [heq]; rfl
  have hm_out : (mackeyOutEquiv D).symm ⟨μ, (i, j)⟩ = ⟨⟨(l, μ, lt), (Q, R)⟩, h1m, h2m⟩ := rfl
  have hreindex : ∀ m : MackeyMid D,
      (mackeyReindexMat D *
        Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D))
        ⟨μ, (i, j)⟩ m =
      frameMat (A := D.Lab × D.Lab) (totalA D)
        (mackeyOutEmb D ((mackeyOutEquiv D).symm ⟨μ, (i, j)⟩)) (mackeyMidEmb D m) := by
    intro m
    simp only [Matrix.mul_apply, mackeyReindexMat, permMat, Matrix.submatrix_apply, Matrix.of_apply]
    rw [Finset.sum_eq_single ((mackeyOutEquiv D).symm ⟨μ, (i, j)⟩)]
    · have happ : mackeyReindexFun D ((mackeyOutEquiv D).symm ⟨μ, (i, j)⟩) = ⟨μ, (i, j)⟩ :=
        (mackeyOutEquiv D).apply_symm_apply ⟨μ, (i, j)⟩
      simp [happ]
    · intro m' _ hm'
      have hne : mackeyReindexFun D m' ≠ ⟨μ, (i, j)⟩ := fun h =>
        hm' ((mackeyOutEquiv D).injective (h.trans ((mackeyOutEquiv D).apply_symm_apply ⟨μ, (i, j)⟩).symm))
      rw [if_neg hne.symm, zero_mul]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  -- Step 4: expand `... * mackeyNopMat D`, swap `bo` and `m`, collapse `bo`
  have hstep3 : (∑ bo : D.BOutLabel,
      (mackeyReindexMat D *
        Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
        mackeyNopMat D) ⟨μ, (i, j)⟩ (t₀, bo) * D.qftB bo b₀) =
      ∑ m : MackeyMid D,
        frameMat (A := D.Lab × D.Lab) (totalA D)
          (mackeyOutEmb D ((mackeyOutEquiv D).symm ⟨μ, (i, j)⟩)) (mackeyMidEmb D m) *
        ∑ P : D.BBas m.1.1.1,
          mackeyNopMat D m (t₀, ⟨m.1.1.1, (P, m.2.2)⟩) * D.qftB ⟨m.1.1.1, (P, m.2.2)⟩ b₀ := by
    have hmul1 : ∀ bo : D.BOutLabel, (mackeyReindexMat D *
        Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
        mackeyNopMat D) ⟨μ, (i, j)⟩ (t₀, bo) =
      ∑ m : MackeyMid D,
        frameMat (A := D.Lab × D.Lab) (totalA D)
          (mackeyOutEmb D ((mackeyOutEquiv D).symm ⟨μ, (i, j)⟩)) (mackeyMidEmb D m) *
        mackeyNopMat D m (t₀, bo) := by
      intro bo
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [hreindex m]
    simp_rw [hmul1, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    have hbo_sum : (∑ bo : D.BOutLabel, mackeyNopMat D m (t₀, bo) * D.qftB bo b₀) =
        ∑ P : D.BBas m.1.1.1,
          mackeyNopMat D m (t₀, ⟨m.1.1.1, (P, m.2.2)⟩) * D.qftB ⟨m.1.1.1, (P, m.2.2)⟩ b₀ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single m.1.1.1]
      · rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl; intro P _
        rw [Finset.sum_eq_single m.2.2]
        · intro R' _ hR'
          simp [mackeyNopMat, Matrix.of_apply, hR'.symm]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      · intro ν _ hν
        apply Finset.sum_eq_zero; intro PR _
        simp [mackeyNopMat, Matrix.of_apply, hν]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    rw [hbo_sum]
  rw [hstep3]
  -- Step 5: collapse `m : MackeyMid D` to `{p // ValidIn D l p.1 p.2 lt}`
  let injMid : {p : D.BIrr × Bool // ValidIn D l p.1 p.2 lt} → MackeyMid D :=
    fun x => ⟨⟨(l, x.1.1, x.1.2, lt), x.2⟩, (Q, R)⟩
  have hinj : Function.Injective injMid := by
    rintro ⟨⟨κ₁, ω₁⟩, hv₁⟩ ⟨⟨κ₂, ω₂⟩, hv₂⟩ h
    have h1 := congrArg (fun m : MackeyMid D => m.1.1.2.1) h
    have h2 := congrArg (fun m : MackeyMid D => m.1.1.2.2.1) h
    dsimp only [injMid] at h1 h2
    exact Subtype.ext (Prod.ext h1 h2)
  rw [sum_eq_sum_of_inj_vanish injMid hinj]
  · apply Finset.sum_congr rfl; intro x _
    rw [hm_out]
    simp only [injMid, frameMat, mackeyOutEmb, mackeyMidEmb, totalA, Matrix.of_apply,
      ↓reduceIte, and_self]
  · intro m hm
    suffices h0 : frameMat (A := D.Lab × D.Lab) (totalA D)
        (mackeyOutEmb D ((mackeyOutEquiv D).symm ⟨μ, (i, j)⟩)) (mackeyMidEmb D m) = 0 by
      rw [h0, zero_mul]
    by_contra hne
    rcases m with ⟨⟨⟨lm, κm, ωm, ltm⟩, hvm⟩, ⟨Qm, Rm⟩⟩
    rw [hm_out] at hne
    simp only [frameMat, mackeyOutEmb, mackeyMidEmb, totalA, Matrix.of_apply] at hne
    split_ifs at hne with hlab hll
    · rcases hll with ⟨hl_eq, hlt_eq⟩
      subst hl_eq; subst hlt_eq
      simp only [Prod.mk.injEq] at hlab
      have hQ : Qm = Q := bbasLab_injective D lt hlab.1.symm
      have hR : Rm = R := bbasLab_injective D l hlab.2.symm
      subst hQ; subst hR
      exact hm ⟨(κm, ωm), hvm⟩ rfl
    · exact hne rfl
    · exact hne rfl

lemma qftB_entry_eq (D : FieldData) (b₀ : D.BElt) (l : D.BIrr) (P R : D.BBas l) :
    fourierMatrix (RH D) ⟨l, (P, R)⟩ (bEltEquivB D b₀) = D.qftB ⟨l, (P, R)⟩ b₀ := by
  simp only [FieldData.qftB, fourierMatrix, RH, Matrix.of_apply, bEltEquivB_coe_mat]
  rw [← Fintype.card_congr (bEltEquivB D)]

lemma nop_entry_eq (D : FieldData) (l lt : D.BIrr) (Q : D.BBas lt) (R : D.BBas l)
    (P : D.BBas l) (t₀ : CosetT D) (x : {p : D.BIrr × Bool // ValidIn D l p.1 p.2 lt}) :
    let k := validInEquivKSet D l lt x
    let o_nop : NOut (omegaSet D) D.BBas (NmW D) (Ntw D) l :=
      ⟨k.1, ⟨k.2.1, k.2.2.1⟩, ⟨lt, k.2.2.2⟩, Q⟩
    Nop (BSub D) (omegaSet D) (tOmega D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) (Ntw D) (Utw D)
        l o_nop (mackeyT_equiv D t₀, P) =
      mackeyNopMat D ⟨⟨(l, x.1.1, x.1.2, lt), x.2⟩, (Q, R)⟩ (t₀, ⟨l, (P, R)⟩) := by
  have hpos_BBas : ∀ ν : D.BIrr, 0 < Fintype.card (D.BBas ν) := fun ν => by
    cases ν with
    | inl _ => exact Fintype.card_pos (α := Unit)
    | inr _ => exact Fintype.card_pos (α := D.Lab)
  rcases x with ⟨⟨κ, ω⟩, hv⟩
  cases ω
  · dsimp [ValidIn] at hv
    have hκ : κ = l := hv.1
    have hlt : lt = l := hv.2
    revert Q R hv
    subst κ; subst lt
    intro Q R hv
    let k0 : KSet (omegaSet D) (NmW D) (Ntw D) l l :=
      ⟨⟨1, Or.inl rfl⟩, ⟨Sum.inl ⟨l, rfl⟩, by simp [Ntw], by simp [NmW]⟩⟩
    have hK : validInEquivKSet D l l ⟨(l, false), hv⟩ = k0 := rfl
    dsimp only
    rw [hK]
    cases t₀ with
    | inl u =>
        rcases u with ⟨⟩
        have hex : ∃ a : tOmega D 1, ((a : BSub D) : D.G) * (1 : D.G) = (mackeyT_equiv D (.inl ()) : D.G) :=
          ⟨⟨1, by simp [tOmega]⟩, by simp [mackeyT_equiv, cosetRep]⟩
        simp only [Nop, Matrix.of_apply, k0, dif_pos hex]
        have ha1 : (Classical.choose hex).1 = 1 := by
          have ha := (Classical.choose hex).2
          simp only [tOmega, ↓reduceIte, Set.mem_singleton_iff] at ha
          exact ha
        have ht1_card : Fintype.card (tOmega D 1) = 1 := by
          let e1 : Unit ≃ tOmega D 1 :=
            { toFun := fun _ => ⟨1, by simp [tOmega]⟩
              invFun := fun _ => ()
              left_inv := fun _ => rfl
              right_inv := fun ⟨a, ha⟩ => by
                simp only [tOmega, ↓reduceIte, Set.mem_singleton_iff] at ha
                subst ha; rfl }
          exact (Fintype.card_congr e1).symm.trans Fintype.card_unit
        have hbw1 : Fintype.card (BW D 1 (.inl ⟨l, rfl⟩)) = Fintype.card (D.BBas l) :=
          Fintype.card_congr (Equiv.refl _)
        have hsqrt : Real.sqrt ((Fintype.card (AdBas (BW D 1) (NmW D 1) l) : ℝ) /
            ((Fintype.card (BW D 1 (.inl ⟨l, rfl⟩)) : ℝ) * (Fintype.card (tOmega D 1) : ℝ))) = 1 := by
          rw [← Fintype.card_congr (adaptW D 1 l), hbw1, ht1_card]
          simp only [Nat.cast_one, mul_one]
          rw [div_self (Nat.cast_ne_zero.mpr (hpos_BBas l).ne'), Real.sqrt_one]
        have hRH_one : ∀ Pt : D.BBas l, RH D l 1 Q Pt = if Q = Pt then 1 else 0 := by
          intro Pt
          have hmat1 := ((RH_isIrrepSystem D).1 l).1.1
          simpa [Matrix.one_apply] using congrFun (congrFun hmat1 Q) Pt
        have hsum_P : (∑ Pt : D.BBas l,
            UIndLam (tOmega D 1) (BW D 1) (NmW D 1) (RHad (BSub D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) 1)
              (.inl ⟨l, rfl⟩) ⟨⟨l, by simp [NmW]⟩, adaptW D 1 l Q⟩ (Classical.choose hex, Pt) *
            Utw D 1 l ⟨⟨.inl ⟨l, rfl⟩, by simp [Ntw]⟩, Pt⟩ P) = if Q = P then 1 else 0 := by
          have hterm : ∀ Pt : D.BBas l,
              UIndLam (tOmega D 1) (BW D 1) (NmW D 1)
                (RHad (BSub D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) 1)
                (.inl ⟨l, rfl⟩) ⟨⟨l, by simp [NmW]⟩, adaptW D 1 l Q⟩ (Classical.choose hex, Pt) *
                Utw D 1 l ⟨⟨.inl ⟨l, rfl⟩, by simp [Ntw]⟩, Pt⟩ P =
              (if Q = Pt then 1 else 0) * (if Pt = P then 1 else 0) := by
            intro Pt
            simp only [UIndLam, Matrix.of_apply, hsqrt, Complex.ofReal_one, one_mul,
              RHad, Matrix.submatrix_apply, ha1, adaptW, ↓reduceDIte, Equiv.coe_fn_symm_mk,
              Equiv.coe_fn_mk, cast_eq, Utw]
            congr 1
            exact hRH_one Pt
          simp_rw [hterm]
          rw [Finset.sum_eq_single Q]
          · simp [eq_comm]
          · intro Pt _ hPt; simp [Ne.symm hPt]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        have hsum_eq : (∑ Pt : BW D 1 (.inl ⟨l, rfl⟩),
            UIndLam (tOmega D 1) (BW D 1) (NmW D 1) (RHad (BSub D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) 1)
              (.inl ⟨l, rfl⟩) ⟨⟨l, by simp [NmW]⟩, adaptW D 1 l Q⟩ (Classical.choose hex, Pt) *
            Utw D 1 l ⟨⟨.inl ⟨l, rfl⟩, by simp [Ntw]⟩, Pt⟩ P) =
          (∑ Pt : D.BBas l,
            UIndLam (tOmega D 1) (BW D 1) (NmW D 1) (RHad (BSub D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) 1)
              (.inl ⟨l, rfl⟩) ⟨⟨l, by simp [NmW]⟩, adaptW D 1 l Q⟩ (Classical.choose hex, Pt) *
            Utw D 1 l ⟨⟨.inl ⟨l, rfl⟩, by simp [Ntw]⟩, Pt⟩ P) := rfl
        rw [hsum_eq, hsum_P]
        simp only [mackeyNopMat, Matrix.of_apply, ↓reduceDIte, cast_eq, ↓reduceIte]
    | inr xq =>
        have hnex : ¬ ∃ a : tOmega D 1, ((a : BSub D) : D.G) * (1 : D.G) = (mackeyT_equiv D (.inr xq) : D.G) := by
          rintro ⟨⟨a, ha⟩, hmul⟩
          simp only [tOmega, ↓reduceIte, Set.mem_singleton_iff] at ha
          subst ha
          have h10 := congrFun (congrFun (congrArg (fun z : D.G => (z : Matrix (Fin 2) (Fin 2) D.Fq)) hmul) 1) 0
          simp only [Units.val_mul, Units.val_one, mul_one, mackeyT_equiv, Equiv.coe_fn_mk,
            cosetRep, Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
            Matrix.head_cons] at h10
          change (1 : Matrix (Fin 2) (Fin 2) D.Fq) 1 0 = 1 at h10
          rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h10
          exact zero_ne_one h10
        simp only [Nop, Matrix.of_apply, k0, dif_neg hnex]
        simp only [mackeyNopMat, Matrix.of_apply, cast_eq, ↓reduceDIte, ↓reduceIte]
        rw [if_neg (by decide : (false : Bool) ≠ true)]
  · have hv' := hv
    dsimp [ValidIn] at hv'
    rcases hv' with ⟨ab', hab', hnl, hnlt⟩
    rcases κ with ab | γ
    · obtain rfl := Sum.inl.inj hab'
      have hmem_ntw : (Sum.inr ⟨ab, wGL_ne_one D⟩ : LambdaW D (wGL D)) ∈ Ntw D (wGL D) l := by
        cases l with
        | inl αβ => simp [Ntw, dif_neg (wGL_ne_one D), hnl]
        | inr γ =>
            simp only [Ntw, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨ab.2, by congr 1; apply Subtype.ext; exact Prod.ext (eq_sub_of_add_eq hnl).symm rfl⟩
      have hmem_nmw : (Sum.inr ⟨ab, wGL_ne_one D⟩ : LambdaW D (wGL D)) ∈ NmW D (wGL D) lt := by
        cases lt with
        | inl αβ => simp [NmW, dif_neg (wGL_ne_one D), hnlt]
        | inr γ =>
            simp only [NmW, dif_neg (wGL_ne_one D), Finset.mem_image, Finset.mem_univ, true_and]
            exact ⟨ab.1, by congr 1; apply Subtype.ext; exact Prod.ext rfl (eq_sub_of_add_eq' hnlt).symm⟩
      have htlab := tLab_eq_some_adaptW_symm D lt ab hnlt hmem_nmw
      let k1 : KSet (omegaSet D) (NmW D) (Ntw D) l lt :=
        ⟨⟨wGL D, Or.inr rfl⟩, ⟨Sum.inr ⟨ab, wGL_ne_one D⟩, hmem_ntw, hmem_nmw⟩⟩
      have hK : validInEquivKSet D l lt ⟨(Sum.inl ab, true), hv⟩ = k1 := rfl
      dsimp only
      rw [hK]
      cases t₀ with
      | inl u =>
          rcases u with ⟨⟩
          have hnex : ¬ ∃ a : tOmega D (wGL D),
              ((a : BSub D) : D.G) * wGL D = (mackeyT_equiv D (.inl ()) : D.G) := by
            rintro ⟨⟨a, ha⟩, hmul⟩
            simp only [tOmega, if_neg (wGL_ne_one D)] at ha
            obtain ⟨x, rfl⟩ := ha
            have hmul' : (cosetRep D (.inr x) : D.G) = 1 := by
              simpa [uB_mul_wGL D x, mackeyT_equiv, cosetRep] using hmul
            have h10 := congrFun (congrFun (congrArg (fun z : D.G => (z : Matrix (Fin 2) (Fin 2) D.Fq)) hmul') 1) 0
            simp [cosetRep] at h10
          simp only [Nop, Matrix.of_apply, k1]
          split_ifs with hex'
          · exfalso
            rcases hex' with ⟨a, hq⟩
            exact hnex ⟨a, hq⟩
          · simp only [mackeyNopMat, Matrix.of_apply, cast_eq, ↓reduceDIte, ↓reduceIte]
            rw [if_neg (by decide : (true : Bool) ≠ false)]
      | inr xq =>
          have hex : ∃ a : tOmega D (wGL D),
              ((a : BSub D) : D.G) * wGL D = (mackeyT_equiv D (.inr xq) : D.G) :=
            ⟨⟨uB D xq, by simp [tOmega, wGL_ne_one D]⟩,
              by simpa [mackeyT_equiv] using uB_mul_wGL D xq⟩
          have ha_eq : (Classical.choose hex).1 = uB D xq := by
            have h1 : (((Classical.choose hex).1 : BSub D) : D.G) * wGL D = cosetRep D (.inr xq) :=
              Classical.choose_spec hex
            have h2 : ((uB D xq : BSub D) : D.G) * wGL D = cosetRep D (.inr xq) :=
              uB_mul_wGL D xq
            exact Subtype.ext (mul_right_cancel (h1.trans h2.symm))
          have htw_card : Fintype.card (tOmega D (wGL D)) = D.q := by
            let ew : D.Fq ≃ tOmega D (wGL D) :=
              { toFun := fun x => ⟨uB D x, by simp [tOmega, wGL_ne_one D]⟩
                invFun := fun b => (b.1.1 : Matrix (Fin 2) (Fin 2) D.Fq) 0 1
                left_inv := fun x => by simp [uB_mat]
                right_inv := fun ⟨b, hb⟩ => by
                  simp only [tOmega, if_neg (wGL_ne_one D)] at hb
                  obtain ⟨x, rfl⟩ := hb
                  simp [uB_mat] }
            exact (Fintype.card_congr ew).symm.trans (card_Fq D)
          have hcard_bw : Fintype.card (BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩)) = 1 :=
            (Fintype.card_congr (Equiv.refl Unit)).trans Fintype.card_unit
          have hsqrt : (Real.sqrt ((Fintype.card (AdBas (BW D (wGL D)) (NmW D (wGL D)) lt) : ℝ) /
              ((Fintype.card (BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩)) : ℝ) *
                (Fintype.card (tOmega D (wGL D)) : ℝ))) : ℂ) =
              FieldData.isqrt D.q * (Real.sqrt (Fintype.card (D.BBas lt) : ℝ) : ℂ) := by
            rw [Fintype.card_congr (adaptW D (wGL D) lt), hcard_bw, htw_card]
            simp only [Nat.cast_one, one_mul, FieldData.isqrt]
            rw [Real.sqrt_div (Nat.cast_nonneg _), Complex.ofReal_div, Complex.ofReal_inv, inv_mul_eq_div]
          simp only [Nop, Matrix.of_apply, k1, dif_pos hex]
          have hsum_pt : (∑ Pt : BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩),
              UIndLam (tOmega D (wGL D)) (BW D (wGL D)) (NmW D (wGL D))
                  (RHad (BSub D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) (wGL D))
                  (.inr ⟨ab, wGL_ne_one D⟩) ⟨⟨lt, hmem_nmw⟩, adaptW D (wGL D) lt Q⟩
                  (Classical.choose hex, Pt) *
                Utw D (wGL D) l ⟨⟨.inr ⟨ab, wGL_ne_one D⟩, hmem_ntw⟩, Pt⟩ P) =
              UIndLam (tOmega D (wGL D)) (BW D (wGL D)) (NmW D (wGL D))
                  (RHad (BSub D) D.BBas (RH D) (BW D) (NmW D) (adaptW D) (wGL D))
                  (.inr ⟨ab, wGL_ne_one D⟩) ⟨⟨lt, hmem_nmw⟩, adaptW D (wGL D) lt Q⟩
                  (Classical.choose hex, ()) *
                Utw D (wGL D) l ⟨⟨.inr ⟨ab, wGL_ne_one D⟩, hmem_ntw⟩, ()⟩ P := by
            let : Unique (BW D (wGL D) (.inr ⟨ab, wGL_ne_one D⟩)) :=
              ⟨⟨()⟩, fun z => Subsingleton.elim (α := Unit) z ()⟩
            exact Fintype.sum_unique _
          rw [hsum_pt]
          simp only [UIndLam, Matrix.of_apply, hsqrt, RHad, Matrix.submatrix_apply,
            Equiv.symm_apply_apply, ha_eq, RH, uB_mat, Utw]
          simp only [mackeyNopMat, Matrix.of_apply, ↓reduceDIte, ↓reduceIte, cast_eq, htlab]
    · cases hab'

lemma qftGL2_factorization (D : FieldData) :
    D.qftGL2 = mackeyReindexMat D *
      Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
      mackeyNopMat D * frameMat (A := CosetT D) D.qftB * mackeyEncMat D := by
  ext o g
  rcases o with ⟨μ, i, j⟩
  rw [circuit_entry_eq D μ i j g]
  let ltQ := (labMuEquiv D μ).symm i
  let lR := (labMuEquiv D μ).symm j
  let l := lR.1.1
  let hl := lR.1.2
  let lt := ltQ.1.1
  let hlt := ltQ.1.2
  let Q := ltQ.2
  let R := lR.2
  let t₀ := ((bruhatEquiv D).symm g).1
  let b₀ := ((bruhatEquiv D).symm g).2
  change _ = ∑ x : {p : D.BIrr × Bool // ValidIn D l p.1 p.2 lt},
    A70 D l lt x.1.1 x.1.2 μ *
    ∑ P : D.BBas l, mackeyNopMat D ⟨⟨(l, x.1.1, x.1.2, lt), x.2⟩, (Q, R)⟩ (t₀, ⟨l, (P, R)⟩) *
      D.qftB ⟨l, (P, R)⟩ b₀
  have h35 := (lemma_3_5 (BSub D) (mackeyT (BSub D) (omegaSet D) (tOmega D))
    (mackeyT_isComplement D) D.BBas (Nminus D) (RH D) (RG D)
    (fun ν => by convert ((RG_isIrrepSystem D).1 ν).1; all_goals rfl)
    (RG_isSubgroupAdapted D)).2
  have hlhs : D.qftGL2 ⟨μ, (i, j)⟩ g = fourierMatrix (RG D) ⟨μ, (ltQ, lR)⟩ g := by
    simp only [FieldData.qftGL2, fourierMatrix, Matrix.of_apply, RG, Matrix.submatrix_apply,
      ltQ, lR, Equiv.apply_symm_apply, Fintype.card_congr (labMuEquiv D μ)]
  rw [hlhs, congrFun (congrFun h35 ⟨μ, (ltQ, lR)⟩) g, Matrix.submatrix_apply, id_eq]
  -- Peel `Enc (BSub D) (mackeyT ...)`
  have hg_prod : ((mackeyT_equiv D t₀ : D.G) * (bEltEquivB D b₀ : D.G) : D.G) = g := by
    have hbr : bruhatEquiv D (t₀, b₀) = g := (bruhatEquiv D).apply_symm_apply g
    apply Units.ext
    rw [Units.val_mul]
    have ht' : ((mackeyT_equiv D t₀ : mackeyT (BSub D) (omegaSet D) (tOmega D)) : D.G) = cosetRep D t₀ := rfl
    rw [ht']
    have hbrM := congrArg (fun z : D.G => (z : Matrix (Fin 2) (Fin 2) D.Fq)) hbr
    simpa [bruhatEquiv, Equiv.coe_fn_mk, bEltEquivB_coe_mat] using hbrM
  have henc_unique : ∀ th : mackeyT (BSub D) (omegaSet D) (tOmega D) × BSub D,
      g = (th.1 : D.G) * (th.2 : D.G) ↔ th = (mackeyT_equiv D t₀, bEltEquivB D b₀) := by
    intro th
    constructor
    · intro h
      have hbij : Function.Bijective (fun p : mackeyT (BSub D) (omegaSet D) (tOmega D) × BSub D =>
          (p.1 : D.G) * (p.2 : D.G)) := mackeyT_isComplement D
      exact hbij.1 (h.symm.trans hg_prod.symm)
    · intro h; rw [h]; exact hg_prod.symm
  rw [Matrix.mul_apply]
  have henc_sum : (∑ th : mackeyT (BSub D) (omegaSet D) (tOmega D) × BSub D,
      (UIndTensorI (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D) *
        Matrix.kronecker (1 : Matrix (mackeyT (BSub D) (omegaSet D) (tOmega D))
          (mackeyT (BSub D) (omegaSet D) (tOmega D)) ℂ) (fourierMatrix (RH D)))
        (ident D.BBas (Nminus D) ⟨μ, (ltQ, lR)⟩) th *
        Enc (BSub D) (mackeyT (BSub D) (omegaSet D) (tOmega D)) th g) =
      (UIndTensorI (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D) *
        Matrix.kronecker (1 : Matrix (mackeyT (BSub D) (omegaSet D) (tOmega D))
          (mackeyT (BSub D) (omegaSet D) (tOmega D)) ℂ) (fourierMatrix (RH D)))
        (ident D.BBas (Nminus D) ⟨μ, (ltQ, lR)⟩) (mackeyT_equiv D t₀, bEltEquivB D b₀) := by
    rw [Finset.sum_eq_single (mackeyT_equiv D t₀, bEltEquivB D b₀)]
    · simp only [Enc, Matrix.of_apply, if_pos hg_prod.symm, mul_one]
    · intro th _ hth
      have hne : g ≠ (th.1 : D.G) * (th.2 : D.G) := fun h =>
        hth ((henc_unique th).mp h)
      simp [Enc, Matrix.of_apply, hne]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  trans ((UIndTensorI (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D) *
      Matrix.kronecker (1 : Matrix (mackeyT (BSub D) (omegaSet D) (tOmega D))
        (mackeyT (BSub D) (omegaSet D) (tOmega D)) ℂ) (fourierMatrix (RH D)))
    (ident D.BBas (Nminus D) ⟨μ, (ltQ, lR)⟩) (mackeyT_equiv D t₀, bEltEquivB D b₀))
  · convert henc_sum
  -- Peel `1 ⊗ fourierMatrix (RH D)` and `UIndTensorI`
  rw [Matrix.mul_apply]
  let fP : D.BBas l → mackeyT (BSub D) (omegaSet D) (tOmega D) × D.BOutLabel :=
    fun P => (mackeyT_equiv D t₀, ⟨l, (P, R)⟩)
  have hfP_inj : Function.Injective fP := by
    intro P₁ P₂ h
    have h2 : (⟨l, (P₁, R)⟩ : D.BOutLabel) = ⟨l, (P₂, R)⟩ := congrArg Prod.snd h
    have h3 : (P₁, R) = (P₂, R) := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
    exact congrArg Prod.fst h3
  rw [sum_eq_sum_of_inj_vanish fP hfP_inj]
  · have hP_term : ∀ P : D.BBas l,
        UIndTensorI (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D)
            (ident D.BBas (Nminus D) ⟨μ, (ltQ, lR)⟩) (fP P) *
          Matrix.kronecker (1 : Matrix (mackeyT (BSub D) (omegaSet D) (tOmega D))
            (mackeyT (BSub D) (omegaSet D) (tOmega D)) ℂ) (fourierMatrix (RH D))
            (fP P) (mackeyT_equiv D t₀, bEltEquivB D b₀) =
        UIndLam (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D) l
            ⟨⟨μ, hl⟩, ltQ⟩ (mackeyT_equiv D t₀, P) *
          D.qftB ⟨l, (P, R)⟩ b₀ := by
      intro P
      refine congrArg₂ (· * ·) ?_ ?_
      · dsimp only [fP, ident, l, R, UIndTensorI, Matrix.of_apply]
        rw [dif_pos rfl]
        simp only [cast_eq, ↓reduceIte, mul_one]
      · dsimp only [fP, Matrix.kronecker]
        rw [Matrix.kronecker_apply, Matrix.one_apply_eq, one_mul, qftB_entry_eq]
    simp_rw [hP_term]
    -- Apply `(theorem_5_4_inst D l).1`
    have h54_1 : ∀ P : D.BBas l,
        UIndLam (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D) l
            ⟨⟨μ, hl⟩, ltQ⟩ (mackeyT_equiv D t₀, P) =
          ∑ o_nop : NOut (omegaSet D) D.BBas (NmW D) (Ntw D) l,
            Aop (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D)
              (Ntw D) (Utw D) l ⟨⟨μ, hl⟩, ltQ⟩ o_nop *
            Nop (BSub D) (omegaSet D) (tOmega D) D.BBas (RH D) (BW D) (NmW D) (adaptW D)
              (Ntw D) (Utw D) l o_nop (mackeyT_equiv D t₀, P) := by
      intro P
      have heq := congrFun (congrFun (theorem_5_4_inst D l).1 ⟨⟨μ, hl⟩, ltQ⟩) (mackeyT_equiv D t₀, P)
      simpa [Matrix.mul_apply] using heq.symm
    simp_rw [h54_1, Finset.sum_mul]
    rw [Finset.sum_comm]
    -- Collapse `o_nop : NOut ... l` to `KSet ... l lt`
    let fK : KSet (omegaSet D) (NmW D) (Ntw D) l lt → NOut (omegaSet D) D.BBas (NmW D) (Ntw D) l :=
      fun k => ⟨k.1, ⟨k.2.1, k.2.2.1⟩, ⟨lt, k.2.2.2⟩, Q⟩
    have hfK_inj : Function.Injective fK := by
      rintro ⟨ω₁, ⟨κ₁, hn1, hm1⟩⟩ ⟨ω₂, ⟨κ₂, hn2, hm2⟩⟩ h
      have hω : ω₁ = ω₂ := congrArg Sigma.fst h
      subst hω
      have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have hκ : κ₁ = κ₂ := congrArg (fun x => x.1.1) h2
      subst hκ; rfl
    rw [sum_eq_sum_of_inj_vanish fK hfK_inj]
    · rw [← Fintype.sum_equiv (validInEquivKSet D l lt) _ _ (fun x => rfl)]
      apply Finset.sum_congr rfl; intro x _
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      have hA : Aop (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D)
          (Ntw D) (Utw D) l ⟨⟨μ, hl⟩, ltQ⟩ (fK (validInEquivKSet D l lt x)) =
          A70 D l lt x.1.1 x.1.2 μ := by
        simp only [fK, Aop, Matrix.of_apply, lt, Q, ↓reduceDIte, cast_eq, ↓reduceIte]
        exact (A70_eq_Ablock D l lt ⟨μ, hl, hlt⟩ x).symm
      have hNop : (∑ P : D.BBas l,
            Nop (BSub D) (omegaSet D) (tOmega D) D.BBas (RH D) (BW D) (NmW D) (adaptW D)
              (Ntw D) (Utw D) l (fK (validInEquivKSet D l lt x)) (mackeyT_equiv D t₀, P) *
            D.qftB ⟨l, (P, R)⟩ b₀) =
          ∑ P : D.BBas l,
            mackeyNopMat D ⟨⟨(l, x.1.1, x.1.2, lt), x.2⟩, (Q, R)⟩ (t₀, ⟨l, (P, R)⟩) *
            D.qftB ⟨l, (P, R)⟩ b₀ :=
        Finset.sum_congr rfl fun P _ =>
          congrArg (· * D.qftB ⟨l, (P, R)⟩ b₀) (nop_entry_eq D l lt Q R P t₀ x)
      exact congrArg₂ (· * ·) hA hNop
    · intro o_nop ho_nop
      suffices hA0 : Aop (BSub D) (omegaSet D) D.BBas (Nminus D) (RG D) (BW D) (NmW D) (adaptW D)
          (Ntw D) (Utw D) l ⟨⟨μ, hl⟩, ltQ⟩ o_nop = 0 by
        apply Finset.sum_eq_zero; intro P _; simp [hA0]
      by_contra hne
      rcases o_nop with ⟨ω, ⟨κ, hntw⟩, ⟨lt', hnmw⟩, Q'⟩
      simp only [Aop, Matrix.of_apply] at hne
      split_ifs at hne with hlt' hQ'
      · subst hlt'
        dsimp only [cast_eq] at hQ'
        subst hQ'
        exact ho_nop ⟨ω, ⟨κ, hntw, hnmw⟩⟩ rfl
      · exact hne rfl
      · exact hne rfl
  · rintro ⟨t', ⟨ν', ⟨P', R'⟩⟩⟩ hinp
    by_cases ht : t' = mackeyT_equiv D t₀
    · subst ht
      by_cases hl' : ν' = l
      · subst hl'
        have hR' : R' ≠ R := fun h => hinp P' (by subst h; rfl)
        have hzero : UIndTensorI (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D)
            (ident D.BBas (Nminus D) ⟨μ, (ltQ, lR)⟩) (mackeyT_equiv D t₀, ⟨l, (P', R')⟩) = 0 := by
          dsimp only [UIndTensorI, Matrix.of_apply, ident, l]
          rw [dif_pos rfl, if_neg, mul_zero]
          intro h; apply hR'; simpa [R, lR] using h
        rw [hzero, zero_mul]
      · have hzero : UIndTensorI (mackeyT (BSub D) (omegaSet D) (tOmega D)) D.BBas (Nminus D) (RG D)
            (ident D.BBas (Nminus D) ⟨μ, (ltQ, lR)⟩) (mackeyT_equiv D t₀, ⟨ν', (P', R')⟩) = 0 := by
          dsimp only [UIndTensorI, Matrix.of_apply, ident, l, lR] at hl' ⊢
          rw [dif_neg hl']
        rw [hzero, zero_mul]
    · have hzero : Matrix.kronecker (1 : Matrix (mackeyT (BSub D) (omegaSet D) (tOmega D))
          (mackeyT (BSub D) (omegaSet D) (tOmega D)) ℂ) (fourierMatrix (RH D))
          (t', ⟨ν', (P', R')⟩) (mackeyT_equiv D t₀, bEltEquivB D b₀) = 0 := by
        dsimp only [Matrix.kronecker]
        rw [Matrix.kronecker_apply, Matrix.one_apply_ne ht, zero_mul]
      rw [hzero, mul_zero]

end GL2QFT_MackeyFactorization_Aux

end

open Classical
open GL2QFT GL2QFT.Circuits GL2QFT.Supplement GL2QFT.Supplement.TotalA GL2QFT.Supplement.AGammaGates
open QAlgorithms QAlgorithms.Complexity

theorem solution (D : FieldData) :
    (D.qftGL2 = mackeyReindexMat D *
      Matrix.submatrix (frameMat (A := D.Lab × D.Lab) (totalA D)) (mackeyOutEmb D) (mackeyMidEmb D) *
      mackeyNopMat D * frameMat (A := CosetT D) D.qftB * mackeyEncMat D) ∧
    ((mackeyEncMat D).conjTranspose * mackeyEncMat D = 1) ∧
    (D.qftB.conjTranspose * D.qftB = 1) ∧
    ((mackeyNopMat D).conjTranspose * mackeyNopMat D = 1) ∧
    ((totalA D).conjTranspose * totalA D = 1) ∧
    (∀ m : MackeyMid D, ∀ y : (D.Lab × D.Lab) × OutReg D,
      (∀ m' : MackeyOut D, mackeyOutEmb D m' ≠ y) →
      frameMat (A := D.Lab × D.Lab) (totalA D) y (mackeyMidEmb D m) = 0) ∧
    Function.Injective (mackeyMidEmb D) ∧
    Function.Injective (mackeyOutEmb D) :=
  ⟨GL2QFT_MackeyFactorization_Aux.qftGL2_factorization D,
   GL2QFT_MackeyFactorization_Aux.mackeyEncMat_iso D,
   GL2QFT_MackeyFactorization_Aux.qftB_iso D,
   GL2QFT_MackeyFactorization_Aux.mackeyNopMat_iso D,
   GL2QFT_MackeyFactorization_Aux.totalA_iso D,
   GL2QFT_MackeyFactorization_Aux.frameMat_totalA_off_out D,
   GL2QFT_MackeyFactorization_Aux.mackeyMidEmb_injective D,
   GL2QFT_MackeyFactorization_Aux.mackeyOutEmb_injective D⟩
