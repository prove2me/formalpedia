-- Prove2me | solution 1 for GL2QFT.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:42:55.971232+00:00
-- url     : https://prove2.me/submissions/8e891a4f-f37d-4c4c-a1f6-797c8d3f0361

import Definitions.Def_GL2QFT_Irreps

open Classical

noncomputable section

namespace GL2QFT_Lemma65_Aux

open GL2QFT FieldData
open scoped ComplexConjugate Matrix

section FieldAndChars

variable (D : FieldData)

lemma card_Fq : Fintype.card D.Fq = D.q := by
  have hdim : Module.finrank (ZMod D.p) D.Fq = D.r := by
    rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]
  have hc := Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq)
  rw [hdim, ZMod.card] at hc
  exact hc

lemma card_Fq2 : Fintype.card D.Fq2 = D.q ^ 2 := by
  have hdim : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  have hc := Module.card_eq_pow_finrank (K := D.Fq) (V := D.Fq2)
  rw [hdim, card_Fq] at hc
  exact hc

lemma card_Fq_units : Fintype.card D.Fqˣ = D.q - 1 := by
  rw [Fintype.card_units, card_Fq]

lemma algebraMap_gen : algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  unfold gen
  have hnorm := @FiniteField.algebraMap_norm_eq_pow D.Fq D.Fq2 _ _ _ _ D.h
  rw [hnorm, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, card_Fq2, card_Fq]
  have hq : 1 < D.q := D.one_lt_q
  have hdiv : (D.q ^ 2 - 1) / (D.q - 1) = D.q + 1 := by
    have hsq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
      zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]
      ring
    rw [hsq, Nat.mul_div_cancel _ (by omega)]
  rw [hdiv]

lemma orderOf_gen : orderOf D.gen = D.q - 1 := by
  let f : D.Fq →* D.Fq2 := (algebraMap D.Fq D.Fq2).toMonoidHom
  have hf : Function.Injective f := (algebraMap D.Fq D.Fq2).injective
  rw [← orderOf_injective f hf D.gen]
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = D.q - 1
  rw [algebraMap_gen, orderOf_pow' D.h (by omega), D.h_order]
  change (D.q ^ 2 - 1) / ((D.q ^ 2 - 1).gcd (D.q + 1)) = D.q - 1
  have hq : 1 < D.q := D.one_lt_q
  have hsq : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]
    ring
  rw [hsq, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

lemma gen_ne_zero : D.gen ≠ 0 := by
  intro h
  have ho := orderOf_gen D
  rw [h, orderOf_zero] at ho
  have := D.one_lt_q
  omega

def uGen : D.Fqˣ := Units.mk0 D.gen (gen_ne_zero D)

lemma orderOf_uGen : orderOf (uGen D) = D.q - 1 := by
  rw [← orderOf_injective (Units.coeHom D.Fq) Units.val_injective (uGen D)]
  exact orderOf_gen D

lemma exists_pow_gen {x : D.Fq} (hx : x ≠ 0) : ∃ n : ℕ, D.gen ^ n = x := by
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

lemma gen_pow_dlog {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  unfold dlog
  rw [dif_pos (exists_pow_gen D hx)]
  exact Nat.find_spec (exists_pow_gen D hx)

lemma dlog_one : D.dlog 1 = 0 := by
  unfold dlog
  have h : ∃ n : ℕ, D.gen ^ n = 1 := ⟨0, pow_zero _⟩
  rw [dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h (pow_zero _))

lemma dlog_gen (hq : 2 < D.q) : D.dlog D.gen = 1 := by
  unfold dlog
  have h : ∃ n : ℕ, D.gen ^ n = D.gen := ⟨1, pow_one _⟩
  rw [dif_pos h]
  apply le_antisymm
  · exact Nat.find_min' h (pow_one _)
  · by_contra! hlt
    have h0 : Nat.find h = 0 := by omega
    have hs := Nat.find_spec h
    rw [h0, pow_zero] at hs
    have ho := orderOf_gen D
    rw [← hs, orderOf_one] at ho
    omega

lemma dlog_mul {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.dlog (x * y) ≡ D.dlog x + D.dlog y [MOD (D.q - 1)] := by
  have h1 : (uGen D) ^ D.dlog (x * y) = (uGen D) ^ (D.dlog x + D.dlog y) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, pow_add]
    dsimp [uGen]
    rw [gen_pow_dlog D (mul_ne_zero hx hy), gen_pow_dlog D hx, gen_pow_dlog D hy]
  rw [pow_eq_pow_iff_modEq, orderOf_uGen] at h1
  exact h1

lemma exp_mod (m : ℕ) (hm : 0 < m) (a b : ℕ) (h : a ≡ b [MOD m]) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (m : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (m : ℂ)) := by
  have hm_ne : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have aux : ∀ n : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (m : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * ((n % m : ℕ) : ℂ) / (m : ℂ)) := by
    intro n
    have hdiv : (n : ℂ) / (m : ℂ) = (((n / m : ℕ) : ℤ) : ℂ) + ((n % m : ℕ) : ℂ) / (m : ℂ) := by
      have hnat : (n : ℂ) = ((n / m : ℕ) : ℂ) * (m : ℂ) + ((n % m : ℕ) : ℂ) := by
        exact_mod_cast (Nat.div_add_mod' n m).symm
      rw [hnat, Int.cast_natCast]
      field_simp [hm_ne]
    have harg : 2 * ↑Real.pi * Complex.I * (n : ℂ) / (m : ℂ) =
        (((n / m : ℕ) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) +
        2 * ↑Real.pi * Complex.I * ((n % m : ℕ) : ℂ) / (m : ℂ) := by
      calc 2 * ↑Real.pi * Complex.I * (n : ℂ) / (m : ℂ)
          = 2 * ↑Real.pi * Complex.I * ((n : ℂ) / (m : ℂ)) := by ring
        _ = 2 * ↑Real.pi * Complex.I *
              ((((n / m : ℕ) : ℤ) : ℂ) + ((n % m : ℕ) : ℂ) / (m : ℂ)) := by rw [hdiv]
        _ = _ := by ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  rw [aux a, aux b, show a % m = b % m from h]

@[simp]
lemma chi_zero (α : D.Lab) : D.chi α 0 = 0 := by
  simp [chi]

@[simp]
lemma chi_one (α : D.Lab) : D.chi α 1 = 1 := by
  simp [chi, dlog_one]

lemma chi_ne_zero (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) : D.chi α x ≠ 0 := by
  simp [chi, hx, Complex.exp_ne_zero]

lemma chi_mul (α : D.Lab) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.chi α (x * y) = D.chi α x * D.chi α y := by
  unfold chi
  rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, ← Complex.exp_add]
  have hm : 0 < D.q - 1 := by have := D.one_lt_q; omega
  have hmod : α.val * D.dlog (x * y) ≡ α.val * D.dlog x + α.val * D.dlog y [MOD (D.q - 1)] := by
    simpa [Nat.mul_add] using Nat.ModEq.mul_left α.val (dlog_mul D hx hy)
  rw [exp_mod (D.q - 1) hm _ _ hmod]
  congr 1
  push_cast
  ring

lemma chi_add_label (α β : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    D.chi (α + β) x = D.chi α x * D.chi β x := by
  unfold chi
  simp only [hx, ↓reduceIte, ← Complex.exp_add]
  have hm : 0 < D.q - 1 := by have := D.one_lt_q; omega
  have hmod : (α + β).val * D.dlog x ≡ α.val * D.dlog x + β.val * D.dlog x [MOD (D.q - 1)] := by
    have hval : (α + β).val ≡ α.val + β.val [MOD (D.q - 1)] := by
      rw [ZMod.val_add]
      exact Nat.mod_modEq _ _
    simpa [Nat.add_mul] using Nat.ModEq.mul_right (D.dlog x) hval
  rw [exp_mod (D.q - 1) hm _ _ hmod]
  congr 1
  push_cast
  ring

@[simp]
lemma chi_zero_label {x : D.Fq} (hx : x ≠ 0) : D.chi 0 x = 1 := by
  simp [chi, hx, ZMod.val_zero]

lemma chi_neg_label (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    D.chi (-α) x = (D.chi α x)⁻¹ := by
  have h : D.chi α x * D.chi (-α) x = 1 := by
    rw [← chi_add_label D α (-α) hx, add_neg_cancel, chi_zero_label D hx]
  exact eq_inv_of_mul_eq_one_right h

lemma star_chi (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    star (D.chi α x) = D.chi (-α) x := by
  rw [chi_neg_label D α hx]
  unfold chi
  rw [if_neg hx]
  change (starRingEnd ℂ) (Complex.exp _) = (Complex.exp _)⁻¹
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

lemma chi_inv (α : D.Lab) {x : D.Fq} (hx : x ≠ 0) :
    D.chi α x⁻¹ = D.chi (-α) x := by
  have h : D.chi α x * D.chi α x⁻¹ = 1 := by
    rw [← chi_mul D α hx (inv_ne_zero hx), mul_inv_cancel₀ hx, chi_one]
  rw [chi_neg_label D α hx]
  exact eq_inv_of_mul_eq_one_right h

lemma chi_div (α : D.Lab) {x y : D.Fq} (hx : x ≠ 0) (hy : y ≠ 0) :
    D.chi α (x / y) = D.chi α x * D.chi (-α) y := by
  rw [div_eq_mul_inv, chi_mul D α hx (inv_ne_zero hy), chi_inv D α hy]

lemma chi_neg_one_sq (α : D.Lab) : D.chi α (-1) * D.chi α (-1) = 1 := by
  rw [← chi_mul D α (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)]
  simp

lemma chi_gen_ne_one {α : D.Lab} (hα : α ≠ 0) : D.chi α D.gen ≠ 1 := by
  have hq : 2 < D.q := by
    by_contra! hle
    have hq1 : D.q - 1 = 1 := by have := D.one_lt_q; omega
    have hsub : Subsingleton D.Lab := by
      change Subsingleton (ZMod (D.q - 1))
      rw [hq1]
      infer_instance
    exact hα (@Subsingleton.elim _ hsub α 0)
  unfold chi
  rw [if_neg (gen_ne_zero D), dlog_gen D hq, mul_one]
  intro heq
  rw [Complex.exp_eq_one_iff] at heq
  obtain ⟨n, hn⟩ := heq
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hm_ne : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiv : ((α.val : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hpi
    calc 2 * Real.pi * Complex.I * (((α.val : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ))
        = 2 * Real.pi * Complex.I * (α.val : ℂ) / ((D.q - 1 : ℕ) : ℂ) := by ring
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      _ = 2 * Real.pi * Complex.I * (n : ℂ) := by ring
  have hmul : ((α.val : ℕ) : ℂ) = (n : ℂ) * ((D.q - 1 : ℕ) : ℂ) := by
    rw [← hdiv]; field_simp [hm_ne]
  have hre := congrArg Complex.re hmul
  simp only [Complex.mul_re, Complex.natCast_re, Complex.intCast_re,
    Complex.natCast_im, Complex.intCast_im, mul_zero, sub_zero] at hre
  have hint : (α.val : ℤ) = n * ((D.q - 1 : ℕ) : ℤ) := by exact_mod_cast hre
  have hpos : 0 < α.val := Nat.pos_of_ne_zero (fun hz => hα (by
    rw [← ZMod.natCast_zmod_val α, hz]; simp))
  have hlt : α.val < D.q - 1 := ZMod.val_lt α
  have hn_pos : 0 < n := by nlinarith
  nlinarith

lemma sum_chi_units_eq_zero {α : D.Lab} (hα : α ≠ 0) :
    ∑ x : D.Fqˣ, D.chi α (x : D.Fq) = 0 := by
  let u := uGen D
  have hmul : D.chi α (u : D.Fq) * ∑ x : D.Fqˣ, D.chi α (x : D.Fq) =
      ∑ x : D.Fqˣ, D.chi α (x : D.Fq) := by
    rw [Finset.mul_sum]
    conv_rhs =>
      rw [← Equiv.sum_comp (Equiv.mulLeft u)]
    refine Finset.sum_congr rfl fun x _ => ?_
    change D.chi α (u : D.Fq) * D.chi α (x : D.Fq) = D.chi α ((u * x : D.Fqˣ) : D.Fq)
    rw [Units.val_mul, chi_mul D α u.ne_zero x.ne_zero]
  have hne : D.chi α (u : D.Fq) - 1 ≠ 0 := sub_ne_zero.mpr (chi_gen_ne_one D hα)
  have h0 : (D.chi α (u : D.Fq) - 1) * ∑ x : D.Fqˣ, D.chi α (x : D.Fq) = 0 := by
    linear_combination hmul
  exact (mul_eq_zero.mp h0).resolve_left hne

lemma sum_chi_eq_zero {α : D.Lab} (hα : α ≠ 0) :
    ∑ x : D.Fq, D.chi α x = 0 := by
  have hmul : D.chi α D.gen * ∑ x : D.Fq, D.chi α x = ∑ x : D.Fq, D.chi α x := by
    rw [Finset.mul_sum]
    conv_rhs =>
      rw [← Equiv.sum_comp (Equiv.mulLeft₀ D.gen (gen_ne_zero D))]
    refine Finset.sum_congr rfl fun x _ => ?_
    change D.chi α D.gen * D.chi α x = D.chi α (D.gen * x)
    by_cases hx : x = 0
    · simp [hx]
    · rw [chi_mul D α (gen_ne_zero D) hx]
  have hne : D.chi α D.gen - 1 ≠ 0 := sub_ne_zero.mpr (chi_gen_ne_one D hα)
  have h0 : (D.chi α D.gen - 1) * ∑ x : D.Fq, D.chi α x = 0 := by
    linear_combination hmul
  exact (mul_eq_zero.mp h0).resolve_left hne

lemma sum_chi_units_orthog (α β : D.Lab) :
    ∑ x : D.Fqˣ, star (D.chi α (x : D.Fq)) * D.chi β (x : D.Fq) =
      if α = β then ((D.q - 1 : ℕ) : ℂ) else 0 := by
  have hrew : ∀ x : D.Fqˣ, star (D.chi α (x : D.Fq)) * D.chi β (x : D.Fq) =
      D.chi (β - α) (x : D.Fq) := fun x => by
    rw [star_chi D α x.ne_zero, ← chi_add_label D (-α) β x.ne_zero, neg_add_eq_sub]
  simp_rw [hrew]
  by_cases h : α = β
  · subst h
    simp only [sub_self, ↓reduceIte]
    have h1 : ∀ x : D.Fqˣ, D.chi 0 (x : D.Fq) = 1 := fun x => chi_zero_label D x.ne_zero
    simp_rw [h1, Finset.sum_const, Finset.card_univ, card_Fq_units, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    exact sum_chi_units_eq_zero D (sub_ne_zero.mpr (Ne.symm h))

lemma chi_pair_eq_imp {α β γ δ : D.Lab}
    (h : ∀ x : D.Fqˣ, D.chi α (x : D.Fq) + D.chi β (x : D.Fq) =
      D.chi γ (x : D.Fq) + D.chi δ (x : D.Fq)) :
    (α = γ ∧ β = δ) ∨ (α = δ ∧ β = γ) := by
  have hsum :
      ∑ x : D.Fqˣ, star (D.chi α (x : D.Fq)) * (D.chi α (x : D.Fq) + D.chi β (x : D.Fq)) =
      ∑ x : D.Fqˣ, star (D.chi α (x : D.Fq)) * (D.chi γ (x : D.Fq) + D.chi δ (x : D.Fq)) :=
    Finset.sum_congr rfl fun x _ => by rw [h x]
  simp_rw [mul_add, Finset.sum_add_distrib, sum_chi_units_orthog] at hsum
  simp only [↓reduceIte] at hsum
  have hq1 : ((D.q - 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by have := D.one_lt_q; omega)
  have hor : α = γ ∨ α = δ := by
    by_contra! hne
    rw [if_neg hne.1, if_neg hne.2, add_zero] at hsum
    by_cases hab : α = β
    · rw [if_pos hab] at hsum
      have : (2 : ℂ) * ((D.q - 1 : ℕ) : ℂ) = 0 := by linear_combination hsum
      exact (mul_ne_zero (by norm_num) hq1) this
    · rw [if_neg hab, add_zero] at hsum
      exact hq1 hsum
  have cancel_one : ∀ u v : D.Lab,
      (∀ x : D.Fqˣ, D.chi u (x : D.Fq) = D.chi v (x : D.Fq)) → u = v := by
    intro u v huv
    have hs : ∑ x : D.Fqˣ, star (D.chi u (x : D.Fq)) * D.chi u (x : D.Fq) =
        ∑ x : D.Fqˣ, star (D.chi u (x : D.Fq)) * D.chi v (x : D.Fq) :=
      Finset.sum_congr rfl fun x _ => by rw [huv x]
    simp_rw [sum_chi_units_orthog] at hs
    simp only [↓reduceIte] at hs
    by_contra huv_ne
    rw [if_neg huv_ne] at hs
    exact hq1 hs
  rcases hor with rfl | rfl
  · left
    refine ⟨rfl, cancel_one β δ fun x => ?_⟩
    have hx := h x
    linear_combination hx
  · right
    refine ⟨rfl, cancel_one β γ fun x => ?_⟩
    have hx := h x
    linear_combination hx

lemma exists_chi_ne {α β : D.Lab} (h : α ≠ β) :
    ∃ a : D.Fqˣ, D.chi α (a : D.Fq) ≠ D.chi β (a : D.Fq) := by
  refine ⟨uGen D, ?_⟩
  intro heq
  dsimp [uGen] at heq
  have h1 : D.chi (α - β) D.gen = 1 := by
    rw [sub_eq_add_neg, chi_add_label D α (-β) (gen_ne_zero D),
      chi_neg_label D β (gen_ne_zero D), heq, mul_inv_cancel₀ (chi_ne_zero D β (gen_ne_zero D))]
  exact chi_gen_ne_one D (sub_ne_zero.mpr h) h1

/-! Additive character `psi` -/

lemma exp_mod_p (a b : ℕ) (h : a ≡ b [MOD D.p]) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (D.p : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (D.p : ℂ)) :=
  exp_mod D.p D.hp.pos a b h

@[simp]
lemma psi_zero : D.psi 0 = 1 := by
  simp [psi]

lemma psi_add (x y : D.Fq) : D.psi (x + y) = D.psi x * D.psi y := by
  unfold psi
  rw [map_add, ← Complex.exp_add]
  have : NeZero D.p := ⟨D.hp.ne_zero⟩
  have hmod : (Algebra.trace (ZMod D.p) D.Fq x + Algebra.trace (ZMod D.p) D.Fq y).val ≡
      (Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val [MOD D.p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  rw [exp_mod_p D _ _ hmod]
  congr 1
  push_cast
  ring

lemma star_psi (x : D.Fq) : star (D.psi x) = D.psi (-x) := by
  have hmul : D.psi x * D.psi (-x) = 1 := by
    rw [← psi_add, add_neg_cancel, psi_zero]
  have hinv : D.psi (-x) = (D.psi x)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  rw [hinv]
  unfold psi
  change (starRingEnd ℂ) (Complex.exp _) = (Complex.exp _)⁻¹
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
  ring

lemma psi_sub (x y : D.Fq) : D.psi (x - y) = D.psi x * star (D.psi y) := by
  rw [sub_eq_add_neg, psi_add, star_psi]

lemma exists_trace_ne_zero : ∃ x : D.Fq, Algebra.trace (ZMod D.p) D.Fq x ≠ 0 := by
  have hnd := (traceForm_nondegenerate (ZMod D.p) D.Fq).1 1
  by_contra! h
  have : (1 : D.Fq) = 0 := hnd fun y => by
    rw [Algebra.traceForm_apply, one_mul]
    exact h y
  exact one_ne_zero this

lemma exists_psi_ne_one : ∃ x₀ : D.Fq, D.psi x₀ ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ := exists_trace_ne_zero D
  refine ⟨x₀, ?_⟩
  unfold psi
  intro heq
  rw [Complex.exp_eq_one_iff] at heq
  obtain ⟨n, hn⟩ := heq
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hp_ne : (D.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.hp.ne_zero
  let t := Algebra.trace (ZMod D.p) D.Fq x₀
  have hdiv : ((t.val : ℕ) : ℂ) / (D.p : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hpi
    calc 2 * Real.pi * Complex.I * ((t.val : ℂ) / (D.p : ℂ))
        = 2 * Real.pi * Complex.I * (t.val : ℂ) / (D.p : ℂ) := by ring
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      _ = 2 * Real.pi * Complex.I * (n : ℂ) := by ring
  have hmul : (t.val : ℂ) = (n : ℂ) * (D.p : ℂ) := by
    rw [← hdiv]; field_simp [hp_ne]
  have hre := congrArg Complex.re hmul
  simp only [Complex.mul_re, Complex.natCast_re, Complex.intCast_re,
    Complex.natCast_im, Complex.intCast_im, mul_zero, sub_zero] at hre
  have hint : (t.val : ℤ) = n * (D.p : ℤ) := by exact_mod_cast hre
  have : NeZero D.p := ⟨D.hp.ne_zero⟩
  have hpos : 0 < t.val := Nat.pos_of_ne_zero (fun hz => hx₀ (by
    change t = 0
    rw [← ZMod.natCast_zmod_val t, hz]; simp))
  have hlt : t.val < D.p := ZMod.val_lt t
  have hn_pos : 0 < n := by nlinarith
  nlinarith

lemma sum_psi_mul_eq (z : D.Fq) :
    ∑ t : D.Fq, D.psi (t * z) = if z = 0 then (D.q : ℂ) else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [mul_zero, psi_zero, ↓reduceIte, Finset.sum_const, Finset.card_univ,
      card_Fq, nsmul_eq_mul, mul_one]
  · rw [if_neg hz]
    obtain ⟨x₀, hx₀⟩ := exists_psi_ne_one D
    let t₀ := x₀ / z
    have hmul : D.psi (t₀ * z) * ∑ t : D.Fq, D.psi (t * z) = ∑ t : D.Fq, D.psi (t * z) := by
      rw [Finset.mul_sum]
      conv_rhs =>
        rw [← Equiv.sum_comp (Equiv.addRight t₀)]
      refine Finset.sum_congr rfl fun t _ => ?_
      change D.psi (t₀ * z) * D.psi (t * z) = D.psi ((t + t₀) * z)
      rw [add_mul, psi_add, mul_comm (D.psi (t * z))]
    have ht₀z : t₀ * z = x₀ := div_mul_cancel₀ x₀ hz
    rw [ht₀z] at hmul
    have hne : D.psi x₀ - 1 ≠ 0 := sub_ne_zero.mpr hx₀
    have h0 : (D.psi x₀ - 1) * ∑ t : D.Fq, D.psi (t * z) = 0 := by linear_combination hmul
    exact (mul_eq_zero.mp h0).resolve_left hne

lemma sum_conj_psi_mul_eq (z : D.Fq) :
    ∑ t : D.Fq, conj (D.psi (t * z)) = if z = 0 then (D.q : ℂ) else 0 := by
  have h : ∑ t : D.Fq, conj (D.psi (t * z)) = conj (∑ t : D.Fq, D.psi (t * z)) := by
    rw [map_sum]
  rw [h, sum_psi_mul_eq]
  split_ifs <;> simp

end FieldAndChars

/-! ### Section 2: `psModel` as a Monomial Unitary Representation -/

section PSModelRep

variable (D : FieldData)

def tRep (x : Option D.Fq) : Matrix (Fin 2) (Fin 2) D.Fq :=
  match x with
  | none => !![1, 0; 0, 1]
  | some a => !![a, 1; 1, 0]

def tRepInv (x : Option D.Fq) : Matrix (Fin 2) (Fin 2) D.Fq :=
  match x with
  | none => !![1, 0; 0, 1]
  | some a => !![0, 1; 1, -a]

def mobius (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) : Option D.Fq :=
  let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
  match x with
  | none => if c ≠ 0 then some (a / c) else none
  | some u => if c * u + d ≠ 0 then some ((a * u + b) / (c * u + d)) else none

def bMat (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) : Matrix (Fin 2) (Fin 2) D.Fq :=
  let a := M 0 0; let b := M 0 1; let c := M 1 0; let d := M 1 1
  let det := M.det
  match x with
  | none => if c ≠ 0 then !![c, d; 0, -det / c] else !![a, b; 0, d]
  | some u => if c * u + d ≠ 0 then !![c * u + d, c; 0, det / (c * u + d)] else !![a * u + b, a; 0, c]

def cocycle (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) : ℂ :=
  D.chi α ((bMat D M x) 0 0) * D.chi β ((bMat D M x) 1 1)

lemma psModel_eq_ite (α β : D.Lab) (M : Matrix (Fin 2) (Fin 2) D.Fq) (y x : Option D.Fq) :
    D.psModel α β M y x = if y = mobius D M x then cocycle D α β M x else 0 := by
  unfold psModel mobius cocycle bMat
  rw [Matrix.det_fin_two]
  cases x with
  | none =>
    dsimp
    split_ifs <;> simp_all
  | some u =>
    dsimp
    split_ifs <;> simp_all

lemma bMat_upper (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) :
    (bMat D M x) 1 0 = 0 := by
  cases x <;> dsimp [bMat] <;> split_ifs <;> simp

lemma mul_tRep (M : Matrix (Fin 2) (Fin 2) D.Fq) (x : Option D.Fq) :
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

lemma tRepInv_mul_tRep (x : Option D.Fq) : tRepInv D x * tRep D x = 1 := by
  cases x <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two]

lemma tRep_det_ne_zero (x : Option D.Fq) : (tRep D x).det ≠ 0 := by
  cases x <;> simp [tRep, Matrix.det_fin_two]

lemma bMat_diag_ne_zero {M : Matrix (Fin 2) (Fin 2) D.Fq} (hM : M.det ≠ 0) (x : Option D.Fq) :
    (bMat D M x) 0 0 ≠ 0 ∧ (bMat D M x) 1 1 ≠ 0 := by
  have hdet_lhs : (M * tRep D x).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero hM (tRep_det_ne_zero D x)
  rw [mul_tRep, Matrix.det_mul] at hdet_lhs
  have hdet_b : (bMat D M x).det ≠ 0 := right_ne_zero_of_mul hdet_lhs
  rw [Matrix.det_fin_two, bMat_upper, mul_zero, sub_zero] at hdet_b
  exact mul_ne_zero_iff.mp hdet_b

lemma tRep_mul_unique {y y' : Option D.Fq} {B₁ B₂ : Matrix (Fin 2) (Fin 2) D.Fq}
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
      | some b =>
        simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two] at hx10
    | some a =>
      cases y' with
      | none =>
        simp [tRepInv, tRep, Matrix.mul_apply, Fin.sum_univ_two] at hx10
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

lemma mobius_bMat_mul {M₁ M₂ : Matrix (Fin 2) (Fin 2) D.Fq} (hM₁ : M₁.det ≠ 0) (hM₂ : M₂.det ≠ 0)
    (x : Option D.Fq) :
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
    rw [Matrix.mul_apply, Fin.sum_univ_two, bMat_upper, bMat_upper]
    simp
  have hB2_00 : (bMat D M₁ (mobius D M₂ x) * bMat D M₂ x) 0 0 ≠ 0 := by
    rw [Matrix.mul_apply, Fin.sum_univ_two, bMat_upper, mul_zero, add_zero]
    exact mul_ne_zero (bMat_diag_ne_zero D hM₁ _).1 (bMat_diag_ne_zero D hM₂ _).1
  exact tRep_mul_unique D hb1 hb2 hB2_00 hmul

lemma cocycle_mul (α β : D.Lab) {M₁ M₂ : Matrix (Fin 2) (Fin 2) D.Fq}
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

lemma mobius_one (x : Option D.Fq) : mobius D 1 x = x := by
  cases x <;> simp [mobius]

lemma cocycle_one (α β : D.Lab) (x : Option D.Fq) : cocycle D α β 1 x = 1 := by
  cases x <;> simp [cocycle, bMat]

lemma gl_det_ne_zero (g : D.G) : (g : Matrix (Fin 2) (Fin 2) D.Fq).det ≠ 0 := by
  intro h
  have h1 : (g : Matrix (Fin 2) (Fin 2) D.Fq) * ((g⁻¹ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
    exact_mod_cast Units.mul_inv g
  have hd := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one, h, zero_mul] at hd
  exact zero_ne_one hd

lemma psModel_one (α β : D.Lab) :
    D.psModel α β (1 : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
  ext y x
  rw [psModel_eq_ite, mobius_one, cocycle_one]
  simp [Matrix.one_apply]

lemma psModel_mul (α β : D.Lab) (g₁ g₂ : D.G) :
    D.psModel α β ((g₁ * g₂ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) =
    D.psModel α β (g₁ : Matrix (Fin 2) (Fin 2) D.Fq) *
    D.psModel α β (g₂ : Matrix (Fin 2) (Fin 2) D.Fq) := by
  ext y x
  have h1 : (g₁ : Matrix (Fin 2) (Fin 2) D.Fq).det ≠ 0 := gl_det_ne_zero D g₁
  have h2 : (g₂ : Matrix (Fin 2) (Fin 2) D.Fq).det ≠ 0 := gl_det_ne_zero D g₂
  have hm := mobius_bMat_mul D h1 h2 x
  have hc := cocycle_mul D α β h1 h2 x
  change D.psModel α β ((g₁ : Matrix _ _ _) * (g₂ : Matrix _ _ _)) y x = _
  rw [Matrix.mul_apply, psModel_eq_ite, hm.1, hc]
  simp_rw [psModel_eq_ite]
  rw [Finset.sum_eq_single (mobius D (g₂ : Matrix _ _ _) x)]
  · simp only [↓reduceIte]
    split_ifs <;> simp [mul_comm]
  · intro z _ hzne
    simp [hzne]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

lemma mobius_inv_left (g : D.G) (x : Option D.Fq) :
    mobius D (g⁻¹ : D.G) (mobius D g x) = x := by
  have hm := (mobius_bMat_mul D (gl_det_ne_zero D g⁻¹) (gl_det_ne_zero D g) x).1
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, mobius_one] at hm
  exact hm.symm

lemma mobius_inv_right (g : D.G) (y : Option D.Fq) :
    mobius D g (mobius D (g⁻¹ : D.G) y) = y := by
  have hm := (mobius_bMat_mul D (gl_det_ne_zero D g) (gl_det_ne_zero D g⁻¹) y).1
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mobius_one] at hm
  exact hm.symm

lemma mobius_inj (g : D.G) : Function.Injective (mobius D (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  intro x₁ x₂ h
  have := congrArg (mobius D (g⁻¹ : D.G)) h
  rwa [mobius_inv_left, mobius_inv_left] at this

lemma psModel_unitary (α β : D.Lab) (g : D.G) :
    (D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))ᴴ *
      D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq) = 1 := by
  ext x₁ x₂
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Matrix.conjTranspose_apply, psModel_eq_ite]
  by_cases h : x₁ = x₂
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single (mobius D g x₁)]
    · simp only [↓reduceIte]
      have hd := bMat_diag_ne_zero D (gl_det_ne_zero D g) x₁
      unfold cocycle
      rw [star_mul, star_chi D α hd.1, star_chi D β hd.2]
      calc (D.chi (-β) _ * D.chi (-α) _) * (D.chi α _ * D.chi β _)
          = (D.chi (-α) _ * D.chi α _) * (D.chi (-β) _ * D.chi β _) := by ring
        _ = D.chi (-α + α) _ * D.chi (-β + β) _ := by
            rw [chi_add_label D (-α) α hd.1, chi_add_label D (-β) β hd.2]
        _ = 1 := by simp [neg_add_cancel, chi_zero_label D hd.1, chi_zero_label D hd.2]
    · intro y _ hyne
      simp [hyne]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy1 : y = mobius D g x₁
    · subst hy1
      have hy2 : mobius D g x₁ ≠ mobius D g x₂ := fun heq => h (mobius_inj D g heq)
      simp [hy2]
    · simp [hy1]

lemma psModel_mulVec (α β : D.Lab) (g : D.G) (u : Option D.Fq → ℂ) (y : Option D.Fq) :
    ((D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec u) y =
      cocycle D α β g (mobius D (g⁻¹ : D.G) y) * u (mobius D (g⁻¹ : D.G) y) := by
  rw [Matrix.mulVec, dotProduct]
  simp_rw [psModel_eq_ite]
  rw [Finset.sum_eq_single (mobius D (g⁻¹ : D.G) y)]
  · rw [mobius_inv_right, if_pos rfl]
  · intro x _ hxne
    have hne : y ≠ mobius D g x := by
      intro heq
      apply hxne
      calc x = mobius D (g⁻¹ : D.G) (mobius D g x) := (mobius_inv_left D g x).symm
        _ = mobius D (g⁻¹ : D.G) y := by rw [← heq]
    simp [hne]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

end PSModelRep

/-! ### Section 3: Part 2a & 2b (`detVec` invariance and orthogonal complement) -/

section DetVecProps

variable (D : FieldData)

lemma tRep_det_sq (x : Option D.Fq) : (tRep D x).det * (tRep D x).det = 1 := by
  cases x <;> simp [tRep, Matrix.det_fin_two]

lemma detVec_eq (α : D.Lab) (x : Option D.Fq) :
    D.detVec α x = isqrt (D.q + 1) * D.chi α (-(tRep D x).det) := by
  cases x <;> simp [detVec, tRep, Matrix.det_fin_two]

lemma detVec_eig (α : D.Lab) (g : D.G) :
    (D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (D.detVec α) =
      D.chi α ((g : Matrix (Fin 2) (Fin 2) D.Fq).det) • D.detVec α := by
  ext y
  have hx := psModel_mulVec D α α g (D.detVec α) y
  set x := mobius D (g⁻¹ : D.G) y
  have hy : mobius D g x = y := mobius_inv_right D g y
  rw [hx, Pi.smul_apply, smul_eq_mul, detVec_eq, detVec_eq]
  have hmul_det : (g : Matrix (Fin 2) (Fin 2) D.Fq).det * (tRep D x).det =
      (tRep D y).det * (bMat D g x).det := by
    have h := congrArg Matrix.det (mul_tRep D g x)
    rw [hy] at h
    simpa [Matrix.det_mul] using h
  have hb_det : (bMat D g x).det = (bMat D g x) 0 0 * (bMat D g x) 1 1 := by
    rw [Matrix.det_fin_two, bMat_upper, mul_zero, sub_zero]
  have hbd := bMat_diag_ne_zero D (gl_det_ne_zero D g) x
  have hcoc : cocycle D α α g x = D.chi α ((bMat D g x).det) := by
    unfold cocycle
    rw [hb_det, chi_mul D α hbd.1 hbd.2]
  have hdet_b_ne : (bMat D g x).det ≠ 0 := by
    rw [hb_det]; exact mul_ne_zero hbd.1 hbd.2
  have hneg_tx : -(tRep D x).det ≠ 0 := neg_ne_zero.mpr (tRep_det_ne_zero D x)
  have hneg_ty : -(tRep D y).det ≠ 0 := neg_ne_zero.mpr (tRep_det_ne_zero D y)
  have hprod_eq : (bMat D g x).det * (-(tRep D x).det) =
      (g : Matrix (Fin 2) (Fin 2) D.Fq).det * (-(tRep D y).det) := by
    have h1 : (tRep D y).det * ((bMat D g x).det * -(tRep D x).det) =
        (tRep D y).det * ((g : Matrix (Fin 2) (Fin 2) D.Fq).det * -(tRep D y).det) := by
      calc (tRep D y).det * ((bMat D g x).det * -(tRep D x).det)
          = -((tRep D y).det * (bMat D g x).det * (tRep D x).det) := by ring
        _ = -((g : Matrix (Fin 2) (Fin 2) D.Fq).det * ((tRep D x).det * (tRep D x).det)) := by
            rw [← hmul_det]; ring
        _ = -((g : Matrix (Fin 2) (Fin 2) D.Fq).det * 1) := by rw [tRep_det_sq]
        _ = -((g : Matrix (Fin 2) (Fin 2) D.Fq).det * ((tRep D y).det * (tRep D y).det)) := by
            rw [tRep_det_sq]
        _ = (tRep D y).det * ((g : Matrix (Fin 2) (Fin 2) D.Fq).det * -(tRep D y).det) := by ring
    exact mul_left_cancel₀ (tRep_det_ne_zero D y) h1
  rw [hcoc]
  calc D.chi α (bMat D g x).det * (isqrt (D.q + 1) * D.chi α (-(tRep D x).det))
      = isqrt (D.q + 1) * (D.chi α (bMat D g x).det * D.chi α (-(tRep D x).det)) := by ring
    _ = isqrt (D.q + 1) * D.chi α ((bMat D g x).det * -(tRep D x).det) := by
        rw [← chi_mul D α hdet_b_ne hneg_tx]
    _ = isqrt (D.q + 1) * D.chi α ((g : Matrix (Fin 2) (Fin 2) D.Fq).det * -(tRep D y).det) := by
        rw [hprod_eq]
    _ = isqrt (D.q + 1) * (D.chi α (g : Matrix (Fin 2) (Fin 2) D.Fq).det * D.chi α (-(tRep D y).det)) := by
        rw [chi_mul D α (gl_det_ne_zero D g) hneg_ty]
    _ = D.chi α (g : Matrix (Fin 2) (Fin 2) D.Fq).det * (isqrt (D.q + 1) * D.chi α (-(tRep D y).det)) := by
        ring

lemma detVec_orthog_inv (α : D.Lab) (g : D.G) (u : Option D.Fq → ℂ)
    (hu : dotProduct (star (D.detVec α)) u = 0) :
    dotProduct (star (D.detVec α))
      ((D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec u) = 0 := by
  set M := D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)
  have hunit : Mᴴ * M = 1 := psModel_unitary D α α g
  have hinner : dotProduct (star (M.mulVec (D.detVec α))) (M.mulVec u) =
      dotProduct (star (D.detVec α)) u := by
    calc dotProduct (star (M.mulVec (D.detVec α))) (M.mulVec u)
        = dotProduct (Matrix.vecMul (star (D.detVec α)) Mᴴ) (M.mulVec u) := by
          rw [Matrix.star_mulVec]
      _ = dotProduct (star (D.detVec α)) (Mᴴ *ᵥ (M.mulVec u)) := by
          rw [← Matrix.dotProduct_mulVec]
      _ = dotProduct (star (D.detVec α)) ((Mᴴ * M).mulVec u) := by
          rw [Matrix.mulVec_mulVec]
      _ = dotProduct (star (D.detVec α)) u := by
          rw [hunit, Matrix.one_mulVec]
  rw [detVec_eig, hu] at hinner
  have hc_ne : star (D.chi α (g : Matrix (Fin 2) (Fin 2) D.Fq).det) ≠ 0 :=
    star_ne_zero.mpr (chi_ne_zero D α (gl_det_ne_zero D g))
  rw [star_smul, smul_dotProduct, smul_eq_mul] at hinner
  exact (mul_eq_zero.mp hinner).resolve_left hc_ne

end DetVecProps

/-! ### Section 4: Bruhat Generators, Fourier Projections, and Irreducibility -/

section Irreducibility

variable (D : FieldData)

def uMat (b : D.Fq) : D.G where
  val := !![1, b; 0, 1]
  inv := !![1, -b; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def tMat (a d : D.Fqˣ) : D.G where
  val := !![(a : D.Fq), 0; 0, (d : D.Fq)]
  inv := !![((a⁻¹ : D.Fqˣ) : D.Fq), 0; 0, ((d⁻¹ : D.Fqˣ) : D.Fq)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def dMat (a : D.Fqˣ) : D.G := tMat D a 1

def wMat : D.G where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma uMat_inv (b : D.Fq) : (uMat D b)⁻¹ = uMat D (-b) := by
  ext i j; rfl

lemma dMat_inv (a : D.Fqˣ) : (dMat D a)⁻¹ = dMat D a⁻¹ := by
  ext i j; simp [dMat, tMat]

lemma wMat_inv : (wMat D)⁻¹ = wMat D := by
  ext i j; rfl

lemma mobius_uMat (b : D.Fq) (x : Option D.Fq) :
    mobius D (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq) x =
      match x with | none => none | some u => some (u + b) := by
  cases x <;> simp [mobius, uMat]

lemma cocycle_uMat (α β : D.Lab) (b : D.Fq) (x : Option D.Fq) :
    cocycle D α β (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq) x = 1 := by
  cases x <;> simp [cocycle, bMat, uMat, Matrix.det_fin_two]

lemma mobius_dMat (a : D.Fqˣ) (x : Option D.Fq) :
    mobius D (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq) x =
      match x with | none => none | some u => some ((a : D.Fq) * u) := by
  cases x <;> simp [mobius, dMat, tMat]

lemma cocycle_dMat (α β : D.Lab) (a : D.Fqˣ) (x : Option D.Fq) :
    cocycle D α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq) x =
      match x with | none => D.chi α (a : D.Fq) | some _ => D.chi β (a : D.Fq) := by
  cases x <;> simp [cocycle, bMat, dMat, tMat, Matrix.det_fin_two]

lemma mobius_wMat (x : Option D.Fq) :
    mobius D (wMat D : Matrix (Fin 2) (Fin 2) D.Fq) x =
      match x with
      | none => some 0
      | some u => if u = 0 then none else some u⁻¹ := by
  cases x with
  | none => simp [mobius, wMat]
  | some u =>
    by_cases hu : u = 0
    · simp [mobius, wMat, hu]
    · simp [mobius, wMat, hu]

lemma cocycle_wMat (α β : D.Lab) (x : Option D.Fq) :
    cocycle D α β (wMat D : Matrix (Fin 2) (Fin 2) D.Fq) x =
      match x with
      | none => 1
      | some u => if u = 0 then 1 else D.chi α u * D.chi β (-1 / u) := by
  cases x with
  | none => simp [cocycle, bMat, wMat, Matrix.det_fin_two]
  | some u =>
    by_cases hu : u = 0
    · simp [cocycle, bMat, wMat, hu]
    · simp [cocycle, bMat, wMat, Matrix.det_fin_two, hu]

def eNone : Option D.Fq → ℂ := Pi.single none 1
def eSome (x : D.Fq) : Option D.Fq → ℂ := Pi.single (some x) 1

def vT0 (t : D.Fq) : Option D.Fq → ℂ
  | none => 0
  | some x => conj (D.psi (t * x))

def coeff (f : Option D.Fq → ℂ) (t : D.Fq) : ℂ :=
  ((D.q : ℂ)⁻¹) * ∑ z : D.Fq, D.psi (t * z) * f (some z)

def projT (α β : D.Lab) (t : D.Fq) (f : Option D.Fq → ℂ) : Option D.Fq → ℂ :=
  ((D.q : ℂ)⁻¹) • ∑ b : D.Fq,
    conj (D.psi (t * b)) • (D.psModel α β (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec f

lemma psModel_uMat_mulVec (α β : D.Lab) (b : D.Fq) (f : Option D.Fq → ℂ) :
    (D.psModel α β (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec f =
      fun y => match y with | none => f none | some x => f (some (x - b)) := by
  ext y
  rw [psModel_mulVec, uMat_inv, mobius_uMat, cocycle_uMat]
  cases y <;> simp [sub_eq_add_neg]

lemma projT_mem (α β : D.Lab) (W : Submodule ℂ (Option D.Fq → ℂ))
    (hW : IsInvariantSubspace (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq)) W)
    (t : D.Fq) {f : Option D.Fq → ℂ} (hf : f ∈ W) :
    projT D α β t f ∈ W := by
  apply W.smul_mem
  apply W.sum_mem
  intro b _
  exact W.smul_mem _ (hW (uMat D b) f hf)

lemma projT_eq (α β : D.Lab) (t : D.Fq) (f : Option D.Fq → ℂ) :
    projT D α β t f =
      (if t = 0 then f none else 0) • eNone D + coeff D f t • vT0 D t := by
  ext y
  unfold projT coeff
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, smul_eq_mul, psModel_uMat_mulVec]
  have hq_ne : (D.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.one_lt_q; omega)
  cases y with
  | none =>
    simp only [eNone, vT0, Pi.single_eq_same, mul_one, mul_zero, add_zero]
    have hc : ∑ b : D.Fq, conj (D.psi (t * b)) = ∑ b : D.Fq, conj (D.psi (b * t)) :=
      Finset.sum_congr rfl fun b _ => by rw [mul_comm]
    rw [← Finset.sum_mul, hc, sum_conj_psi_mul_eq]
    split_ifs <;> simp [hq_ne]
  | some x =>
    simp only [eNone, vT0, Pi.single_apply, Option.some_ne_none, ↓reduceIte, mul_zero, zero_add]
    have hsum : ∑ b : D.Fq, conj (D.psi (t * b)) * f (some (x - b)) =
        ∑ z : D.Fq, conj (D.psi (t * (x - z))) * f (some z) := by
      rw [← Equiv.sum_comp (Equiv.subLeft x)]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp [Equiv.subLeft_apply]
    rw [hsum]
    have hterm : ∀ z : D.Fq, conj (D.psi (t * (x - z))) * f (some z) =
        (D.psi (t * z) * f (some z)) * conj (D.psi (t * x)) := fun z => by
      have h1 : t * (x - z) = t * x - t * z := by ring
      rw [h1, psi_sub, map_mul]
      change conj (D.psi (t * x)) * conj (conj (D.psi (t * z))) * f (some z) = _
      rw [Complex.conj_conj]
      ring
    simp_rw [hterm, ← Finset.sum_mul]
    ring

lemma sum_projT (α β : D.Lab) (f : Option D.Fq → ℂ) :
    ∑ t : D.Fq, projT D α β t f = f := by
  ext y
  rw [Finset.sum_apply]
  have hq_ne : (D.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.one_lt_q; omega)
  simp_rw [projT_eq]
  cases y with
  | none =>
    simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eNone, vT0]
    simp
  | some x =>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eNone,
      Pi.single_apply, Option.some_ne_none, ↓reduceIte, mul_zero, zero_add, vT0, coeff]
    have h1 : ∑ t : D.Fq, ((D.q : ℂ)⁻¹ * ∑ z : D.Fq, D.psi (t * z) * f (some z)) *
        conj (D.psi (t * x)) =
        (D.q : ℂ)⁻¹ * ∑ z : D.Fq, (∑ t : D.Fq, D.psi (t * (z - x))) * f (some z) := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      congr 1
      calc ∑ t : D.Fq, (∑ z : D.Fq, D.psi (t * z) * f (some z)) * conj (D.psi (t * x))
          = ∑ t : D.Fq, ∑ z : D.Fq, (D.psi (t * z) * f (some z)) * conj (D.psi (t * x)) := by
              simp_rw [Finset.sum_mul]
        _ = ∑ z : D.Fq, ∑ t : D.Fq, (D.psi (t * z) * f (some z)) * conj (D.psi (t * x)) :=
              Finset.sum_comm
        _ = ∑ z : D.Fq, (∑ t : D.Fq, D.psi (t * (z - x))) * f (some z) := by
              refine Finset.sum_congr rfl fun z _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun t _ => ?_
              have hs : t * (z - x) = t * z - t * x := by ring
              rw [hs, psi_sub]
              simp only [Complex.star_def]
              ring
    rw [h1]
    simp_rw [sum_psi_mul_eq]
    rw [Finset.sum_eq_single x]
    · simp [hq_ne]
    · intro z _ hzne
      simp [sub_eq_zero.not.mpr hzne]
    · intro hx
      exact absurd (Finset.mem_univ x) hx

lemma dMat_mulVec_eNone (α β : D.Lab) (a : D.Fqˣ) :
    (D.psModel α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (eNone D) =
      D.chi α (a : D.Fq) • eNone D := by
  ext y
  rw [psModel_mulVec, dMat_inv, mobius_dMat, cocycle_dMat, Pi.smul_apply, smul_eq_mul]
  cases y with
  | none => simp [eNone]
  | some u => simp [eNone]

lemma dMat_mulVec_vT0 (α β : D.Lab) (a : D.Fqˣ) (t : D.Fq) :
    (D.psModel α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (vT0 D t) =
      D.chi β (a : D.Fq) • vT0 D ((a⁻¹ : D.Fqˣ) * t) := by
  ext y
  rw [psModel_mulVec, dMat_inv, mobius_dMat, cocycle_dMat, Pi.smul_apply, smul_eq_mul]
  cases y with
  | none => simp [vT0]
  | some u =>
    simp only [vT0]
    have harg : t * ((a⁻¹ : D.Fqˣ) * u) = ((a⁻¹ : D.Fqˣ) * t) * u := by ring
    rw [harg]

lemma wMat_mulVec_eNone (α β : D.Lab) :
    (D.psModel α β (wMat D : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (eNone D) = eSome D 0 := by
  ext y
  rw [psModel_mulVec, wMat_inv, mobius_wMat]
  cases y with
  | none => simp [eNone, eSome]
  | some u =>
    by_cases hu : u = 0
    · subst hu; simp [eNone, eSome, cocycle_wMat]
    · simp [eNone, eSome, hu]

lemma uMat_mulVec_eSome_zero (α β : D.Lab) (b : D.Fq) :
    (D.psModel α β (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (eSome D 0) = eSome D b := by
  ext y
  rw [psModel_uMat_mulVec]
  cases y with
  | none => simp [eSome]
  | some u =>
    simp only [eSome, Pi.single_apply, Option.some.injEq, sub_eq_zero, eq_comm]

lemma wMat_mulVec_vT0_none (α β : D.Lab) (t : D.Fq) :
    ((D.psModel α β (wMat D : Matrix (Fin 2) (Fin 2) D.Fq)).mulVec (vT0 D t)) none = 1 := by
  rw [psModel_mulVec, wMat_inv, mobius_wMat, cocycle_wMat]
  simp [vT0]

lemma span_basis_eq_top (W : Submodule ℂ (Option D.Fq → ℂ))
    (h0 : eNone D ∈ W) (hs : ∀ x : D.Fq, eSome D x ∈ W) : W = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  have hdec : f = f none • eNone D + ∑ x : D.Fq, f (some x) • eSome D x := by
    ext y
    cases y with
    | none => simp [eNone, eSome]
    | some u =>
      simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, eNone, eSome,
        Pi.single_apply, Option.some_ne_none, ↓reduceIte, mul_zero, zero_add]
      rw [Finset.sum_eq_single u]
      · simp
      · intro x _ hne; simp [Ne.symm hne]
      · intro hx; exact absurd (Finset.mem_univ u) hx
  rw [hdec]
  exact W.add_mem (W.smul_mem _ h0) (W.sum_mem fun x _ => W.smul_mem _ (hs x))

lemma psModel_irred (α β : D.Lab) (hαβ : α ≠ β) :
    IsIrreducibleRep (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq)) := by
  refine ⟨⟨none⟩, fun W hW => ?_⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    set I := fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq)
    have h_extract_eNone : ∀ c₁ c₂ : ℂ, c₁ ≠ 0 →
        c₁ • eNone D + c₂ • vT0 D 0 ∈ W → eNone D ∈ W := by
      intro c₁ c₂ hc₁ hmem
      obtain ⟨a, ha⟩ := exists_chi_ne D hαβ
      have hact := hW (dMat D a) _ hmem
      have h1 : (I (dMat D a)).mulVec (c₁ • eNone D + c₂ • vT0 D 0) -
          D.chi β (a : D.Fq) • (c₁ • eNone D + c₂ • vT0 D 0) ∈ W :=
        W.sub_mem hact (W.smul_mem _ hmem)
      have hvec : (I (dMat D a)).mulVec (c₁ • eNone D + c₂ • vT0 D 0) -
          D.chi β (a : D.Fq) • (c₁ • eNone D + c₂ • vT0 D 0) =
          (c₁ * (D.chi α (a : D.Fq) - D.chi β (a : D.Fq))) • eNone D := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        rw [dMat_mulVec_eNone, dMat_mulVec_vT0, mul_zero]
        ext y
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hvec] at h1
      have hcoeff_ne : c₁ * (D.chi α (a : D.Fq) - D.chi β (a : D.Fq)) ≠ 0 :=
        mul_ne_zero hc₁ (sub_ne_zero.mpr ha)
      have hsm := W.smul_mem (c₁ * (D.chi α (a : D.Fq) - D.chi β (a : D.Fq)))⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hcoeff_ne, one_smul] at hsm
    have heNone : eNone D ∈ W := by
      have hne_bot : ∃ f ∈ W, f ≠ 0 := by
        by_contra! hall
        apply hbot
        rw [eq_bot_iff]
        intro f hf
        rw [Submodule.mem_bot]
        exact hall f hf
      obtain ⟨f, hfW, hf_ne⟩ := hne_bot
      have hsum : ∑ t : D.Fq, projT D α β t f ≠ 0 := by
        rw [sum_projT]; exact hf_ne
      obtain ⟨t₀, _, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      have hp_mem : projT D α β t₀ f ∈ W := projT_mem D α β W hW t₀ hfW
      have h_from_vT0 : ∀ t : D.Fq, vT0 D t ∈ W → eNone D ∈ W := fun t htW => by
        have hw := hW (wMat D) _ htW
        have hp0 := projT_mem D α β W hW 0 hw
        rw [projT_eq, if_pos rfl, wMat_mulVec_vT0_none] at hp0
        exact h_extract_eNone 1 _ one_ne_zero hp0
      rw [projT_eq] at hp_mem ht₀
      by_cases ht_zero : t₀ = 0
      · subst ht_zero
        rw [if_pos rfl] at hp_mem ht₀
        by_cases hf0 : f none = 0
        · rw [hf0, zero_smul, zero_add] at hp_mem ht₀
          have hc_ne : coeff D f 0 ≠ 0 := fun hz => ht₀ (by simp [hz])
          have hv0 : vT0 D 0 ∈ W := by
            have := W.smul_mem (coeff D f 0)⁻¹ hp_mem
            rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at this
          exact h_from_vT0 0 hv0
        · exact h_extract_eNone (f none) (coeff D f 0) hf0 hp_mem
      · rw [if_neg ht_zero, zero_smul, zero_add] at hp_mem ht₀
        have hc_ne : coeff D f t₀ ≠ 0 := fun hz => ht₀ (by simp [hz])
        have hvt : vT0 D t₀ ∈ W := by
          have := W.smul_mem (coeff D f t₀)⁻¹ hp_mem
          rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at this
        exact h_from_vT0 t₀ hvt
    refine span_basis_eq_top D W heNone fun x => ?_
    have he0 : eSome D 0 ∈ W := by
      have := hW (wMat D) _ heNone
      rwa [wMat_mulVec_eNone] at this
    have hex := hW (uMat D x) _ he0
    rwa [uMat_mulVec_eSome_zero] at hex

/-! Steinberg irreducibility (Part 2c) -/

def vPerp0 (α : D.Lab) : Option D.Fq → ℂ
  | none => (D.q : ℂ) * D.chi α (-1)
  | some _ => -1

lemma dotProduct_detVec_vPerp0 (α : D.Lab) :
    dotProduct (star (D.detVec α)) (vPerp0 D α) = 0 := by
  rw [dotProduct, Fintype.sum_option]
  simp only [Pi.star_apply, detVec, vPerp0, isqrt, star_mul, Complex.star_def,
    mul_one, Finset.sum_const, Finset.card_univ, card_Fq, nsmul_eq_mul]
  have hconj_r : conj (((Real.sqrt (D.q + 1))⁻¹ : ℝ) : ℂ) = (((Real.sqrt (D.q + 1))⁻¹ : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  have hchi : conj (D.chi α (-1)) * D.chi α (-1) = 1 := by
    rw [← Complex.star_def, star_chi D α (neg_ne_zero.mpr one_ne_zero),
      ← chi_add_label D (-α) α (neg_ne_zero.mpr one_ne_zero), neg_add_cancel,
      chi_zero_label D (neg_ne_zero.mpr one_ne_zero)]
  rw [hconj_r]
  calc (conj (D.chi α (-1)) * (((Real.sqrt (D.q + 1))⁻¹ : ℝ) : ℂ)) * ((D.q : ℂ) * D.chi α (-1)) +
        (D.q : ℂ) * ((((Real.sqrt (D.q + 1))⁻¹ : ℝ) : ℂ) * -1)
      = (((Real.sqrt (D.q + 1))⁻¹ : ℝ) : ℂ) * (D.q : ℂ) * (conj (D.chi α (-1)) * D.chi α (-1) - 1) := by
        ring
    _ = 0 := by rw [hchi, sub_self, mul_zero]

lemma orthog_p0_eq_smul_vPerp0 (α : D.Lab) (c₁ c₂ : ℂ)
    (h : dotProduct (star (D.detVec α)) (c₁ • eNone D + c₂ • vT0 D 0) = 0) :
    c₁ • eNone D + c₂ • vT0 D 0 = (-c₂) • vPerp0 D α := by
  rw [dotProduct, Fintype.sum_option] at h
  simp only [Pi.star_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eNone, vT0,
    Pi.single_apply, ↓reduceIte, Option.some_ne_none, mul_one, mul_zero, zero_add,
    detVec, isqrt, star_mul] at h
  have hq1_pos : (0 : ℝ) < Real.sqrt (D.q + 1) := Real.sqrt_pos.mpr (by positivity)
  have hisqrt_ne : ((Real.sqrt (D.q + 1) : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hq1_pos.ne')
  simp [psi_zero, card_Fq] at h
  have hlin : star (D.chi α (-1)) * c₁ + (D.q : ℂ) * c₂ = 0 := by
    rw [Complex.star_def]
    apply mul_left_cancel₀ hisqrt_ne
    linear_combination h
  have hc₁ : c₁ = -(c₂ * (D.q : ℂ) * D.chi α (-1)) := by
    have hm := congrArg (fun z => D.chi α (-1) * z) hlin
    simp only [mul_zero] at hm
    have hchi1 : D.chi α (-1) * star (D.chi α (-1)) = 1 := by
      rw [star_chi D α (neg_ne_zero.mpr one_ne_zero),
        ← chi_add_label D α (-α) (neg_ne_zero.mpr one_ne_zero), add_neg_cancel,
        chi_zero_label D (neg_ne_zero.mpr one_ne_zero)]
    linear_combination hm - c₁ * hchi1
  ext y
  cases y with
  | none =>
    simp [eNone, vT0, vPerp0, hc₁]; ring
  | some x =>
    simp [eNone, vT0, vPerp0]

lemma steinberg_irred (α : D.Lab) :
    ∀ W : Submodule ℂ (Option D.Fq → ℂ), (∀ u ∈ W, dotProduct (star (D.detVec α)) u = 0) →
      IsInvariantSubspace (fun g : D.G => D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)) W →
      W = ⊥ ∨ ∀ u : Option D.Fq → ℂ, dotProduct (star (D.detVec α)) u = 0 → u ∈ W := by
  intro W hW_orth hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    set I := fun g : D.G => D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)
    have h_vT0_all : ∀ t₀ : D.Fq, t₀ ≠ 0 → vT0 D t₀ ∈ W →
        ∀ t : D.Fq, t ≠ 0 → vT0 D t ∈ W := by
      intro t₀ ht₀ hmem t ht
      let a : D.Fqˣ := Units.mk0 (t₀ / t) (div_ne_zero ht₀ ht)
      have hact := hW (dMat D a) _ hmem
      rw [dMat_mulVec_vT0] at hact
      have harg : ((a⁻¹ : D.Fqˣ) : D.Fq) * t₀ = t := by
        change (t₀ / t)⁻¹ * t₀ = t
        field_simp [ht₀, ht]
      rw [harg] at hact
      have hchi_ne : D.chi α (a : D.Fq) ≠ 0 := chi_ne_zero D α a.ne_zero
      have hsm := W.smul_mem (D.chi α (a : D.Fq))⁻¹ hact
      rwa [smul_smul, inv_mul_cancel₀ hchi_ne, one_smul] at hsm
    have h_vPerp_of_vT0 : ∀ t₀ : D.Fq, t₀ ≠ 0 → vT0 D t₀ ∈ W → vPerp0 D α ∈ W := by
      intro t₀ _ hmem
      have hw := hW (wMat D) _ hmem
      have hp0 := projT_mem D α α W hW 0 hw
      have h_orth := hW_orth _ hp0
      rw [projT_eq, if_pos rfl, wMat_mulVec_vT0_none] at hp0 h_orth
      have heq := orthog_p0_eq_smul_vPerp0 D α 1 (coeff D (I (wMat D) *ᵥ vT0 D t₀) 0) h_orth
      rw [heq] at hp0
      have hc_ne : (-coeff D (I (wMat D) *ᵥ vT0 D t₀) 0 : ℂ) ≠ 0 := by
        intro hc0
        have h0 := congrArg (fun f : Option D.Fq → ℂ => f none) heq
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, eNone, vT0,
          Pi.single_eq_same, mul_one, mul_zero, add_zero, vPerp0] at h0
        have hc0' : coeff D (I (wMat D) *ᵥ vT0 D t₀) 0 = 0 := by linear_combination -hc0
        rw [hc0', neg_zero, zero_mul] at h0
        exact one_ne_zero h0
      have hsm := W.smul_mem (-coeff D (I (wMat D) *ᵥ vT0 D t₀) 0)⁻¹ hp0
      rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at hsm
    have h_vT0_of_vPerp : vPerp0 D α ∈ W → ∃ t₀ : D.Fq, t₀ ≠ 0 ∧ vT0 D t₀ ∈ W := by
      intro hpW
      let g := (I (wMat D)).mulVec (vPerp0 D α)
      have hgW : g ∈ W := hW (wMat D) _ hpW
      have hg0 : g (some 0) = (D.q : ℂ) * D.chi α (-1) := by
        dsimp [g, I]
        rw [psModel_mulVec, wMat_inv, mobius_wMat, cocycle_wMat]
        simp [vPerp0]
      have hg1 : g (some 1) = -D.chi α (-1) := by
        dsimp [g, I]
        rw [psModel_mulVec, wMat_inv, mobius_wMat, cocycle_wMat]
        simp [vPerp0]
      have hg_ne : g (some 0) ≠ g (some 1) := by
        rw [hg0, hg1]
        intro heq
        have hchi_ne : D.chi α (-1) ≠ 0 := chi_ne_zero D α (neg_ne_zero.mpr one_ne_zero)
        have hq1 : ((D.q : ℂ) + 1) * D.chi α (-1) = 0 := by linear_combination heq
        have hqp : (D.q : ℂ) + 1 = 0 := (mul_eq_zero.mp hq1).resolve_right hchi_ne
        have hre := congrArg Complex.re hqp
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
        have : (0 : ℝ) < (D.q : ℝ) + 1 := by positivity
        linarith
      have hnot_zero : ¬ ∀ t : D.Fq, t ≠ 0 → projT D α α t g = 0 := by
        intro hall
        have hg_eq : g = projT D α α 0 g := by
          conv_lhs => rw [← sum_projT D α α g]
          rw [Finset.sum_eq_single 0]
          · intro t _ ht; exact hall t ht
          · intro hmem; exact absurd (Finset.mem_univ 0) hmem
        have h0_eq : (projT D α α 0 g) (some 0) = (projT D α α 0 g) (some 1) := by
          simp [projT_eq, eNone, vT0]
        apply hg_ne
        calc g (some 0) = (projT D α α 0 g) (some 0) := congrFun hg_eq (some 0)
          _ = (projT D α α 0 g) (some 1) := h0_eq
          _ = g (some 1) := (congrFun hg_eq (some 1)).symm
      push Not at hnot_zero
      obtain ⟨t₀, ht₀, hp_ne⟩ := hnot_zero
      have hp_mem := projT_mem D α α W hW t₀ hgW
      rw [projT_eq, if_neg ht₀, zero_smul, zero_add] at hp_mem hp_ne
      have hc_ne : coeff D g t₀ ≠ 0 := fun hz => hp_ne (by simp [hz])
      refine ⟨t₀, ht₀, ?_⟩
      have hsm := W.smul_mem (coeff D g t₀)⁻¹ hp_mem
      rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at hsm
    have hbasis : vPerp0 D α ∈ W ∧ ∀ t : D.Fq, t ≠ 0 → vT0 D t ∈ W := by
      have hne_bot : ∃ f ∈ W, f ≠ 0 := by
        by_contra! hall
        apply hbot
        rw [eq_bot_iff]
        intro f hf
        rw [Submodule.mem_bot]
        exact hall f hf
      obtain ⟨f, hfW, hf_ne⟩ := hne_bot
      have hsum : ∑ t : D.Fq, projT D α α t f ≠ 0 := by
        rw [sum_projT]; exact hf_ne
      obtain ⟨t₀, _, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      have hp_mem : projT D α α t₀ f ∈ W := projT_mem D α α W hW t₀ hfW
      by_cases ht_zero : t₀ = 0
      · subst ht_zero
        have horth0 := hW_orth _ hp_mem
        rw [projT_eq, if_pos rfl] at hp_mem ht₀ horth0
        have heq_p := orthog_p0_eq_smul_vPerp0 D α (f none) (coeff D f 0) horth0
        rw [heq_p] at hp_mem ht₀
        have hc_ne : -coeff D f 0 ≠ 0 := fun hz => ht₀ (by simp [hz])
        have hvP : vPerp0 D α ∈ W := by
          have := W.smul_mem (-coeff D f 0)⁻¹ hp_mem
          rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at this
        obtain ⟨t₁, ht₁, hvt₁⟩ := h_vT0_of_vPerp hvP
        exact ⟨hvP, h_vT0_all t₁ ht₁ hvt₁⟩
      · rw [projT_eq, if_neg ht_zero, zero_smul, zero_add] at hp_mem ht₀
        have hc_ne : coeff D f t₀ ≠ 0 := fun hz => ht₀ (by simp [hz])
        have hvt : vT0 D t₀ ∈ W := by
          have := W.smul_mem (coeff D f t₀)⁻¹ hp_mem
          rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at this
        exact ⟨h_vPerp_of_vT0 t₀ ht_zero hvt, h_vT0_all t₀ ht_zero hvt⟩
    intro u hu
    rw [← sum_projT D α α u]
    have hsplit : ∑ t : D.Fq, projT D α α t u =
        projT D α α 0 u + ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), projT D α α t u := by
      rw [← Finset.add_sum_erase Finset.univ (fun t => projT D α α t u) (Finset.mem_univ 0)]
      congr 1
      refine Finset.sum_congr (by ext t; simp) fun _ _ => rfl
    rw [hsplit]
    have hsum_ne : ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), projT D α α t u ∈ W := by
      apply W.sum_mem
      intro t ht
      have ht_ne : t ≠ 0 := (Finset.mem_filter.mp ht).2
      rw [projT_eq, if_neg ht_ne, zero_smul, zero_add]
      exact W.smul_mem _ (hbasis.2 t ht_ne)
    have h0_orth : dotProduct (star (D.detVec α)) (projT D α α 0 u) = 0 := by
      have hsum_orth : dotProduct (star (D.detVec α))
          (∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), projT D α α t u) = 0 :=
        hW_orth _ hsum_ne
      have hadd := congrArg (dotProduct (star (D.detVec α))) hsplit
      rw [sum_projT, hu, dotProduct_add, hsum_orth, add_zero] at hadd
      exact hadd.symm
    rw [projT_eq, if_pos rfl] at h0_orth ⊢
    rw [orthog_p0_eq_smul_vPerp0 D α _ _ h0_orth]
    exact W.add_mem (W.smul_mem _ hbasis.1) hsum_ne

end Irreducibility

/-! ### Section 5: Equivalence `RepEquiv` (Part 3) -/

section Equivalence

variable (D : FieldData)

def intertwiner (α β : D.Lab) : Matrix (Option D.Fq) (Option D.Fq) ℂ :=
  fun y x => match y, x with
    | none, none => 0
    | none, some _ => 1
    | some _, none => 1
    | some y', some x' => D.chi β (-1) * D.chi (α - β) (x' - y')

lemma intertwiner_mul (α β : D.Lab) (hαβ : α ≠ β) :
    intertwiner D β α * intertwiner D α β = (D.q : ℂ) • 1 := by
  ext y x
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Fintype.sum_option]
  have hsign : D.chi α (-1) * D.chi β (-1) * D.chi (β - α) (-1) = 1 := by
    have hne : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
    rw [← chi_add_label D α β hne, ← chi_add_label D (α + β) (β - α) hne]
    have h2 : α + β + (β - α) = β + β := by ring
    rw [h2, chi_add_label D β β hne, chi_neg_one_sq]
  cases y with
  | none =>
    cases x with
    | none =>
      simp [intertwiner, card_Fq]
    | some x' =>
      simp [intertwiner]
      rw [← Finset.mul_sum]
      have hsum : ∑ z : D.Fq, D.chi (α - β) (x' - z) = 0 := by
        rw [← Equiv.sum_comp (Equiv.subLeft x')]
        simpa [Equiv.subLeft_apply] using sum_chi_eq_zero D (sub_ne_zero.mpr hαβ)
      rw [hsum, mul_zero]
  | some y' =>
    cases x with
    | none =>
      simp only [intertwiner, mul_zero, zero_add, mul_one, Option.some_ne_none, ↓reduceIte]
      rw [← Finset.mul_sum]
      have hsum : ∑ z : D.Fq, D.chi (β - α) (z - y') = 0 := by
        rw [← Equiv.sum_comp (Equiv.subRight (-y'))]
        simpa [Equiv.subRight_apply, sub_eq_add_neg] using sum_chi_eq_zero D (sub_ne_zero.mpr (Ne.symm hαβ))
      rw [hsum, mul_zero]
    | some x' =>
      simp only [intertwiner, one_mul, Option.some.injEq]
      by_cases hxy : y' = x'
      · subst hxy
        rw [if_pos rfl, mul_one]
        have hterm : ∀ z : D.Fq,
            (D.chi α (-1) * D.chi (β - α) (z - y')) * (D.chi β (-1) * D.chi (α - β) (y' - z)) =
              if z = y' then 0 else 1 := fun z => by
          by_cases hz : z = y'
          · subst hz; simp
          · have h1 : z - y' = (-1) * (y' - z) := by ring
            have hne_yz : y' - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
            rw [if_neg hz, h1, chi_mul D (β - α) (neg_ne_zero.mpr one_ne_zero) hne_yz]
            calc (D.chi α (-1) * (D.chi (β - α) (-1) * D.chi (β - α) (y' - z))) *
                  (D.chi β (-1) * D.chi (α - β) (y' - z))
                = (D.chi α (-1) * D.chi β (-1) * D.chi (β - α) (-1)) *
                  (D.chi (β - α) (y' - z) * D.chi (α - β) (y' - z)) := by ring
              _ = 1 * D.chi ((β - α) + (α - β)) (y' - z) := by
                  rw [hsign, chi_add_label D (β - α) (α - β) hne_yz]
              _ = 1 := by simp [sub_add_sub_cancel, chi_zero_label D hne_yz]
        simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add,
          Finset.sum_const, nsmul_eq_mul, mul_one]
        have hc : (Finset.univ.filter (fun z : D.Fq => ¬ z = y')).card = D.q - 1 := by
          have := Finset.card_erase_of_mem (Finset.mem_univ y')
          rw [Finset.card_univ, card_Fq] at this
          convert this using 2
          ext z; simp [Finset.mem_erase]
        rw [hc]
        have hq1 : 1 ≤ D.q := by have := D.one_lt_q; omega
        have : (1 : ℂ) + ((D.q - 1 : ℕ) : ℂ) = (D.q : ℂ) := by
          exact_mod_cast (by omega : 1 + (D.q - 1) = D.q)
        exact this
      · rw [if_neg hxy, mul_zero]
        have hxy' : x' ≠ y' := Ne.symm hxy
        let S_fin : Finset D.Fq := Finset.univ.filter (fun z : D.Fq => z ≠ x' ∧ z ≠ y')
        let T_fin : Finset D.Fq := Finset.univ.filter (fun w : D.Fq => w ≠ 0 ∧ w ≠ -1)
        let φ : ↥S_fin ≃ ↥T_fin := {
          toFun := fun z => ⟨(z.1 - y') / (x' - z.1), by
            have hzmem := Finset.mem_filter.mp z.2
            have hzx : x' - z.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hzmem.2.1)
            have hzy : z.1 - y' ≠ 0 := sub_ne_zero.mpr hzmem.2.2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, div_ne_zero hzy hzx, ?_⟩
            intro heq
            have h1 : z.1 - y' = -(x' - z.1) := by
              have := congrArg (· * (x' - z.1)) heq
              rwa [div_mul_cancel₀ _ hzx, neg_one_mul] at this
            rw [neg_sub] at h1
            exact hxy' (sub_right_inj.mp h1).symm⟩
          invFun := fun w => ⟨(w.1 * x' + y') / (w.1 + 1), by
            have hwmem := Finset.mem_filter.mp w.2
            have hw1 : w.1 + 1 ≠ 0 := fun hz => hwmem.2.2 (eq_neg_of_add_eq_zero_left hz)
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
            · intro heq
              have h1 : w.1 * x' + y' = x' * (w.1 + 1) := by
                have := congrArg (· * (w.1 + 1)) heq
                rwa [div_mul_cancel₀ _ hw1] at this
              have : x' = y' := by linear_combination -h1
              exact hxy' this
            · intro heq
              have h1 : w.1 * x' + y' = y' * (w.1 + 1) := by
                have := congrArg (· * (w.1 + 1)) heq
                rwa [div_mul_cancel₀ _ hw1] at this
              have h2 : w.1 * (x' - y') = 0 := by linear_combination h1
              exact hwmem.2.1 ((mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hxy'))⟩
          left_inv := fun z => by
            ext
            have hzmem := Finset.mem_filter.mp z.2
            have hzx : x' - z.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hzmem.2.1)
            have hxy_ne : x' - y' ≠ 0 := sub_ne_zero.mpr hxy'
            have h1 : (z.1 - y') / (x' - z.1) + 1 ≠ 0 := by
              intro hz
              have hadd : (z.1 - y') + (x' - z.1) = 0 := by
                have := congrArg (· * (x' - z.1)) hz
                rwa [add_mul, div_mul_cancel₀ _ hzx, one_mul, zero_mul] at this
              exact hxy_ne (by linear_combination hadd)
            field_simp [hzx, h1, hxy_ne]
            ring
          right_inv := fun w => by
            ext
            have hwmem := Finset.mem_filter.mp w.2
            have hw1 : w.1 + 1 ≠ 0 := fun hz => hwmem.2.2 (eq_neg_of_add_eq_zero_left hz)
            have hxy_ne : x' - y' ≠ 0 := sub_ne_zero.mpr hxy'
            have h2 : x' - (w.1 * x' + y') / (w.1 + 1) ≠ 0 := by
              intro hz
              have hsub : x' * (w.1 + 1) - (w.1 * x' + y') = 0 := by
                have := congrArg (· * (w.1 + 1)) hz
                rwa [sub_mul, div_mul_cancel₀ _ hw1, zero_mul] at this
              exact hxy_ne (by linear_combination hsub)
            have hden : x' * (w.1 + 1) - (w.1 * x' + y') ≠ 0 := by
              have hrew : x' * (w.1 + 1) - (w.1 * x' + y') = x' - y' := by ring
              rwa [hrew]
            field_simp [hw1, h2, hden]
            ring
        }
        have hsum_split :
            ∑ z : D.Fq, (D.chi α (-1) * D.chi (β - α) (z - y')) * (D.chi β (-1) * D.chi (α - β) (x' - z)) =
            D.chi α (-1) * D.chi β (-1) *
              ∑ z : ↥S_fin, D.chi (β - α) (z.1 - y') * D.chi (α - β) (x' - z.1) := by
          have hsub : ∑ z : D.Fq, (D.chi α (-1) * D.chi (β - α) (z - y')) * (D.chi β (-1) * D.chi (α - β) (x' - z)) =
              ∑ z ∈ S_fin,
                (D.chi α (-1) * D.chi (β - α) (z - y')) * (D.chi β (-1) * D.chi (α - β) (x' - z)) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun z _ => ?_
            split_ifs with h
            · rfl
            · rw [not_and_or, not_not, not_not] at h
              rcases h with rfl | rfl <;> simp
          rw [hsub, ← Finset.sum_coe_sort S_fin]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => by ring
        rw [hsum_split]
        have hbij_sum : ∑ z : ↥S_fin, D.chi (β - α) (z.1 - y') * D.chi (α - β) (x' - z.1) =
            ∑ w : ↥T_fin, D.chi (β - α) w.1 := by
          rw [← Equiv.sum_comp φ.symm]
          refine Finset.sum_congr rfl fun w _ => ?_
          have hzmem := Finset.mem_filter.mp (φ.symm w).2
          have hzx : x' - (φ.symm w).1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hzmem.2.1)
          have hzy : (φ.symm w).1 - y' ≠ 0 := sub_ne_zero.mpr hzmem.2.2
          have hinv : D.chi (α - β) (x' - (φ.symm w).1) = D.chi (-(α - β)) (x' - (φ.symm w).1)⁻¹ := by
            conv_lhs => rw [← inv_inv (x' - (φ.symm w).1), chi_inv D (α - β) (inv_ne_zero hzx)]
          have hneg : -(α - β) = β - α := by ring
          rw [hinv, hneg, ← chi_mul D (β - α) hzy (inv_ne_zero hzx), ← div_eq_mul_inv]
          have hval : ((φ.symm w).1 - y') / (x' - (φ.symm w).1) = w.1 :=
            congrArg Subtype.val (φ.apply_symm_apply w)
          rw [hval]
        rw [hbij_sum, Finset.sum_coe_sort T_fin]
        have hsum_T : ∑ w ∈ T_fin, D.chi (β - α) w = -D.chi (β - α) (-1) := by
          have htot := sum_chi_eq_zero D (sub_ne_zero.mpr (Ne.symm hαβ))
          have h1 : ∑ w : D.Fq, D.chi (β - α) w =
              D.chi (β - α) (-1) + ∑ w ∈ Finset.univ.erase (-1), D.chi (β - α) w :=
            (Finset.add_sum_erase Finset.univ (fun w => D.chi (β - α) w) (Finset.mem_univ (-1))).symm
          have h0_mem : (0 : D.Fq) ∈ Finset.univ.erase (-1) :=
            Finset.mem_erase.mpr ⟨(neg_ne_zero.mpr one_ne_zero).symm, Finset.mem_univ 0⟩
          have h2 : ∑ w ∈ Finset.univ.erase (-1), D.chi (β - α) w =
              D.chi (β - α) 0 + ∑ w ∈ (Finset.univ.erase (-1)).erase 0, D.chi (β - α) w :=
            (Finset.add_sum_erase (Finset.univ.erase (-1)) (fun w => D.chi (β - α) w) h0_mem).symm
          have hfilt : (Finset.univ.erase (-1 : D.Fq)).erase 0 = T_fin := by
            ext w; simp [T_fin, and_comm]
          rw [h2, hfilt, chi_zero, zero_add] at h1
          rw [h1] at htot
          linear_combination htot
        rw [hsum_T]
        linear_combination -hsign

lemma intertwiner_comm_uMat (α β : D.Lab) (b : D.Fq) :
    intertwiner D α β * D.psModel α β (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq) =
      D.psModel β α (uMat D b : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β := by
  ext y x
  simp_rw [Matrix.mul_apply, psModel_eq_ite]
  rw [Finset.sum_eq_single (mobius D (uMat D b) x)]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single (mobius D (uMat D (-b)) y)]
    · have hm : y = mobius D (uMat D b) (mobius D (uMat D (-b)) y) := by
        rw [← uMat_inv]; exact (mobius_inv_right D (uMat D b) y).symm
      rw [if_pos hm, cocycle_uMat, cocycle_uMat, mobius_uMat, mobius_uMat]
      cases y with
      | none =>
        cases x with
        | none => simp [intertwiner]
        | some x' => simp [intertwiner]
      | some y' =>
        cases x with
        | none => simp [intertwiner]
        | some x' =>
          simp only [intertwiner, mul_one, one_mul]
          congr 2; ring
    · intro z _ hzne
      have hne : y ≠ mobius D (uMat D b) z := by
        intro heq; apply hzne
        calc z = mobius D (uMat D (-b)) (mobius D (uMat D b) z) := by
              rw [← uMat_inv]; exact (mobius_inv_left D (uMat D b) z).symm
          _ = mobius D (uMat D (-b)) y := by rw [← heq]
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro z _ hzne; simp [hzne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

lemma intertwiner_comm_tMat (α β : D.Lab) (a d : D.Fqˣ) :
    intertwiner D α β * D.psModel α β (tMat D a d : Matrix (Fin 2) (Fin 2) D.Fq) =
      D.psModel β α (tMat D a d : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β := by
  have hmob : ∀ (u v : D.Fqˣ) (z : Option D.Fq), mobius D (tMat D u v) z =
      match z with | none => none | some s => some ((u : D.Fq) / (v : D.Fq) * s) := fun u v z => by
    cases z <;> simp [mobius, tMat, div_mul_eq_mul_div]
  have hcoc : ∀ (u v : D.Fqˣ) (α' β' : D.Lab) (z : Option D.Fq), cocycle D α' β' (tMat D u v) z =
      match z with
      | none => D.chi α' (u : D.Fq) * D.chi β' (v : D.Fq)
      | some _ => D.chi α' (v : D.Fq) * D.chi β' (u : D.Fq) := fun u v α' β' z => by
    cases z <;> simp [cocycle, bMat, tMat, Matrix.det_fin_two, mul_div_cancel_right₀ _ v.ne_zero]
  have hinv : (tMat D a d)⁻¹ = tMat D a⁻¹ d⁻¹ := by ext i j; simp [tMat]
  ext y x
  simp_rw [Matrix.mul_apply, psModel_eq_ite]
  rw [Finset.sum_eq_single (mobius D (tMat D a d) x)]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single (mobius D (tMat D a⁻¹ d⁻¹) y)]
    · have hm : y = mobius D (tMat D a d) (mobius D (tMat D a⁻¹ d⁻¹) y) := by
        rw [← hinv]; exact (mobius_inv_right D (tMat D a d) y).symm
      rw [if_pos hm, hcoc a d, hcoc a d, hmob a d, hmob a⁻¹ d⁻¹]
      cases y with
      | none =>
        cases x with
        | none => simp [intertwiner]
        | some x' =>
          simp only [intertwiner, mul_one, one_mul]
          ring
      | some y' =>
        cases x with
        | none =>
          simp only [intertwiner, mul_one, one_mul]
          ring
        | some x' =>
          simp only [intertwiner]
          have hda : ((a⁻¹ : D.Fqˣ) : D.Fq) / ((d⁻¹ : D.Fqˣ) : D.Fq) = (d : D.Fq) / (a : D.Fq) := by
            simp [div_eq_mul_inv, mul_comm]
          rw [hda]
          have hrel : x' - (d : D.Fq) / (a : D.Fq) * y' =
              (d : D.Fq) / (a : D.Fq) * ((a : D.Fq) / (d : D.Fq) * x' - y') := by
            field_simp [a.ne_zero, d.ne_zero]
          by_cases h0 : (a : D.Fq) / (d : D.Fq) * x' - y' = 0
          · have h0' : x' - (d : D.Fq) / (a : D.Fq) * y' = 0 := by rw [hrel, h0, mul_zero]
            simp [h0, h0']
          · rw [hrel, chi_mul D (α - β) (div_ne_zero d.ne_zero a.ne_zero) h0,
              chi_div D (α - β) d.ne_zero a.ne_zero]
            have h_d : D.chi α (d : D.Fq) = D.chi β (d : D.Fq) * D.chi (α - β) (d : D.Fq) := by
              rw [← chi_add_label D β (α - β) d.ne_zero, add_sub_cancel]
            have h_a : D.chi β (a : D.Fq) = D.chi α (a : D.Fq) * D.chi (-(α - β)) (a : D.Fq) := by
              rw [← chi_add_label D α (-(α - β)) a.ne_zero]
              congr 1; ring
            rw [h_d, h_a]
            ring
    · intro z _ hzne
      have hne : y ≠ mobius D (tMat D a d) z := by
        intro heq; apply hzne
        calc z = mobius D (tMat D a⁻¹ d⁻¹) (mobius D (tMat D a d) z) := by
              rw [← hinv]; exact (mobius_inv_left D (tMat D a d) z).symm
          _ = mobius D (tMat D a⁻¹ d⁻¹) y := by rw [← heq]
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro z _ hzne; simp [hzne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

lemma intertwiner_comm_wMat (α β : D.Lab) :
    intertwiner D α β * D.psModel α β (wMat D : Matrix (Fin 2) (Fin 2) D.Fq) =
      D.psModel β α (wMat D : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β := by
  have hneg1 : (-1 : D.Fq) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  ext y x
  simp_rw [Matrix.mul_apply, psModel_eq_ite]
  rw [Finset.sum_eq_single (mobius D (wMat D) x)]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single (mobius D (wMat D) y)]
    · have hm : y = mobius D (wMat D) (mobius D (wMat D) y) := by
        nth_rw 2 [← wMat_inv]; exact (mobius_inv_right D (wMat D) y).symm
      rw [if_pos hm, mobius_wMat, mobius_wMat, cocycle_wMat, cocycle_wMat]
      cases y with
      | none =>
        cases x with
        | none => simp [intertwiner]
        | some x' =>
          by_cases hx : x' = 0
          · subst hx; simp [intertwiner]
          · simp only [hx, ↓reduceIte, intertwiner, one_mul, sub_zero]
            rw [chi_div D β hneg1 hx]
            calc D.chi α x' * (D.chi β (-1) * D.chi (-β) x')
                = D.chi β (-1) * (D.chi α x' * D.chi (-β) x') := by ring
              _ = D.chi β (-1) * D.chi (α + (-β)) x' := by
                  rw [chi_add_label D α (-β) hx]
              _ = D.chi β (-1) * D.chi (α - β) x' := by rw [← sub_eq_add_neg]
      | some y' =>
        by_cases hy : y' = 0
        · subst hy
          cases x with
          | none => simp [intertwiner]
          | some x' =>
            by_cases hx : x' = 0
            · subst hx; simp [intertwiner]
            · simp only [hx, ↓reduceIte, intertwiner, mul_one, sub_zero]
              rw [chi_div D β hneg1 hx, chi_inv D (α - β) hx]
              calc D.chi β (-1) * D.chi (-(α - β)) x' * (D.chi α x' * (D.chi β (-1) * D.chi (-β) x'))
                  = (D.chi β (-1) * D.chi β (-1)) * (D.chi (-(α - β)) x' * D.chi α x' * D.chi (-β) x') := by ring
                _ = 1 * D.chi (-(α - β) + α + (-β)) x' := by
                    rw [chi_neg_one_sq, ← chi_add_label D (-(α - β)) α hx,
                      ← chi_add_label D (-(α - β) + α) (-β) hx]
                _ = D.chi 0 x' := by rw [one_mul, show -(α - β) + α + (-β) = 0 by ring]
                _ = 1 := chi_zero_label D hx
        · cases x with
          | none =>
            simp only [hy, inv_ne_zero hy, ↓reduceIte, intertwiner, mul_one, zero_sub]
            have hdiv : (-1 : D.Fq) / y'⁻¹ = (-1 : D.Fq) * y' := by field_simp [hy]
            have hny' : -y' = (-1 : D.Fq) * y' := by ring
            rw [hdiv, hny', chi_mul D (α - β) hneg1 hy, chi_inv D β hy, chi_mul D α hneg1 hy]
            calc D.chi β (-1) * (D.chi (α - β) (-1) * D.chi (α - β) y')
                = (D.chi β (-1) * D.chi (α - β) (-1)) * D.chi (α - β) y' := by ring
              _ = D.chi (β + (α - β)) (-1) * D.chi (α - β) y' := by
                  rw [chi_add_label D β (α - β) hneg1]
              _ = D.chi α (-1) * D.chi (-β + α) y' := by
                  rw [add_sub_cancel, show α - β = -β + α by ring]
              _ = D.chi (-β) y' * (D.chi α (-1) * D.chi α y') := by
                  rw [chi_add_label D (-β) α hy]; ring
          | some x' =>
            by_cases hx : x' = 0
            · subst hx
              simp only [hy, inv_ne_zero hy, ↓reduceIte, intertwiner, mul_one, zero_sub]
              have hdiv : (-1 : D.Fq) / y'⁻¹ = (-1 : D.Fq) * y' := by field_simp [hy]
              have hny : -y'⁻¹ = (-1 : D.Fq) * y'⁻¹ := by ring
              rw [hdiv, hny, chi_inv D β hy, chi_mul D α hneg1 hy,
                chi_mul D (α - β) hneg1 (inv_ne_zero hy), chi_inv D (α - β) hy]
              have h1 : D.chi α (-1) * D.chi β (-1) * D.chi (α - β) (-1) = 1 := by
                rw [← chi_add_label D α β hneg1, ← chi_add_label D (α + β) (α - β) hneg1]
                have h2 : α + β + (α - β) = α + α := by ring
                rw [h2, chi_add_label D α α hneg1, chi_neg_one_sq]
              calc (1 : ℂ)
                  = (D.chi α (-1) * D.chi β (-1) * D.chi (α - β) (-1)) *
                      D.chi (-β + α + -(α - β)) y' := by
                    rw [h1, show (-β + α + -(α - β) : D.Lab) = 0 by ring, chi_zero_label D hy, mul_one]
                _ = D.chi (-β) y' * (D.chi α (-1) * D.chi α y') *
                      (D.chi β (-1) * (D.chi (α - β) (-1) * D.chi (-(α - β)) y')) := by
                    rw [chi_add_label D (-β + α) (-(α - β)) hy, chi_add_label D (-β) α hy]; ring
            · simp only [hx, hy, inv_ne_zero hy, ↓reduceIte, intertwiner]
              by_cases hxy : x' * y' = 1
              · have hl : x'⁻¹ - y' = 0 := by
                  have hsub : x'⁻¹ - y' = (1 - x' * y') * x'⁻¹ := by field_simp [hx]
                  rw [hsub, hxy, sub_self, zero_mul]
                have hr : x' - y'⁻¹ = 0 := by
                  have hsub : x' - y'⁻¹ = (-1 : D.Fq) * (1 - x' * y') * y'⁻¹ := by field_simp [hy]; ring
                  rw [hsub, hxy, sub_self, mul_zero, zero_mul]
                simp [hl, hr]
              · have h1xy : 1 - x' * y' ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
                have hdiv_x : (-1 : D.Fq) / x' = (-1 : D.Fq) * x'⁻¹ := by ring
                have hdiv_y : (-1 : D.Fq) / y'⁻¹ = (-1 : D.Fq) * y' := by field_simp [hy]
                have hsub_l : x'⁻¹ - y' = (1 - x' * y') * x'⁻¹ := by field_simp [hx]
                have hsub_r : x' - y'⁻¹ = (-1 : D.Fq) * (1 - x' * y') * y'⁻¹ := by field_simp [hy]; ring
                rw [hdiv_x, hdiv_y, hsub_l, hsub_r]
                rw [chi_mul D (α - β) h1xy (inv_ne_zero hx), chi_inv D (α - β) hx,
                  chi_mul D β hneg1 (inv_ne_zero hx), chi_inv D β hx,
                  chi_inv D β hy, chi_mul D α hneg1 hy,
                  chi_mul D (α - β) (mul_ne_zero hneg1 h1xy) (inv_ne_zero hy),
                  chi_mul D (α - β) hneg1 h1xy, chi_inv D (α - β) hy]
                have hsign_l : D.chi β (-1) * D.chi β (-1) = 1 := chi_neg_one_sq D β
                have hsign_r : D.chi α (-1) * D.chi β (-1) * D.chi (α - β) (-1) = 1 := by
                  rw [← chi_add_label D α β hneg1, ← chi_add_label D (α + β) (α - β) hneg1]
                  have h2 : α + β + (α - β) = α + α := by ring
                  rw [h2, chi_add_label D α α hneg1, chi_neg_one_sq]
                have hx_pow : D.chi (-(α - β)) x' * D.chi α x' * D.chi (-β) x' = 1 := by
                  rw [← chi_add_label D (-(α - β)) α hx, ← chi_add_label D (-(α - β) + α) (-β) hx]
                  have h0 : -(α - β) + α + (-β) = 0 := by ring
                  rw [h0, chi_zero_label D hx]
                have hy_pow : D.chi (-β) y' * D.chi α y' * D.chi (-(α - β)) y' = 1 := by
                  rw [← chi_add_label D (-β) α hy, ← chi_add_label D (-β + α) (-(α - β)) hy]
                  have h0 : -β + α + -(α - β) = 0 := by ring
                  rw [h0, chi_zero_label D hy]
                calc D.chi β (-1) * (D.chi (α - β) (1 - x' * y') * D.chi (-(α - β)) x') *
                      (D.chi α x' * (D.chi β (-1) * D.chi (-β) x'))
                    = (D.chi β (-1) * D.chi β (-1)) *
                        (D.chi (-(α - β)) x' * D.chi α x' * D.chi (-β) x') *
                        D.chi (α - β) (1 - x' * y') := by ring
                  _ = D.chi (α - β) (1 - x' * y') := by rw [hsign_l, hx_pow, one_mul, one_mul]
                  _ = (D.chi α (-1) * D.chi β (-1) * D.chi (α - β) (-1)) *
                        (D.chi (-β) y' * D.chi α y' * D.chi (-(α - β)) y') *
                        D.chi (α - β) (1 - x' * y') := by rw [hsign_r, hy_pow, one_mul, one_mul]
                  _ = D.chi (-β) y' * (D.chi α (-1) * D.chi α y') *
                        (D.chi β (-1) * (D.chi (α - β) (-1) * D.chi (α - β) (1 - x' * y') *
                          D.chi (-(α - β)) y')) := by ring
    · intro z _ hzne
      have hne : y ≠ mobius D (wMat D) z := by
        intro heq; apply hzne
        calc z = mobius D (wMat D) (mobius D (wMat D) z) := by
              nth_rw 2 [← wMat_inv]; exact (mobius_inv_left D (wMat D) z).symm
          _ = mobius D (wMat D) y := by rw [← heq]
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · intro z _ hzne; simp [hzne]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

lemma intertwiner_comm (α β : D.Lab) (g : D.G) :
    intertwiner D α β * D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq) =
      D.psModel β α (g : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β := by
  have hmul : ∀ g₁ g₂ : D.G,
      (intertwiner D α β * D.psModel α β (g₁ : Matrix (Fin 2) (Fin 2) D.Fq) =
        D.psModel β α (g₁ : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β) →
      (intertwiner D α β * D.psModel α β (g₂ : Matrix (Fin 2) (Fin 2) D.Fq) =
        D.psModel β α (g₂ : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β) →
      intertwiner D α β * D.psModel α β ((g₁ * g₂ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) =
        D.psModel β α ((g₁ * g₂ : D.G) : Matrix (Fin 2) (Fin 2) D.Fq) * intertwiner D α β := by
    intro g₁ g₂ h₁ h₂
    rw [psModel_mul, psModel_mul]
    calc intertwiner D α β * (D.psModel α β g₁ * D.psModel α β g₂)
        = (intertwiner D α β * D.psModel α β g₁) * D.psModel α β g₂ := (Matrix.mul_assoc _ _ _).symm
      _ = (D.psModel β α g₁ * intertwiner D α β) * D.psModel α β g₂ := by rw [h₁]
      _ = D.psModel β α g₁ * (intertwiner D α β * D.psModel α β g₂) := Matrix.mul_assoc _ _ _
      _ = D.psModel β α g₁ * (D.psModel β α g₂ * intertwiner D α β) := by rw [h₂]
      _ = (D.psModel β α g₁ * D.psModel β α g₂) * intertwiner D α β := (Matrix.mul_assoc _ _ _).symm
  let a := (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 0
  let b := (g : Matrix (Fin 2) (Fin 2) D.Fq) 0 1
  let c := (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) D.Fq) 1 1
  let det := (g : Matrix (Fin 2) (Fin 2) D.Fq).det
  have hdet_ne : det ≠ 0 := gl_det_ne_zero D g
  by_cases hc : c = 0
  · have had : a * d ≠ 0 := by
      have hdet' : det = a * d := by
        simp [det, Matrix.det_fin_two, a, c, d, hc]
      rwa [← hdet']
    have ha : a ≠ 0 := (mul_ne_zero_iff.mp had).1
    have hd : d ≠ 0 := (mul_ne_zero_iff.mp had).2
    have hfac : g = uMat D (b / d) * tMat D (Units.mk0 a ha) (Units.mk0 d hd) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [uMat, tMat, Matrix.mul_apply, Fin.sum_univ_two, a, b, c, d, hc, div_mul_cancel₀ _ hd]
    rw [hfac]
    exact hmul _ _ (intertwiner_comm_uMat D α β _) (intertwiner_comm_tMat D α β _ _)
  · have hd'_ne : -det / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hdet_ne) hc
    have hfac1 : (uMat D (d / (-det / c)) * tMat D (Units.mk0 c hc) (Units.mk0 (-det / c) hd'_ne) :
        Matrix (Fin 2) (Fin 2) D.Fq) = !![c, d; 0, -det / c] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [uMat, tMat, Matrix.mul_apply, Fin.sum_univ_two, div_mul_cancel₀ _ hd'_ne]
    have hfac2 : (uMat D (a / c) * wMat D : Matrix (Fin 2) (Fin 2) D.Fq) = !![a / c, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [uMat, wMat, Matrix.mul_apply, Fin.sum_univ_two]
    have hfac : g = uMat D (a / c) * wMat D * uMat D (d / (-det / c)) *
        tMat D (Units.mk0 c hc) (Units.mk0 (-det / c) hd'_ne) := by
      apply Units.ext
      rw [mul_assoc (uMat D (a / c) * wMat D)]
      push_cast
      rw [hfac1, hfac2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, a, c, d]
      · exact (div_mul_cancel₀ a hc).symm
      · dsimp [det]
        rw [Matrix.det_fin_two]
        change b = a / c * d + -(a * d - b * c) / c
        field_simp [hc]; ring
    rw [hfac]
    exact hmul _ _
      (hmul _ _ (hmul _ _ (intertwiner_comm_uMat D α β _) (intertwiner_comm_wMat D α β))
        (intertwiner_comm_uMat D α β _))
      (intertwiner_comm_tMat D α β _ _)

lemma psModel_repEquiv_iff (α β γ δ : D.Lab) :
    RepEquiv (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))
        (fun g : D.G => D.psModel γ δ (g : Matrix (Fin 2) (Fin 2) D.Fq)) ↔
      (α = γ ∧ β = δ) ∨ (α = δ ∧ β = γ) := by
  constructor
  · rintro ⟨A, B, hAB, hBA, hcomm⟩
    have htr : ∀ a : D.Fqˣ, (a : D.Fq) ≠ 1 →
        (D.psModel α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace =
          (D.psModel γ δ (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace := by
      intro a _
      have hc := hcomm (dMat D a) (Set.mem_univ _)
      calc (D.psModel α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace
          = ((B * A) * D.psModel α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace := by
              rw [hBA, one_mul]
        _ = (B * (A * D.psModel α β (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq))).trace := by
              rw [Matrix.mul_assoc]
        _ = (B * (D.psModel γ δ (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq) * A)).trace := by
              rw [hc]
        _ = ((B * D.psModel γ δ (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)) * A).trace := by
              rw [Matrix.mul_assoc]
        _ = (A * (B * D.psModel γ δ (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq))).trace :=
              Matrix.trace_mul_comm _ _
        _ = ((A * B) * D.psModel γ δ (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace := by
              rw [Matrix.mul_assoc]
        _ = (D.psModel γ δ (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace := by
              rw [hAB, one_mul]
    have htr_val : ∀ (μ ν : D.Lab) (a : D.Fqˣ), (a : D.Fq) ≠ 1 →
        (D.psModel μ ν (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq)).trace =
          D.chi μ (a : D.Fq) + D.chi ν (a : D.Fq) := by
      intro μ ν a ha1
      change ∑ i : Option D.Fq, D.psModel μ ν (dMat D a : Matrix (Fin 2) (Fin 2) D.Fq) i i = _
      rw [Fintype.sum_option]
      simp_rw [psModel_eq_ite, mobius_dMat, cocycle_dMat]
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single (0 : D.Fq)]
      · simp
      · intro x _ hx0
        have hne : x ≠ (a : D.Fq) * x := by
          intro heq
          have hmul : ((a : D.Fq) - 1) * x = 0 := by linear_combination -heq
          exact ((mul_eq_zero.mp hmul).resolve_right hx0) |> fun hz => ha1 (sub_eq_zero.mp hz)
        simp [hne]
      · intro hmem; exact absurd (Finset.mem_univ 0) hmem
    apply chi_pair_eq_imp D
    intro a
    by_cases ha1 : (a : D.Fq) = 1
    · simp [ha1]
    · have h1 := htr a ha1
      rwa [htr_val α β a ha1, htr_val γ δ a ha1] at h1
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨1, 1, mul_one 1, mul_one 1, fun _ _ => by simp⟩
    · by_cases hαβ : α = β
      · subst hαβ
        exact ⟨1, 1, mul_one 1, mul_one 1, fun _ _ => by simp⟩
      · have hq_ne : (D.q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := D.one_lt_q; omega)
        refine ⟨intertwiner D α β, ((D.q : ℂ)⁻¹) • intertwiner D β α, ?_, ?_, ?_⟩
        · rw [Matrix.mul_smul, intertwiner_mul D β α (Ne.symm hαβ), smul_smul, inv_mul_cancel₀ hq_ne,
            one_smul]
        · rw [Matrix.smul_mul, intertwiner_mul D α β hαβ, smul_smul, inv_mul_cancel₀ hq_ne,
            one_smul]
        · intro g _
          exact intertwiner_comm D α β g

end Equivalence

end GL2QFT_Lemma65_Aux

theorem solution (D : GL2QFT.FieldData) :
    (∀ α β : D.Lab, α ≠ β →
      GL2QFT.IsIrreducibleRep (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))) ∧
    (∀ α : D.Lab,
      let I := fun g : D.G => D.psModel α α (g : Matrix (Fin 2) (Fin 2) D.Fq)
      let v := D.detVec α
      (∀ g : D.G, ∃ c : ℂ, (I g).mulVec v = c • v) ∧
      (∀ (g : D.G) (u : Option D.Fq → ℂ), dotProduct (star v) u = 0 →
        dotProduct (star v) ((I g).mulVec u) = 0) ∧
      (∀ W : Submodule ℂ (Option D.Fq → ℂ), (∀ u ∈ W, dotProduct (star v) u = 0) →
        GL2QFT.IsInvariantSubspace I W →
        W = ⊥ ∨ ∀ u : Option D.Fq → ℂ, dotProduct (star v) u = 0 → u ∈ W)) ∧
    (∀ α β γ δ : D.Lab,
      GL2QFT.RepEquiv (fun g : D.G => D.psModel α β (g : Matrix (Fin 2) (Fin 2) D.Fq))
          (fun g : D.G => D.psModel γ δ (g : Matrix (Fin 2) (Fin 2) D.Fq)) ↔
        (α = γ ∧ β = δ) ∨ (α = δ ∧ β = γ)) := by
  refine ⟨fun α β h => GL2QFT_Lemma65_Aux.psModel_irred D α β h, fun α => ?_,
    fun α β γ δ => GL2QFT_Lemma65_Aux.psModel_repEquiv_iff D α β γ δ⟩
  exact ⟨fun g => ⟨_, GL2QFT_Lemma65_Aux.detVec_eig D α g⟩,
    fun g u hu => GL2QFT_Lemma65_Aux.detVec_orthog_inv D α g u hu,
    GL2QFT_Lemma65_Aux.steinberg_irred D α⟩
