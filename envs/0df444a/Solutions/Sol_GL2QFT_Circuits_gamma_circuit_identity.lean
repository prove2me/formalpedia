-- Prove2me | solution 1 for GL2QFT.Circuits.gamma_circuit_identity
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:23:07.704817+00:00
-- url     : https://prove2.me/submissions/74556cec-e6b4-41de-9aa0-61ba40ccd050

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical

noncomputable section

namespace GL2QFT_Circuits_GammaIdentity_Aux

open GL2QFT FieldData Circuits
open scoped ComplexConjugate Matrix

section FieldHelpers

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

lemma dlog_gen_pow (k : ℕ) : D.dlog (D.gen ^ k) ≡ k [MOD (D.q - 1)] := by
  have hne : D.gen ^ k ≠ 0 := pow_ne_zero k (gen_ne_zero D)
  have h1 : (uGen D) ^ D.dlog (D.gen ^ k) = (uGen D) ^ k := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    dsimp [uGen]
    exact gen_pow_dlog D hne
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

lemma chi_gen_pow_symm (α d : D.Lab) :
    D.chi α (D.gen ^ d.val) = D.chi d (D.gen ^ α.val) := by
  have hm : 0 < D.q - 1 := by have := D.one_lt_q; omega
  have aux : ∀ a b : D.Lab,
      D.chi a (D.gen ^ b.val) =
      Complex.exp (2 * Real.pi * Complex.I * ((a.val * b.val : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ)) := by
    intro a b
    unfold chi
    rw [if_neg (pow_ne_zero b.val (gen_ne_zero D))]
    have hmod : a.val * D.dlog (D.gen ^ b.val) ≡ a.val * b.val [MOD (D.q - 1)] :=
      Nat.ModEq.mul_left a.val (dlog_gen_pow D b.val)
    exact exp_mod (D.q - 1) hm _ _ hmod
  rw [aux α d, aux d α, mul_comm α.val d.val]

@[simp]
lemma psi_zero : D.psi 0 = 1 := by
  simp [psi]

lemma isqrt_sq_nat (n : ℕ) :
    FieldData.isqrt (n : ℝ) * FieldData.isqrt (n : ℝ) = ((n : ℂ)⁻¹) := by
  unfold FieldData.isqrt
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n),
    Complex.ofReal_inv, Complex.ofReal_natCast]

lemma isqrt_q_sub_one_sq :
    FieldData.isqrt ((D.q : ℝ) - 1) * FieldData.isqrt ((D.q : ℝ) - 1) =
      (((D.q - 1 : ℕ) : ℂ)⁻¹) := by
  have hcast : (D.q : ℝ) - 1 = ((D.q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (le_of_lt D.one_lt_q), Nat.cast_one]
  rw [hcast, isqrt_sq_nat]

def uGenEquiv : D.Lab ≃ D.Fqˣ := by
  refine Equiv.ofBijective (fun d : D.Lab => (uGen D) ^ d.val) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro d₁ d₂ h
    rw [pow_eq_pow_iff_modEq, orderOf_uGen] at h
    change d₁.val % (D.q - 1) = d₂.val % (D.q - 1) at h
    rw [Nat.mod_eq_of_lt (ZMod.val_lt d₁), Nat.mod_eq_of_lt (ZMod.val_lt d₂)] at h
    exact ZMod.val_injective (D.q - 1) h
  · rw [ZMod.card, card_Fq_units]

def fExp (x : Option D.Lab) : D.Fq :=
  match x with
  | none => 0
  | some d => D.gen ^ d.val

def expEquiv : Option D.Lab ≃ D.Fq := by
  refine Equiv.ofBijective (fExp D) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro x₁ x₂ h
    cases x₁ with
    | none =>
      cases x₂ with
      | none => rfl
      | some d₂ =>
        exfalso
        exact pow_ne_zero d₂.val (gen_ne_zero D) h.symm
    | some d₁ =>
      cases x₂ with
      | none =>
        exfalso
        exact pow_ne_zero d₁.val (gen_ne_zero D) h
      | some d₂ =>
        have hu : (uGen D) ^ d₁.val = (uGen D) ^ d₂.val := by
          apply Units.ext
          simpa [uGen, Units.val_pow_eq_pow_val, fExp] using h
        exact congrArg some ((uGenEquiv D).injective hu)
  · have hq : 1 < D.q := D.one_lt_q
    rw [Fintype.card_option, ZMod.card, card_Fq]
    omega

end FieldHelpers

section GammaCircuit

variable (D : FieldData)

lemma gauss_eq_sum_univ (α : D.Lab) :
    D.gauss α = ∑ u : D.Fq, D.chi α u * D.psi (1 * u) := by
  unfold gauss gaussG
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : u = 0
  · simp [hu]
  · simp [hu]

lemma phiExp_mul_phiFmult (α : D.Lab) (y : D.Fq) :
    (phiExp D * phiFmult D) y (some α) =
      FieldData.isqrt ((D.q : ℝ) - 1) * D.chi α y := by
  rw [Matrix.mul_apply, Fintype.sum_option]
  have h0 : phiExp D y none * phiFmult D none (some α) = 0 := by simp [phiFmult]
  rw [h0, zero_add]
  have hterm : ∀ d : D.Lab,
      phiExp D y (some d) * phiFmult D (some d) (some α) =
        if expEquiv D (some d) = y then
          FieldData.isqrt ((D.q : ℝ) - 1) * D.chi α y else 0 := by
    intro d
    simp only [phiExp, phiFmult, Matrix.of_apply, expEquiv, Equiv.ofBijective_apply, fExp]
    by_cases hy : D.gen ^ d.val = y
    · subst hy
      simp [chi_gen_pow_symm]
    · have hy' : y ≠ D.gen ^ d.val := Ne.symm hy
      simp [hy, hy']
  simp_rw [hterm]
  by_cases hy : y = 0
  · subst hy
    have hne : ∀ d : D.Lab, expEquiv D (some d) ≠ 0 := fun d =>
      pow_ne_zero d.val (gen_ne_zero D)
    simp [hne]
  · obtain ⟨x, hx⟩ := (expEquiv D).surjective y
    cases x with
    | none =>
      exfalso
      exact hy (by simpa [expEquiv, fExp] using hx.symm)
    | some d₀ =>
      have hiff : ∀ d : D.Lab, expEquiv D (some d) = y ↔ d = d₀ := by
        intro d
        rw [← hx, (expEquiv D).injective.eq_iff]
        simp
      simp [hiff]

lemma phiFplus_mul_phiExp_phiFmult {α : D.Lab} (hα : α ≠ 0) (z : D.Fq) :
    (phiFplus D * (phiExp D * phiFmult D)) z (some α) =
      FieldData.isqrt (D.q : ℝ) * FieldData.isqrt ((D.q : ℝ) - 1) *
        D.gauss α * D.chi (-α) z := by
  rw [Matrix.mul_apply]
  have hterm : ∀ y : D.Fq,
      phiFplus D z y * (phiExp D * phiFmult D) y (some α) =
        (FieldData.isqrt (D.q : ℝ) * FieldData.isqrt ((D.q : ℝ) - 1)) *
          (D.chi α y * D.psi (y * z)) := by
    intro y
    rw [phiFplus, Matrix.of_apply, phiExp_mul_phiFmult]
    ring
  simp_rw [hterm, ← Finset.mul_sum]
  have hsum : ∑ y : D.Fq, D.chi α y * D.psi (y * z) = D.gauss α * D.chi (-α) z := by
    by_cases hz : z = 0
    · subst hz
      simp [sum_chi_eq_zero D hα]
    · have hreidx : ∑ y : D.Fq, D.chi α y * D.psi (y * z) =
          ∑ u : D.Fq, D.chi α (z⁻¹ * u) * D.psi ((z⁻¹ * u) * z) := by
        rw [← Equiv.sum_comp (Equiv.mulLeft₀ z⁻¹ (inv_ne_zero hz))]
        rfl
      rw [hreidx]
      have hsub : ∀ u : D.Fq,
          D.chi α (z⁻¹ * u) * D.psi ((z⁻¹ * u) * z) =
            D.chi (-α) z * (D.chi α u * D.psi (1 * u)) := by
        intro u
        have hmulz : (z⁻¹ * u) * z = 1 * u := by
          rw [mul_comm (z⁻¹ * u) z, ← mul_assoc, mul_inv_cancel₀ hz]
        rw [hmulz]
        by_cases hu : u = 0
        · simp [hu]
        · rw [chi_mul D α (inv_ne_zero hz) hu, chi_inv D α hz]
          ring
      simp_rw [hsub]
      rw [← Finset.mul_sum, ← gauss_eq_sum_univ D α, mul_comm]
  rw [hsum]
  ring

lemma phiLog_mul_phiFplus_phiExp_phiFmult {α : D.Lab} (hα : α ≠ 0) (out : Option D.Lab) :
    (phiLog D * (phiFplus D * (phiExp D * phiFmult D))) out (some α) =
      match out with
      | none => 0
      | some d => FieldData.isqrt (D.q : ℝ) * FieldData.isqrt ((D.q : ℝ) - 1) *
          D.gauss α * D.chi (-α) (D.gen ^ d.val) := by
  rw [Matrix.mul_apply]
  cases out with
  | none =>
    have hterm : ∀ z : D.Fq,
        phiLog D none z * (phiFplus D * (phiExp D * phiFmult D)) z (some α) = 0 := by
      intro z
      rw [phiLog, Matrix.of_apply, phiFplus_mul_phiExp_phiFmult D hα]
      by_cases hz : z = 0
      · subst hz; simp
      · simp [hz]
    simp [hterm]
  | some d =>
    have hne : D.gen ^ d.val ≠ 0 := pow_ne_zero d.val (gen_ne_zero D)
    have hterm : ∀ z : D.Fq,
        phiLog D (some d) z * (phiFplus D * (phiExp D * phiFmult D)) z (some α) =
          if z = D.gen ^ d.val then
            FieldData.isqrt (D.q : ℝ) * FieldData.isqrt ((D.q : ℝ) - 1) *
              D.gauss α * D.chi (-α) (D.gen ^ d.val) else 0 := by
      intro z
      rw [phiLog, Matrix.of_apply, phiFplus_mul_phiExp_phiFmult D hα]
      by_cases hz : z = D.gen ^ d.val
      · subst hz
        simp [hne]
      · have hz' : D.gen ^ d.val ≠ z := Ne.symm hz
        simp [hz, hz']
    simp [hterm]

lemma gamma_circuit_id {α : D.Lab} (hα : α ≠ 0) (c : Option D.Lab) :
    (phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D) c (some α) =
      if c = some α then D.gauss α * FieldData.isqrt D.q else 0 := by
  have hassoc : phiFmult D * phiLog D * phiFplus D * phiExp D * phiFmult D =
      phiFmult D * (phiLog D * (phiFplus D * (phiExp D * phiFmult D))) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, Matrix.mul_apply, Fintype.sum_option]
  have h0 : phiFmult D c none *
      (phiLog D * (phiFplus D * (phiExp D * phiFmult D))) none (some α) = 0 := by
    rw [phiLog_mul_phiFplus_phiExp_phiFmult D hα none, mul_zero]
  rw [h0, zero_add]
  cases c with
  | none =>
    simp [phiFmult]
  | some β =>
    have hq1_pos : 0 < D.q - 1 := by have := D.one_lt_q; omega
    have hq1_ne : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq1_pos.ne'
    have hterm : ∀ d : D.Lab,
        phiFmult D (some β) (some d) *
            (phiLog D * (phiFplus D * (phiExp D * phiFmult D))) (some d) (some α) =
          (D.gauss α * FieldData.isqrt (D.q : ℝ)) * (((D.q - 1 : ℕ) : ℂ)⁻¹) *
            (star (D.chi α (D.gen ^ d.val)) * D.chi β (D.gen ^ d.val)) := by
      intro d
      rw [phiLog_mul_phiFplus_phiExp_phiFmult D hα (some d)]
      simp only [phiFmult, Matrix.of_apply]
      rw [← star_chi D α (pow_ne_zero d.val (gen_ne_zero D))]
      calc (FieldData.isqrt ((D.q : ℝ) - 1) * D.chi β (D.gen ^ d.val)) *
            (FieldData.isqrt (D.q : ℝ) * FieldData.isqrt ((D.q : ℝ) - 1) *
              D.gauss α * star (D.chi α (D.gen ^ d.val)))
          = (D.gauss α * FieldData.isqrt (D.q : ℝ)) *
              (FieldData.isqrt ((D.q : ℝ) - 1) * FieldData.isqrt ((D.q : ℝ) - 1)) *
              (star (D.chi α (D.gen ^ d.val)) * D.chi β (D.gen ^ d.val)) := by ring
        _ = (D.gauss α * FieldData.isqrt (D.q : ℝ)) * (((D.q - 1 : ℕ) : ℂ)⁻¹) *
              (star (D.chi α (D.gen ^ d.val)) * D.chi β (D.gen ^ d.val)) := by
            rw [isqrt_q_sub_one_sq]
    simp_rw [hterm, ← Finset.mul_sum]
    have hsum : ∑ d : D.Lab, star (D.chi α (D.gen ^ d.val)) * D.chi β (D.gen ^ d.val) =
        ∑ x : D.Fqˣ, star (D.chi α (x : D.Fq)) * D.chi β (x : D.Fq) := by
      rw [← Equiv.sum_comp (uGenEquiv D)]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp [uGenEquiv, uGen, Units.val_pow_eq_pow_val]
    rw [hsum, sum_chi_units_orthog]
    by_cases hβα : β = α
    · subst hβα
      simp only [↓reduceIte, mul_assoc, inv_mul_cancel₀ hq1_ne, mul_one]
    · have hαβ : α ≠ β := Ne.symm hβα
      simp [hβα, hαβ]

end GammaCircuit

end GL2QFT_Circuits_GammaIdentity_Aux

theorem solution (D : GL2QFT.FieldData) (α : D.Lab) (hα : α ≠ 0) (c : Option D.Lab) :
    (GL2QFT.Circuits.phiFmult D * GL2QFT.Circuits.phiLog D * GL2QFT.Circuits.phiFplus D *
      GL2QFT.Circuits.phiExp D * GL2QFT.Circuits.phiFmult D) c (some α) =
      if c = some α then D.gauss α * GL2QFT.FieldData.isqrt D.q else 0 :=
  GL2QFT_Circuits_GammaIdentity_Aux.gamma_circuit_id D hα c
