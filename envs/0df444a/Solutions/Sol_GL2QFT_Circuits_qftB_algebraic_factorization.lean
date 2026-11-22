-- Prove2me | solution 1 for GL2QFT.Circuits.qftB_algebraic_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T05:28:21.475848+00:00
-- url     : https://prove2.me/submissions/b04a1ad7-aa74-4a74-8f29-d4306f199aad

import Definitions.Def_GL2QFT_Circuits_Combinators

open Classical

noncomputable section

namespace GL2QFT_QftB_Aux

open GL2QFT GL2QFT.Circuits GL2QFT.FieldData
open scoped ComplexConjugate

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
  have hsq : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
    zify [Nat.le_of_lt hq, show 1 ≤ D.q ^ 2 by nlinarith]
    ring
  rw [hsq, Nat.mul_div_cancel _ (by omega)]

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

lemma gen_pow_dlogLab (a : D.Fqˣ) :
    D.gen ^ (D.dlogLab (a : D.Fq)).val = (a : D.Fq) := by
  change D.gen ^ ((D.dlog (a : D.Fq) : ZMod (D.q - 1)).val) = (a : D.Fq)
  rw [ZMod.val_natCast]
  have hpow : (uGen D) ^ (D.dlog (a : D.Fq) % (D.q - 1)) = (uGen D) ^ D.dlog (a : D.Fq) := by
    rw [← orderOf_uGen D]
    exact pow_mod_orderOf (uGen D) (D.dlog (a : D.Fq))
  have hval := congrArg Units.val hpow
  dsimp [uGen] at hval
  rw [hval, gen_pow_dlog D a.ne_zero]

def labEquivUnits : D.Lab ≃ D.Fqˣ := by
  let φ : D.Lab → D.Fqˣ := fun k => (uGen D) ^ k.val
  have hinj : Function.Injective φ := by
    intro i j hij
    have hmod : i.val ≡ j.val [MOD orderOf (uGen D)] := pow_eq_pow_iff_modEq.mp hij
    rw [orderOf_uGen D] at hmod
    exact ZMod.val_injective _ (Nat.ModEq.eq_of_lt_of_lt hmod (ZMod.val_lt i) (ZMod.val_lt j))
  have hcard : Fintype.card D.Lab = Fintype.card D.Fqˣ := by
    rw [ZMod.card, card_Fq_units]
  exact Equiv.ofBijective φ ((Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩)

lemma labEquivUnits_apply_val (k : D.Lab) :
    ((labEquivUnits D k : D.Fqˣ) : D.Fq) = D.gen ^ k.val := by
  change (((uGen D) ^ k.val : D.Fqˣ) : D.Fq) = D.gen ^ k.val
  rw [Units.val_pow_eq_pow_val]
  rfl

lemma dlog_one : D.dlog 1 = 0 := by
  unfold dlog
  have h : ∃ n : ℕ, D.gen ^ n = 1 := ⟨0, pow_zero _⟩
  rw [dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h (pow_zero _))

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

lemma psi_zero : D.psi 0 = 1 := by
  simp [FieldData.psi, map_zero, ZMod.val_zero]

end FieldAndChars

section MatrixFactorization

variable (D : FieldData)

def fbOutPermInv : D.BOutLabel → D.Lab × D.Lab × Option D.Lab
  | ⟨.inl ab, _, _⟩ => (ab.1, ab.2, none)
  | ⟨.inr γ, δ, δ'⟩ =>
    let δ₀ : D.Lab := δ
    let δ₀' : D.Lab := δ'
    (δ₀', γ - δ₀', some (δ₀' - δ₀))

lemma fbOutPerm_left_inv (p : D.Lab × D.Lab × Option D.Lab) :
    fbOutPermInv D (fbOutPerm D p) = p := by
  rcases p with ⟨α, β, _ | η⟩ <;> simp [fbOutPerm, fbOutPermInv]

lemma fbOutPerm_right_inv (r : D.BOutLabel) :
    fbOutPerm D (fbOutPermInv D r) = r := by
  rcases r with ⟨⟨α, β⟩ | γ, i, j⟩
  · cases i; cases j; rfl
  · dsimp [BBas] at i j
    dsimp [fbOutPermInv, fbOutPerm]
    simp
    rfl

lemma permMat_fbOutPerm_mul
    (M : Matrix (D.Lab × D.Lab × Option D.Lab) D.BElt ℂ)
    (r : D.BOutLabel) (x : D.BElt) :
    (permMat (fbOutPerm D) * M) r x = M (fbOutPermInv D r) x := by
  simp only [Matrix.mul_apply, permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (fbOutPermInv D r)]
  · simp [fbOutPerm_right_inv D r]
  · intro p _ hp
    have hne : r ≠ fbOutPerm D p := by
      intro h
      apply hp
      rw [h, fbOutPerm_left_inv D p]
    simp [hne]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma frameMatRight_mul_aux {A B C : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : Matrix A A ℂ) (N : Matrix B B ℂ)
    (a' : A) (b' : B) (c' : C) (a : A) (b : B) (c : C) :
    (frameMatRight (B := C) (frameMatRight (B := B) M) *
      frameMatRight (B := C) (frameMat (A := A) N))
      ((a', b'), c') ((a, b), c) =
    if c' = c then M a' a * N b' b else 0 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, frameMatRight, frameMat, Matrix.of_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b']
    · rw [Finset.sum_eq_single c]
      · by_cases hc : c' = c <;> simp [hc]
      · intro z _ hz; simp [hz]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · intro y _ hy
      rw [Finset.sum_eq_zero]
      intro z _
      simp [Ne.symm hy]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · intro x _ hx
    rw [Finset.sum_eq_zero]; intro y _
    rw [Finset.sum_eq_zero]; intro z _
    simp [hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma midMat_apply (a' d' η? : Option D.Lab) (a d : Option D.Lab) (b : D.Fq) :
    (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
      frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) *
      frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D))
      ((a', d'), η?) ((a, d), b) =
    phiFmult D a' a * phiFmult D d' d * (phiFmult D * phiLog D * phiFplus D) η? b := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single d]
    · rw [Finset.sum_eq_single η?]
      · rw [frameMatRight_mul_aux]
        simp [frameMat]
      · intro z _ hz
        rw [frameMatRight_mul_aux]
        simp [Ne.symm hz]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · intro y _ hy
      rw [Finset.sum_eq_zero]; intro z _
      simp [frameMat, hy]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  · intro x _ hx
    rw [Finset.sum_eq_zero]; intro y _
    rw [Finset.sum_eq_zero]; intro z _
    simp [frameMat, hx]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma phiLog_mul_phiFplus_none (b : D.Fq) :
    (phiLog D * phiFplus D) none b = FieldData.isqrt D.q := by
  simp only [Matrix.mul_apply, phiLog, phiFplus, Matrix.of_apply]
  rw [Finset.sum_eq_single (0 : D.Fq)]
  · simp [psi_zero D]
  · intro y _ hy
    simp [hy]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma phiLog_mul_phiFplus_some (k : D.Lab) (b : D.Fq) :
    (phiLog D * phiFplus D) (some k) b = FieldData.isqrt D.q * D.psi (b * D.gen ^ k.val) := by
  simp only [Matrix.mul_apply, phiLog, phiFplus, Matrix.of_apply]
  rw [Finset.sum_eq_single (D.gen ^ k.val)]
  · simp [pow_ne_zero k.val (gen_ne_zero D)]
  · intro y _ hy
    simp [Ne.symm hy]
  · intro hm; exact absurd (Finset.mem_univ _) hm

lemma phiBlock_none (b : D.Fq) :
    (phiFmult D * phiLog D * phiFplus D) none b = FieldData.isqrt D.q := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_option]
  have hnone : phiFmult D none none = 1 := by simp [phiFmult]
  have hsome : ∀ k : D.Lab, phiFmult D none (some k) = 0 := fun k => by simp [phiFmult]
  simp [hnone, hsome, phiLog_mul_phiFplus_none]

lemma phiBlock_some (η : D.Lab) (b : D.Fq) :
    (phiFmult D * phiLog D * phiFplus D) (some η) b =
      FieldData.isqrt D.q * FieldData.isqrt (D.q - 1) *
        ∑ u : D.Fqˣ, D.chi η (u : D.Fq) * D.psi (b * (u : D.Fq)) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_option]
  have hnone : phiFmult D (some η) none = 0 := by simp [phiFmult]
  rw [hnone, zero_mul, zero_add]
  have hsum_k : (∑ k : D.Lab, phiFmult D (some η) (some k) * (phiLog D * phiFplus D) (some k) b) =
      FieldData.isqrt D.q * FieldData.isqrt (D.q - 1) *
        ∑ k : D.Lab, D.chi η (D.gen ^ k.val) * D.psi (b * D.gen ^ k.val) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [phiFmult, Matrix.of_apply, phiLog_mul_phiFplus_some]
    ring
  rw [hsum_k]
  congr 1
  refine Fintype.sum_equiv (labEquivUnits D) _ _ fun k => ?_
  rw [labEquivUnits_apply_val]

lemma star_isqrt (x : ℝ) : star (FieldData.isqrt x) = FieldData.isqrt x := by
  simp [FieldData.isqrt]

lemma sqrt_inv_one :
    ((Real.sqrt ((1 : ℝ) / (((D.q - 1 : ℕ) : ℝ) * (((D.q - 1 : ℕ) : ℝ) * (D.q : ℝ))))) : ℂ) =
      FieldData.isqrt D.q * FieldData.isqrt (D.q - 1) * FieldData.isqrt (D.q - 1) := by
  have hq : (0 : ℝ) < D.q := Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one D.one_lt_q)
  have hq1 : (0 : ℝ) < ((D.q - 1 : ℕ) : ℝ) := by
    have := D.one_lt_q
    exact Nat.cast_pos.mpr (by omega)
  have hsub : ((D.q - 1 : ℕ) : ℝ) = (D.q : ℝ) - 1 := by
    rw [Nat.cast_sub D.one_lt_q.le]
    norm_num
  have hreal : Real.sqrt ((1 : ℝ) / (((D.q - 1 : ℕ) : ℝ) * (((D.q - 1 : ℕ) : ℝ) * (D.q : ℝ)))) =
      (Real.sqrt (D.q : ℝ))⁻¹ * (Real.sqrt ((D.q : ℝ) - 1))⁻¹ *
        (Real.sqrt ((D.q : ℝ) - 1))⁻¹ := by
    have hmul : (1 : ℝ) / (((D.q - 1 : ℕ) : ℝ) * (((D.q - 1 : ℕ) : ℝ) * (D.q : ℝ))) =
        (D.q : ℝ)⁻¹ * (((D.q - 1 : ℕ) : ℝ)⁻¹ * ((D.q - 1 : ℕ) : ℝ)⁻¹) := by
      field_simp [hq.ne', hq1.ne']
    rw [hmul, Real.sqrt_mul (inv_nonneg.mpr hq.le),
      Real.sqrt_mul (inv_nonneg.mpr hq1.le), Real.sqrt_inv, Real.sqrt_inv, hsub]
    ring
  simpa [FieldData.isqrt] using congrArg (fun x : ℝ => (x : ℂ)) hreal

lemma sqrt_inv_qm1 :
    ((Real.sqrt (((D.q - 1 : ℕ) : ℝ) /
        (((D.q - 1 : ℕ) : ℝ) * (((D.q - 1 : ℕ) : ℝ) * (D.q : ℝ))))) : ℂ) =
      FieldData.isqrt D.q * FieldData.isqrt (D.q - 1) := by
  have hq : (0 : ℝ) < D.q := Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one D.one_lt_q)
  have hq1 : (0 : ℝ) < ((D.q - 1 : ℕ) : ℝ) := by
    have := D.one_lt_q
    exact Nat.cast_pos.mpr (by omega)
  have hsub : ((D.q - 1 : ℕ) : ℝ) = (D.q : ℝ) - 1 := by
    rw [Nat.cast_sub D.one_lt_q.le]
    norm_num
  have hreal : Real.sqrt (((D.q - 1 : ℕ) : ℝ) /
        (((D.q - 1 : ℕ) : ℝ) * (((D.q - 1 : ℕ) : ℝ) * (D.q : ℝ)))) =
      (Real.sqrt (D.q : ℝ))⁻¹ * (Real.sqrt ((D.q : ℝ) - 1))⁻¹ := by
    have hmul : ((D.q - 1 : ℕ) : ℝ) /
        (((D.q - 1 : ℕ) : ℝ) * (((D.q - 1 : ℕ) : ℝ) * (D.q : ℝ))) =
        (D.q : ℝ)⁻¹ * ((D.q - 1 : ℕ) : ℝ)⁻¹ := by
      field_simp [hq.ne', hq1.ne']
    rw [hmul, Real.sqrt_mul (inv_nonneg.mpr hq.le), Real.sqrt_inv, Real.sqrt_inv, hsub]
  simpa [FieldData.isqrt] using congrArg (fun x : ℝ => (x : ℂ)) hreal

lemma card_BElt :
    Fintype.card D.BElt = (D.q - 1) * ((D.q - 1) * D.q) := by
  change Fintype.card (D.Fqˣ × D.Fqˣ × D.Fq) = _
  rw [Fintype.card_prod, Fintype.card_prod, card_Fq_units, card_Fq]

lemma qftB_eq_rhs_entry (r : D.BOutLabel) (x : D.BElt) :
    D.qftB r x =
      (permMat (fbOutPerm D) * Matrix.submatrix
        (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
         frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) *
         frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D))
        (bMidInj D) (bInEmb D)) r x := by
  rcases x with ⟨a, d, b⟩
  rw [permMat_fbOutPerm_mul]
  simp only [Matrix.submatrix_apply, bInEmb]
  rcases r with ⟨⟨α, β⟩ | γ, i, j⟩
  · -- Case 1: 1-dimensional character χ_{α,β}
    dsimp [fbOutPermInv, bMidInj]
    rw [midMat_apply, phiBlock_none]
    have ha : phiFmult D (some α) (some (D.dlogLab (a : D.Fq))) =
        FieldData.isqrt (D.q - 1) * D.chi α (a : D.Fq) := by
      simp [phiFmult, gen_pow_dlogLab]
    have hd : phiFmult D (some β) (some (D.dlogLab (d : D.Fq))) =
        FieldData.isqrt (D.q - 1) * D.chi β (d : D.Fq) := by
      simp [phiFmult, gen_pow_dlogLab]
    rw [ha, hd]
    change (Real.sqrt ((Fintype.card (D.BBas (.inl (α, β))) : ℝ) / (Fintype.card D.BElt : ℝ)) : ℂ) *
        (D.chi α ((D.bmat (a, d, b)) 0 0) * D.chi β ((D.bmat (a, d, b)) 1 1)) = _
    have hcard_bas : Fintype.card (D.BBas (.inl (α, β))) = 1 := by
      change Fintype.card Unit = 1; simp
    rw [hcard_bas, card_BElt]
    push_cast
    rw [sqrt_inv_one]
    simp only [bmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  · -- Case 2: (q-1)-dimensional representation ρ_γ
    dsimp [BBas] at i j
    dsimp [fbOutPermInv, bMidInj]
    rw [midMat_apply, phiBlock_some]
    have ha : phiFmult D (some j) (some (D.dlogLab (a : D.Fq))) =
        FieldData.isqrt (D.q - 1) * D.chi j (a : D.Fq) := by
      simp [phiFmult, gen_pow_dlogLab]
    have hd : phiFmult D (some (γ - j)) (some (D.dlogLab (d : D.Fq))) =
        FieldData.isqrt (D.q - 1) * D.chi (γ - j) (d : D.Fq) := by
      simp [phiFmult, gen_pow_dlogLab]
    rw [ha, hd]
    change (Real.sqrt ((Fintype.card (D.BBas (.inr γ)) : ℝ) / (Fintype.card D.BElt : ℝ)) : ℂ) *
        matEntry (D.borelModel γ ((D.bmat (a, d, b)) 0 0) ((D.bmat (a, d, b)) 0 1)
          ((D.bmat (a, d, b)) 1 1)) (D.multVec i) (D.multVec j) = _
    have hcard_bas : Fintype.card (D.BBas (.inr γ)) = D.q - 1 := by
      change Fintype.card D.Lab = D.q - 1; rw [ZMod.card]
    rw [hcard_bas, card_BElt]
    push_cast
    rw [sqrt_inv_qm1]
    simp only [bmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hmat : matEntry (D.borelModel γ (a : D.Fq) (b * (d : D.Fq)) (d : D.Fq))
        (D.multVec i) (D.multVec j) =
        FieldData.isqrt (D.q - 1) * FieldData.isqrt (D.q - 1) *
          D.chi j (a : D.Fq) * D.chi (γ - j) (d : D.Fq) *
          ∑ u : D.Fqˣ, D.chi (j - i) (u : D.Fq) * D.psi (b * (u : D.Fq)) := by
      unfold matEntry borelModel multVec
      rw [Finset.sum_comm]
      have hrow : ∀ col : D.Fqˣ,
          (∑ row : D.Fqˣ, star (FieldData.isqrt (D.q - 1) * D.chi i (row : D.Fq)) *
            (if (row : D.Fq) = (d : D.Fq) / (a : D.Fq) * (col : D.Fq) then
              D.chi γ (d : D.Fq) * D.psi (b * (d : D.Fq) / (a : D.Fq) * (col : D.Fq)) else 0) *
            (FieldData.isqrt (D.q - 1) * D.chi j (col : D.Fq))) =
          FieldData.isqrt (D.q - 1) * FieldData.isqrt (D.q - 1) *
            (D.chi (-i) ((d : D.Fq) / (a : D.Fq) * (col : D.Fq)) *
              D.chi γ (d : D.Fq) * D.psi (b * (d : D.Fq) / (a : D.Fq) * (col : D.Fq)) *
              D.chi j (col : D.Fq)) := by
        intro col
        rw [Finset.sum_eq_single (d * a⁻¹ * col)]
        · have hval : ((d * a⁻¹ * col : D.Fqˣ) : D.Fq) = (d : D.Fq) / (a : D.Fq) * (col : D.Fq) := by
            simp [div_eq_mul_inv]
          rw [hval, if_pos rfl, star_mul', star_isqrt, star_chi D i (by
            rw [← hval]; exact Units.ne_zero _)]
          ring
        · intro row _ hne
          have hneq : (row : D.Fq) ≠ (d : D.Fq) / (a : D.Fq) * (col : D.Fq) := by
            intro h
            apply hne
            apply Units.ext
            simpa [div_eq_mul_inv] using h
          rw [if_neg hneq]
          ring
        · intro hm; exact absurd (Finset.mem_univ _) hm
      change (∑ col : D.Fqˣ, ∑ row : D.Fqˣ,
          star (FieldData.isqrt (D.q - 1) * D.chi i (row : D.Fq)) *
            (if (row : D.Fq) = (d : D.Fq) / (a : D.Fq) * (col : D.Fq) then
              D.chi γ (d : D.Fq) * D.psi (b * (d : D.Fq) / (a : D.Fq) * (col : D.Fq)) else 0) *
            (FieldData.isqrt (D.q - 1) * D.chi j (col : D.Fq))) = _
      rw [Finset.sum_congr rfl fun col _ => hrow col]
      rw [← Finset.mul_sum]
      conv_rhs => rw [mul_assoc, mul_assoc]
      congr 1
      rw [← Equiv.sum_comp (Equiv.mulLeft (a * d⁻¹))]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hmul_val : ((Equiv.mulLeft (a * d⁻¹) u : D.Fqˣ) : D.Fq) =
          (a : D.Fq) * (d : D.Fq)⁻¹ * (u : D.Fq) := by
        simp [Equiv.coe_mulLeft, mul_assoc]
      have harg1 : (d : D.Fq) / (a : D.Fq) * ((Equiv.mulLeft (a * d⁻¹) u : D.Fqˣ) : D.Fq) =
          (u : D.Fq) := by
        rw [hmul_val]
        field_simp [a.ne_zero, d.ne_zero]
      have harg2 : b * (d : D.Fq) / (a : D.Fq) * ((Equiv.mulLeft (a * d⁻¹) u : D.Fqˣ) : D.Fq) =
          b * (u : D.Fq) := by
        rw [hmul_val]
        field_simp [a.ne_zero, d.ne_zero]
      have hchi_j : D.chi j ((Equiv.mulLeft (a * d⁻¹) u : D.Fqˣ) : D.Fq) =
          D.chi j (a : D.Fq) * D.chi (-j) (d : D.Fq) * D.chi j (u : D.Fq) := by
        rw [hmul_val]
        rw [chi_mul D j (mul_ne_zero a.ne_zero (inv_ne_zero d.ne_zero)) u.ne_zero,
          chi_mul D j a.ne_zero (inv_ne_zero d.ne_zero), chi_inv D j d.ne_zero]
      have hchi_d : D.chi γ (d : D.Fq) * D.chi (-j) (d : D.Fq) = D.chi (γ - j) (d : D.Fq) := by
        rw [← chi_add_label D γ (-j) d.ne_zero, ← sub_eq_add_neg]
      have hchi_u : D.chi (-i) (u : D.Fq) * D.chi j (u : D.Fq) = D.chi (j - i) (u : D.Fq) := by
        rw [← chi_add_label D (-i) j u.ne_zero, neg_add_eq_sub]
      rw [harg1, harg2, hchi_j]
      calc D.chi (-i) (u : D.Fq) * D.chi γ (d : D.Fq) * D.psi (b * (u : D.Fq)) *
            (D.chi j (a : D.Fq) * D.chi (-j) (d : D.Fq) * D.chi j (u : D.Fq))
          = D.chi j (a : D.Fq) * (D.chi γ (d : D.Fq) * D.chi (-j) (d : D.Fq)) *
              ((D.chi (-i) (u : D.Fq) * D.chi j (u : D.Fq)) * D.psi (b * (u : D.Fq))) := by ring
        _ = D.chi j (a : D.Fq) * D.chi (γ - j) (d : D.Fq) *
              (D.chi (j - i) (u : D.Fq) * D.psi (b * (u : D.Fq))) := by rw [hchi_d, hchi_u]
        _ = _ := by ring
    rw [hmat]
    ring

end MatrixFactorization

end GL2QFT_QftB_Aux

open GL2QFT GL2QFT.Circuits QAlgorithms QAlgorithms.Complexity

theorem solution (D : FieldData) : D.qftB =
    permMat (fbOutPerm D) * Matrix.submatrix
      (frameMatRight (B := Option D.Lab) (frameMatRight (B := Option D.Lab) (phiFmult D)) *
       frameMatRight (B := Option D.Lab) (frameMat (A := Option D.Lab) (phiFmult D)) *
       frameMat (A := Option D.Lab × Option D.Lab) (phiFmult D * phiLog D * phiFplus D))
      (bMidInj D) (bInEmb D) := by
  ext r x
  exact GL2QFT_QftB_Aux.qftB_eq_rhs_entry D r x
