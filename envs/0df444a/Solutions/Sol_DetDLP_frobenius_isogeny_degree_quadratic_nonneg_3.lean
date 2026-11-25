-- Prove2me | solution 3 for DetDLP.frobenius_isogeny_degree_quadratic_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T18:13:56.368063+00:00
-- url     : https://prove2.me/submissions/70d3e177-7c73-44a6-9ade-4f9888368c88

import Mathlib
import Definitions.Def_DetDLP_FactorBase
import Theorems.Thm_DetDLP_quadratic_form_nonneg_iff_hasse_discriminant

set_option autoImplicit false

open DetDLP
open scoped WeierstrassCurve.Affine

section ShortNFReduction

private lemma zmod_two_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  omega

private lemma zmod_three_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) : (3 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by simpa using h)
  have hle : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
  omega

private lemma equation_variableChange_iff {F : Type*} [Field F] (E : WeierstrassCurve F)
    (C : WeierstrassCurve.VariableChange F) (x' y' : F) :
    (C • E).toAffine.Equation x' y' ↔
      E.toAffine.Equation ((C.u : F) ^ 2 * x' + C.r)
        ((C.u : F) ^ 3 * y' + (C.u : F) ^ 2 * C.s * x' + C.t) := by
  rw [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.Affine.equation_iff]
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, Units.val_inv_eq_inv_val]
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  constructor <;> intro h <;> rw [← sub_eq_zero] at h ⊢
  · rw [← mul_left_inj' (inv_ne_zero (pow_ne_zero 6 hu)), zero_mul, ← h]
    field_simp [hu]
    ring
  · rw [← mul_left_inj' (pow_ne_zero 6 hu), zero_mul, ← h]
    field_simp [hu]
    ring

private noncomputable def ecPointEquivVariableChange {F : Type*} [Field F]
    (E : WeierstrassCurve F) [E.IsElliptic] (C : WeierstrassCurve.VariableChange F) :
    (C • E).toAffine.Point ≃ E.toAffine.Point where
  toFun P :=
    match P with
    | .zero => .zero
    | .some x' y' h' =>
      .some ((C.u : F) ^ 2 * x' + C.r) ((C.u : F) ^ 3 * y' + (C.u : F) ^ 2 * C.s * x' + C.t)
        (E.toAffine.equation_iff_nonsingular.mp
          ((equation_variableChange_iff E C x' y').mp
            (WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h')))
  invFun P :=
    match P with
    | .zero => .zero
    | .some x y h =>
      let x' := (C.u : F)⁻¹ ^ 2 * (x - C.r)
      let y' := (C.u : F)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)
      .some x' y'
        ((C • E).toAffine.equation_iff_nonsingular.mp
          ((equation_variableChange_iff E C x' y').mpr (by
            have hx : (C.u : F) ^ 2 * x' + C.r = x := by
              dsimp [x']
              field_simp [C.u.ne_zero]
              ring
            have hy : (C.u : F) ^ 3 * y' + (C.u : F) ^ 2 * C.s * x' + C.t = y := by
              dsimp [x', y']
              field_simp [C.u.ne_zero]
              ring
            rw [hx, hy]
            exact WeierstrassCurve.Affine.equation_iff_nonsingular.mpr h)))
  left_inv P := by
    rcases P with _ | ⟨x', y', h'⟩
    · rfl
    · simp only [WeierstrassCurve.Affine.Point.some.injEq]
      constructor <;> field_simp [C.u.ne_zero] <;> ring
  right_inv P := by
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · simp only [WeierstrassCurve.Affine.Point.some.injEq]
      constructor <;> field_simp [C.u.ne_zero] <;> ring

private lemma card_variableChange_eq {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (C : WeierstrassCurve.VariableChange (ZMod p)) [E.IsElliptic] :
    @Fintype.card E.toAffine.Point (ecPointFintype E) =
      @Fintype.card (C • E).toAffine.Point (ecPointFintype (C • E)) := by
  let : Fintype E.toAffine.Point := ecPointFintype E
  let : Fintype (C • E).toAffine.Point := ecPointFintype (C • E)
  exact Fintype.card_congr (ecPointEquivVariableChange E C).symm

end ShortNFReduction

section ManinHasse

open Classical

private noncomputable def fPoly {p : ℕ} (E : WeierstrassCurve (ZMod p)) :
    Polynomial (ZMod p) :=
  Polynomial.X ^ 3 + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆

private lemma fPoly_natDegree {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (fPoly E).natDegree = 3 := by
  have h1 : (Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le ?_ (by simp)
    refine le_trans Polynomial.natDegree_mul_le ?_
    simp
  have hlt : (Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆).natDegree <
      (Polynomial.X ^ 3 : Polynomial (ZMod p)).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    omega
  rw [fPoly, add_assoc, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt,
    Polynomial.natDegree_X_pow]

private lemma fPoly_ne_zero {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) : fPoly E ≠ 0 := by
  intro h0
  have hd := fPoly_natDegree E
  rw [h0, Polynomial.natDegree_zero] at hd
  omega

private lemma fPoly_eval {p : ℕ} (E : WeierstrassCurve (ZMod p)) (a : ZMod p) :
    (fPoly E).eval a = a ^ 3 + E.a₄ * a + E.a₆ := by
  simp [fPoly]

private noncomputable def fRat {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    RatFunc (ZMod p) :=
  algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (fPoly E)

private lemma fRat_ne_zero {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    fRat E ≠ 0 :=
  RatFunc.algebraMap_ne_zero (fPoly_ne_zero E)

private lemma fRat_eq {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    fRat E = RatFunc.X ^ 3 + RatFunc.C E.a₄ * RatFunc.X + RatFunc.C E.a₆ := by
  simp only [fRat, fPoly, map_add, map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

private instance instFactIrredF {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    Fact (∀ r : RatFunc (ZMod p), r ^ 2 ≠ fRat E + 0 * r) := by
  refine ⟨fun r hr => ?_⟩
  rw [zero_mul, add_zero] at hr
  have hfrac := RatFunc.num_div_denom r
  have hdn : r.denom ≠ 0 := RatFunc.denom_ne_zero r
  have hdnF : (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) r.denom) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hdn
  have hmul_r : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) r.num =
      r * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) r.denom := by
    rw [← div_mul_cancel₀ (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) r.num) hdnF,
      hfrac]
  have hpow :
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) r.num) ^ 2 =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (fPoly E) *
          (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) r.denom) ^ 2 := by
    rw [hmul_r, mul_pow, hr]; rfl
  rw [← map_pow, ← map_pow, ← map_mul] at hpow
  have heq : r.num ^ 2 = fPoly E * r.denom ^ 2 :=
    IsFractionRing.injective (Polynomial (ZMod p)) (RatFunc (ZMod p)) hpow
  have hfn : fPoly E ≠ 0 := fPoly_ne_zero E
  have hrhs_ne : fPoly E * r.denom ^ 2 ≠ 0 := mul_ne_zero hfn (pow_ne_zero 2 hdn)
  have hlhs_ne : r.num ^ 2 ≠ 0 := heq ▸ hrhs_ne
  have hdeg := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_mul hfn (pow_ne_zero 2 hdn),
    Polynomial.natDegree_pow, fPoly_natDegree] at hdeg
  omega

private abbrev QuadK {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :=
  QuadraticAlgebra (RatFunc (ZMod p)) (fRat E) 0

private lemma quadK_one_re {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (1 : QuadK E).re = 1 := rfl

private lemma quadK_one_im {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (1 : QuadK E).im = 0 := rfl

private lemma quadK_mk0_pow {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (r : RatFunc (ZMod p)) (n : ℕ) :
    (⟨r, 0⟩ : QuadK E) ^ n = ⟨r ^ n, 0⟩ := by
  rw [← QuadraticAlgebra.algebraMap_eq, ← map_pow, QuadraticAlgebra.algebraMap_eq]

private noncomputable def sigmaK {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    QuadK E →ₐ[ZMod p] QuadK E :=
  (QuadraticAlgebra.lift ⟨-(QuadraticAlgebra.omega : QuadK E), by
    rw [QuadraticAlgebra.ext_iff]
    simp [QuadraticAlgebra.omega, quadK_one_re, quadK_one_im]⟩).restrictScalars (ZMod p)

@[simp]
private lemma sigmaK_apply {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (a b : RatFunc (ZMod p)) :
    sigmaK E ⟨a, b⟩ = ⟨a, -b⟩ := by
  rw [QuadraticAlgebra.ext_iff]
  simp [sigmaK, QuadraticAlgebra.lift, QuadraticAlgebra.omega, quadK_one_re, quadK_one_im]

private lemma ratFunc_two_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) :
    (2 : RatFunc (ZMod p)) ≠ 0 := by
  have hne : algebraMap (ZMod p) (RatFunc (ZMod p)) 2 ≠ algebraMap (ZMod p) (RatFunc (ZMod p)) 0 :=
    (algebraMap (ZMod p) (RatFunc (ZMod p))).injective.ne (zmod_two_ne_zero hp3)
  simpa only [map_ofNat, map_zero] using hne

private lemma quadK_two_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) : (2 : QuadK E) ≠ 0 := by
  have hne : algebraMap (ZMod p) (QuadK E) 2 ≠ algebraMap (ZMod p) (QuadK E) 0 :=
    (algebraMap (ZMod p) (QuadK E)).injective.ne (zmod_two_ne_zero hp3)
  simpa only [map_ofNat, map_zero] using hne

private lemma eq_of_sigmaK_eq_self {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) {z : QuadK E} (hz : sigmaK E z = z) : z.im = 0 := by
  rcases z with ⟨a, b⟩
  rw [sigmaK_apply] at hz
  have him : -b = b := congrArg QuadraticAlgebra.im hz
  have h2b : (2 : RatFunc (ZMod p)) * b = 0 := by linear_combination -him
  exact (mul_eq_zero.mp h2b).resolve_left (ratFunc_two_ne_zero hp3)

private lemma eq_of_sigmaK_eq_neg {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) {z : QuadK E} (hz : sigmaK E z = -z) : z.re = 0 := by
  rcases z with ⟨a, b⟩
  rw [sigmaK_apply] at hz
  have hre : a = -a := congrArg QuadraticAlgebra.re hz
  have h2a : (2 : RatFunc (ZMod p)) * a = 0 := by linear_combination hre
  exact (mul_eq_zero.mp h2a).resolve_left (ratFunc_two_ne_zero hp3)

private lemma charP_quadK {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    CharP (QuadK E) p :=
  (RingHom.charP_iff_charP (algebraMap (ZMod p) (QuadK E)) p).mp inferInstance

private instance quadK_base_isElliptic {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    [E.IsElliptic] : (E⁄(QuadK E)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  change IsUnit (E.map (algebraMap (ZMod p) (QuadK E))).Δ
  rw [WeierstrassCurve.map_Δ]
  exact E.isUnit_Δ.map _

private instance quadK_base_isShortNF {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    [E.IsShortNF] : (E⁄(QuadK E)).IsShortNF := by
  refine ⟨?_, ?_, ?_⟩
  · change algebraMap (ZMod p) (QuadK E) E.a₁ = 0
    rw [E.a₁_of_isShortNF, map_zero]
  · change algebraMap (ZMod p) (QuadK E) E.a₂ = 0
    rw [E.a₂_of_isShortNF, map_zero]
  · change algebraMap (ZMod p) (QuadK E) E.a₃ = 0
    rw [E.a₃_of_isShortNF, map_zero]

private lemma algebraMap_zmod_quadK_apply {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (c : ZMod p) :
    algebraMap (ZMod p) (QuadK E) c = ⟨RatFunc.C c, 0⟩ := by
  have h1 : algebraMap (ZMod p) (QuadK E) c =
      algebraMap (RatFunc (ZMod p)) (QuadK E) (algebraMap (ZMod p) (RatFunc (ZMod p)) c) :=
    IsScalarTower.algebraMap_apply (ZMod p) (RatFunc (ZMod p)) (QuadK E) c
  rw [h1, QuadraticAlgebra.algebraMap_eq]
  rfl

private lemma base_a₁ {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsShortNF] :
    (E.toAffine⁄(QuadK E)).a₁ = 0 := (E⁄(QuadK E)).a₁_of_isShortNF

private lemma base_a₂ {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsShortNF] :
    (E.toAffine⁄(QuadK E)).a₂ = 0 := (E⁄(QuadK E)).a₂_of_isShortNF

private lemma base_a₃ {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsShortNF] :
    (E.toAffine⁄(QuadK E)).a₃ = 0 := (E⁄(QuadK E)).a₃_of_isShortNF

private lemma base_a₄ {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (E.toAffine⁄(QuadK E)).a₄ = ⟨RatFunc.C E.a₄, 0⟩ :=
  algebraMap_zmod_quadK_apply E E.a₄

private lemma base_a₆ {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (E.toAffine⁄(QuadK E)).a₆ = ⟨RatFunc.C E.a₆, 0⟩ :=
  algebraMap_zmod_quadK_apply E E.a₆

private noncomputable def ratDeg {p : ℕ} [Fact p.Prime] (r : RatFunc (ZMod p)) : ℕ :=
  max r.num.natDegree r.denom.natDegree

private lemma ratDeg_zero {p : ℕ} [Fact p.Prime] : ratDeg (0 : RatFunc (ZMod p)) = 0 := by
  simp [ratDeg]

private lemma ratDeg_X {p : ℕ} [Fact p.Prime] : ratDeg (RatFunc.X : RatFunc (ZMod p)) = 1 := by
  simp [ratDeg, RatFunc.num_X, RatFunc.denom_X]

private lemma ratDeg_X_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    ratDeg ((RatFunc.X : RatFunc (ZMod p)) ^ n) = n := by
  set F := RatFunc (ZMod p)
  set r : F := RatFunc.X ^ n
  have h1 : algebraMap (Polynomial (ZMod p)) F (Polynomial.X ^ n) /
      algebraMap (Polynomial (ZMod p)) F 1 = r := by
    rw [map_pow, RatFunc.algebraMap_X, map_one, div_one]
  have hdvd : r.denom ∣ 1 := (RatFunc.denom_dvd (x := r) one_ne_zero).mpr ⟨Polynomial.X ^ n, h1.symm⟩
  have hunit : IsUnit r.denom := isUnit_of_dvd_one hdvd
  have hdn_deg : r.denom.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  have hdn_ne : r.denom ≠ 0 := RatFunc.denom_ne_zero r
  have hdnF : algebraMap (Polynomial (ZMod p)) F r.denom ≠ 0 := RatFunc.algebraMap_ne_zero hdn_ne
  have hfrac : algebraMap (Polynomial (ZMod p)) F r.num =
      algebraMap (Polynomial (ZMod p)) F (Polynomial.X ^ n * r.denom) := by
    rw [map_mul, ← mul_one (algebraMap _ F r.num), ← map_one (algebraMap (Polynomial (ZMod p)) F),
      ← div_eq_div_iff hdnF (RatFunc.algebraMap_ne_zero one_ne_zero), RatFunc.num_div_denom, h1]
  have heq : r.num = Polynomial.X ^ n * r.denom :=
    IsFractionRing.injective (Polynomial (ZMod p)) F hfrac
  have hnum_deg : r.num.natDegree = n := by
    rw [heq, Polynomial.natDegree_mul (pow_ne_zero n Polynomial.X_ne_zero) hdn_ne,
      Polynomial.natDegree_X_pow, hdn_deg, add_zero]
  simp [ratDeg, r, hnum_deg, hdn_deg]

private lemma ratDeg_div_le {p : ℕ} [Fact p.Prime] (a b : Polynomial (ZMod p)) (hb : b ≠ 0) :
    ratDeg (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) a /
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) b) ≤ max a.natDegree b.natDegree := by
  by_cases ha : a = 0
  · subst ha
    simp [ratDeg_zero]
  · set x := algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) a /
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) b
    have hndvd : x.num ∣ a := (RatFunc.num_dvd ha).mpr ⟨b, hb, rfl⟩
    have hddvd : x.denom ∣ b := (RatFunc.denom_dvd hb).mpr ⟨a, rfl⟩
    exact max_le_max (Polynomial.natDegree_le_of_dvd hndvd ha)
      (Polynomial.natDegree_le_of_dvd hddvd hb)

private lemma quadK_im_div_re {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (a b : RatFunc (ZMod p)) (hb : b ≠ 0) :
    (⟨0, a⟩ : QuadK E) / ⟨b, 0⟩ = ⟨0, a / b⟩ := by
  have hbK : (⟨b, 0⟩ : QuadK E) ≠ 0 := fun h0 => hb (congrArg QuadraticAlgebra.re h0)
  rw [div_eq_iff hbK]
  ext <;> simp [div_mul_cancel₀ _ hb]

private lemma pt_generic_eq {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsShortNF] :
    (E.toAffine⁄(QuadK E)).Equation ⟨RatFunc.X, 0⟩ (QuadraticAlgebra.omega : QuadK E) := by
  rw [WeierstrassCurve.Affine.equation_iff, base_a₁ E, base_a₂ E, base_a₃ E, base_a₄ E, base_a₆ E,
    quadK_mk0_pow E RatFunc.X 3]
  have hsq : (QuadraticAlgebra.omega : QuadK E) ^ 2 = ⟨fRat E, 0⟩ := by
    rw [sq, QuadraticAlgebra.omega_mul_omega_eq_mk]
  rw [hsq]
  ext <;> simp [fRat_eq]

private lemma pt_frob_eq {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (E : WeierstrassCurve (ZMod p))
    [E.IsShortNF] :
    (E.toAffine⁄(QuadK E)).Equation ⟨RatFunc.X ^ p, 0⟩ ⟨0, fRat E ^ ((p - 1) / 2)⟩ := by
  have : CharP (QuadK E) p := charP_quadK E
  have hp_odd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left (by omega)
  have hp_decomp : 2 * ((p - 1) / 2) + 1 = p := by omega
  have hyQ_eq : (⟨0, fRat E ^ ((p - 1) / 2)⟩ : QuadK E) = (QuadraticAlgebra.omega : QuadK E) ^ p := by
    conv_rhs => arg 2; rw [← hp_decomp]
    rw [pow_succ, pow_mul]
    have hsq : (QuadraticAlgebra.omega : QuadK E) ^ 2 =
        algebraMap (RatFunc (ZMod p)) (QuadK E) (fRat E) := by
      rw [sq, QuadraticAlgebra.omega_mul_omega_eq_mk, QuadraticAlgebra.algebraMap_eq]
    rw [hsq, ← map_pow, QuadraticAlgebra.algebraMap_eq]
    ext <;> simp [QuadraticAlgebra.omega]
  have hxQ_eq : (⟨RatFunc.X ^ p, 0⟩ : QuadK E) = (⟨RatFunc.X, 0⟩ : QuadK E) ^ p :=
    (quadK_mk0_pow E RatFunc.X p).symm
  rw [WeierstrassCurve.Affine.equation_iff, base_a₁ E, base_a₂ E, base_a₃ E]
  have hgen := pt_generic_eq E
  rw [WeierstrassCurve.Affine.equation_iff, base_a₁ E, base_a₂ E, base_a₃ E] at hgen
  have hgenp := congrArg (· ^ p) hgen
  simp only [zero_mul, add_zero] at hgenp ⊢
  rw [hyQ_eq, hxQ_eq, ← pow_mul, mul_comm p 2, pow_mul, hgenp]
  simp only [add_pow_char, mul_pow, ← pow_mul, mul_comm 3 p]
  have ha4p : (E.toAffine⁄(QuadK E)).a₄ ^ p = (E.toAffine⁄(QuadK E)).a₄ := by
    change (algebraMap (ZMod p) (QuadK E) E.a₄) ^ p = algebraMap (ZMod p) (QuadK E) E.a₄
    rw [← map_pow, ZMod.pow_card]
  have ha6p : (E.toAffine⁄(QuadK E)).a₆ ^ p = (E.toAffine⁄(QuadK E)).a₆ := by
    change (algebraMap (ZMod p) (QuadK E) E.a₆) ^ p = algebraMap (ZMod p) (QuadK E) E.a₆
    rw [← map_pow, ZMod.pow_card]
  rw [ha4p, ha6p, mul_comm p 3]

private noncomputable def ptP {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    [E.IsElliptic] [E.IsShortNF] : (E.toAffine⁄(QuadK E)).Point :=
  .some ⟨RatFunc.X, 0⟩ QuadraticAlgebra.omega
    ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E))

private noncomputable def ptQ {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (E : WeierstrassCurve (ZMod p))
    [E.IsElliptic] [E.IsShortNF] : (E.toAffine⁄(QuadK E)).Point :=
  .some ⟨RatFunc.X ^ p, 0⟩ ⟨0, fRat E ^ ((p - 1) / 2)⟩
    ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_frob_eq hp3 E))

private lemma two_smul_ptP_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] [E.IsShortNF] :
    (2 : ℤ) • ptP E ≠ 0 := by
  intro h0
  rw [two_zsmul] at h0
  have hneg : ptP E = -(ptP E) := by
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact h0
  simp only [ptP, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, WeierstrassCurve.Affine.negY,
    base_a₁ E, base_a₃ E] at hneg
  have h1_eq : (1 : RatFunc (ZMod p)) = -1 := by
    have := congrArg QuadraticAlgebra.im hneg.2
    simpa [QuadraticAlgebra.omega] using this
  have h2b : (2 : RatFunc (ZMod p)) * 1 = 0 := by linear_combination h1_eq
  rw [mul_one] at h2b
  exact ratFunc_two_ne_zero hp3 h2b

private noncomputable def sigmaPt {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (E.toAffine⁄(QuadK E)).Point →+ (E.toAffine⁄(QuadK E)).Point :=
  WeierstrassCurve.Affine.Point.map (sigmaK E)

private lemma sigmaPt_ptP {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    [E.IsElliptic] [E.IsShortNF] : sigmaPt E (ptP E) = -(ptP E) := by
  rw [ptP, sigmaPt, WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, WeierstrassCurve.Affine.negY, base_a₁ E, base_a₃ E]
  constructor
  · rw [sigmaK_apply, neg_zero]
  · have hω : (QuadraticAlgebra.omega : QuadK E) = ⟨0, 1⟩ := rfl
    rw [hω, sigmaK_apply]
    ext <;> simp

private lemma sigmaPt_ptQ {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (E : WeierstrassCurve (ZMod p))
    [E.IsElliptic] [E.IsShortNF] : sigmaPt E (ptQ hp3 E) = -(ptQ hp3 E) := by
  rw [ptQ, sigmaPt, WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, WeierstrassCurve.Affine.negY, base_a₁ E, base_a₃ E]
  constructor
  · rw [sigmaK_apply, neg_zero]
  · rw [sigmaK_apply]
    ext <;> simp

private lemma sigmaPt_orbit {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (E : WeierstrassCurve (ZMod p))
    [E.IsElliptic] [E.IsShortNF] (n : ℤ) :
    sigmaPt E (ptQ hp3 E + n • ptP E) = -(ptQ hp3 E + n • ptP E) := by
  rw [map_add, map_zsmul, sigmaPt_ptQ hp3 E, sigmaPt_ptP E]
  module

private noncomputable def ptDeg {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    (E.toAffine⁄(QuadK E)).Point → ℕ
  | .zero => 0
  | .some x _ _ => ratDeg x.re

@[simp]
private lemma ptDeg_zero {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) :
    ptDeg E 0 = 0 := rfl

@[simp]
private lemma ptDeg_neg {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (R : (E.toAffine⁄(QuadK E)).Point) : ptDeg E (-R) = ptDeg E R := by
  rcases R with _ | ⟨x, y, h⟩ <;> rfl

private lemma coords_of_sigmaPt_neg {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsShortNF]
    {x y : QuadK E} {h : (E.toAffine⁄(QuadK E)).Nonsingular x y}
    (hσ : sigmaPt E (.some x y h) = -(.some x y h)) :
    x.im = 0 ∧ y.re = 0 := by
  rw [sigmaPt, WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.neg_some,
    WeierstrassCurve.Affine.Point.some.injEq, WeierstrassCurve.Affine.negY,
    base_a₁ E, base_a₃ E] at hσ
  have hx : sigmaK E x = x := hσ.1
  have hy : sigmaK E y = -y := by simpa using hσ.2
  exact ⟨eq_of_sigmaK_eq_self hp3 E hx, eq_of_sigmaK_eq_neg hp3 E hy⟩

private lemma quadK_mk0i_sq {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    (v : RatFunc (ZMod p)) :
    (⟨0, v⟩ : QuadK E) ^ 2 = ⟨fRat E * v ^ 2, 0⟩ := by
  ext <;> [simp [sq, mul_assoc]; simp [sq]]

private lemma curve_eq_of_coords {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p))
    [E.IsShortNF] {u v : RatFunc (ZMod p)}
    (heq : (E.toAffine⁄(QuadK E)).Equation ⟨u, 0⟩ ⟨0, v⟩) :
    v ^ 2 * fRat E = u ^ 3 + RatFunc.C E.a₄ * u + RatFunc.C E.a₆ := by
  rw [WeierstrassCurve.Affine.equation_iff, base_a₁ E, base_a₂ E, base_a₃ E,
    base_a₄ E, base_a₆ E, quadK_mk0_pow E u 3, quadK_mk0i_sq E v] at heq
  have hre := congrArg QuadraticAlgebra.re heq
  simp only [zero_mul, add_zero, mul_zero, QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul] at hre
  linear_combination hre

private lemma two_smul_eq_zero_of_ptDeg_eq_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] [E.IsShortNF]
    {R : (E.toAffine⁄(QuadK E)).Point} (hσ : sigmaPt E R = -R) (hd : ptDeg E R = 0) :
    (2 : ℤ) • R = 0 := by
  rcases R with _ | ⟨xR, yR, hR⟩
  · change (2 : ℤ) • (0 : (E.toAffine⁄(QuadK E)).Point) = 0
    rw [two_zsmul, zero_add]
  · obtain ⟨hxim, hyre⟩ := coords_of_sigmaPt_neg hp3 E hσ
    have hxR_eq : xR = ⟨xR.re, 0⟩ := by ext <;> [rfl; exact hxim]
    have hyR_eq : yR = ⟨0, yR.im⟩ := by ext <;> [exact hyre; rfl]
    have hnd : xR.re.num.natDegree = 0 := by
      have : ratDeg xR.re = 0 := hd
      dsimp [ratDeg] at this
      omega
    have hdd : xR.re.denom.natDegree = 0 := by
      have : ratDeg xR.re = 0 := hd
      dsimp [ratDeg] at this
      omega
    set c : ZMod p := xR.re.num.coeff 0 / xR.re.denom.coeff 0
    have hx_const : xR.re = RatFunc.C c := by
      rw [← RatFunc.num_div_denom xR.re, Polynomial.eq_C_of_natDegree_eq_zero hnd,
        Polynomial.eq_C_of_natDegree_eq_zero hdd, RatFunc.algebraMap_C, RatFunc.algebraMap_C,
        ← map_div₀]
    have heqn : yR.im ^ 2 * fRat E = RatFunc.C (c ^ 3 + E.a₄ * c + E.a₆) := by
      have he := hR.1
      rw [hxR_eq, hyR_eq] at he
      have hc := curve_eq_of_coords E he
      rw [hx_const] at hc
      simpa only [map_add, map_mul, map_pow] using hc
    have hyim_zero : yR.im = 0 := by
      by_contra hne
      set v := yR.im
      have hvn : v.num ≠ 0 := RatFunc.num_ne_zero hne
      have hvd : v.denom ≠ 0 := RatFunc.denom_ne_zero v
      have hvdF : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) v.denom ≠ 0 :=
        RatFunc.algebraMap_ne_zero hvd
      have hmul_v : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) v.num =
          v * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) v.denom := by
        rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) v.num) hvdF, RatFunc.num_div_denom]
      have hrat :
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (v.num ^ 2 * fPoly E) =
            algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
              (Polynomial.C (c ^ 3 + E.a₄ * c + E.a₆) * v.denom ^ 2) := by
        simp only [map_mul, map_pow]
        calc (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) v.num) ^ 2 * fRat E
            = v ^ 2 * fRat E *
                (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) v.denom) ^ 2 := by
                rw [hmul_v]; ring
          _ = RatFunc.C (c ^ 3 + E.a₄ * c + E.a₆) *
                (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) v.denom) ^ 2 := by
                rw [heqn]
      have hpoly : v.num ^ 2 * fPoly E = Polynomial.C (c ^ 3 + E.a₄ * c + E.a₆) * v.denom ^ 2 :=
        IsFractionRing.injective (Polynomial (ZMod p)) (RatFunc (ZMod p)) hrat
      have hlhs_ne : v.num ^ 2 * fPoly E ≠ 0 :=
        mul_ne_zero (pow_ne_zero 2 hvn) (fPoly_ne_zero E)
      have hc0 : c ^ 3 + E.a₄ * c + E.a₆ ≠ 0 := by
        intro hc0
        rw [hc0, map_zero, zero_mul] at hpoly
        exact hlhs_ne hpoly
      have hdeg := congrArg Polynomial.natDegree hpoly
      rw [Polynomial.natDegree_mul (pow_ne_zero 2 hvn) (fPoly_ne_zero E),
        Polynomial.natDegree_pow, fPoly_natDegree,
        Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr hc0) (pow_ne_zero 2 hvd),
        Polynomial.natDegree_C, zero_add, Polynomial.natDegree_pow] at hdeg
      omega
    have hyR_zero : yR = 0 := by ext <;> [exact hyre; exact hyim_zero]
    have hneg_self : -(WeierstrassCurve.Affine.Point.some xR yR hR : (E.toAffine⁄(QuadK E)).Point) =
        WeierstrassCurve.Affine.Point.some xR yR hR := by
      simp [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.negY, hyR_zero]
    rw [two_zsmul]
    nth_rw 1 [← hneg_self]
    exact neg_add_cancel _

private lemma ratDeg_add_mul_bound {p : ℕ} [Fact p.Prime]
    {g₁ h₁ g₂ h₂ : Polynomial (ZMod p)} (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
    max g₁.natDegree h₁.natDegree + max g₂.natDegree h₂.natDegree ≤
      max (h₁ * h₂).natDegree (max (g₁ * h₂ + g₂ * h₁).natDegree (g₁ * g₂).natDegree) := by
  rcases le_or_gt g₁.natDegree h₁.natDegree with h1 | h1 <;>
    rcases le_or_gt g₂.natDegree h₂.natDegree with h2 | h2
  · have hq0 : (h₁ * h₂).natDegree = h₁.natDegree + h₂.natDegree :=
      Polynomial.natDegree_mul hh₁ hh₂
    omega
  · have hg2_ne : g₂ ≠ 0 := fun h0 => by simp [h0] at h2
    have hlt : (g₁ * h₂).natDegree < (g₂ * h₁).natDegree := by
      by_cases hg1_zero : g₁ = 0
      · simp only [hg1_zero, zero_mul, Polynomial.natDegree_zero]
        rw [Polynomial.natDegree_mul hg2_ne hh₁]
        omega
      · rw [Polynomial.natDegree_mul hg1_zero hh₂, Polynomial.natDegree_mul hg2_ne hh₁]
        omega
    have hq1 : (g₁ * h₂ + g₂ * h₁).natDegree = g₂.natDegree + h₁.natDegree := by
      rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt, Polynomial.natDegree_mul hg2_ne hh₁]
    omega
  · have hg1_ne : g₁ ≠ 0 := fun h0 => by simp [h0] at h1
    have hlt : (g₂ * h₁).natDegree < (g₁ * h₂).natDegree := by
      by_cases hg2_zero : g₂ = 0
      · simp only [hg2_zero, zero_mul, Polynomial.natDegree_zero]
        rw [Polynomial.natDegree_mul hg1_ne hh₂]
        omega
      · rw [Polynomial.natDegree_mul hg2_zero hh₁, Polynomial.natDegree_mul hg1_ne hh₂]
        omega
    have hq1 : (g₁ * h₂ + g₂ * h₁).natDegree = g₁.natDegree + h₂.natDegree := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_mul hg1_ne hh₂]
    omega
  · have hg1_ne : g₁ ≠ 0 := fun h0 => by simp [h0] at h1
    have hg2_ne : g₂ ≠ 0 := fun h0 => by simp [h0] at h2
    have hq2 : (g₁ * g₂).natDegree = g₁.natDegree + g₂.natDegree :=
      Polynomial.natDegree_mul hg1_ne hg2_ne
    omega

private lemma coprime_cancel_three_denom {p : ℕ} [Fact p.Prime]
    {w₀ w₁ w₂ g₁ h₁ g₂ h₂ : Polynomial (ZMod p)}
    (hw₀ : w₀ ≠ 0) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0)
    (hc1 : IsCoprime g₁ h₁) (hc2 : IsCoprime g₂ h₂)
    (heq1 : w₀ * (g₁ * h₂ + g₂ * h₁) = w₁ * (h₁ * h₂))
    (heq2 : w₀ * (g₁ * g₂) = w₂ * (h₁ * h₂)) :
    (h₁ * h₂).natDegree ≤ w₀.natDegree ∧
      (g₁ * h₂ + g₂ * h₁).natDegree ≤ w₁.natDegree ∧
      (g₁ * g₂).natDegree ≤ w₂.natDegree := by
  set q₀ := h₁ * h₂
  set q₁ := g₁ * h₂ + g₂ * h₁
  set q₂ := g₁ * g₂
  have hq₀ : q₀ ≠ 0 := mul_ne_zero hh₁ hh₂
  set c := EuclideanDomain.gcd w₀ q₀
  have hc_dvd_w₀ : c ∣ w₀ := EuclideanDomain.gcd_dvd_left w₀ q₀
  have hc_dvd_q₀ : c ∣ q₀ := EuclideanDomain.gcd_dvd_right w₀ q₀
  have hc_ne : c ≠ 0 := fun h0 => hq₀ (zero_dvd_iff.mp (h0 ▸ hc_dvd_q₀))
  obtain ⟨w₀', hw₀_eq⟩ := hc_dvd_w₀
  obtain ⟨q₀', hq₀_eq⟩ := hc_dvd_q₀
  have hq₀'_ne : q₀' ≠ 0 := fun h0 => hq₀ (by simp [hq₀_eq, h0])
  have hcop : IsCoprime w₀' q₀' := by
    refine ⟨EuclideanDomain.gcdA w₀ q₀, EuclideanDomain.gcdB w₀ q₀, ?_⟩
    apply mul_left_cancel₀ hc_ne
    calc c * (EuclideanDomain.gcdA w₀ q₀ * w₀' + EuclideanDomain.gcdB w₀ q₀ * q₀')
        = (c * w₀') * EuclideanDomain.gcdA w₀ q₀ + (c * q₀') * EuclideanDomain.gcdB w₀ q₀ := by ring
      _ = w₀ * EuclideanDomain.gcdA w₀ q₀ + q₀ * EuclideanDomain.gcdB w₀ q₀ := by rw [← hw₀_eq, ← hq₀_eq]
      _ = c := (EuclideanDomain.gcd_eq_gcd_ab w₀ q₀).symm
      _ = c * 1 := (mul_one c).symm
  have heq1' : w₀' * q₁ = w₁ * q₀' := by
    apply mul_left_cancel₀ hc_ne
    calc c * (w₀' * q₁) = (c * w₀') * q₁ := by ring
      _ = w₀ * q₁ := by rw [hw₀_eq]
      _ = w₁ * q₀ := heq1
      _ = w₁ * (c * q₀') := by rw [hq₀_eq]
      _ = c * (w₁ * q₀') := by ring
  have heq2' : w₀' * q₂ = w₂ * q₀' := by
    apply mul_left_cancel₀ hc_ne
    calc c * (w₀' * q₂) = (c * w₀') * q₂ := by ring
      _ = w₀ * q₂ := by rw [hw₀_eq]
      _ = w₂ * q₀ := heq2
      _ = w₂ * (c * q₀') := by rw [hq₀_eq]
      _ = c * (w₂ * q₀') := by ring
  have heq1'' : w₀' * q₁ = q₀' * w₁ := by rw [heq1', mul_comm]
  have heq2'' : w₀' * q₂ = q₀' * w₂ := by rw [heq2', mul_comm]
  have hq₀'_dvd_q1 : q₀' ∣ q₁ := hcop.symm.dvd_of_dvd_mul_left ⟨w₁, heq1''⟩
  have hq₀'_dvd_q2 : q₀' ∣ q₂ := hcop.symm.dvd_of_dvd_mul_left ⟨w₂, heq2''⟩
  have hq₀'_unit : IsUnit q₀' := by
    by_contra hnu
    obtain ⟨π, hπ_irred, hπ_dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnu hq₀'_ne
    have hπ_prime : Prime π := irreducible_iff_prime.mp hπ_irred
    have hπ_q₀ : π ∣ h₁ * h₂ := hπ_dvd.trans ⟨c, by change h₁ * h₂ = q₀' * c; rw [← mul_comm c q₀', ← hq₀_eq]⟩
    have hπ_q₁ : π ∣ g₁ * h₂ + g₂ * h₁ := hπ_dvd.trans hq₀'_dvd_q1
    have hπ_q₂ : π ∣ g₁ * g₂ := hπ_dvd.trans hq₀'_dvd_q2
    rcases hπ_prime.dvd_or_dvd hπ_q₀ with hπ_h1 | hπ_h2
    · have hπ_g2h1 : π ∣ g₂ * h₁ := dvd_mul_of_dvd_right hπ_h1 g₂
      have hπ_g1h2 : π ∣ g₁ * h₂ := (dvd_add_left hπ_g2h1).mp hπ_q₁
      rcases hπ_prime.dvd_or_dvd hπ_g1h2 with hπ_g1 | hπ_h2
      · exact hπ_prime.not_isUnit (hc1.isUnit_of_dvd' hπ_g1 hπ_h1)
      · rcases hπ_prime.dvd_or_dvd hπ_q₂ with hπ_g1 | hπ_g2
        · exact hπ_prime.not_isUnit (hc1.isUnit_of_dvd' hπ_g1 hπ_h1)
        · exact hπ_prime.not_isUnit (hc2.isUnit_of_dvd' hπ_g2 hπ_h2)
    · have hπ_g1h2 : π ∣ g₁ * h₂ := dvd_mul_of_dvd_right hπ_h2 g₁
      have hπ_g2h1 : π ∣ g₂ * h₁ := (dvd_add_right hπ_g1h2).mp hπ_q₁
      rcases hπ_prime.dvd_or_dvd hπ_g2h1 with hπ_g2 | hπ_h1
      · exact hπ_prime.not_isUnit (hc2.isUnit_of_dvd' hπ_g2 hπ_h2)
      · rcases hπ_prime.dvd_or_dvd hπ_q₂ with hπ_g1 | hπ_g2
        · exact hπ_prime.not_isUnit (hc1.isUnit_of_dvd' hπ_g1 hπ_h1)
        · exact hπ_prime.not_isUnit (hc2.isUnit_of_dvd' hπ_g2 hπ_h2)
  have hc_dvd_w₀' : c ∣ w₀ := ⟨w₀', hw₀_eq⟩
  have hmul_inv : q₀' * (hq₀'_unit.unit⁻¹ : (Polynomial (ZMod p))ˣ) = 1 := by
    conv_lhs => arg 1; rw [← hq₀'_unit.unit_spec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hq₀_dvd_w₀ : q₀ ∣ w₀ := by
    have h1 : q₀ ∣ c := ⟨(hq₀'_unit.unit⁻¹ : (Polynomial (ZMod p))ˣ), by
      rw [hq₀_eq, mul_assoc, hmul_inv, mul_one]⟩
    exact h1.trans hc_dvd_w₀'
  obtain ⟨s, hs⟩ := hq₀_dvd_w₀
  have hs_ne : s ≠ 0 := fun h0 => hw₀ (by simp [hs, h0])
  have hw1_eq : w₁ = s * q₁ := by
    apply mul_left_cancel₀ hq₀
    calc q₀ * w₁ = w₁ * q₀ := mul_comm _ _
      _ = w₀ * q₁ := heq1.symm
      _ = (q₀ * s) * q₁ := by rw [hs]
      _ = q₀ * (s * q₁) := by ring
  have hw2_eq : w₂ = s * q₂ := by
    apply mul_left_cancel₀ hq₀
    calc q₀ * w₂ = w₂ * q₀ := mul_comm _ _
      _ = w₀ * q₂ := heq2.symm
      _ = (q₀ * s) * q₂ := by rw [hs]
      _ = q₀ * (s * q₂) := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, Polynomial.natDegree_mul hq₀ hs_ne]; omega
  · by_cases hq1z : q₁ = 0
    · simp [hq1z]
    · rw [hw1_eq, Polynomial.natDegree_mul hs_ne hq1z]; omega
  · by_cases hq2z : q₂ = 0
    · simp [hq2z]
    · rw [hw2_eq, Polynomial.natDegree_mul hs_ne hq2z]; omega

private lemma ptDeg_parallelogram_le {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] [E.IsShortNF]
    (R : (E.toAffine⁄(QuadK E)).Point) (hσ : sigmaPt E R = -R) :
    ptDeg E (R + ptP E) + ptDeg E (R - ptP E) ≤ 2 * ptDeg E R + 2 := by
  rcases R with _ | ⟨xR, yR, hR⟩
  · change ptDeg E (0 + ptP E) + ptDeg E (0 - ptP E) ≤ 2 * 0 + 2
    rw [zero_add, zero_sub, ptDeg_neg]
    have hdegP : ptDeg E (ptP E) = 1 := ratDeg_X
    rw [hdegP]
  · set xK : QuadK E := ⟨RatFunc.X, 0⟩
    set yK : QuadK E := QuadraticAlgebra.omega
    by_cases hx_eq : xR = xK
    · have hy_cases : yR = yK ∨ yR = (E.toAffine⁄(QuadK E)).negY xK yK :=
        WeierstrassCurve.Affine.Y_eq_of_X_eq hR.1 (pt_generic_eq E) hx_eq
      have hsub_zero_or_add_zero :
          WeierstrassCurve.Affine.Point.some xR yR hR = ptP E ∨
            WeierstrassCurve.Affine.Point.some xR yR hR = -(ptP E) := by
        rcases hy_cases with hy | hy
        · left
          rw [ptP, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx_eq, hy⟩
        · right
          rw [ptP, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx_eq, hy⟩
      have hP2_deg : ptDeg E (ptP E + ptP E) ≤ 4 := by
        have hyne : yK ≠ (E.toAffine⁄(QuadK E)).negY xK yK := by
          intro h
          have h2y : (2 : QuadK E) * yK = 0 := by
            rw [WeierstrassCurve.Affine.negY, base_a₁ E, base_a₃ E] at h
            linear_combination h
          have hy0 : yK = 0 := (mul_eq_zero.mp h2y).resolve_left (quadK_two_ne_zero hp3 E)
          have : (1 : RatFunc (ZMod p)) = 0 := congrArg QuadraticAlgebra.im hy0
          exact one_ne_zero this
        have hadd := WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := (E.toAffine⁄(QuadK E)))
          (h₁ := ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E))) hyne
        have hptP : ptP E = .some xK yK
            ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E)) := rfl
        rw [hptP, hadd]
        dsimp only [ptDeg]
        set F := RatFunc (ZMod p)
        set numP := (Polynomial.C (3 : ZMod p) * Polynomial.X ^ 2 + Polynomial.C E.a₄) ^ 2 -
          Polynomial.C (8 : ZMod p) * Polynomial.X * fPoly E
        set denP := Polynomial.C (4 : ZMod p) * fPoly E
        have h4_ne : (4 : ZMod p) ≠ 0 := by
          have : (4 : ZMod p) = 2 * 2 := by ring
          rw [this]
          exact mul_ne_zero (zmod_two_ne_zero hp3) (zmod_two_ne_zero hp3)
        have hden_ne : denP ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr h4_ne) (fPoly_ne_zero E)
        have hre_eq : ((E.toAffine⁄(QuadK E)).addX xK xK
            ((E.toAffine⁄(QuadK E)).slope xK xK yK yK)).re =
            algebraMap (Polynomial (ZMod p)) F numP /
              algebraMap (Polynomial (ZMod p)) F denP := by
          rw [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.slope_of_Y_ne rfl hyne,
            WeierstrassCurve.Affine.negY, base_a₁ E, base_a₂ E, base_a₃ E, base_a₄ E]
          have h2yK_sq : ((yK - -yK) ^ 2 : QuadK E) = ⟨4 * fRat E, 0⟩ := by
            have hyK_sq : yK ^ 2 = ⟨fRat E, 0⟩ := by
              change (QuadraticAlgebra.omega : QuadK E) ^ 2 = ⟨fRat E, 0⟩
              rw [sq, QuadraticAlgebra.omega_mul_omega_eq_mk]
            have h4q : (4 : QuadK E) = algebraMap (RatFunc (ZMod p)) (QuadK E) 4 :=
              (map_ofNat (algebraMap (RatFunc (ZMod p)) (QuadK E)) 4).symm
            have h4y : (yK - -yK) ^ 2 =
                algebraMap (RatFunc (ZMod p)) (QuadK E) 4 * yK ^ 2 := by
              rw [← h4q]
              ring
            rw [h4y, hyK_sq, QuadraticAlgebra.algebraMap_eq]
            ext <;> simp
          have h4F : (4 : F) ≠ 0 := by
            have hne : algebraMap (ZMod p) F 4 ≠ algebraMap (ZMod p) F 0 :=
              (algebraMap (ZMod p) F).injective.ne h4_ne
            simpa only [map_ofNat, map_zero] using hne
          have hf_ne : (4 : F) * fRat E ≠ 0 := mul_ne_zero h4F (fRat_ne_zero E)
          have h4f_K : (⟨4 * fRat E, 0⟩ : QuadK E) ≠ 0 := by
            intro h0
            have := congrArg QuadraticAlgebra.re h0
            exact hf_ne this
          have hslope_sq : (((3 * xK ^ 2 + 2 * 0 * xK + (⟨RatFunc.C E.a₄, 0⟩ : QuadK E) - 0 * yK) /
              (yK - (-yK - 0 * xK - 0))) ^ 2 +
              0 * ((3 * xK ^ 2 + 2 * 0 * xK + (⟨RatFunc.C E.a₄, 0⟩ : QuadK E) - 0 * yK) /
                (yK - (-yK - 0 * xK - 0))) - 0 - xK - xK).re =
              ((3 * RatFunc.X ^ 2 + RatFunc.C E.a₄) ^ 2 - 8 * RatFunc.X * fRat E) / (4 * fRat E) := by
            simp only [zero_mul, mul_zero, add_zero, sub_zero]
            rw [div_pow, h2yK_sq]
            have hnumK_base :
                (3 * xK ^ 2 + (⟨RatFunc.C E.a₄, 0⟩ : QuadK E)) =
                (⟨3 * RatFunc.X ^ 2 + RatFunc.C E.a₄, 0⟩ : QuadK E) := by
              have h3q : (3 : QuadK E) = algebraMap F (QuadK E) 3 :=
                (map_ofNat (algebraMap F (QuadK E)) 3).symm
              rw [h3q, QuadraticAlgebra.algebraMap_eq, quadK_mk0_pow E RatFunc.X 2]
              ext <;> simp
            have hnumK :
                (3 * xK ^ 2 + (⟨RatFunc.C E.a₄, 0⟩ : QuadK E)) ^ 2 =
                (⟨(3 * RatFunc.X ^ 2 + RatFunc.C E.a₄) ^ 2, 0⟩ : QuadK E) := by
              rw [hnumK_base, quadK_mk0_pow E]
            rw [hnumK]
            have hdivK : (⟨(3 * RatFunc.X ^ 2 + RatFunc.C E.a₄) ^ 2, 0⟩ : QuadK E) / ⟨4 * fRat E, 0⟩ =
                ⟨(3 * RatFunc.X ^ 2 + RatFunc.C E.a₄) ^ 2 / (4 * fRat E), 0⟩ := by
              rw [div_eq_iff h4f_K]
              ext <;> simp [div_mul_cancel₀ _ hf_ne]
            rw [hdivK]
            have hx2 : (xK : QuadK E) = ⟨RatFunc.X, 0⟩ := rfl
            rw [hx2]
            simp only [QuadraticAlgebra.re_sub]
            field_simp [h4F, fRat_ne_zero E]
            ring
          rw [hslope_sq]
          dsimp only [F, numP, denP, fRat]
          simp only [map_sub, map_add, map_mul, map_pow, RatFunc.algebraMap_X,
            RatFunc.algebraMap_C, map_ofNat]
        rw [hre_eq]
        refine le_trans (ratDeg_div_le numP denP hden_ne) ?_
        have hnum_deg : numP.natDegree ≤ 4 := by
          refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
          · rw [Polynomial.natDegree_pow]
            have hdeg1 : (Polynomial.C (3 : ZMod p) * Polynomial.X ^ 2 + Polynomial.C E.a₄).natDegree ≤ 2 := by
              refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (by simp))
              refine le_trans Polynomial.natDegree_mul_le ?_
              simp
            omega
          · refine le_trans Polynomial.natDegree_mul_le ?_
            have hdegL : (Polynomial.C (8 : ZMod p) * Polynomial.X).natDegree ≤ 1 := by
              refine le_trans Polynomial.natDegree_mul_le ?_
              simp
            rw [fPoly_natDegree]
            omega
        have hden_deg : denP.natDegree ≤ 3 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          rw [Polynomial.natDegree_C, zero_add, fPoly_natDegree]
        omega
      have hdegP : ptDeg E (ptP E) = 1 := ratDeg_X
      have hdeg_negP : ptDeg E (-ptP E) = 1 := by rw [ptDeg_neg, hdegP]
      rcases hsub_zero_or_add_zero with hRP | hRP
      · rw [hRP, sub_self, ptDeg_zero, add_zero, hdegP]
        omega
      · rw [hRP, neg_add_cancel, ptDeg_zero, zero_add, hdeg_negP]
        have hsub : -(ptP E) - ptP E = -(ptP E + ptP E) := by abel
        rw [hsub, ptDeg_neg]
        omega
    · obtain ⟨hxim, hyre⟩ := coords_of_sigmaPt_neg hp3 E hσ
      set uR : RatFunc (ZMod p) := xR.re
      set vR : RatFunc (ZMod p) := yR.im
      have hxR_eq : xR = ⟨uR, 0⟩ := by ext <;> simp [hxim, uR]
      have hyR_eq : yR = ⟨0, vR⟩ := by ext <;> simp [hyre, vR]
      have huR_ne : uR ≠ RatFunc.X := by
        intro heq
        apply hx_eq
        rw [hxR_eq, heq]
      have huR_sub_ne : uR - RatFunc.X ≠ 0 := sub_ne_zero.mpr huR_ne
      have hptP : ptP E = .some xK yK
          ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E)) := rfl
      have hyneg_eq : (E.toAffine⁄(QuadK E)).negY xK yK = -yK := by
        rw [WeierstrassCurve.Affine.negY, base_a₁ E, base_a₃ E]
        ring
      have hnegP_ns : (E.toAffine⁄(QuadK E)).Nonsingular xK (-yK) := by
        rw [← hyneg_eq]
        exact (WeierstrassCurve.Affine.nonsingular_neg (W' := (E.toAffine⁄(QuadK E))) xK yK).mpr
          ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E))
      have hnegP : -(ptP E) = .some xK (-yK) hnegP_ns := by
        simp only [hptP, WeierstrassCurve.Affine.Point.neg_some, hyneg_eq]
      have hadd_pos := WeierstrassCurve.Affine.Point.add_of_X_ne (W := (E.toAffine⁄(QuadK E)))
        (h₁ := hR)
        (h₂ := (E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E)) hx_eq
      have hadd_neg := WeierstrassCurve.Affine.Point.add_of_X_ne (W := (E.toAffine⁄(QuadK E)))
        (h₁ := hR) (h₂ := hnegP_ns) hx_eq
      set x_plus := (E.toAffine⁄(QuadK E)).addX xR xK ((E.toAffine⁄(QuadK E)).slope xR xK yR yK)
      set x_minus := (E.toAffine⁄(QuadK E)).addX xR xK ((E.toAffine⁄(QuadK E)).slope xR xK yR (-yK))
      set u1 : RatFunc (ZMod p) := x_plus.re
      set u2 : RatFunc (ZMod p) := x_minus.re
      have hu1_eq : u1 = fRat E * (vR - 1) ^ 2 / (uR - RatFunc.X) ^ 2 - uR - RatFunc.X := by
        have hy_diff : yR - yK = ⟨0, vR - 1⟩ := by
          rw [hyR_eq]
          ext <;> simp [yK, QuadraticAlgebra.omega]
        have hx_diff : xR - xK = ⟨uR - RatFunc.X, 0⟩ := by
          rw [hxR_eq]
          ext <;> simp [xK]
        have hslope_eq : (E.toAffine⁄(QuadK E)).slope xR xK yR yK =
            ⟨0, (vR - 1) / (uR - RatFunc.X)⟩ := by
          rw [WeierstrassCurve.Affine.slope_of_X_ne hx_eq, hy_diff, hx_diff]
          exact quadK_im_div_re E (vR - 1) (uR - RatFunc.X) huR_sub_ne
        dsimp only [u1, x_plus]
        rw [WeierstrassCurve.Affine.addX, base_a₁ E, base_a₂ E, hslope_eq, hxR_eq]
        rw [quadK_mk0i_sq E ((vR - 1) / (uR - RatFunc.X))]
        rw [zero_mul, add_zero, sub_zero]
        simp only [QuadraticAlgebra.re_sub]
        change fRat E * ((vR - 1) / (uR - RatFunc.X)) ^ 2 - uR - RatFunc.X = _
        field_simp [huR_sub_ne]
      have hu2_eq : u2 = fRat E * (vR + 1) ^ 2 / (uR - RatFunc.X) ^ 2 - uR - RatFunc.X := by
        have hy_diff : yR - (-yK) = ⟨0, vR + 1⟩ := by
          rw [hyR_eq]
          ext <;> simp [yK, QuadraticAlgebra.omega, sub_eq_add_neg]
        have hx_diff : xR - xK = ⟨uR - RatFunc.X, 0⟩ := by
          rw [hxR_eq]
          ext <;> simp [xK]
        have hslope_eq : (E.toAffine⁄(QuadK E)).slope xR xK yR (-yK) =
            ⟨0, (vR + 1) / (uR - RatFunc.X)⟩ := by
          rw [WeierstrassCurve.Affine.slope_of_X_ne hx_eq, hy_diff, hx_diff]
          exact quadK_im_div_re E (vR + 1) (uR - RatFunc.X) huR_sub_ne
        dsimp only [u2, x_minus]
        rw [WeierstrassCurve.Affine.addX, base_a₁ E, base_a₂ E, hslope_eq, hxR_eq]
        rw [quadK_mk0i_sq E ((vR + 1) / (uR - RatFunc.X))]
        rw [zero_mul, add_zero, sub_zero]
        simp only [QuadraticAlgebra.re_sub]
        change fRat E * ((vR + 1) / (uR - RatFunc.X)) ^ 2 - uR - RatFunc.X = _
        field_simp [huR_sub_ne]
      have heqR : vR ^ 2 * fRat E = uR ^ 3 + RatFunc.C E.a₄ * uR + RatFunc.C E.a₆ := by
        have h := hR.1
        rw [hxR_eq, hyR_eq] at h
        exact curve_eq_of_coords E h
      have hv2 : vR ^ 2 = (uR ^ 3 + RatFunc.C E.a₄ * uR + RatFunc.C E.a₆) / fRat E := by
        rw [← heqR, mul_div_cancel_right₀ _ (fRat_ne_zero E)]
      have hf_eq : fRat E = RatFunc.X ^ 3 + RatFunc.C E.a₄ * RatFunc.X + RatFunc.C E.a₆ :=
        fRat_eq E
      have hsum_v2 :
          u1 + u2 = 2 * fRat E * (vR ^ 2 + 1) / (uR - RatFunc.X) ^ 2 - 2 * (uR + RatFunc.X) := by
        rw [hu1_eq, hu2_eq]
        ring
      have hprod_v2 :
          u1 * u2 =
            (fRat E * (vR ^ 2 + 1) / (uR - RatFunc.X) ^ 2 - (uR + RatFunc.X)) ^ 2 -
              (2 * fRat E / (uR - RatFunc.X) ^ 2) ^ 2 * vR ^ 2 := by
        rw [hu1_eq, hu2_eq]
        ring
      have hsum_rat :
          u1 + u2 =
            (2 * (uR + RatFunc.X) * (RatFunc.X * uR + RatFunc.C E.a₄) +
              RatFunc.C (4 * E.a₆)) / (uR - RatFunc.X) ^ 2 := by
        rw [hsum_v2, hv2]
        have h4 : RatFunc.C (4 * E.a₆) = (4 : RatFunc (ZMod p)) * RatFunc.C E.a₆ := by
          simp [map_mul, map_ofNat]
        rw [h4]
        field_simp [huR_sub_ne, fRat_ne_zero E]
        rw [hf_eq]
        ring
      have hprod_rat :
          u1 * u2 =
            ((RatFunc.X * uR - RatFunc.C E.a₄) ^ 2 -
              RatFunc.C (4 * E.a₆) * (uR + RatFunc.X)) / (uR - RatFunc.X) ^ 2 := by
        rw [hprod_v2, hv2]
        have h4 : RatFunc.C (4 * E.a₆) = (4 : RatFunc (ZMod p)) * RatFunc.C E.a₆ := by
          simp [map_mul, map_ofNat]
        rw [h4]
        field_simp [huR_sub_ne, fRat_ne_zero E]
        rw [hf_eq]
        ring
      set g := uR.num
      set h := uR.denom
      have hh_ne : h ≠ 0 := RatFunc.denom_ne_zero uR
      have hhF : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h ≠ 0 :=
        RatFunc.algebraMap_ne_zero hh_ne
      set w₀ : Polynomial (ZMod p) := (g - Polynomial.X * h) ^ 2
      set w₁ : Polynomial (ZMod p) :=
        2 * (g + Polynomial.X * h) * (Polynomial.X * g + Polynomial.C E.a₄ * h) +
          Polynomial.C (4 * E.a₆) * h ^ 2
      set w₂ : Polynomial (ZMod p) :=
        (Polynomial.X * g - Polynomial.C E.a₄ * h) ^ 2 -
          Polynomial.C (4 * E.a₆) * h * (g + Polynomial.X * h)
      have hw₀_ne : w₀ ≠ 0 := by
        intro h0
        have h1 : g - Polynomial.X * h = 0 := eq_zero_of_pow_eq_zero h0
        have heq_gh : g = Polynomial.X * h := sub_eq_zero.mp h1
        apply huR_ne
        calc uR = algebraMap _ (RatFunc (ZMod p)) g / algebraMap _ (RatFunc (ZMod p)) h :=
              (RatFunc.num_div_denom uR).symm
          _ = algebraMap _ (RatFunc (ZMod p)) (Polynomial.X * h) / algebraMap _ (RatFunc (ZMod p)) h := by
              rw [heq_gh]
          _ = RatFunc.X := by
              rw [map_mul, RatFunc.algebraMap_X, mul_div_cancel_right₀ _ hhF]
      have hw₀_deg : w₀.natDegree ≤ 2 * max g.natDegree h.natDegree + 2 := by
        dsimp [w₀]
        rw [Polynomial.natDegree_pow]
        have hxh : (Polynomial.X * h).natDegree ≤ h.natDegree + 1 :=
          le_trans Polynomial.natDegree_mul_le (by simp; omega)
        have hsub : (g - Polynomial.X * h).natDegree ≤ max g.natDegree h.natDegree + 1 :=
          le_trans (Polynomial.natDegree_sub_le _ _) (max_le (le_max_left _ _ |>.trans (Nat.le_succ _)) (by omega))
        omega
      have hw₁_deg : w₁.natDegree ≤ 2 * max g.natDegree h.natDegree + 2 := by
        dsimp [w₁]
        set d := max g.natDegree h.natDegree
        have hadd1 : (g + Polynomial.X * h).natDegree ≤ d + 1 := by
          refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) ?_)
          exact le_trans Polynomial.natDegree_mul_le (by simp [d]; omega)
        have hadd2 : (Polynomial.X * g + Polynomial.C E.a₄ * h).natDegree ≤ d + 1 := by
          refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
          · exact le_trans Polynomial.natDegree_mul_le (by simp [d]; omega)
          · exact le_trans Polynomial.natDegree_mul_le (by simp [d]; omega)
        have hm1 : (2 * (g + Polynomial.X * h) * (Polynomial.X * g + Polynomial.C E.a₄ * h)).natDegree ≤ 2 * d + 2 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          have hm0 : (2 * (g + Polynomial.X * h)).natDegree ≤ d + 1 := by
            refine le_trans Polynomial.natDegree_mul_le ?_
            have : (2 : Polynomial (ZMod p)).natDegree = 0 := Polynomial.natDegree_ofNat 2
            rw [this, zero_add]
            exact hadd1
          omega
        have hm2 : (Polynomial.C (4 * E.a₆) * h ^ 2).natDegree ≤ 2 * d + 2 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          rw [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_pow]
          omega
        exact le_trans (Polynomial.natDegree_add_le _ _) (max_le hm1 hm2)
      have hw₂_deg : w₂.natDegree ≤ 2 * max g.natDegree h.natDegree + 2 := by
        dsimp [w₂]
        set d := max g.natDegree h.natDegree
        have hm1 : ((Polynomial.X * g - Polynomial.C E.a₄ * h) ^ 2).natDegree ≤ 2 * d + 2 := by
          rw [Polynomial.natDegree_pow]
          have hsub : (Polynomial.X * g - Polynomial.C E.a₄ * h).natDegree ≤ d + 1 := by
            refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
            · exact le_trans Polynomial.natDegree_mul_le (by simp [d]; omega)
            · exact le_trans Polynomial.natDegree_mul_le (by simp [d]; omega)
          omega
        have hm2 : (Polynomial.C (4 * E.a₆) * h * (g + Polynomial.X * h)).natDegree ≤ 2 * d + 2 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          have hm2a : (Polynomial.C (4 * E.a₆) * h).natDegree ≤ d := by
            refine le_trans Polynomial.natDegree_mul_le ?_
            rw [Polynomial.natDegree_C, zero_add]
            exact le_max_right _ _
          have hm2b : (g + Polynomial.X * h).natDegree ≤ d + 1 := by
            refine le_trans (Polynomial.natDegree_add_le _ _) (max_le (by omega) ?_)
            exact le_trans Polynomial.natDegree_mul_le (by simp [d]; omega)
          omega
        exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hm1 hm2)
      set g₁ := u1.num
      set h₁ := u1.denom
      set g₂ := u2.num
      set h₂ := u2.denom
      have hh1_ne : h₁ ≠ 0 := RatFunc.denom_ne_zero u1
      have hh2_ne : h₂ ≠ 0 := RatFunc.denom_ne_zero u2
      have hh1F : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h₁ ≠ 0 :=
        RatFunc.algebraMap_ne_zero hh1_ne
      have hh2F : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h₂ ≠ 0 :=
        RatFunc.algebraMap_ne_zero hh2_ne
      have heq1 : w₀ * (g₁ * h₂ + g₂ * h₁) = w₁ * (h₁ * h₂) := by
        apply IsFractionRing.injective (Polynomial (ZMod p)) (RatFunc (ZMod p))
        simp only [w₀, w₁, map_mul, map_add, map_sub, map_pow, map_ofNat,
          RatFunc.algebraMap_X, RatFunc.algebraMap_C]
        have hu1F : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g₁ =
            u1 * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h₁ := by
          rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) g₁) hh1F, RatFunc.num_div_denom]
        have hu2F : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g₂ =
            u2 * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h₂ := by
          rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) g₂) hh2F, RatFunc.num_div_denom]
        have huRF : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g =
            uR * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h := by
          rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) g) hhF, RatFunc.num_div_denom]
        rw [hu1F, hu2F, huRF]
        have hid :
            ((uR * algebraMap _ (RatFunc (ZMod p)) h - RatFunc.X * algebraMap _ (RatFunc (ZMod p)) h) ^ 2) *
              ((u1 * algebraMap _ (RatFunc (ZMod p)) h₁) * algebraMap _ (RatFunc (ZMod p)) h₂ +
                (u2 * algebraMap _ (RatFunc (ZMod p)) h₂) * algebraMap _ (RatFunc (ZMod p)) h₁) =
            (uR - RatFunc.X) ^ 2 * (u1 + u2) *
              (algebraMap _ (RatFunc (ZMod p)) h) ^ 2 *
              (algebraMap _ (RatFunc (ZMod p)) h₁ * algebraMap _ (RatFunc (ZMod p)) h₂) := by
          ring
        rw [hid, hsum_rat, mul_div_cancel₀ _ (pow_ne_zero 2 huR_sub_ne)]
        have h4a : RatFunc.C (4 * E.a₆) = (4 : RatFunc (ZMod p)) * RatFunc.C E.a₆ := by
          simp [map_mul, map_ofNat]
        rw [h4a]
        ring
      have heq2 : w₀ * (g₁ * g₂) = w₂ * (h₁ * h₂) := by
        apply IsFractionRing.injective (Polynomial (ZMod p)) (RatFunc (ZMod p))
        simp only [w₀, w₂, map_mul, map_sub, map_add, map_pow, map_ofNat,
          RatFunc.algebraMap_X, RatFunc.algebraMap_C]
        have hu1F : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g₁ =
            u1 * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h₁ := by
          rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) g₁) hh1F, RatFunc.num_div_denom]
        have hu2F : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g₂ =
            u2 * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h₂ := by
          rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) g₂) hh2F, RatFunc.num_div_denom]
        have huRF : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g =
            uR * algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) h := by
          rw [← div_mul_cancel₀ (algebraMap _ (RatFunc (ZMod p)) g) hhF, RatFunc.num_div_denom]
        rw [hu1F, hu2F, huRF]
        have hid :
            ((uR * algebraMap _ (RatFunc (ZMod p)) h - RatFunc.X * algebraMap _ (RatFunc (ZMod p)) h) ^ 2) *
              ((u1 * algebraMap _ (RatFunc (ZMod p)) h₁) * (u2 * algebraMap _ (RatFunc (ZMod p)) h₂)) =
            (uR - RatFunc.X) ^ 2 * (u1 * u2) *
              (algebraMap _ (RatFunc (ZMod p)) h) ^ 2 *
              (algebraMap _ (RatFunc (ZMod p)) h₁ * algebraMap _ (RatFunc (ZMod p)) h₂) := by
          ring
        rw [hid, hprod_rat, mul_div_cancel₀ _ (pow_ne_zero 2 huR_sub_ne)]
        have h4a : RatFunc.C (4 * E.a₆) = (4 : RatFunc (ZMod p)) * RatFunc.C E.a₆ := by
          simp [map_mul, map_ofNat]
        rw [h4a]
        ring
      obtain ⟨hq0, hq1, hq2⟩ := coprime_cancel_three_denom hw₀_ne hh1_ne hh2_ne
        (RatFunc.isCoprime_num_denom u1) (RatFunc.isCoprime_num_denom u2) heq1 heq2
      change (g₁ * h₂ + g₂ * h₁).natDegree ≤ w₁.natDegree at hq1
      change (g₁ * g₂).natDegree ≤ w₂.natDegree at hq2
      have hdeg_add_mul := ratDeg_add_mul_bound (g₁ := g₁) (g₂ := g₂) hh1_ne hh2_ne
      have hsub_pt : WeierstrassCurve.Affine.Point.some xR yR hR - ptP E =
          WeierstrassCurve.Affine.Point.some xR yR hR + -(ptP E) := sub_eq_add_neg _ _
      have hdeg_pos : ptDeg E (.some xR yR hR + ptP E) = max g₁.natDegree h₁.natDegree := by
        rw [hptP, hadd_pos]
        rfl
      have hdeg_neg : ptDeg E (.some xR yR hR - ptP E) = max g₂.natDegree h₂.natDegree := by
        rw [hsub_pt, hnegP, hadd_neg]
        rfl
      change ptDeg E (.some xR yR hR + ptP E) + ptDeg E (.some xR yR hR - ptP E) ≤
        2 * max g.natDegree h.natDegree + 2
      rw [hdeg_pos, hdeg_neg]
      omega

private lemma euler_neg_one {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) {c : ZMod p}
    (hc : c ≠ 0) (hnsq : ¬ IsSquare c) :
    c ^ ((p - 1) / 2) = -1 := by
  have hp_odd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left (by omega)
  have hdiv : (p - 1) / 2 = p / 2 := by omega
  have hmul : 2 * (p / 2) = p - 1 := by omega
  have hsq : (c ^ (p / 2)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm (p / 2) 2, hmul]
    exact ZMod.pow_card_sub_one_eq_one hc
  rcases sq_eq_one_iff.mp hsq with h1 | hm1
  · exfalso
    exact hnsq ((ZMod.euler_criterion p hc).mpr h1)
  · rw [hdiv, hm1]

private lemma orbit_end_bounds {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] [E.IsShortNF] :
    letI := ecPointFintype E
    let N := Fintype.card E.toAffine.Point
    N ≤ 2 * p + 1 ∧
      ptDeg E (ptQ hp3 E) = p ∧
      ptDeg E (ptQ hp3 E - ptP E) ≤ N ∧
      ptDeg E (ptQ hp3 E + ptP E) ≤ 2 * p + 2 - N := by
  let : Fintype E.toAffine.Point := ecPointFintype E
  set N := Fintype.card E.toAffine.Point
  have hd0 : ptDeg E (ptQ hp3 E) = p := by
    change ratDeg ((RatFunc.X : RatFunc (ZMod p)) ^ p) = p
    exact ratDeg_X_pow p
  set S0 : Finset (ZMod p) := Finset.univ.filter fun a => (fPoly E).eval a = 0
  set Spos : Finset (ZMod p) :=
    Finset.univ.filter fun a => (fPoly E).eval a ≠ 0 ∧ IsSquare ((fPoly E).eval a)
  set Sneg : Finset (ZMod p) :=
    Finset.univ.filter fun a => (fPoly E).eval a ≠ 0 ∧ ¬ IsSquare ((fPoly E).eval a)
  have hpart : S0.card + Spos.card + Sneg.card = p := by
    have h1 : Spos.card + Sneg.card =
        (Finset.univ.filter fun a : ZMod p => (fPoly E).eval a ≠ 0).card := by
      have hu : Spos ∪ Sneg = Finset.univ.filter fun a : ZMod p => (fPoly E).eval a ≠ 0 := by
        ext a
        simp only [Spos, Sneg, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have hd : Disjoint Spos Sneg := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        simp only [Spos, Sneg, Finset.mem_filter, Finset.mem_univ, true_and] at ha1 ha2
        exact ha2.2 ha1.2
      rw [← Finset.card_union_of_disjoint hd, hu]
    have h2 : S0.card + (Finset.univ.filter fun a : ZMod p => (fPoly E).eval a ≠ 0).card =
        (Finset.univ : Finset (ZMod p)).card := by
      simpa [S0] using Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod p)))
        (fun a => (fPoly E).eval a = 0)
    rw [add_assoc, h1, h2, Finset.card_univ, ZMod.card]
  have hN : N = 1 + S0.card + 2 * Spos.card := by
    have heq_iff : ∀ x y : ZMod p, E.toAffine.Equation x y ↔ y ^ 2 = (fPoly E).eval x := by
      intro x y
      rw [WeierstrassCurve.Affine.equation_iff]
      change y ^ 2 + E.a₁ * x * y + E.a₃ * y = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ ↔
        y ^ 2 = (fPoly E).eval x
      rw [E.a₁_of_isShortNF, E.a₂_of_isShortNF, E.a₃_of_isShortNF, fPoly_eval]
      simp
    have heqv : E.toAffine.Point ≃
        Option (Σ x : ZMod p, {y : ZMod p // y ^ 2 = (fPoly E).eval x}) :=
      { toFun := fun
          | .zero => none
          | .some x y h => some ⟨x, ⟨y, (heq_iff x y).mp ((E.toAffine.equation_iff_nonsingular).mpr h)⟩⟩
        invFun := fun
          | none => .zero
          | some ⟨x, ⟨y, hy⟩⟩ => .some x y ((E.toAffine.equation_iff_nonsingular).mp ((heq_iff x y).mpr hy))
        left_inv := by rintro (_ | ⟨x, y, h⟩) <;> rfl
        right_inv := by rintro (_ | ⟨x, ⟨y, hy⟩⟩) <;> rfl }
    have hcard_eq : N = 1 + ∑ x : ZMod p, Fintype.card {y : ZMod p // y ^ 2 = (fPoly E).eval x} := by
      rw [show N = Fintype.card E.toAffine.Point from rfl, Fintype.card_congr heqv,
        Fintype.card_option, Fintype.card_sigma, add_comm]
    rw [hcard_eq]
    have hfiber : ∀ x : ZMod p,
        Fintype.card {y : ZMod p // y ^ 2 = (fPoly E).eval x} =
          if (fPoly E).eval x = 0 then 1 else if IsSquare ((fPoly E).eval x) then 2 else 0 := by
      intro x
      split_ifs with hz hsq
      · have heqv0 : {y : ZMod p // y ^ 2 = (fPoly E).eval x} ≃ Unit :=
          { toFun := fun _ => ()
            invFun := fun _ => ⟨0, by simp [hz]⟩
            left_inv := fun ⟨y, hy⟩ => by
              ext
              have hy0 : y ^ 2 = 0 := hy.trans hz
              exact (eq_zero_of_pow_eq_zero hy0).symm
            right_inv := fun () => rfl }
        exact Fintype.card_congr heqv0
      · obtain ⟨b, hb⟩ := hsq
        have hfb : (fPoly E).eval x = b ^ 2 := by rw [hb, sq]
        have hb_ne : b ≠ 0 := by
          intro hb0
          apply hz
          rw [hfb, hb0, sq, mul_zero]
        have hb_neg : b ≠ -b := by
          intro hneg
          have h2b : (2 : ZMod p) * b = 0 := by linear_combination hneg
          exact hb_ne ((mul_eq_zero.mp h2b).resolve_left (zmod_two_ne_zero hp3))
        have heqv2 : {y : ZMod p // y ^ 2 = (fPoly E).eval x} ≃ Bool :=
          { toFun := fun ⟨y, _⟩ => decide (y = b)
            invFun := fun t => if t then ⟨b, hfb.symm⟩ else ⟨-b, by rw [neg_sq]; exact hfb.symm⟩
            left_inv := fun ⟨y, hy⟩ => by
              have hsqy : y * y = b * b := by rw [← sq, ← sq]; exact hy.trans hfb
              rcases mul_self_eq_mul_self_iff.mp hsqy with hyb | hyb
              · subst hyb; simp
              · subst hyb; simp [hb_neg.symm]
            right_inv := fun t => by cases t <;> simp [hb_neg.symm] }
        exact Fintype.card_congr heqv2
      · have hemp : IsEmpty {y : ZMod p // y ^ 2 = (fPoly E).eval x} :=
          ⟨fun ⟨y, hy⟩ => hsq ⟨y, by rw [← hy, sq]⟩⟩
        exact Fintype.card_eq_zero
    simp_rw [hfiber, Finset.sum_ite]
    have hc1 : (Finset.univ.filter fun x : ZMod p => (fPoly E).eval x = 0).card = S0.card := rfl
    have hc2 :
        ((Finset.univ.filter fun x : ZMod p => ¬(fPoly E).eval x = 0).filter
          fun x => IsSquare ((fPoly E).eval x)).card = Spos.card := by
      congr 1
      ext x
      simp [Spos]
    simp only [Finset.sum_const, smul_eq_mul, hc1, hc2, mul_comm]
    omega
  have hxQ_ne : (⟨RatFunc.X ^ p, 0⟩ : QuadK E) ≠ ⟨RatFunc.X, 0⟩ := by
    intro heq
    have hre : (RatFunc.X : RatFunc (ZMod p)) ^ p = RatFunc.X := congrArg QuadraticAlgebra.re heq
    have h1 := congrArg ratDeg hre
    rw [ratDeg_X_pow, ratDeg_X] at h1
    omega
  set xK : QuadK E := ⟨RatFunc.X, 0⟩
  set yK : QuadK E := QuadraticAlgebra.omega
  set xQ : QuadK E := ⟨RatFunc.X ^ p, 0⟩
  set yQ : QuadK E := ⟨0, fRat E ^ ((p - 1) / 2)⟩
  have hQ_pt : ptQ hp3 E = .some xQ yQ
      ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_frob_eq hp3 E)) := rfl
  have hP_pt : ptP E = .some xK yK
      ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E)) := rfl
  have hyneg_eq : (E.toAffine⁄(QuadK E)).negY xK yK = -yK := by
    rw [WeierstrassCurve.Affine.negY, base_a₁ E, base_a₃ E]
    ring
  have hnegP_ns : (E.toAffine⁄(QuadK E)).Nonsingular xK (-yK) := by
    rw [← hyneg_eq]
    exact (WeierstrassCurve.Affine.nonsingular_neg (W' := (E.toAffine⁄(QuadK E))) xK yK).mpr
      ((E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E))
  have hnegP_pt : -(ptP E) = .some xK (-yK) hnegP_ns := by
    simp only [hP_pt, WeierstrassCurve.Affine.Point.neg_some, hyneg_eq]
  have hadd_pos := WeierstrassCurve.Affine.Point.add_of_X_ne (W := (E.toAffine⁄(QuadK E)))
    (h₁ := (E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_frob_eq hp3 E))
    (h₂ := (E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_generic_eq E)) hxQ_ne
  have hadd_neg := WeierstrassCurve.Affine.Point.add_of_X_ne (W := (E.toAffine⁄(QuadK E)))
    (h₁ := (E.toAffine⁄(QuadK E)).equation_iff_nonsingular.mp (pt_frob_eq hp3 E))
    (h₂ := hnegP_ns) hxQ_ne
  set m := (p - 1) / 2
  have hp_odd : p % 2 = 1 := ((Fact.out : p.Prime).eq_two_or_odd).resolve_left (by omega)
  have hm_decomp : 2 * m + 1 = p := by omega
  set D_frob : Polynomial (ZMod p) := (Polynomial.X ^ p - Polynomial.X) ^ 2
  set N_eps : ZMod p → Polynomial (ZMod p) := fun ε =>
    fPoly E * (fPoly E ^ m + Polynomial.C ε) ^ 2 - (Polynomial.X ^ p + Polynomial.X) * D_frob
  have hX_sub_monic : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).Monic :=
    Polynomial.monic_X_pow_sub (by simp; omega)
  have hD_frob_monic : D_frob.Monic := hX_sub_monic.pow 2
  have hD_frob_ne : D_frob ≠ 0 := hD_frob_monic.ne_zero
  have hD_frob_deg : D_frob.natDegree = 2 * p := by
    have hsub_deg : (Polynomial.X ^ p - Polynomial.X : Polynomial (ZMod p)).natDegree = p := by
      have hlt : (Polynomial.X : Polynomial (ZMod p)).natDegree <
          (Polynomial.X ^ p : Polynomial (ZMod p)).natDegree := by
        rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
        omega
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
    rw [Polynomial.natDegree_pow, hsub_deg, mul_comm]
  have hN_eps_deg : ∀ ε : ZMod p, (N_eps ε).natDegree ≤ 2 * p + 1 := by
    intro ε
    have hfp : fPoly E ^ p =
        Polynomial.X ^ (3 * p) + Polynomial.C E.a₄ * Polynomial.X ^ p + Polynomial.C E.a₆ := by
      have : CharP (Polynomial (ZMod p)) p := Polynomial.charP
      dsimp [fPoly]
      simp only [add_pow_char, mul_pow, ← pow_mul, ← Polynomial.C_pow, ZMod.pow_card]
    have hf_pow : fPoly E * fPoly E ^ (2 * m) = fPoly E ^ p := by
      calc fPoly E * fPoly E ^ (2 * m) = fPoly E ^ (2 * m + 1) := by rw [pow_succ']
        _ = fPoly E ^ p := by rw [hm_decomp]
    have hdecomp_N : N_eps ε =
        (Polynomial.X ^ (2 * p + 1) + Polynomial.X ^ (p + 2) +
          Polynomial.C E.a₄ * Polynomial.X ^ p - Polynomial.X ^ 3 + Polynomial.C E.a₆) +
        (Polynomial.C (2 * ε) * fPoly E ^ (m + 1) + Polynomial.C (ε ^ 2) * fPoly E) := by
      have hsq : fPoly E * (fPoly E ^ m + Polynomial.C ε) ^ 2 =
          fPoly E * fPoly E ^ (2 * m) +
            Polynomial.C (2 * ε) * fPoly E ^ (m + 1) + Polynomial.C (ε ^ 2) * fPoly E := by
        have hp2m : (fPoly E ^ m) ^ 2 = fPoly E ^ (2 * m) := by rw [← pow_mul, mul_comm]
        have hm1 : fPoly E * fPoly E ^ m = fPoly E ^ (m + 1) := by rw [pow_succ']
        simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_ofNat]
        calc fPoly E * (fPoly E ^ m + Polynomial.C ε) ^ 2
            = fPoly E * (fPoly E ^ m) ^ 2 +
                2 * Polynomial.C ε * (fPoly E * fPoly E ^ m) +
                Polynomial.C ε ^ 2 * fPoly E := by ring
          _ = fPoly E * fPoly E ^ (2 * m) +
                2 * Polynomial.C ε * fPoly E ^ (m + 1) + Polynomial.C ε ^ 2 * fPoly E := by
              rw [hp2m, hm1]
      have hDf_exp : (Polynomial.X ^ p + Polynomial.X : Polynomial (ZMod p)) * D_frob =
          Polynomial.X ^ (3 * p) - Polynomial.X ^ (2 * p + 1) -
            Polynomial.X ^ (p + 2) + Polynomial.X ^ 3 := by
        dsimp [D_frob]
        have hx2p : (Polynomial.X ^ p : Polynomial (ZMod p)) ^ 2 = Polynomial.X ^ (2 * p) := by
          rw [← pow_mul, mul_comm]
        have hx3p : (Polynomial.X ^ p : Polynomial (ZMod p)) * Polynomial.X ^ (2 * p) =
            Polynomial.X ^ (3 * p) := by
          rw [← pow_add]; congr 1; omega
        have hx2p1 : (Polynomial.X ^ p : Polynomial (ZMod p)) ^ 2 * Polynomial.X =
            Polynomial.X ^ (2 * p + 1) := by
          rw [hx2p, ← pow_succ]
        have hxp2 : (Polynomial.X ^ p : Polynomial (ZMod p)) * Polynomial.X ^ 2 =
            Polynomial.X ^ (p + 2) := by
          rw [← pow_add]
        linear_combination (norm := ring) -hx3p + hx2p1 + hxp2
      dsimp [N_eps]
      rw [hsq, hf_pow, hfp, hDf_exp]
      ring
    rw [hdecomp_N]
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ (by simp))
      refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ (by simp; omega))
      refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) (by simp; omega))
      · exact le_trans Polynomial.natDegree_mul_le (by simp; omega)
    · refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
      · refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_pow, fPoly_natDegree]
        omega
      · refine le_trans Polynomial.natDegree_mul_le ?_
        rw [Polynomial.natDegree_C, zero_add, fPoly_natDegree]
        omega
  have hlin_coprime : ∀ a b : ZMod p, a ≠ b →
      IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := by
    intro a b hab
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    refine ⟨Polynomial.C (b - a)⁻¹, -Polynomial.C (b - a)⁻¹, ?_⟩
    calc Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C a) +
          -Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C b)
        = Polynomial.C (b - a)⁻¹ * Polynomial.C (b - a) := by
          simp only [Polynomial.C_sub]; ring
      _ = Polynomial.C ((b - a)⁻¹ * (b - a)) := by rw [← Polynomial.C_mul]
      _ = 1 := by rw [inv_mul_cancel₀ hba, Polynomial.C_1]
  have hdvd_Dfrob : ∀ a : ZMod p, (Polynomial.X - Polynomial.C a) ^ 2 ∣ D_frob := by
    intro a
    dsimp [D_frob]
    apply pow_dvd_pow_of_dvd
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    simp [ZMod.pow_card]
  have hcancel_deg : ∀ (ε : ZMod p) (G : Polynomial (ZMod p)),
      G.Monic → G ∣ D_frob → G ∣ N_eps ε →
      ratDeg (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (N_eps ε) /
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) D_frob) ≤
        2 * p + 1 - G.natDegree := by
    intro ε G hGm hGD hGN
    obtain ⟨B, hB⟩ := hGD
    obtain ⟨A, hA⟩ := hGN
    have hB_ne : B ≠ 0 := fun h0 => hD_frob_ne (by simp [hB, h0])
    have hG_ne : G ≠ 0 := hGm.ne_zero
    have hGF : algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) G ≠ 0 :=
      RatFunc.algebraMap_ne_zero hG_ne
    have hB_deg : G.natDegree + B.natDegree = 2 * p := by
      have := congrArg Polynomial.natDegree hB
      rw [Polynomial.natDegree_mul hG_ne hB_ne, hD_frob_deg] at this
      exact this.symm
    have hA_deg : A.natDegree ≤ 2 * p + 1 - G.natDegree := by
      by_cases hAz : A = 0
      · simp [hAz]
      · have hNA_eq := congrArg Polynomial.natDegree hA
        rw [Polynomial.natDegree_mul hG_ne hAz] at hNA_eq
        have hNA : G.natDegree + A.natDegree ≤ 2 * p + 1 := by
          rw [← hNA_eq]
          exact hN_eps_deg ε
        omega
    have hdiv_eq :
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (N_eps ε) /
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) D_frob =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) A /
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) B := by
      rw [hA, hB, map_mul, map_mul, mul_div_mul_left _ _ hGF]
    rw [hdiv_eq]
    refine le_trans (ratDeg_div_le A B hB_ne) ?_
    omega
  have hx_minus_eq :
      ((E.toAffine⁄(QuadK E)).addX xQ xK
        ((E.toAffine⁄(QuadK E)).slope xQ xK yQ (-yK))).re =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (N_eps 1) /
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) D_frob := by
    have hx_diff_ne : (RatFunc.X : RatFunc (ZMod p)) ^ p - RatFunc.X ≠ 0 := by
      intro h0
      apply hxQ_ne
      ext <;> simp [xQ, xK, sub_eq_zero.mp h0]
    have hy_diff : yQ - (-yK) = ⟨0, fRat E ^ m + 1⟩ := by
      ext <;> simp [yQ, yK, QuadraticAlgebra.omega, m, sub_eq_add_neg]
    have hx_diff : xQ - xK = ⟨RatFunc.X ^ p - RatFunc.X, 0⟩ := by
      ext <;> simp [xQ, xK]
    have hslope_eq : (E.toAffine⁄(QuadK E)).slope xQ xK yQ (-yK) =
        ⟨0, (fRat E ^ m + 1) / (RatFunc.X ^ p - RatFunc.X)⟩ := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxQ_ne, hy_diff, hx_diff]
      exact quadK_im_div_re E (fRat E ^ m + 1) (RatFunc.X ^ p - RatFunc.X) hx_diff_ne
    rw [WeierstrassCurve.Affine.addX, base_a₁ E, base_a₂ E, hslope_eq, zero_mul, add_zero, sub_zero]
    rw [quadK_mk0i_sq E ((fRat E ^ m + 1) / (RatFunc.X ^ p - RatFunc.X))]
    simp only [QuadraticAlgebra.re_sub]
    change fRat E * ((fRat E ^ m + 1) / (RatFunc.X ^ p - RatFunc.X)) ^ 2 -
        RatFunc.X ^ p - RatFunc.X = _
    simp only [N_eps, D_frob, map_sub, map_mul, map_pow, map_add, map_one,
      RatFunc.algebraMap_X, fRat]
    field_simp [hx_diff_ne]
    ring
  have hx_plus_eq :
      ((E.toAffine⁄(QuadK E)).addX xQ xK ((E.toAffine⁄(QuadK E)).slope xQ xK yQ yK)).re =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (N_eps (-1)) /
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) D_frob := by
    have hx_diff_ne : (RatFunc.X : RatFunc (ZMod p)) ^ p - RatFunc.X ≠ 0 := by
      intro h0
      apply hxQ_ne
      ext <;> simp [xQ, xK, sub_eq_zero.mp h0]
    have hy_diff : yQ - yK = ⟨0, fRat E ^ m - 1⟩ := by
      ext <;> simp [yQ, yK, QuadraticAlgebra.omega, m]
    have hx_diff : xQ - xK = ⟨RatFunc.X ^ p - RatFunc.X, 0⟩ := by
      ext <;> simp [xQ, xK]
    have hslope_eq : (E.toAffine⁄(QuadK E)).slope xQ xK yQ yK =
        ⟨0, (fRat E ^ m - 1) / (RatFunc.X ^ p - RatFunc.X)⟩ := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxQ_ne, hy_diff, hx_diff]
      exact quadK_im_div_re E (fRat E ^ m - 1) (RatFunc.X ^ p - RatFunc.X) hx_diff_ne
    rw [WeierstrassCurve.Affine.addX, base_a₁ E, base_a₂ E, hslope_eq, zero_mul, add_zero, sub_zero]
    rw [quadK_mk0i_sq E ((fRat E ^ m - 1) / (RatFunc.X ^ p - RatFunc.X))]
    simp only [QuadraticAlgebra.re_sub]
    change fRat E * ((fRat E ^ m - 1) / (RatFunc.X ^ p - RatFunc.X)) ^ 2 -
        RatFunc.X ^ p - RatFunc.X = _
    simp only [N_eps, D_frob, map_sub, map_mul, map_pow, map_add, map_neg, map_one,
      RatFunc.algebraMap_X, fRat]
    field_simp [hx_diff_ne]
    ring
  set G0 : Polynomial (ZMod p) := ∏ a ∈ S0, (Polynomial.X - Polynomial.C a)
  set Gneg : Polynomial (ZMod p) := ∏ a ∈ Sneg, (Polynomial.X - Polynomial.C a) ^ 2
  set Gpos : Polynomial (ZMod p) := ∏ a ∈ Spos, (Polynomial.X - Polynomial.C a) ^ 2
  have hG0_m : G0.Monic := Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a
  have hGneg_m : Gneg.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => (Polynomial.monic_X_sub_C a).pow 2
  have hGpos_m : Gpos.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun a _ => (Polynomial.monic_X_sub_C a).pow 2
  have hG0_deg : G0.natDegree = S0.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a]
    simp
  have hGneg_deg : Gneg.natDegree = 2 * Sneg.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ => (Polynomial.monic_X_sub_C a).pow 2]
    simp [mul_comm]
  have hGpos_deg : Gpos.natDegree = 2 * Spos.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ => (Polynomial.monic_X_sub_C a).pow 2]
    simp [mul_comm]
  have hG0_dvd_D : G0 ∣ D_frob := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact hlin_coprime a b hab
    · intro a _
      exact dvd_trans ⟨Polynomial.X - Polynomial.C a, sq _⟩ (hdvd_Dfrob a)
  have hGneg_dvd_D : Gneg ∣ D_frob := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact (hlin_coprime a b hab).pow
    · intro a _
      exact hdvd_Dfrob a
  have hGpos_dvd_D : Gpos ∣ D_frob := by
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro a _ b _ hab
      exact (hlin_coprime a b hab).pow
    · intro a _
      exact hdvd_Dfrob a
  have hG0_Gneg_cop : IsCoprime G0 Gneg := by
    refine IsCoprime.prod_left fun a ha => IsCoprime.prod_right fun b hb => ?_
    have hab : a ≠ b := by
      intro heq; subst heq
      simp only [S0, Sneg, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hb.1 ha
    exact (hlin_coprime a b hab).pow_right
  have hG0_Gpos_cop : IsCoprime G0 Gpos := by
    refine IsCoprime.prod_left fun a ha => IsCoprime.prod_right fun b hb => ?_
    have hab : a ≠ b := by
      intro heq; subst heq
      simp only [S0, Spos, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hb.1 ha
    exact (hlin_coprime a b hab).pow_right
  have hG0_dvd_N : ∀ ε : ZMod p, G0 ∣ N_eps ε := by
    intro ε
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => hlin_coprime a b hab) fun a ha => ?_
    have ha0 : (fPoly E).eval a = 0 := by
      simpa [S0] using ha
    have hd1 : Polynomial.X - Polynomial.C a ∣ fPoly E :=
      Polynomial.dvd_iff_isRoot.mpr ha0
    have hd2 : Polynomial.X - Polynomial.C a ∣ D_frob :=
      dvd_trans ⟨Polynomial.X - Polynomial.C a, sq _⟩ (hdvd_Dfrob a)
    exact dvd_sub (dvd_mul_of_dvd_left hd1 _) (dvd_mul_of_dvd_right hd2 _)
  have hGneg_dvd_N1 : Gneg ∣ N_eps 1 := by
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => (hlin_coprime a b hab).pow) fun a ha => ?_
    simp only [Sneg, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hr1 : (Polynomial.X - Polynomial.C a) ∣ (fPoly E ^ m + Polynomial.C (1 : ZMod p)) := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp [euler_neg_one hp3 ha.1 ha.2, m]
    have hd1 : (Polynomial.X - Polynomial.C a) ^ 2 ∣ (fPoly E ^ m + Polynomial.C (1 : ZMod p)) ^ 2 :=
      pow_dvd_pow_of_dvd hr1 2
    exact dvd_sub (dvd_mul_of_dvd_right hd1 _) (dvd_mul_of_dvd_right (hdvd_Dfrob a) _)
  have hGpos_dvd_Nm1 : Gpos ∣ N_eps (-1) := by
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => (hlin_coprime a b hab).pow) fun a ha => ?_
    simp only [Spos, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hp_div : m = p / 2 := by omega
    have hpow1 : ((fPoly E).eval a) ^ m = 1 := by
      rw [hp_div]
      exact (ZMod.euler_criterion p ha.1).mp ha.2
    have hr1 : (Polynomial.X - Polynomial.C a) ∣ (fPoly E ^ m + Polynomial.C (-1 : ZMod p)) := by
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
      simp [hpow1]
    have hd1 : (Polynomial.X - Polynomial.C a) ^ 2 ∣ (fPoly E ^ m + Polynomial.C (-1 : ZMod p)) ^ 2 :=
      pow_dvd_pow_of_dvd hr1 2
    exact dvd_sub (dvd_mul_of_dvd_right hd1 _) (dvd_mul_of_dvd_right (hdvd_Dfrob a) _)
  have hGm_dvd_D : G0 * Gneg ∣ D_frob := hG0_Gneg_cop.mul_dvd hG0_dvd_D hGneg_dvd_D
  have hGm_dvd_N : G0 * Gneg ∣ N_eps 1 := hG0_Gneg_cop.mul_dvd (hG0_dvd_N 1) hGneg_dvd_N1
  have hGp_dvd_D : G0 * Gpos ∣ D_frob := hG0_Gpos_cop.mul_dvd hG0_dvd_D hGpos_dvd_D
  have hGp_dvd_N : G0 * Gpos ∣ N_eps (-1) := hG0_Gpos_cop.mul_dvd (hG0_dvd_N (-1)) hGpos_dvd_Nm1
  have hGm_deg : (G0 * Gneg).natDegree = 2 * p + 1 - N := by
    rw [Polynomial.natDegree_mul hG0_m.ne_zero hGneg_m.ne_zero, hG0_deg, hGneg_deg]
    omega
  have hGp_deg : (G0 * Gpos).natDegree = N - 1 := by
    rw [Polynomial.natDegree_mul hG0_m.ne_zero hGpos_m.ne_zero, hG0_deg, hGpos_deg]
    omega
  have hdm1 : ptDeg E (ptQ hp3 E - ptP E) ≤ N := by
    rw [sub_eq_add_neg, hQ_pt, hnegP_pt, hadd_neg]
    dsimp only [ptDeg]
    rw [hx_minus_eq]
    have hb := hcancel_deg 1 (G0 * Gneg) (hG0_m.mul hGneg_m) hGm_dvd_D hGm_dvd_N
    rw [hGm_deg] at hb
    omega
  have hd1 : ptDeg E (ptQ hp3 E + ptP E) ≤ 2 * p + 2 - N := by
    rw [hQ_pt, hP_pt, hadd_pos]
    dsimp only [ptDeg]
    rw [hx_plus_eq]
    have hb := hcancel_deg (-1) (G0 * Gpos) (hG0_m.mul hGpos_m) hGp_dvd_D hGp_dvd_N
    rw [hGp_deg] at hb
    omega
  have hN_le : N ≤ 2 * p + 1 := by omega
  exact ⟨hN_le, hd0, hdm1, hd1⟩

private lemma quadratic_c_induction (c : ℤ → ℤ)
    (hconc : ∀ n : ℤ, c (n + 1) - c n ≤ c n - c (n - 1)) :
    (∀ m : ℕ, c m ≤ c 0 + (m : ℤ) * (c 1 - c 0)) ∧
      (∀ m : ℕ, c (-(m : ℤ)) ≤ c 0 + (m : ℤ) * (c (-1) - c 0)) := by
  have hstep_pos : ∀ m : ℕ, c ((m : ℤ) + 1) - c (m : ℤ) ≤ c 1 - c 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hconc ((m : ℤ) + 1)
      have hsub : (m : ℤ) + 1 - 1 = (m : ℤ) := by ring
      rw [hsub] at h1
      have hm : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by omega
      rw [hm]
      linarith
  have hstep_neg : ∀ m : ℕ, c (-(m : ℤ) - 1) - c (-(m : ℤ)) ≤ c (-1) - c 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hconc (-(m : ℤ) - 1)
      have hadd : -(m : ℤ) - 1 + 1 = -(m : ℤ) := by ring
      rw [hadd] at h1
      have hm : -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 := by omega
      rw [hm]
      linarith
  constructor
  · intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hstep_pos m
      push_cast
      linarith
  · intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := hstep_neg m
      have hm : -((m + 1 : ℕ) : ℤ) = -(m : ℤ) - 1 := by omega
      rw [hm]
      push_cast
      linarith

private lemma hasse_discriminant_le_shortNF {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] [E.IsShortNF] :
    letI := ecPointFintype E
    let N := Fintype.card E.toAffine.Point
    ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) := by
  let : Fintype E.toAffine.Point := ecPointFintype E
  set N := Fintype.card E.toAffine.Point
  set d : ℤ → ℕ := fun n => ptDeg E (ptQ hp3 E + n • ptP E)
  set c : ℤ → ℤ := fun n => (d n : ℤ) - n ^ 2
  set t : ℤ := (p : ℤ) + 1 - (N : ℤ)
  obtain ⟨hN_le, hd0, hdm1, hd1⟩ := orbit_end_bounds hp3 E
  have hconc : ∀ n : ℤ, c (n + 1) - c n ≤ c n - c (n - 1) := by
    intro n
    have hpar := ptDeg_parallelogram_le hp3 E (ptQ hp3 E + n • ptP E) (sigmaPt_orbit hp3 E n)
    have hplus : ptQ hp3 E + n • ptP E + ptP E = ptQ hp3 E + (n + 1) • ptP E := by
      module
    have hminus : ptQ hp3 E + n • ptP E - ptP E = ptQ hp3 E + (n - 1) • ptP E := by
      module
    rw [hplus, hminus] at hpar
    have hparZ : (d (n + 1) : ℤ) + (d (n - 1) : ℤ) ≤ 2 * (d n : ℤ) + 2 := by
      exact_mod_cast hpar
    dsimp [c]
    linarith
  obtain ⟨hpos_ind, hneg_ind⟩ := quadratic_c_induction c hconc
  have hc0 : c 0 = (p : ℤ) := by
    dsimp [c, d]
    rw [zero_zsmul, add_zero, hd0]
    ring
  have hc1 : c 1 - c 0 ≤ t := by
    have hd1Z : (d 1 : ℤ) ≤ 2 * (p : ℤ) + 2 - (N : ℤ) := by
      have hm1 : ptQ hp3 E + (1 : ℤ) • ptP E = ptQ hp3 E + ptP E := by rw [one_zsmul]
      dsimp [d]
      rw [hm1]
      have hcast : (ptDeg E (ptQ hp3 E + ptP E) : ℤ) ≤ ((2 * p + 2 - N : ℕ) : ℤ) :=
        Int.ofNat_le.mpr hd1
      have hsubZ : ((2 * p + 2 - N : ℕ) : ℤ) = 2 * (p : ℤ) + 2 - (N : ℤ) := by
        omega
      linarith
    dsimp [c]
    linarith [hc0]
  have hcm1 : c (-1) - c 0 ≤ -t := by
    have hdm1Z : (d (-1) : ℤ) ≤ (N : ℤ) := by
      have hm1 : ptQ hp3 E + (-1 : ℤ) • ptP E = ptQ hp3 E - ptP E := by
        rw [neg_one_zsmul, ← sub_eq_add_neg]
      dsimp [d]
      rw [hm1]
      exact_mod_cast hdm1
    dsimp [c]
    linarith [hc0]
  have hd_le : ∀ n : ℤ, (d n : ℤ) ≤ n ^ 2 + t * n + (p : ℤ) := by
    intro n
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      have h1 := hpos_ind n
      have h2 : (n : ℤ) * (c 1 - c 0) ≤ (n : ℤ) * t :=
        mul_le_mul_of_nonneg_left hc1 (Int.natCast_nonneg n)
      dsimp [c] at h1
      linarith
    · have hm : 0 ≤ -n := by omega
      lift -n to ℕ using hm with m hm_eq
      have hn_eq : n = -(m : ℤ) := by omega
      have h1 := hneg_ind m
      have h2 : (m : ℤ) * (c (-1) - c 0) ≤ (m : ℤ) * (-t) :=
        mul_le_mul_of_nonneg_left hcm1 (Int.natCast_nonneg m)
      have hm_sq : (-(m : ℤ)) ^ 2 = n ^ 2 := by rw [← hn_eq]
      have hm_t : (m : ℤ) * (-t) = t * n := by rw [hn_eq]; ring
      rw [← hn_eq] at h1
      dsimp [c] at h1
      linarith [hm_sq, hm_t]
  have ht_sq : t ^ 2 ≤ 4 * (p : ℤ) := by
    by_cases heven : t % 2 = 0
    · set k := t / 2
      have ht_eq : t = 2 * k := by omega
      have hdn := hd_le (-k)
      have hdn_nn : (0 : ℤ) ≤ (d (-k) : ℤ) := Int.natCast_nonneg _
      nlinarith
    · set k := t / 2
      have ht_eq : t = 2 * k + 1 := by omega
      by_contra hlt
      push Not at hlt
      have hpk : (p : ℤ) - k * (k + 1) ≤ 0 := by nlinarith
      have hd_k : d (-k) = 0 := by
        have hdn := hd_le (-k)
        have hdn_le0 : (d (-k) : ℤ) ≤ 0 := by
          have hid : (-k) ^ 2 + t * (-k) + (p : ℤ) = (p : ℤ) - k * (k + 1) := by
            rw [ht_eq]; ring
          linarith
        omega
      have hd_k1 : d (-k - 1) = 0 := by
        have hdn := hd_le (-k - 1)
        have hdn_le0 : (d (-k - 1) : ℤ) ≤ 0 := by
          have hid : (-k - 1) ^ 2 + t * (-k - 1) + (p : ℤ) = (p : ℤ) - k * (k + 1) := by
            rw [ht_eq]; ring
          linarith
        omega
      have h2k := two_smul_eq_zero_of_ptDeg_eq_zero hp3 E (sigmaPt_orbit hp3 E (-k)) hd_k
      have h2k1 := two_smul_eq_zero_of_ptDeg_eq_zero hp3 E (sigmaPt_orbit hp3 E (-k - 1)) hd_k1
      have hdiff : (2 : ℤ) • ptP E = 0 := by
        calc (2 : ℤ) • ptP E
            = (2 : ℤ) • (ptQ hp3 E + (-k) • ptP E) -
                (2 : ℤ) • (ptQ hp3 E + (-k - 1) • ptP E) := by module
          _ = 0 - 0 := by rw [h2k, h2k1]
          _ = 0 := sub_self 0
      exact two_smul_ptP_ne_zero hp3 E hdiff
  dsimp only
  have hsq_eq : ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 = t ^ 2 := by
    dsimp [t]; ring
  rw [hsq_eq]
  exact ht_sq

end ManinHasse

theorem solution :
    ∀ (p : ℕ) [Fact p.Prime], 3 < p →
      ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
        letI := ecPointFintype E
        let N := Fintype.card E.toAffine.Point
        ∀ m n : ℤ, 0 ≤ m ^ 2 * (p : ℤ) - m * n * ((p : ℤ) + 1 - (N : ℤ)) + n ^ 2 := by
  intro p _ hp3 E _
  letI := ecPointFintype E
  set N := Fintype.card E.toAffine.Point
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero (zmod_two_ne_zero hp3)
  haveI : Invertible (3 : ZMod p) := invertibleOfNonzero (zmod_three_ne_zero hp3)
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_isShortNF E
  have hcard : N = @Fintype.card (C • E).toAffine.Point (ecPointFintype (C • E)) :=
    card_variableChange_eq E C
  have hdisc : ((N : ℤ) - ((p : ℤ) + 1)) ^ 2 ≤ 4 * (p : ℤ) := by
    rw [hcard]
    exact hasse_discriminant_le_shortNF hp3 (C • E)
  have hp_pos : (0 : ℤ) < (p : ℤ) := by omega
  exact (quadratic_form_nonneg_iff_hasse_discriminant.2 (p : ℤ) (N : ℤ) hp_pos).mpr hdisc
