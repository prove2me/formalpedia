-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/bf1c7ec2-f713-537e-afa5-c5397e60a693

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

noncomputable section

namespace DDF3b

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule IsLocalRing
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)
open scoped Matrix

variable {q : ℕ} [Fact q.Prime]

section homs

variable {A : Type u} [CommRing A] {A' : Type u} [CommRing A']

theorem cc_map {φ : Series A} (hφ : ∀ i, constantCoeff (φ i) = 0) (f : A →+* A') (i : Fin 2) :
    constantCoeff ((φ.map f) i) = 0 := by
  show constantCoeff (MvPowerSeries.map f (φ i)) = 0
  rw [MvPowerSeries.constantCoeff_map, hφ i, map_zero]

theorem cc_id (i : Fin 2) : constantCoeff (Series.id A i) = 0 := constantCoeff_X _

variable {X Y Z : FormalODModule q A}

theorem hom_cc (f : X.Hom Y) (i : Fin 2) : constantCoeff (f.toSeries i) = 0 :=
  f.isODHom.constantCoeff i

@[scoped simp] theorem comp_toSeries (g : Y.Hom Z) (f : X.Hom Y) :
    (g.comp f).toSeries = g.toSeries.comp f.toSeries := rfl

@[scoped simp] theorem map_toSeries (r : A →+* A') (f : X.Hom Y) :
    (f.map r).toSeries = f.toSeries.map r := rfl

@[scoped simp] theorem id_toSeries : (FormalODModule.Hom.id X).toSeries = Series.id A := rfl

theorem id_isIso (X : FormalODModule q A) : (FormalODModule.Hom.id X).IsIso :=
  ⟨FormalODModule.Hom.id X, FormalODModule.Hom.ext (Series.comp_id _),
    FormalODModule.Hom.ext (Series.comp_id _)⟩

def castHom {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A} (w : X.Hom Y) :
    X'.Hom Y :=
  ⟨w.toSeries, by rw [← h]; exact w.isODHom⟩

@[scoped simp] theorem castHom_toSeries {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A}
    (w : X.Hom Y) : (castHom h w).toSeries = w.toSeries := rfl

theorem castHom_isIso {X X' : FormalODModule q A} (h : X = X') {Y : FormalODModule q A}
    (w : X.Hom Y) (hw : w.IsIso) : (castHom h w).IsIso := by
  subst h
  have : castHom rfl w = w := FormalODModule.Hom.ext rfl
  rw [this]
  exact hw

def castHomT {Y Y' : FormalODModule q A} (h : Y = Y') {X : FormalODModule q A} (w : X.Hom Y) :
    X.Hom Y' :=
  ⟨w.toSeries, by rw [← h]; exact w.isODHom⟩

@[scoped simp] theorem castHomT_toSeries {Y Y' : FormalODModule q A} (h : Y = Y') {X : FormalODModule q A}
    (w : X.Hom Y) : (castHomT h w).toSeries = w.toSeries := rfl

theorem castHomT_isIso {Y Y' : FormalODModule q A} (h : Y = Y') {X : FormalODModule q A}
    (w : X.Hom Y) (hw : w.IsIso) : (castHomT h w).IsIso := by
  subst h
  have : castHomT rfl w = w := FormalODModule.Hom.ext rfl
  rw [this]
  exact hw

theorem inverse_unique {s g₁ g₂ : Series A} (hs : ∀ i, constantCoeff (s i) = 0)
    (hg₂ : ∀ i, constantCoeff (g₂ i) = 0)
    (h₁ : g₁.comp s = Series.id A) (h₂ : s.comp g₂ = Series.id A) : g₁ = g₂ := by
  calc g₁ = g₁.comp (Series.id A) := (Series.comp_id _).symm
    _ = g₁.comp (s.comp g₂) := by rw [h₂]
    _ = (g₁.comp s).comp g₂ := (Series.comp_assoc _ _ _ hs hg₂).symm
    _ = g₂ := by rw [h₁, Series.id_comp _ hg₂]

theorem isIso_comp {g : Y.Hom Z} {f : X.Hom Y} (hg : g.IsIso) (hf : f.IsIso) : (g.comp f).IsIso := by
  obtain ⟨g', hg'₁, hg'₂⟩ := hg
  obtain ⟨f', hf'₁, hf'₂⟩ := hf
  have e1 := congrArg FormalODModule.Hom.toSeries hg'₁
  have e2 := congrArg FormalODModule.Hom.toSeries hg'₂
  have e3 := congrArg FormalODModule.Hom.toSeries hf'₁
  have e4 := congrArg FormalODModule.Hom.toSeries hf'₂
  simp only [comp_toSeries, id_toSeries] at e1 e2 e3 e4
  refine ⟨f'.comp g', FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · show (f'.toSeries.comp g'.toSeries).comp (g.toSeries.comp f.toSeries) = Series.id A
    rw [Series.comp_assoc _ _ _ (hom_cc g') (Series.constantCoeff_comp (hom_cc g) (hom_cc f)),
      ← Series.comp_assoc g'.toSeries _ _ (hom_cc g) (hom_cc f), e1, Series.id_comp _ (hom_cc f), e3]
  · show (g.toSeries.comp f.toSeries).comp (f'.toSeries.comp g'.toSeries) = Series.id A
    rw [Series.comp_assoc _ _ _ (hom_cc f) (Series.constantCoeff_comp (hom_cc f') (hom_cc g')),
      ← Series.comp_assoc f.toSeries _ _ (hom_cc f') (hom_cc g'), e4, Series.id_comp _ (hom_cc g'), e2]

theorem isIso_map (r : A →+* A') {f : X.Hom Y} (hf : f.IsIso) : (f.map r).IsIso := by
  obtain ⟨f', hf'₁, hf'₂⟩ := hf
  have e3 := congrArg FormalODModule.Hom.toSeries hf'₁
  have e4 := congrArg FormalODModule.Hom.toSeries hf'₂
  simp only [comp_toSeries, id_toSeries] at e3 e4
  refine ⟨f'.map r, FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · show (f'.toSeries.map r).comp (f.toSeries.map r) = Series.id A'
    rw [← Series.map_comp r _ _ (hom_cc f), e3, Series.map_id]
  · show (f.toSeries.map r).comp (f'.toSeries.map r) = Series.id A'
    rw [← Series.map_comp r _ _ (hom_cc f'), e4, Series.map_id]

theorem exists_inv {f : X.Hom Y} (hf : f.IsIso) :
    ∃ g : Y.Hom X, g.toSeries.comp f.toSeries = Series.id A ∧ f.toSeries.comp g.toSeries = Series.id A := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  have e1 := congrArg FormalODModule.Hom.toSeries hg₁
  have e2 := congrArg FormalODModule.Hom.toSeries hg₂
  simp only [comp_toSeries, id_toSeries] at e1 e2
  exact ⟨g, e1, e2⟩

end homs

section dual

variable (k : Type u) [Field k]

abbrev resD : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

theorem resD_surjective : Function.Surjective (resD k) := fun a =>
  ⟨TrivSqZeroExt.inl a, rfl⟩

theorem isLocalHom_resD : IsLocalHom (resD k) := by
  refine ⟨fun x hx => ?_⟩
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hx

theorem ker_resD_sq : RingHom.ker (resD k) ^ (1 + 1) = ⊥ := by
  rw [pow_succ, pow_one, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  change TrivSqZeroExt.fst r = 0 at hr
  change TrivSqZeroExt.fst s = 0 at hs
  rw [Ideal.mem_bot]
  refine TrivSqZeroExt.ext ?_ ?_
  · change TrivSqZeroExt.fst (r * s) = 0
    rw [TrivSqZeroExt.fst_mul, hr, zero_mul]
  · change TrivSqZeroExt.snd (r * s) = 0
    rw [DualNumber.snd_mul, hr, hs, zero_mul, mul_zero, add_zero]

theorem resD_comp_inl : (resD k).comp (TrivSqZeroExt.inlHom k k) = RingHom.id k := RingHom.ext fun _ => rfl

variable {k}

end dual

section nose
variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
include X₀

theorem exists_nose_over {B : Type u} [CommRing B] (resB : B →+* k) (hs : Function.Surjective resB)
    (hloc : IsLocalHom resB) (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule)
    (hu : u.IsIso) :
    ∃ Y' : FormalODModule q B, Y'.map resB = X₀.toFormalODModule ∧
      ∃ v : Y'.Hom Y, v.IsIso ∧ u.toSeries.comp (v.toSeries.map resB) = Series.id k := by
  obtain ⟨part1, -⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_map_eq_and_exists_isIso_of_pullback_of_surjective X₀
      (B := B) (A' := k) (A'' := B) (A := k)
      resB (RingHom.id B) (RingHom.id k) resB (RingHom.ext fun _ => rfl)
      (fun a' a'' h => ⟨a'', ⟨h.symm, rfl⟩, fun b hb => hb.2⟩) hs hloc
      resB (RingHom.id k) resB (RingHom.id k)
      (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)
      (RingHom.ext fun _ => rfl) Function.surjective_id
      ⟨1, by rw [pow_one, (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id]; rfl⟩
  obtain ⟨g, hg₁, hg₂⟩ := exists_inv hu
  have hgiso : g.IsIso := ⟨u, FormalODModule.Hom.ext hg₂, FormalODModule.Hom.ext hg₁⟩
  have hmid : X₀.toFormalODModule.map (RingHom.id k) = X₀.toFormalODModule := FormalODModule.map_id _
  let w' : (X₀.toFormalODModule.map (RingHom.id k)).Hom X₀.toFormalODModule :=
    castHom hmid.symm (FormalODModule.Hom.id _)
  have hw' : w'.IsIso := castHom_isIso _ _ (id_isIso _)
  let φ' : (X₀.toFormalODModule.map (RingHom.id k)).Hom (Y.map resB) := castHom hmid.symm g
  have hφ' : φ'.IsIso := castHom_isIso _ _ hgiso
  have hcompat : u.toSeries.comp (φ'.toSeries.map (RingHom.id k)) = w'.toSeries := by
    show u.toSeries.comp (g.toSeries.map (RingHom.id k)) = Series.id k
    rw [Series.map_ringHom_id, hg₂]
  obtain ⟨Y', u', -, hY', hu', v, hv, -, hc⟩ := part1 X₀.toFormalODModule w' hw' Y u hu φ' hφ' hcompat
  have hvid : Y'.map (RingHom.id B) = Y' := FormalODModule.map_id _
  refine ⟨Y', hY', castHom hvid v, castHom_isIso _ _ hv, ?_⟩
  show u.toSeries.comp (v.toSeries.map resB) = Series.id k
  rw [hc, hu']
  rfl

end nose

end DDF3b
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.DDF3b"

namespace DDF3bGen
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Matrix

section Generic
variable {q : ℕ} [Fact q.Prime]
variable {B : Type} [CommRing B] {B' : Type} [CommRing B']

open MvPowerSeries in
theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_map (f : B →+* B') (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  simp [MvFormalGroup.linearPart, Series.map, MvPowerSeries.coeff_map]

theorem linearPart_id : MvFormalGroup.linearPart (Series.id B) = 1 := by
  unfold Series.id
  exact MvFormalGroup.linearPart_X

theorem mem_lieZero_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieZero j ↔ ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j a • m := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem mem_lieOne_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieOne j ↔
      ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j (WittVector.frobenius a) • m := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem frob_frob (a : Zp2 q) : WittVector.frobenius (WittVector.frobenius a) = a := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  rw [← pow_mul, ← pow_two, ← GaloisField.card q 2 two_ne_zero, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem linearPart_varpi_mul_self (X : FormalODModule q B) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart X.varpi =
      ((q : ℕ) : B) • (1 : Matrix (Fin 2) (Fin 2) B) := by
  have h := congrArg MvFormalGroup.linearPart X.varpi_comp_varpi
  rw [linearPart_comp _ _ X.isLawHom_varpi.1, FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries] at h
  rw [h]
  ext i i'
  simp [Matrix.smul_apply, nsmul_eq_mul]

theorem linearPart_varpi_mul_act (X : FormalODModule q B) (a : Zp2 q) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (X.act (WittVector.frobenius a)) * MvFormalGroup.linearPart X.varpi := by
  have h := congrArg MvFormalGroup.linearPart (X.varpi_comp_act a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ X.isLawHom_varpi.1] at h

theorem Hom.linearPart_mul_act {X Y : FormalODModule q B} (w : X.Hom Y) (a : Zp2 q) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (Y.act a) * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart (w.isODHom.2.1 a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.linearPart_mul_varpi {X Y : FormalODModule q B} (w : X.Hom Y) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart X.varpi =
      MvFormalGroup.linearPart Y.varpi * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart w.isODHom.2.2
  rwa [linearPart_comp _ _ X.isLawHom_varpi.1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.exists_mul_linearPart_eq_one {X Y : FormalODModule q B} (w : X.Hom Y) (hw : w.IsIso) :
    ∃ W' : Matrix (Fin 2) (Fin 2) B, W' * MvFormalGroup.linearPart w.toSeries = 1 := by
  obtain ⟨g, hg, -⟩ := hw
  refine ⟨MvFormalGroup.linearPart g.toSeries, ?_⟩
  have h := congrArg (fun f : X.Hom X => MvFormalGroup.linearPart f.toSeries) hg
  simp only [FormalODModule.Hom.comp] at h
  rw [linearPart_comp _ _ w.isODHom.1.1] at h
  rw [h]
  exact linearPart_id

theorem Hom.isIso_cast {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) (hw : w.IsIso) :
    (h ▸ w : X'.Hom Y).IsIso := by
  subst h
  exact hw

end Generic
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.DDF3b"

section MatrixLemmas
variable {R S : Type} [CommRing R] [CommRing S]

theorem map_sub_smul_one (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (c : R) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) R)).map f = A.map f - f c • (1 : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem sub_smul_one_mulVec (A : Matrix (Fin 2) (Fin 2) R) (c : R) (v : Fin 2 → R) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) R)) *ᵥ v = A *ᵥ v - c • v := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem eq_zero_of_forall_mulVec_eq_zero (A : Matrix (Fin 2) (Fin 2) R) (h : ∀ v, A *ᵥ v = 0) : A = 0 := by
  have : Matrix.toLin' A = 0 := LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v
  exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').mp this

theorem map_mulVec_apply (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) (i : Fin 2) :
    f ((A *ᵥ v) i) = (A.map f *ᵥ (f ∘ v)) i :=
  RingHom.map_mulVec f A v i

theorem funext_fin_two {X : Type} {f g : Fin 2 → X} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i
  exact (Fin.forall_fin_two (p := fun i => f i = g i)).mpr ⟨h0, h1⟩ i

theorem exists_smul_of_det_eq_zero {k : Type} [Field k] (v w : Fin 2 → k) (hv : v ≠ 0)
    (h : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : k, w = c • v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv
      exact funext_fin_two (by simp [h0]) (by simp [h1])
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    refine ⟨w 1 / v 1, funext_fin_two ?_ ?_⟩
    · simp [h0, hw0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨w 0 / v 0, funext_fin_two ?_ ?_⟩
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem existsUnique_coords (e₀ e₁ : Fin 2 → R) (δinv : R)
    (hδ : δinv * (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) = 1) (m : Fin 2 → R) :
    ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁ := by
  refine ⟨(δinv * (m 0 * e₁ 1 - m 1 * e₁ 0), δinv * (e₀ 0 * m 1 - e₀ 1 * m 0)), ?_, ?_⟩
  · refine funext_fin_two ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 0)) * hδ
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 1)) * hδ
  · rintro ⟨c₁, c₂⟩ hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    ext
    · simp only
      linear_combination (-c₁) * hδ - δinv * e₁ 1 * h0 + δinv * e₁ 0 * h1
    · simp only
      linear_combination (-c₂) * hδ + δinv * e₀ 1 * h0 - δinv * e₀ 0 * h1

end MatrixLemmas
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.DDF3b"

end DDF3bGen
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.DDF3b"

namespace DDF3bGen

section DualLinAlg
variable {k : Type} [Field k]
open TrivSqZeroExt
open scoped Matrix

theorem dual_mulVec_congr (L : Matrix (Fin 2) (Fin 2) (DualNumber k)) (hL : ∀ i j, fst (L i j) = 0)
    (z z' : Fin 2 → DualNumber k) (h : ∀ j, fst (z j) = fst (z' j)) : L *ᵥ z = L *ᵥ z' := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply TrivSqZeroExt.ext
  · rw [fst_mul, fst_mul, h j]
  · rw [DualNumber.snd_mul, DualNumber.snd_mul, hL, zero_mul, zero_mul, h j]

theorem fst_comp_mulVec (L : Matrix (Fin 2) (Fin 2) (DualNumber k)) (z : Fin 2 → DualNumber k) :
    (fun i => fst ((L *ᵥ z) i)) = L.map (fstHom k k k).toRingHom *ᵥ (fun i => fst (z i)) := by
  funext i
  exact RingHom.map_mulVec (fstHom k k k).toRingHom L z i

end DualLinAlg
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.DDF3b"

end DDF3bGen
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations.DDF3b"

open DDF3b DDF3bGen IsLocalRing in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
open scoped Matrix in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hnode₀ : (∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (hnode₁ : (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (e₀ e₁ : Xu.Lie) (u v : R)
    (he₀ : e₀ ∈ Xu.lieZero ((algebraMap Onr R).comp ι)) (he₁ : e₁ ∈ Xu.lieOne ((algebraMap Onr R).comp ι))
    (hbasis : ∀ m : Xu.Lie, ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁)
    (hu : Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) e₀ = u • e₁) (hv : Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) e₁ = v • e₀)
    (χ χ' : R →+* DualNumber (IsLocalRing.ResidueField Onr))
    (hχ : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ = resR ∧ χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)))
    (hχ' : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ' = resR ∧ χ'.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)))
    (hχu : χ u = χ' u) (hχv : χ v = χ' v) :
    χ = χ' := by
  classical

  letI iAlg : Algebra Onr (DualNumber (IsLocalRing.ResidueField Onr)) :=
    ((algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)).toAlgebra
  haveI : Module.Finite (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr)) :=
    inferInstanceAs (Module.Finite (IsLocalRing.ResidueField Onr) ((IsLocalRing.ResidueField Onr) × (IsLocalRing.ResidueField Onr)))
  haveI : IsArtinianRing (DualNumber (IsLocalRing.ResidueField Onr)) :=
    IsArtinianRing.of_finite (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))
  have hqk : ((q : ℕ) : IsLocalRing.ResidueField Onr) = 0 := by
    have hmem : ((q : ℕ) : Onr) ∈ maximalIdeal Onr := by
      rw [← IsLocalRing.eq_maximalIdeal hOnr_max, ← map_natCast (algebraMap ℤ_[q] Onr) q]
      exact Ideal.subset_span rfl
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (IsLocalRing.ResidueField Onr) q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hqk
  have hfst_surj : Function.Surjective (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hfst_alg : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp (algebraMap Onr (DualNumber (IsLocalRing.ResidueField Onr))) = IsLocalRing.residue Onr := by
    ext o; rfl
  have Eχ : ∀ ψ : R →+* DualNumber (IsLocalRing.ResidueField Onr), ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp ψ = resR →
      Xu.map resR = (Xu.map ψ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom := by
    intro ψ h; rw [FormalODModule.map_map, h]
  have hSH : ∀ ψ : R →+* DualNumber (IsLocalRing.ResidueField Onr), ∀ h : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp ψ = resR,
      (Xu.map ψ).IsSpecial ((algebraMap Onr (DualNumber (IsLocalRing.ResidueField Onr))).comp ι) ∧ (Xu.map ψ).HasHeight 4 :=
    fun ψ h => CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing Onr ι X₀
      (DualNumber (IsLocalRing.ResidueField Onr)) (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom hfst_surj hfst_alg (Xu.map ψ) (castHom (Eχ ψ h) wu)
      (castHom_isIso _ wu hwu)
  have mkAlg : ∀ ψ : R →+* DualNumber (IsLocalRing.ResidueField Onr),
      ψ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr) →
      ∃ φ : R →ₐ[Onr] DualNumber (IsLocalRing.ResidueField Onr), φ.toRingHom = ψ := fun ψ h =>
    ⟨{ toRingHom := ψ, commutes' := fun o => by
        change ψ (algebraMap Onr R o) = ((algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) o
        rw [← h]; rfl }, rfl⟩

  have hPi0 : MvFormalGroup.linearPart X₀.varpi = 0 := by
    apply eq_zero_of_forall_mulVec_eq_zero
    intro m
    have hm : m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι) ⊔
        X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι) := by
      rw [X₀.isSpecial.1.sup_eq_top]; trivial
    obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hm
    have h0 := hnode₀ y₀ hy₀
    have h1 := hnode₁ y₁ hy₁
    rw [Matrix.mulVecLin_apply] at h0 h1
    rw [Matrix.mulVec_add, h0, h1, add_zero]

  have hsurj : Function.Surjective resR := by
    intro y; obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩

  obtain ⟨gw, hgw₁, hgw₂⟩ := exists_inv hwu
  have hW₁ : MvFormalGroup.linearPart gw.toSeries * MvFormalGroup.linearPart wu.toSeries = 1 := by
    have h := congrArg MvFormalGroup.linearPart hgw₁
    rwa [linearPart_comp _ _ (hom_cc wu), linearPart_id] at h
  have hW₂ : MvFormalGroup.linearPart wu.toSeries * MvFormalGroup.linearPart gw.toSeries = 1 := by
    have h := congrArg MvFormalGroup.linearPart hgw₂
    rwa [linearPart_comp _ _ (hom_cc gw), linearPart_id] at h

  have hspan : ∀ y : Fin 2 → IsLocalRing.ResidueField Onr, ∃ c₀ c₁ : IsLocalRing.ResidueField Onr,
      y = c₀ • (MvFormalGroup.linearPart wu.toSeries *ᵥ ((resR : R → _) ∘ e₀)) +
          c₁ • (MvFormalGroup.linearPart wu.toSeries *ᵥ ((resR : R → _) ∘ e₁)) := by
    intro y
    set x : Fin 2 → IsLocalRing.ResidueField Onr := MvFormalGroup.linearPart gw.toSeries *ᵥ y with hx
    obtain ⟨xt, hxt⟩ : ∃ xt : Fin 2 → R, (resR : R → _) ∘ xt = x :=
      ⟨fun i => (hsurj (x i)).choose, funext fun i => (hsurj (x i)).choose_spec⟩
    obtain ⟨⟨c₀, c₁⟩, hc, -⟩ := hbasis xt
    refine ⟨resR c₀, resR c₁, ?_⟩
    have hy : y = MvFormalGroup.linearPart wu.toSeries *ᵥ x := by
      rw [hx, Matrix.mulVec_mulVec, hW₂, Matrix.one_mulVec]
    have hx' : x = resR c₀ • ((resR : R → _) ∘ e₀) + resR c₁ • ((resR : R → _) ∘ e₁) := by
      rw [← hxt, hc]; funext i; simp
    rw [hy, hx', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]

  set gb₀ : Fin 2 → IsLocalRing.ResidueField Onr := MvFormalGroup.linearPart wu.toSeries *ᵥ ((resR : R → _) ∘ e₀) with hgb₀
  set gb₁ : Fin 2 → IsLocalRing.ResidueField Onr := MvFormalGroup.linearPart wu.toSeries *ᵥ ((resR : R → _) ∘ e₁) with hgb₁
  have hgbne : gb₀ ≠ 0 ∧ gb₁ ≠ 0 := by
    have key : ∀ a b : Fin 2 → IsLocalRing.ResidueField Onr,
        (∀ y : Fin 2 → IsLocalRing.ResidueField Onr, ∃ c₀ c₁ : IsLocalRing.ResidueField Onr, y = c₀ • a + c₁ • b) → a ≠ 0 := by
      intro a b hab ha
      rw [ha] at hab
      obtain ⟨c₀, c₁, h1⟩ := hab (Pi.single 0 1)
      obtain ⟨d₀, d₁, h2⟩ := hab (Pi.single 1 1)
      simp only [smul_zero, zero_add] at h1 h2
      have h10 := congrFun h1 0; have h11 := congrFun h1 1
      have h20 := congrFun h2 0; have h21 := congrFun h2 1
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, ne_eq, Pi.single_eq_of_ne (show (1 : Fin 2) ≠ 0 by decide),
        Pi.single_eq_of_ne (show (0 : Fin 2) ≠ 1 by decide)] at h10 h11 h20 h21

      have hc₁ : c₁ ≠ 0 := fun h => by rw [h, zero_mul] at h10; exact one_ne_zero h10
      have hb1 : b 1 = 0 := (mul_eq_zero.mp h11.symm).resolve_left hc₁
      rw [hb1, mul_zero] at h21; exact one_ne_zero h21
    refine ⟨key gb₀ gb₁ hspan, key gb₁ gb₀ fun y => ?_⟩
    obtain ⟨c₀, c₁, h⟩ := hspan y; exact ⟨c₁, c₀, by rw [h, add_comm]⟩

  have hu' : MvFormalGroup.linearPart Xu.varpi *ᵥ e₀ = u • e₁ := by rw [← Matrix.mulVecLin_apply]; exact hu
  have hv' : MvFormalGroup.linearPart Xu.varpi *ᵥ e₁ = v • e₀ := by rw [← Matrix.mulVecLin_apply]; exact hv
  have nose : ∀ (ψ : R →+* (DualNumber (IsLocalRing.ResidueField Onr)))
      (hψ : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp ψ = resR ∧ ψ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr))),
      ∃ (N : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr))) (hN : N.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = X₀.toFormalODModule)
        (vN : N.Hom (Xu.map ψ)), vN.IsIso ∧
        wu.toSeries.comp (vN.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = Series.id _ ∧
        TrivSqZeroExt.fst (ψ u) = 0 ∧ TrivSqZeroExt.fst (ψ v) = 0 ∧
        ∀ z : Fin 2 → (DualNumber (IsLocalRing.ResidueField Onr)), ∀ c₀ c₁ : IsLocalRing.ResidueField Onr,
          (fun i => TrivSqZeroExt.fst (z i)) = c₀ • gb₀ + c₁ • gb₁ →
          MvFormalGroup.linearPart N.varpi *ᵥ z =
            fun i => TrivSqZeroExt.inr (c₀ * (TrivSqZeroExt.snd (ψ u) * gb₁ i) + c₁ * (TrivSqZeroExt.snd (ψ v) * gb₀ i)) := by
    intro ψ hψ
    obtain ⟨N, hN, vN, hvN, hcN⟩ := exists_nose_over X₀ (resD (IsLocalRing.ResidueField Onr))
      (resD_surjective _) (isLocalHom_resD _) (Xu.map ψ) (castHom (Eχ ψ hψ.1) wu) (castHom_isIso _ wu hwu)
    rw [castHom_toSeries] at hcN
    refine ⟨N, hN, vN, hvN, hcN, ?_⟩

    obtain ⟨g, hg₁, hg₂⟩ := exists_inv hvN
    set L := MvFormalGroup.linearPart N.varpi with hL
    set V := MvFormalGroup.linearPart vN.toSeries with hV
    set G := MvFormalGroup.linearPart g.toSeries with hG
    have hGV : G * V = 1 := by
      have h := congrArg MvFormalGroup.linearPart hg₁
      rwa [linearPart_comp _ _ (hom_cc vN), linearPart_id] at h
    have hVG : V * G = 1 := by
      have h := congrArg MvFormalGroup.linearPart hg₂
      rwa [linearPart_comp _ _ (hom_cc g), linearPart_id] at h
    have hMψ : MvFormalGroup.linearPart (Xu.map ψ).varpi = (MvFormalGroup.linearPart Xu.varpi).map ψ := by
      rw [FormalODModule.map_varpi, linearPart_map]
    have hVL : V * L = (MvFormalGroup.linearPart Xu.varpi).map ψ * V := by
      rw [← hMψ]; exact Hom.linearPart_mul_varpi vN
    have hLG : L * G = G * (MvFormalGroup.linearPart Xu.varpi).map ψ := by
      calc L * G = (G * V) * L * G := by rw [hGV, one_mul]
        _ = G * (V * L) * G := by rw [mul_assoc G V L]
        _ = G * ((MvFormalGroup.linearPart Xu.varpi).map ψ * V) * G := by rw [hVL]
        _ = G * (MvFormalGroup.linearPart Xu.varpi).map ψ * (V * G) := by
              simp only [mul_assoc]
        _ = G * (MvFormalGroup.linearPart Xu.varpi).map ψ := by rw [hVG, mul_one]

    set g₀ : Fin 2 → (DualNumber (IsLocalRing.ResidueField Onr)) := G *ᵥ ((ψ : R → _) ∘ e₀) with hg₀
    set g₁ : Fin 2 → (DualNumber (IsLocalRing.ResidueField Onr)) := G *ᵥ ((ψ : R → _) ∘ e₁) with hg₁'
    have hmape₀ : (MvFormalGroup.linearPart Xu.varpi).map ψ *ᵥ ((ψ : R → _) ∘ e₀) = ψ u • ((ψ : R → _) ∘ e₁) := by
      funext i
      rw [← RingHom.map_mulVec ψ (MvFormalGroup.linearPart Xu.varpi) e₀ i, hu']
      simp
    have hmape₁ : (MvFormalGroup.linearPart Xu.varpi).map ψ *ᵥ ((ψ : R → _) ∘ e₁) = ψ v • ((ψ : R → _) ∘ e₀) := by
      funext i
      rw [← RingHom.map_mulVec ψ (MvFormalGroup.linearPart Xu.varpi) e₁ i, hv']
      simp
    have hLg₀ : L *ᵥ g₀ = ψ u • g₁ := by
      rw [hg₀, Matrix.mulVec_mulVec, hLG, ← Matrix.mulVec_mulVec, hmape₀, Matrix.mulVec_smul]
    have hLg₁ : L *ᵥ g₁ = ψ v • g₀ := by
      rw [hg₁', Matrix.mulVec_mulVec, hLG, ← Matrix.mulVec_mulVec, hmape₁, Matrix.mulVec_smul]

    have hL0 : ∀ i j, TrivSqZeroExt.fst (L i j) = 0 := by
      intro i j
      have h : L.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = 0 := by
        rw [hL, ← linearPart_map, ← FormalODModule.map_varpi, hN, hPi0]
      have := congrFun (congrFun h i) j
      simpa using this
    have hGf : G.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = MvFormalGroup.linearPart wu.toSeries := by
      have h1 : MvFormalGroup.linearPart wu.toSeries * V.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = 1 := by
        have h := congrArg MvFormalGroup.linearPart hcN
        rwa [linearPart_comp _ _ (cc_map (hom_cc vN) _), linearPart_map, linearPart_id] at h
      have h2 : V.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom * G.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = 1 := by
        rw [← Matrix.map_mul, hVG, Matrix.map_one _ (map_zero _) (map_one _)]
      calc G.map _ = (MvFormalGroup.linearPart wu.toSeries * V.map _) * G.map _ := by rw [h1, one_mul]
        _ = MvFormalGroup.linearPart wu.toSeries := by rw [mul_assoc, h2, mul_one]
    have hψres : ∀ r : R, TrivSqZeroExt.fst (ψ r) = resR r := fun r => by
      have := congrArg (fun f : R →+* IsLocalRing.ResidueField Onr => f r) hψ.1
      simpa using this
    have hfg₀ : (fun i => TrivSqZeroExt.fst (g₀ i)) = gb₀ := by
      rw [hg₀, fst_comp_mulVec, hGf, hgb₀]
      congr 1; funext i; exact hψres _
    have hfg₁ : (fun i => TrivSqZeroExt.fst (g₁ i)) = gb₁ := by
      rw [hg₁', fst_comp_mulVec, hGf, hgb₁]
      congr 1; funext i; exact hψres _

    have hLf : ∀ z : Fin 2 → (DualNumber (IsLocalRing.ResidueField Onr)), (fun i => TrivSqZeroExt.fst ((L *ᵥ z) i)) = 0 := by
      intro z
      rw [fst_comp_mulVec]
      have : L.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = 0 := by ext i j; simpa using hL0 i j
      rw [this, Matrix.zero_mulVec]
    have hfu : TrivSqZeroExt.fst (ψ u) = 0 := by
      have h := hLf g₀
      rw [hLg₀] at h
      have h' : TrivSqZeroExt.fst (ψ u) • gb₁ = 0 := by
        rw [← hfg₁]; funext i; have := congrFun h i; simpa [TrivSqZeroExt.fst_mul] using this
      exact (smul_eq_zero.mp h').resolve_right hgbne.2
    have hfv : TrivSqZeroExt.fst (ψ v) = 0 := by
      have h := hLf g₁
      rw [hLg₁] at h
      have h' : TrivSqZeroExt.fst (ψ v) • gb₀ = 0 := by
        rw [← hfg₀]; funext i; have := congrFun h i; simpa [TrivSqZeroExt.fst_mul] using this
      exact (smul_eq_zero.mp h').resolve_right hgbne.1
    refine ⟨hfu, hfv, ?_⟩

    intro z c₀ c₁ hz
    have hz' : ∀ j, TrivSqZeroExt.fst (z j) =
        TrivSqZeroExt.fst ((((TrivSqZeroExt.inl c₀ : DualNumber (IsLocalRing.ResidueField Onr))) • g₀ +
          (TrivSqZeroExt.inl c₁ : DualNumber (IsLocalRing.ResidueField Onr)) • g₁) j) := by
      intro j
      have := congrFun hz j
      rw [this]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul,
        TrivSqZeroExt.fst_inl]
      rw [← congrFun hfg₀ j, ← congrFun hfg₁ j]
    rw [dual_mulVec_congr L hL0 z _ hz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hLg₀, hLg₁]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, hfu, hfv]
    · rw [TrivSqZeroExt.snd_add, DualNumber.snd_mul, DualNumber.snd_mul, DualNumber.snd_mul, DualNumber.snd_mul,
        hfu, hfv, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.snd_inr, ← congrFun hfg₀ i, ← congrFun hfg₁ i]
      ring

  obtain ⟨N, hN, vN, hvN, hcN, -, -, hLN⟩ := nose χ hχ
  obtain ⟨N', hN', vN', hvN', hcN', -, -, hLN'⟩ := nose χ' hχ'
  have hLL : MvFormalGroup.linearPart N.varpi = MvFormalGroup.linearPart N'.varpi := by
    apply sub_eq_zero.mp
    apply eq_zero_of_forall_mulVec_eq_zero
    intro z
    rw [Matrix.sub_mulVec, sub_eq_zero]
    obtain ⟨c₀, c₁, hc⟩ := hspan (fun i => TrivSqZeroExt.fst (z i))
    rw [hLN z c₀ c₁ hc, hLN' z c₀ c₁ hc, hχu, hχv]

  obtain ⟨θ, hθ, hθf⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_isIso_map_fstHom_eq_id_of_linearPart_varpi_eq
      X₀ hnode₀ hnode₁ N N' hN hN' hLL

  obtain ⟨g, hg₁, hg₂⟩ := exists_inv hvN
  have hgiso : g.IsIso := ⟨vN, FormalODModule.Hom.ext hg₂, FormalODModule.Hom.ext hg₁⟩
  have hψiso : (vN'.comp (θ.comp g)).IsIso := isIso_comp hvN' (isIso_comp hθ hgiso)
  have hgf : g.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom = wu.toSeries := by
    have h2 : (vN.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp (g.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = Series.id _ := by
      rw [← Series.map_comp _ _ _ (hom_cc g), hg₂, Series.map_id]
    exact (inverse_unique (cc_map (hom_cc vN) _) (cc_map (hom_cc g) _) hcN h2).symm
  have hcompat : ((castHom (Eχ χ' hχ'.1) wu).comp ((vN'.comp (θ.comp g)).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom)).toSeries = wu.toSeries := by
    show wu.toSeries.comp ((vN'.toSeries.comp (θ.toSeries.comp g.toSeries)).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = wu.toSeries
    rw [Series.map_comp _ _ _ (Series.constantCoeff_comp (hom_cc θ) (hom_cc g)),
      Series.map_comp _ _ _ (hom_cc g), hθf, Series.id_comp _ (cc_map (hom_cc g) _),
      ← Series.comp_assoc _ _ _ (cc_map (hom_cc vN') _) (cc_map (hom_cc g) _), hcN',
      Series.id_comp _ (cc_map (hom_cc g) _), hgf]

  obtain ⟨φ, hφ⟩ := mkAlg χ hχ.2
  obtain ⟨φ', hφ'⟩ := mkAlg χ' hχ'.2
  obtain ⟨ψ₀, -, huniq⟩ := hPRO (DualNumber (IsLocalRing.ResidueField Onr)) (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom hfst_surj hfst_alg (Xu.map χ') (hSH χ' hχ'.1).1 (hSH χ' hχ'.1).2
    (castHom (Eχ χ' hχ'.1) wu) (castHom_isIso _ wu hwu)
  have h1 : φ' = ψ₀ := by
    apply huniq
    refine ⟨by rw [hφ']; exact hχ'.1, ?_⟩
    rw [hφ']
    refine ⟨FormalODModule.Hom.id _, id_isIso _, ?_⟩
    show wu.toSeries.comp ((Series.id _).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = wu.toSeries
    rw [Series.map_id, Series.comp_id]
  have h2 : φ = ψ₀ := by
    apply huniq
    refine ⟨by rw [hφ]; exact hχ.1, ?_⟩
    rw [hφ]
    exact ⟨vN'.comp (θ.comp g), hψiso, hcompat⟩
  calc χ = φ.toRingHom := hφ.symm
    _ = φ'.toRingHom := by rw [h1, h2]
    _ = χ' := hφ'

#print axioms solution

end
end S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_ringHom_dualNumber_ext_of_lieCoordinates_of_isProrepresentedBy_deformations (solution)
