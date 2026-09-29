-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/35fd994a-6092-56e4-881c-6bebd4ab1857

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_injective_deformations_dualNumber_fin_one_of_not_and
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul MvPowerSeries.kw_coeff_pderiv FormalGroup.nthSeries_zero FormalGroup.evalNSMul_zero"

set_option autoImplicit false

universe u

noncomputable section

namespace SmoothVersalLine

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (constantCoeff constantCoeff_X)

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

theorem fst_comp_collapse :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) = (TrivSqZeroExt.fstHom k k k).toRingHom :=
  RingHom.ext fun _ => rfl

theorem snd_collapse (t : DualNumber k) :
    TrivSqZeroExt.snd (((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) t) = 0 * TrivSqZeroExt.snd t := by
  rw [zero_mul]; rfl

theorem fst_comp_inl : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := RingHom.ext fun _ => rfl

end dual

theorem main     {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (X₁ : FormalODModule q (DualNumber k))
    (w₁ : (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw₁ : w₁.IsIso)
    (h₁ : ∀ θ : X₁.Hom (X₀.toFormalODModule.map (algebraMap k (DualNumber k))), ¬ θ.IsIso)
    (X : FormalODModule q (DualNumber k))
    (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    ∃ c : k, ∀ (μ : DualNumber k →+* DualNumber k),
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp μ = (TrivSqZeroExt.fstHom k k k).toRingHom →
      (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
      ∃ v : X.Hom (X₁.map μ), v.IsIso ∧
        w₁.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries := by
  classical
  obtain ⟨e, hconst, hinj, hhom, hadd⟩ :=
    CerednikDrinfeld.SpecialFormalODModule.exists_injective_deformations_dualNumber_fin_one_of_not_and X₀ hsmooth

  have hX₁c : (X₁.map ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)).map (TrivSqZeroExt.fstHom k k k).toRingHom = X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom := by
    rw [FormalODModule.map_map, fst_comp_collapse]
  have he0 : e (X₁.map ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)) (castHom hX₁c.symm w₁)
      (castHom_isIso _ _ hw₁) = (0 : k) • e X₁ w₁ hw₁ :=
    hhom 0 _ (fst_comp_collapse k) (snd_collapse k) X₁ w₁ hw₁ _ _ rfl

  have hT : (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (algebraMap k (DualNumber k)) = X₁.map ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    FormalODModule.map_map _ _ _

  have hne : e X₁ w₁ hw₁ ≠ 0 := by
    intro h0
    have heq : e X₁ w₁ hw₁ = e (X₁.map ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)) (castHom hX₁c.symm w₁)
        (castHom_isIso _ _ hw₁) := by rw [he0, h0, smul_zero]
    obtain ⟨v, hv, -⟩ := hinj _ _ _ _ _ _ heq

    let θ : X₁.Hom (X₀.toFormalODModule.map (algebraMap k (DualNumber k))) :=
      ((w₁.map (algebraMap k (DualNumber k))).comp (castHomT hT.symm v))
    exact h₁ θ (isIso_comp (isIso_map _ hw₁) (castHomT_isIso _ _ hv))
  have ha : e X₁ w₁ hw₁ 0 ≠ 0 := by
    intro h; apply hne; funext i; fin_cases i; simpa using h
  refine ⟨e X w hw 0 * (e X₁ w₁ hw₁ 0)⁻¹, fun μ hμ₁ hμ₂ => ?_⟩
  have hXμ : (X₁.map μ).map (TrivSqZeroExt.fstHom k k k).toRingHom = X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom := by rw [FormalODModule.map_map, hμ₁]
  have hcμ := hhom _ μ hμ₁ hμ₂ X₁ w₁ hw₁ (castHom hXμ.symm w₁) (castHom_isIso _ _ hw₁) rfl
  have heq : e X w hw = e (X₁.map μ) (castHom hXμ.symm w₁) (castHom_isIso _ _ hw₁) := by
    rw [hcμ]; funext i; fin_cases i
    simp only [Pi.smul_apply, smul_eq_mul]
    show e X w hw 0 = e X w hw 0 * (e X₁ w₁ hw₁ 0)⁻¹ * e X₁ w₁ hw₁ 0
    rw [inv_mul_cancel_right₀ ha]
  obtain ⟨v, hv, hc⟩ := hinj _ _ _ _ _ _ heq
  exact ⟨v, hv, hc⟩

end SmoothVersalLine
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and.SmoothVersalLine"

open CerednikDrinfeld in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (X₁ : FormalODModule q (DualNumber k))
    (w₁ : (X₁.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw₁ : w₁.IsIso)
    (h₁ : ∀ θ : X₁.Hom (X₀.toFormalODModule.map (algebraMap k (DualNumber k))), ¬ θ.IsIso)
    (X : FormalODModule q (DualNumber k))
    (w : (X.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    ∃ c : k, ∀ (μ : DualNumber k →+* DualNumber k),
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp μ = (TrivSqZeroExt.fstHom k k k).toRingHom →
      (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
      ∃ v : X.Hom (X₁.map μ), v.IsIso ∧
        w₁.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom) = w.toSeries :=
  SmoothVersalLine.main X₀ hsmooth X₁ w₁ hw₁ h₁ X w hw

end
end S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_forall_exists_isIso_comp_map_eq_of_forall_not_isIso_of_not_and (solution)
