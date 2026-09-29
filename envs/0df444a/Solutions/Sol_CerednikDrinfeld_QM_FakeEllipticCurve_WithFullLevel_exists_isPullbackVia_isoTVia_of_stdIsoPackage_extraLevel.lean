-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fccff419-03d5-5ace-90b6-42d18d19c5a6

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace P8H2C

section transport

variable {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
  {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
  (E : FakeEllipticCurve Λ N R) (E' : FakeEllipticCurve Λ N R')
  (g : E'.A ⟶ E.A) (hg : g ≫ E.f = E'.f ≫ Spec.map (CommRingCat.ofHom φ))
  (k : E'.A ⟶ pullback E.f (Spec.map (CommRingCat.ofHom φ)))
  (hk₁ : k ≫ pullback.fst _ _ = g) (hk₂ : k ≫ pullback.snd _ _ = E'.f)

include hg hk₁ hk₂ in

theorem mul_transport
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' E'.f),
        (E'.L.mul t' P Q).1 ≫ g =
          (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' E'.f) :
    (E'.L.mul t' P Q).1 ≫ k =
      ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t'
        ⟨P.1 ≫ k, by rw [Category.assoc, hk₂, P.2]⟩
        ⟨Q.1 ≫ k, by rw [Category.assoc, hk₂, Q.2]⟩).1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, hk₁, hmul, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst]
    congr 2 <;> exact Subtype.ext (by simp only [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc, hk₁])
  · calc _ = t' := by rw [Category.assoc, hk₂]; exact (E'.L.mul t' P Q).2
      _ = _ := ((E.L.baseChange (Spec.map (CommRingCat.ofHom φ))).mul t' _ _).2.symm

include hk₁ hk₂ in

theorem act_transport (x : ↥Λ) (hact : E'.act x ≫ g = g ≫ E.act x) :
    k ≫ pullback.lift (pullback.fst E.f (Spec.map (CommRingCat.ofHom φ)) ≫ E.act x)
        (pullback.snd E.f (Spec.map (CommRingCat.ofHom φ))) (by rw [Category.assoc, E.act_over x, pullback.condition]) =
      E'.act x ≫ k := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hk₁, Category.assoc, hk₁, hact]
  · rw [Category.assoc, pullback.lift_snd, hk₂, Category.assoc, hk₂, E'.act_over]

end transport

theorem P_transport {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) (u' : FakeEllipticCurve.WithFullLevel Λ N m R')
    (g : u'.1.A ⟶ u.1.A) (k : u'.1.A ⟶ pullback u.1.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₁ : k ≫ pullback.fst _ _ = g) (hk₂ : k ≫ pullback.snd _ _ = u'.1.f)
    (hP : (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1) :
    (u'.2.P).1 ≫ k =
      pullback.lift (Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1) (𝟙 _)
        (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, hk₁, hP, pullback.lift_fst]
  · rw [Category.assoc, hk₂, (u'.2.P).2, pullback.lift_snd]

end P8H2C

open P8H2C in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_mul : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
      ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
        ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1)
    (e_act : ∀ x : ↥Λ,
      pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
        e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, w.1.act_over x, pullback.condition]))
    (e_P : pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
        pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp]))
    (e_lev : ∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_lev' : ∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)     (e_levK : ∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_levK' : ∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) :
    ∃ (uL wL : FakeEllipticCurve.WithFullLevel Λ N m L) (CuL : uL.1.ExtraLevel ℓ) (CwL : wL.1.ExtraLevel ℓ)
      (guL : uL.1.A ⟶ u.1.A) (gwL : wL.1.A ⟶ w.1.A),
      FakeEllipticCurve.IsPullbackVia (algebraMap R L) u.1 uL.1 guL ∧
      (uL.2.P).1 ≫ guL = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (u.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' uL.1.f),
        FactorsThrough CuL.levK P ↔ ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ guL) ∧
      FakeEllipticCurve.IsPullbackVia (algebraMap R L) w.1 wL.1 gwL ∧
      (wL.2.P).1 ≫ gwL = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (w.2.P).1 ∧
      (∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' wL.1.f),
        FactorsThrough CwL.levK P ↔ ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gwL) ∧
      ∃ (e : uL.1.A ≅ wL.1.A) (he : e.hom ≫ wL.1.f = uL.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia uL wL CuL CwL e he := by
  obtain ⟨c, hc⟩ := e_lev
  obtain ⟨c', hc'⟩ := e_lev'
  obtain ⟨cK, hcK⟩ := e_levK
  obtain ⟨cK', hcK'⟩ := e_levK'

  obtain ⟨uL, gu, hgu, umul, uact, ulev, ulev', uP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (algebraMap R L) u
  obtain ⟨wL, gw, hgw, wmul, wact, wlev, wlev', wP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff (algebraMap R L) w
  have hviau : FakeEllipticCurve.IsPullbackVia (algebraMap R L) u.1 uL.1 gu := ⟨hgu, umul, uact, ulev⟩
  have hviaw : FakeEllipticCurve.IsPullbackVia (algebraMap R L) w.1 wL.1 gw := ⟨hgw, wmul, wact, wlev⟩

  obtain ⟨CuL, hCuL⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia (algebraMap R L) u.1 uL.1 gu hviau ℓ Cu
  obtain ⟨CwL, hCwL⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia (algebraMap R L) w.1 wL.1 gw hviaw ℓ Cw
  have hCuL1 : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' uL.1.f),
      FactorsThrough CuL.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ gu := fun t' P h => (hCuL t' P).1 h
  have hCuL2 : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' uL.1.f),
      (∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ gu) → FactorsThrough CuL.levK P := fun t' P h => (hCuL t' P).2 h
  have hCwL1 : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' wL.1.f),
      FactorsThrough CwL.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gw := fun t' P h => (hCwL t' P).1 h
  have hCwL2 : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' wL.1.f),
      (∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gw) → FactorsThrough CwL.levK P := fun t' P h => (hCwL t' P).2 h
  refine ⟨uL, wL, CuL, CwL, gu, gw, hviau, uP, fun t' P => ⟨hCuL1 t' P, hCuL2 t' P⟩, hviaw, wP,
    fun t' P => ⟨hCwL1 t' P, hCwL2 t' P⟩, ?_⟩

  obtain ⟨κu, κu₁, κu₂, κu₃, κu₄⟩ : ∃ κu : uL.1.A ≅ pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      κu.hom ≫ pullback.fst _ _ = gu ∧ κu.hom ≫ pullback.snd _ _ = uL.1.f ∧
      κu.inv ≫ gu = pullback.fst _ _ ∧ κu.inv ≫ uL.1.f = pullback.snd _ _ :=
    ⟨hgu.isoPullback, hgu.isoPullback_hom_fst, hgu.isoPullback_hom_snd, hgu.isoPullback_inv_fst, hgu.isoPullback_inv_snd⟩
  obtain ⟨κw, κw₁, κw₂, κw₃, κw₄⟩ : ∃ κw : wL.1.A ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      κw.hom ≫ pullback.fst _ _ = gw ∧ κw.hom ≫ pullback.snd _ _ = wL.1.f ∧
      κw.inv ≫ gw = pullback.fst _ _ ∧ κw.inv ≫ wL.1.f = pullback.snd _ _ :=
    ⟨hgw.isoPullback, hgw.isoPullback_hom_fst, hgw.isoPullback_hom_snd, hgw.isoPullback_inv_fst, hgw.isoPullback_inv_snd⟩
  obtain ⟨E, Ehom, Einv⟩ : ∃ E : uL.1.A ≅ wL.1.A,
      E.hom = κu.hom ≫ e.hom ≫ κw.inv ∧ E.inv = κw.hom ≫ e.inv ≫ κu.inv :=
    ⟨κu ≪≫ e ≪≫ κw.symm, rfl, by simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]⟩
  have hE : E.hom ≫ wL.1.f = uL.1.f := by
    rw [Ehom, Category.assoc, Category.assoc, κw₄, e_snd, κu₂]
  have hEκ : E.hom ≫ κw.hom = κu.hom ≫ e.hom := by
    rw [Ehom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hEg : E.hom ≫ gw = κu.hom ≫ e.hom ≫ pullback.fst _ _ := by
    rw [Ehom, Category.assoc, Category.assoc, κw₃]
  refine ⟨E, hE, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro T t P Q
    apply Subtype.ext
    rw [mapPt_coe, ← cancel_mono κw.hom, Category.assoc, hEκ]
    have h1 := mul_transport (algebraMap R L) u.1 uL.1 gu hgu.w κu.hom κu₁ κu₂ umul t P Q
    have h3 := mul_transport (algebraMap R L) w.1 wL.1 gw hgw.w κw.hom κw₁ κw₂ wmul t (mapPt E.hom hE P) (mapPt E.hom hE Q)
    rw [← Category.assoc, h1, e_mul, h3]
    congr 2 <;> exact Subtype.ext (by simp only [mapPt_coe, Category.assoc, hEκ])
  ·
    intro x
    have hu1 := act_transport (algebraMap R L) u.1 uL.1 gu κu.hom κu₁ κu₂ x (uact x)
    have hw1 := act_transport (algebraMap R L) w.1 wL.1 gw κw.hom κw₁ κw₂ x (wact x)
    rw [← cancel_mono κw.hom, Category.assoc, hEκ, Category.assoc, ← hw1, ← Category.assoc E.hom, hEκ, Category.assoc,
      ← e_act, ← Category.assoc κu.hom, hu1, Category.assoc]
  ·
    intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := ulev t P hP
      have hr : P₀ ≫ u.1.lev ≫ u.1.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
        rw [← Category.assoc, hP₀, Category.assoc, hgu.w, ← Category.assoc, P.2]
      let r := pullback.lift P₀ t hr
      have hrj : r ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev)
            (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) = P.1 ≫ κu.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hP₀, Category.assoc, κu₁]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, κu₂, P.2]
      apply wlev' t (mapPt E.hom hE P)
      refine ⟨r ≫ c ≫ pullback.fst _ _, ?_⟩
      have hc1 := hc =≫ pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      simp only [Category.assoc, pullback.lift_fst] at hc1
      rw [mapPt_coe, Category.assoc, Category.assoc, hc1, ← Category.assoc r, hrj, Category.assoc, Category.assoc, hEg]
    · intro hP
      obtain ⟨Q₀, hQ₀⟩ := wlev t (mapPt E.hom hE P) hP
      rw [mapPt_coe] at hQ₀
      have hr : Q₀ ≫ w.1.lev ≫ w.1.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
        rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, hgw.w, ← Category.assoc E.hom, hE, ← Category.assoc, P.2]
      let r := pullback.lift Q₀ t hr
      have hrj : r ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev)
            (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) = P.1 ≫ κu.hom ≫ e.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hQ₀, Category.assoc, hEg,
            Category.assoc, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, Category.assoc, e_snd, κu₂, P.2]
      apply ulev' t P
      refine ⟨r ≫ c' ≫ pullback.fst _ _, ?_⟩
      have hc1 := hc' =≫ pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      simp only [Category.assoc, pullback.lift_fst] at hc1
      rw [Category.assoc, Category.assoc, hc1, ← Category.assoc r, hrj, ← κu₁]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ·
    apply Subtype.ext
    have hu1 := P_transport (algebraMap R L) u uL gu κu.hom κu₁ κu₂ uP
    have hw1 := P_transport (algebraMap R L) w wL gw κw.hom κw₁ κw₂ wP
    rw [mapPt_coe, ← cancel_mono κw.hom, Category.assoc, hEκ, hw1, ← e_P, ← hu1, Category.assoc]

  ·
    intro T t P
    constructor
    · intro hP
      obtain ⟨P₀, hP₀⟩ := hCuL1 t P hP
      have hr : P₀ ≫ Cu.levK ≫ u.1.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
        rw [← Category.assoc, hP₀, Category.assoc, hgu.w, ← Category.assoc, P.2]
      let r := pullback.lift P₀ t hr
      have hrj : r ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK)
            (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) = P.1 ≫ κu.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hP₀, Category.assoc, κu₁]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, κu₂, P.2]
      apply hCwL2 t (mapPt E.hom hE P)
      refine ⟨r ≫ cK ≫ pullback.fst _ _, ?_⟩
      have hc1 := hcK =≫ pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      simp only [Category.assoc, pullback.lift_fst] at hc1
      rw [mapPt_coe, Category.assoc, Category.assoc, hc1, ← Category.assoc r, hrj, Category.assoc, Category.assoc, hEg]
    · intro hP
      obtain ⟨Q₀, hQ₀⟩ := hCwL1 t (mapPt E.hom hE P) hP
      rw [mapPt_coe] at hQ₀
      have hr : Q₀ ≫ Cw.levK ≫ w.1.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
        rw [← Category.assoc, hQ₀, Category.assoc, Category.assoc, hgw.w, ← Category.assoc E.hom, hE, ← Category.assoc, P.2]
      let r := pullback.lift Q₀ t hr
      have hrj : r ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK)
            (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) = P.1 ≫ κu.hom ≫ e.hom := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hQ₀, Category.assoc, hEg,
            Category.assoc, Category.assoc]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, Category.assoc, e_snd, κu₂, P.2]
      apply hCuL2 t P
      refine ⟨r ≫ cK' ≫ pullback.fst _ _, ?_⟩
      have hc1 := hcK' =≫ pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))
      simp only [Category.assoc, pullback.lift_fst] at hc1
      rw [Category.assoc, Category.assoc, hc1, ← Category.assoc r, hrj, ← κu₁]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullbackVia_isoTVia_of_stdIsoPackage_extraLevel (solution)
