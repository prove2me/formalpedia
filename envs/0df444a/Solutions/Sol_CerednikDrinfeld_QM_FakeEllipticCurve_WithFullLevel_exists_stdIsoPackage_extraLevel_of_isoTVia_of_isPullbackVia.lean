-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_stdIsoPackage_extraLevel_of_isoTVia_of_isPullbackVia
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/10492907-88e1-56e4-94c3-c2fa9283450f

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_factorsThrough_iff_of_isPullbackVia
import Theorems.Thm_AlgebraicGeometry_isIso_of_isClosedImmersion_of_finrank_eq
import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_stdIsoPackage_extraLevel_of_isoTVia_of_isPullbackVia
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace H2A

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

theorem levK_pullback {R R' : Type} [CommRing R] [CommRing R'] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (E : FakeEllipticCurve Λ N R) (φ : R →+* R') (E' : FakeEllipticCurve Λ N R') (g : E'.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia φ E E' g) {n : ℕ} (K : E.ExtraLevel n) (K' : E'.ExtraLevel n)
    (hinto : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' E'.f),
      FactorsThrough K'.levK P → ∃ P₀ : T ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ g)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P : SchemeHomOver t' E'.f)
    (hP : ∃ P₀ : T ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ g) :
    FactorsThrough K'.levK P := by
  obtain ⟨K'', hK''⟩ := FakeEllipticCurve.ExtraLevel.exists_forall_factorsThrough_iff_of_isPullbackVia φ E E' g hg n K

  obtain ⟨R₀, hR₀⟩ := hinto (K'.levK ≫ E'.f) ⟨K'.levK, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨j, hj⟩ := (hK'' (K'.levK ≫ E'.f) ⟨K'.levK, rfl⟩).2 ⟨R₀, hR₀⟩
  change j ≫ K''.levK = K'.levK at hj
  haveI : IsClosedImmersion K'.levK := K'.levK_closed
  haveI : IsClosedImmersion K''.levK := K''.levK_closed
  haveI : IsClosedImmersion (j ≫ K''.levK) := by rw [hj]; infer_instance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j K''.levK
  haveI := K'.levK_finite; haveI := K'.levK_flat; haveI := K'.levK_finitePresentation
  haveI := K''.levK_finite; haveI := K''.levK_flat; haveI := K''.levK_finitePresentation
  haveI : IsIso j :=
    isIso_of_isClosedImmersion_of_finrank_eq (K'.levK ≫ E'.f) (K''.levK ≫ E'.f) j
      (by rw [← Category.assoc, hj]) (fun z => by rw [K'.levK_rank, K''.levK_rank])
  obtain ⟨q, hq⟩ := (hK'' t' P).2 hP
  refine ⟨q ≫ inv j, ?_⟩
  have hinv : inv j ≫ K'.levK = K''.levK := by rw [IsIso.inv_comp_eq, hj]
  rw [Category.assoc, hinv, hq]

end H2A

open H2A in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m ℓ : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (u' w' : FakeEllipticCurve.WithFullLevel Λ N m L) (Cu' : u'.1.ExtraLevel ℓ) (Cw' : w'.1.ExtraLevel ℓ)
    (gu : u'.1.A ⟶ u.1.A) (gw : w'.1.A ⟶ w.1.A)
    (hgu : FakeEllipticCurve.IsPullbackVia (algebraMap R L) u.1 u'.1 gu)
    (hguP : (u'.2.P).1 ≫ gu = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (u.2.P).1)
    (hguC : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough Cu'.levK P → ∃ P₀ : T₀ ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ gu)
    (hgw : FakeEllipticCurve.IsPullbackVia (algebraMap R L) w.1 w'.1 gw)
    (hgwP : (w'.2.P).1 ≫ gw = Spec.map (CommRingCat.ofHom (algebraMap R L)) ≫ (w.2.P).1)
    (hgwC : ∀ {T₀ : Scheme.{0}} (t' : T₀ ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' w'.1.f),
      FactorsThrough Cw'.levK P → ∃ P₀ : T₀ ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gw)
    (he : ∃ (e : u'.1.A ≅ w'.1.A) (he : e.hom ≫ w'.1.f = u'.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u' w' Cu' Cw' e he) :
    ∃ (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
      (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L)))),
      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
        ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
          ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
            ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1) ∧
      (∀ x : ↥Λ,
        pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
          e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc, w.1.act_over x, pullback.condition])) ∧
      (pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
            (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
          pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
            (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp])) ∧
      (∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom) ∧
      (∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) ∧
      (∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom) ∧
      (∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv) := by
  have ulev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' u'.1.f),
      (∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ gu) → FactorsThrough u'.1.lev P :=
    fun t' P hP => FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia u.1 (algebraMap R L) u'.1 gu hgu t' P hP
  have wlev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' w'.1.f),
      (∃ P₀ : T ⟶ w.1.C, P₀ ≫ w.1.lev = P.1 ≫ gw) → FactorsThrough w'.1.lev P :=
    fun t' P hP => FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_comp_of_isPullbackVia w.1 (algebraMap R L) w'.1 gw hgw t' P hP
  have uClev := @hguC
  have wClev := @hgwC
  have uClev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' u'.1.f),
      (∃ P₀ : T ⟶ Cu.K, P₀ ≫ Cu.levK = P.1 ≫ gu) → FactorsThrough Cu'.levK P :=
    fun t' P hP => levK_pullback u.1 (algebraMap R L) u'.1 gu hgu Cu Cu' hguC t' P hP
  have wClev' : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of L)) (P : SchemeHomOver t' w'.1.f),
      (∃ P₀ : T ⟶ Cw.K, P₀ ≫ Cw.levK = P.1 ≫ gw) → FactorsThrough Cw'.levK P :=
    fun t' P hP => levK_pullback w.1 (algebraMap R L) w'.1 gw hgw Cw Cw' hgwC t' P hP
  obtain ⟨ε, hε, ⟨εmul, εact, εlev, εP⟩, εClev⟩ := he
  have uP := hguP
  have wP := hgwP
  have hguV := hgu
  have hgwV := hgw
  clear hgu hgw
  obtain ⟨hgu, umul, uact, ulev⟩ := hguV
  obtain ⟨hgw, wmul, wact, wlev⟩ := hgwV
  have hε' : ε.inv ≫ u'.1.f = w'.1.f := by rw [Iso.inv_comp_eq, hε]

  obtain ⟨κu, κu₁, κu₂, κu₃, κu₄⟩ : ∃ κu : u'.1.A ≅ pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      κu.hom ≫ pullback.fst _ _ = gu ∧ κu.hom ≫ pullback.snd _ _ = u'.1.f ∧
      κu.inv ≫ gu = pullback.fst _ _ ∧ κu.inv ≫ u'.1.f = pullback.snd _ _ :=
    ⟨hgu.isoPullback, hgu.isoPullback_hom_fst, hgu.isoPullback_hom_snd, hgu.isoPullback_inv_fst, hgu.isoPullback_inv_snd⟩
  obtain ⟨κw, κw₁, κw₂, κw₃, κw₄⟩ : ∃ κw : w'.1.A ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      κw.hom ≫ pullback.fst _ _ = gw ∧ κw.hom ≫ pullback.snd _ _ = w'.1.f ∧
      κw.inv ≫ gw = pullback.fst _ _ ∧ κw.inv ≫ w'.1.f = pullback.snd _ _ :=
    ⟨hgw.isoPullback, hgw.isoPullback_hom_fst, hgw.isoPullback_hom_snd, hgw.isoPullback_inv_fst, hgw.isoPullback_inv_snd⟩

  obtain ⟨e, ehom, einv⟩ : ∃ e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅
      pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
      e.hom = κu.inv ≫ ε.hom ≫ κw.hom ∧ e.inv = κw.inv ≫ ε.inv ≫ κu.hom :=
    ⟨κu.symm ≪≫ ε ≪≫ κw, rfl, by simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]⟩
  have e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) =
      pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rw [ehom, Category.assoc, Category.assoc, κw₂, hε, κu₄]
  have e_fst : e.hom ≫ pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = κu.inv ≫ ε.hom ≫ gw := by
    rw [ehom, Category.assoc, Category.assoc, κw₁]
  have einv_fst : e.inv ≫ pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = κw.inv ≫ ε.inv ≫ gu := by
    rw [einv, Category.assoc, Category.assoc, κu₁]
  have einv_snd : e.inv ≫ pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) =
      pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
    rw [einv, Category.assoc, Category.assoc, κu₂, hε', κw₄]
  refine ⟨e, e_snd, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro T t x y
    let P : SchemeHomOver t u'.1.f := ⟨x.1 ≫ κu.inv, by rw [Category.assoc, κu₄, x.2]⟩
    let Q : SchemeHomOver t u'.1.f := ⟨y.1 ≫ κu.inv, by rw [Category.assoc, κu₄, y.2]⟩
    have hPx : P.1 ≫ κu.hom = x.1 := by simp only [P, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hQy : Q.1 ≫ κu.hom = y.1 := by simp only [Q, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have h1 := mul_transport (algebraMap R L) u.1 u'.1 gu hgu.w κu.hom κu₁ κu₂ umul t P Q
    have h1' : ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 =
        (u'.1.L.mul t P Q).1 ≫ κu.hom := by
      rw [h1]; congr 2
      · exact Subtype.ext hPx.symm
      · exact Subtype.ext hQy.symm
    have h2 := congrArg Subtype.val (εmul t P Q)
    simp only [mapPt_coe] at h2
    have h3 := mul_transport (algebraMap R L) w.1 w'.1 gw hgw.w κw.hom κw₁ κw₂ wmul t (mapPt ε.hom hε P) (mapPt ε.hom hε Q)
    have hL : ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
        (w'.1.L.mul t (mapPt ε.hom hε P) (mapPt ε.hom hε Q)).1 ≫ κw.hom := by
      rw [h1', ehom, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, h2]
    rw [hL, h3]
    congr 2 <;> exact Subtype.ext (by simp only [mapPt_coe, P, Q, ehom, Category.assoc])
  ·
    intro x
    have hu1 := act_transport (algebraMap R L) u.1 u'.1 gu κu.hom κu₁ κu₂ x (uact x)
    have hw1 := act_transport (algebraMap R L) w.1 w'.1 gw κw.hom κw₁ κw₂ x (wact x)
    rw [ehom, ← cancel_epi κu.hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc κu.hom, hu1, Category.assoc, Iso.hom_inv_id_assoc, hw1, ← Category.assoc, εact, Category.assoc]
  ·
    have hu1 := P_transport (algebraMap R L) u u' gu κu.hom κu₁ κu₂ uP
    have hw1 := P_transport (algebraMap R L) w w' gw κw.hom κw₁ κw₂ wP
    have h2 := congrArg Subtype.val εP
    rw [mapPt_coe] at h2
    rw [← hu1, ← hw1, ehom, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, h2]
  ·
    obtain ⟨ju, hju₁, hju₂⟩ : ∃ ju : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶
        pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        ju ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u.1.lev ∧ ju ≫ pullback.snd _ _ = pullback.snd _ _ :=
      ⟨pullback.lift (pullback.fst _ _ ≫ u.1.lev) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let X' : SchemeHomOver (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L)))) u'.1.f :=
      ⟨ju ≫ κu.inv, by rw [Category.assoc, κu₄, hju₂]⟩
    have hX' : X'.1 = ju ≫ κu.inv := rfl
    have hFT1 : FactorsThrough u'.1.lev X' :=
      ulev' _ X' ⟨pullback.fst _ _, by rw [hX', Category.assoc, κu₃, hju₁]⟩
    obtain ⟨yv, hyv⟩ := wlev _ _ ((εlev _ X').1 hFT1)
    rw [mapPt_coe, hX'] at hyv
    have hc : yv ≫ w.1.lev ≫ w.1.f =
        pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
      rw [← Category.assoc, hyv]
      simp only [Category.assoc]
      rw [hgw.w, ← Category.assoc ε.hom, hε, ← Category.assoc κu.inv, κu₄, ← Category.assoc, hju₂]
    refine ⟨pullback.lift yv (pullback.snd _ _) hc, ?_⟩
    apply pullback.hom_ext
    · have : ju = pullback.lift (pullback.fst _ _ ≫ u.1.lev) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) := pullback.hom_ext (by rw [hju₁, pullback.lift_fst])
            (by rw [hju₂, pullback.lift_snd])
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hyv]
      simp only [Category.assoc]
      rw [e_fst, this]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, e_snd, pullback.lift_snd]
  ·
    obtain ⟨jw, hjw₁, hjw₂⟩ : ∃ jw : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶
        pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        jw ≫ pullback.fst _ _ = pullback.fst _ _ ≫ w.1.lev ∧ jw ≫ pullback.snd _ _ = pullback.snd _ _ :=
      ⟨pullback.lift (pullback.fst _ _ ≫ w.1.lev) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let Z' : SchemeHomOver (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L)))) w'.1.f :=
      ⟨jw ≫ κw.inv, by rw [Category.assoc, κw₄, hjw₂]⟩
    have hZ' : Z'.1 = jw ≫ κw.inv := rfl
    have hFT1 : FactorsThrough w'.1.lev Z' :=
      wlev' _ Z' ⟨pullback.fst _ _, by rw [hZ', Category.assoc, κw₃, hjw₁]⟩
    have hFT2 : FactorsThrough w'.1.lev (mapPt ε.hom hε (mapPt ε.inv hε' Z')) := by
      obtain ⟨P₀, hP₀⟩ := hFT1
      exact ⟨P₀, by rw [hP₀, mapPt_coe, mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
    obtain ⟨yv, hyv⟩ := ulev _ _ ((εlev _ (mapPt ε.inv hε' Z')).2 hFT2)
    rw [mapPt_coe, hZ'] at hyv
    have hc : yv ≫ u.1.lev ≫ u.1.f =
        pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
      rw [← Category.assoc, hyv]
      simp only [Category.assoc]
      rw [hgu.w, ← Category.assoc ε.inv, hε', ← Category.assoc κw.inv, κw₄, ← Category.assoc, hjw₂]
    refine ⟨pullback.lift yv (pullback.snd _ _) hc, ?_⟩
    apply pullback.hom_ext
    · have : jw = pullback.lift (pullback.fst _ _ ≫ w.1.lev) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) := pullback.hom_ext (by rw [hjw₁, pullback.lift_fst])
            (by rw [hjw₂, pullback.lift_snd])
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hyv]
      simp only [Category.assoc]
      rw [einv_fst, this]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, einv_snd, pullback.lift_snd]
  ·
    obtain ⟨ju, hju₁, hju₂⟩ : ∃ ju : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶
        pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        ju ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Cu.levK ∧ ju ≫ pullback.snd _ _ = pullback.snd _ _ :=
      ⟨pullback.lift (pullback.fst _ _ ≫ Cu.levK) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let X' : SchemeHomOver (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L)))) u'.1.f :=
      ⟨ju ≫ κu.inv, by rw [Category.assoc, κu₄, hju₂]⟩
    have hX' : X'.1 = ju ≫ κu.inv := rfl
    have hFT1 : FactorsThrough Cu'.levK X' :=
      uClev' _ X' ⟨pullback.fst _ _, by rw [hX', Category.assoc, κu₃, hju₁]⟩
    obtain ⟨yv, hyv⟩ := wClev _ _ ((εClev _ X').1 hFT1)
    rw [mapPt_coe, hX'] at hyv
    have hc : yv ≫ Cw.levK ≫ w.1.f =
        pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
      rw [← Category.assoc, hyv]
      simp only [Category.assoc]
      rw [hgw.w, ← Category.assoc ε.hom, hε, ← Category.assoc κu.inv, κu₄, ← Category.assoc, hju₂]
    refine ⟨pullback.lift yv (pullback.snd _ _) hc, ?_⟩
    apply pullback.hom_ext
    · have : ju = pullback.lift (pullback.fst _ _ ≫ Cu.levK) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) := pullback.hom_ext (by rw [hju₁, pullback.lift_fst])
            (by rw [hju₂, pullback.lift_snd])
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hyv]
      simp only [Category.assoc]
      rw [e_fst, this]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, e_snd, pullback.lift_snd]
  ·
    obtain ⟨jw, hjw₁, hjw₂⟩ : ∃ jw : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶
        pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        jw ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Cw.levK ∧ jw ≫ pullback.snd _ _ = pullback.snd _ _ :=
      ⟨pullback.lift (pullback.fst _ _ ≫ Cw.levK) (pullback.snd _ _) (by rw [Category.assoc]; exact pullback.condition),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    let Z' : SchemeHomOver (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L)))) w'.1.f :=
      ⟨jw ≫ κw.inv, by rw [Category.assoc, κw₄, hjw₂]⟩
    have hZ' : Z'.1 = jw ≫ κw.inv := rfl
    have hFT1 : FactorsThrough Cw'.levK Z' :=
      wClev' _ Z' ⟨pullback.fst _ _, by rw [hZ', Category.assoc, κw₃, hjw₁]⟩
    have hFT2 : FactorsThrough Cw'.levK (mapPt ε.hom hε (mapPt ε.inv hε' Z')) := by
      obtain ⟨P₀, hP₀⟩ := hFT1
      exact ⟨P₀, by rw [hP₀, mapPt_coe, mapPt_coe, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩
    obtain ⟨yv, hyv⟩ := uClev _ _ ((εClev _ (mapPt ε.inv hε' Z')).2 hFT2)
    rw [mapPt_coe, hZ'] at hyv
    have hc : yv ≫ Cu.levK ≫ u.1.f =
        pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
      rw [← Category.assoc, hyv]
      simp only [Category.assoc]
      rw [hgu.w, ← Category.assoc ε.inv, hε', ← Category.assoc κw.inv, κw₄, ← Category.assoc, hjw₂]
    refine ⟨pullback.lift yv (pullback.snd _ _) hc, ?_⟩
    apply pullback.hom_ext
    · have : jw = pullback.lift (pullback.fst _ _ ≫ Cw.levK) (pullback.snd _ _)
          (by rw [Category.assoc]; exact pullback.condition) := pullback.hom_ext (by rw [hjw₁, pullback.lift_fst])
            (by rw [hjw₂, pullback.lift_snd])
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hyv]
      simp only [Category.assoc]
      rw [einv_fst, this]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc, einv_snd, pullback.lift_snd]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_stdIsoPackage_extraLevel_of_isoTVia_of_isPullbackVia
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_stdIsoPackage_extraLevel_of_isoTVia_of_isPullbackVia (solution)
