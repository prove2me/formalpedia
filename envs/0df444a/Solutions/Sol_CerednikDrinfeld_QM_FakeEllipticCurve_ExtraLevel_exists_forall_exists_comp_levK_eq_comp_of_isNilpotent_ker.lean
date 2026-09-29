-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/96178da9-8fba-5a33-9688-1dab0155ffa0

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_etale_lev_and_forall_factorsThrough_iff_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_factorsThrough_lev_of_exists_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM

open scoped Quaternion

noncomputable section

namespace ExtraLevelLiftBody

universe u

theorem hom_ext_of_forall_fromSpecResidueField {T K B : Scheme.{u}} (q : K ⟶ B)
    [FormallyUnramified q] [LocallyOfFiniteType q]
    {u v : T ⟶ K} (huv : u ≫ q = v ≫ q)
    (H : ∀ x : T, T.fromSpecResidueField x ≫ u = T.fromSpecResidueField x ≫ v) : u = v := by
  have hsurj : Function.Surjective (pullback.snd (pullback.diagonal q) (pullback.lift u v huv)).base := by
    intro x
    have hx : (T.fromSpecResidueField x ≫ u) ≫ pullback.diagonal q =
        T.fromSpecResidueField x ≫ pullback.lift u v huv := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst]
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd, H x]
    refine ⟨(pullback.lift _ _ hx).base (IsLocalRing.closedPoint (T.residueField x)), ?_⟩
    rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    exact T.fromSpecResidueField_apply x _
  haveI : IsIso (pullback.snd (pullback.diagonal q) (pullback.lift u v huv)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, ⟨hsurj⟩⟩
  have hc := pullback.condition (f := pullback.diagonal q) (g := pullback.lift u v huv)
  have hu : pullback.fst (pullback.diagonal q) (pullback.lift u v huv) =
      pullback.snd (pullback.diagonal q) (pullback.lift u v huv) ≫ u := by
    have := congrArg (· ≫ pullback.fst q q) hc
    simpa only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] using this
  have hv : pullback.fst (pullback.diagonal q) (pullback.lift u v huv) =
      pullback.snd (pullback.diagonal q) (pullback.lift u v huv) ≫ v := by
    have := congrArg (· ≫ pullback.snd q q) hc
    simpa only [Category.assoc, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] using this
  exact (cancel_epi (pullback.snd (pullback.diagonal q) (pullback.lift u v huv))).mp (hu.symm.trans hv)

section Base

variable {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀) (hp : Function.Surjective p)
  (hI : IsNilpotent (RingHom.ker p))

include hI in

theorem ker_le_ker {k : Type} [CommRing k] [IsReduced k] (φ : S →+* k) : RingHom.ker p ≤ RingHom.ker φ := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  have hxn : x ^ n ∈ RingHom.ker p ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at hxn
  have hx0 : x ^ n = 0 := hxn
  have : IsNilpotent (φ x) := ⟨n, by rw [← map_pow, hx0, map_zero]⟩
  exact this.eq_zero

include hp hI in

theorem exists_eq_comp {k : Type} [CommRing k] [IsReduced k] (φ : S →+* k) : ∃ φ₀ : S₀ →+* k, φ = φ₀.comp p :=
  ⟨RingHom.liftOfSurjective p hp ⟨φ, ker_le_ker p hI φ⟩,
    (RingHom.liftOfSurjective_comp p hp ⟨φ, ker_le_ker p hI φ⟩).symm⟩

include hp hI in

theorem exists_eq_comp_specMap {k : Type} [Field k] (β : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)) :
    ∃ β₀ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S₀), β = β₀ ≫ Spec.map (CommRingCat.ofHom p) := by
  obtain ⟨φ₀, hφ₀⟩ := exists_eq_comp p hp hI (Spec.preimage β).hom
  refine ⟨Spec.map (CommRingCat.ofHom φ₀), ?_⟩
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hφ₀, CommRingCat.ofHom_hom, Spec.map_preimage]

include hp hI in

theorem exists_residue_base {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : T) :
    ∃ t₀ : Spec (T.residueField x) ⟶ Spec (CommRingCat.of S₀),
      T.fromSpecResidueField x ≫ t = t₀ ≫ Spec.map (CommRingCat.ofHom p) :=
  exists_eq_comp_specMap p hp hI _

end Base

theorem one_comp_eq {S S₀ : Type} [CommRing S] [CommRing S₀]
    {A A₀ : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f₀ : A₀ ⟶ Spec (CommRingCat.of S₀)}
    (L : RelativeGroupLaw S f) (L₀ : RelativeGroupLaw S₀ f₀)
    (j : Spec (CommRingCat.of S₀) ⟶ Spec (CommRingCat.of S)) (g : A₀ ⟶ A) (hgw : g ≫ f = f₀ ≫ j)
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' f₀),
      (L₀.mul t' P Q).1 ≫ g =
        (L.mul (t' ≫ j)
          ⟨P.1 ≫ g, by rw [Category.assoc, hgw, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hgw, ← Category.assoc, Q.2]⟩).1)
    {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) :
    (L₀.one t').1 ≫ g = (L.one (t' ≫ j)).1 := by
  letI := L₀.pointGroup t'
  letI := L.pointGroup (t' ≫ j)
  let φ : SchemeHomOver t' f₀ → SchemeHomOver (t' ≫ j) f :=
    fun P => ⟨P.1 ≫ g, by rw [Category.assoc, hgw, ← Category.assoc, P.2]⟩
  have hφ : ∀ P Q, φ (L₀.mul t' P Q) = L.mul (t' ≫ j) (φ P) (φ Q) := fun P Q => Subtype.ext (hmul t' P Q)
  let Φ : SchemeHomOver t' f₀ →* SchemeHomOver (t' ≫ j) f := MonoidHom.mk' φ hφ
  exact congrArg Subtype.val (map_one Φ)

def relevel {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S₀ : Type u} [CommRing S₀]
    (E₀ : FakeEllipticCurve Λ N S₀) {ℓ : ℕ} (K₀ : E₀.ExtraLevel ℓ) : FakeEllipticCurve Λ ℓ S₀ where
  A := E₀.A
  f := E₀.f
  L := E₀.L
  comm := E₀.comm
  bundle := E₀.bundle
  dim_fibre := E₀.dim_fibre
  act := E₀.act
  act_over := E₀.act_over
  act_hom := E₀.act_hom
  act_one := E₀.act_one
  act_mul := E₀.act_mul
  act_add := E₀.act_add
  act_trace := E₀.act_trace
  C := K₀.K
  lev := K₀.levK
  lev_closed := K₀.levK_closed
  lev_sub := K₀.levK_sub
  lev_one := K₀.levK_one
  lev_torsion := K₀.levK_torsion
  lev_stable := K₀.levK_stable
  lev_finite := K₀.levK_finite
  lev_flat := K₀.levK_flat
  lev_finitePresentation := K₀.levK_finitePresentation
  lev_rank := K₀.levK_rank
  lev_fibre := K₀.levK_fibre

theorem main {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (hlev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' E₀.f),
      FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g)
    (K₀ : E₀.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough K₀.levK P → ∃ P₀ : T ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ g := by

  haveI : IsSeparated E.f := by have := E.bundle.proper; infer_instance
  obtain ⟨hfin, het⟩ := FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E ℓ hℓ

  obtain ⟨C, lev, hclosed, hsub, hone, htor, hfinC, hflatC, hfpC, hrank, hfib, hiv, hv⟩ :=
    FakeEllipticCurve.exists_lev_finrank_eq_sq_forall_factorsThrough_iff_of_isPullback_of_isNilpotent_ker
      p hp hI (relevel E₀ K₀) E.L E.comm hℓ hfin het g hg hmul

  have hstable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough lev P → FactorsThrough lev (pushPt (E.act x) (E.act_over x) P) :=
    fun x _ t P hP =>
      hv (E.act x) (E.act_over x) (E.act_hom x) (E₀.act x) (E₀.act_over x) (hact x) (K₀.levK_stable x) t P hP

  let E' : FakeEllipticCurve Λ ℓ S :=
    { A := E.A, f := E.f, L := E.L, comm := E.comm, bundle := E.bundle, dim_fibre := E.dim_fibre,
      act := E.act, act_over := E.act_over, act_hom := E.act_hom, act_one := E.act_one, act_mul := E.act_mul,
      act_add := E.act_add, act_trace := E.act_trace,
      C := C, lev := lev, lev_closed := hclosed, lev_sub := hsub, lev_one := hone, lev_torsion := htor,
      lev_stable := hstable, lev_finite := hfinC, lev_flat := hflatC, lev_finitePresentation := hfpC,
      lev_rank := hrank, lev_fibre := hfib }
  haveI hEt : Etale (lev ≫ E.f) := (FakeEllipticCurve.etale_lev_and_forall_factorsThrough_iff_of_isUnit E' hℓ).1
  haveI : IsClosedImmersion lev := hclosed
  haveI : IsFinite (lev ≫ E.f) := hfinC

  have hdisj : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough lev P → FactorsThrough E.lev P → P = E.L.one t := by
    intro T t P hPK hPC
    obtain ⟨P₀, hP₀⟩ := hPK
    obtain ⟨c, hc⟩ := hPC
    obtain ⟨e', he'⟩ := hone t
    suffices hEq : P₀ = e' by
      apply Subtype.ext
      rw [← hP₀, hEq, he']
    refine hom_ext_of_forall_fromSpecResidueField (lev ≫ E.f) (u := P₀) (v := e') ?_ fun x => ?_
    · rw [← Category.assoc, hP₀, P.2, ← Category.assoc, he', (E.L.one t).2]

    obtain ⟨t₀, ht₀⟩ := exists_residue_base p hp hI t x

    obtain ⟨Q₀, hQ₀f, hQ₀g⟩ : ∃ Q₀ : Spec (T.residueField x) ⟶ E₀.A,
        Q₀ ≫ E₀.f = t₀ ∧ Q₀ ≫ g = T.fromSpecResidueField x ≫ P.1 :=
      ⟨hg.lift (T.fromSpecResidueField x ≫ P.1) t₀ (by rw [Category.assoc, P.2]; exact ht₀),
        hg.lift_snd _ _ _, hg.lift_fst _ _ _⟩

    have hK : FactorsThrough K₀.levK (⟨Q₀, hQ₀f⟩ : SchemeHomOver t₀ E₀.f) :=
      (hiv t₀ ⟨Q₀, hQ₀f⟩).mpr ⟨T.fromSpecResidueField x ≫ P₀, by rw [Category.assoc, hP₀]; exact hQ₀g.symm⟩
    have hC : FactorsThrough E₀.lev (⟨Q₀, hQ₀f⟩ : SchemeHomOver t₀ E₀.f) :=
      FakeEllipticCurve.factorsThrough_lev_of_exists_comp_eq_of_isPullback p E E₀ g hg hmul hlev t₀ ⟨Q₀, hQ₀f⟩
        ⟨T.fromSpecResidueField x ≫ c, by rw [Category.assoc, hc]; exact hQ₀g.symm⟩
    have hQ₀one : (⟨Q₀, hQ₀f⟩ : SchemeHomOver t₀ E₀.f) = E₀.L.one t₀ := K₀.levK_disjoint t₀ _ hK hC

    have h1 : T.fromSpecResidueField x ≫ P.1 = T.fromSpecResidueField x ≫ (E.L.one t).1 :=
      calc T.fromSpecResidueField x ≫ P.1
          = (⟨Q₀, hQ₀f⟩ : SchemeHomOver t₀ E₀.f).1 ≫ g := hQ₀g.symm
        _ = (E₀.L.one t₀).1 ≫ g := by rw [hQ₀one]
        _ = (E.L.one (t₀ ≫ Spec.map (CommRingCat.ofHom p))).1 :=
          one_comp_eq E.L E₀.L (Spec.map (CommRingCat.ofHom p)) g hg.w hmul t₀
        _ = T.fromSpecResidueField x ≫ (E.L.one t).1 :=
          (congrArg Subtype.val
            (E.L.one_natural t (t₀ ≫ Spec.map (CommRingCat.ofHom p)) (T.fromSpecResidueField x) ht₀)).symm

    rw [← cancel_mono lev, Category.assoc, Category.assoc, hP₀, he', h1]

  let K : E.ExtraLevel ℓ :=
    { K := C, levK := lev, levK_closed := hclosed, levK_sub := hsub, levK_one := hone, levK_torsion := htor,
      levK_stable := hstable, levK_disjoint := hdisj, levK_finite := hfinC, levK_flat := hflatC,
      levK_finitePresentation := hfpC, levK_rank := hrank, levK_fibre := hfib }
  exact ⟨K, fun t' P h => (hiv t' P).mp h⟩

end ExtraLevelLiftBody

end

open ExtraLevelLiftBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [CommRing S₀] (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (hlev : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' E₀.f),
      FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ g)
    (K₀ : E₀.ExtraLevel ℓ) :
    ∃ K : E.ExtraLevel ℓ,
      ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t' E₀.f),
        FactorsThrough K₀.levK P → ∃ P₀ : T ⟶ K.K, P₀ ≫ K.levK = P.1 ≫ g :=
  ExtraLevelLiftBody.main E E₀ ℓ hℓ p hp hI g hg hmul hact hlev K₀

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_forall_exists_comp_levK_eq_comp_of_isNilpotent_ker (solution)
