-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isReduced_C_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/6ffb8b56-6544-551b-b2d9-37583f036bc2

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_IsReduced_of_finrank_le_natCard_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion
open CerednikDrinfeld CerednikDrinfeld.QM QuaternionAlgebra

namespace LEVRED

variable {k : Type u} [Field k]

theorem finrank_sections_eq {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsFinite z] [Flat z] [IsAffine C]
    (n : ℕ) (hrank : ∀ s : ↥(Spec (CommRingCat.of k)), z.finrank s = n) :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Module.Finite k Γ(C, ⊤) ∧ Module.finrank k Γ(C, ⊤) = n := by
  set φ : CommRingCat.of k ⟶ Γ(C, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop with hφ
  letI alg : Algebra k Γ(C, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  have hFin : φ.hom.Finite := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Finite
    exact z.finite_appTop.comp (RingHom.Finite.of_surjective _ hbij.surjective)
  have hFlat : φ.hom.Flat := by
    show (z.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).Flat
    exact (RingHom.Flat.of_bijective hbij).comp z.flat_appTop
  have hfin : Module.Finite k Γ(C, ⊤) := hFin
  refine ⟨hfin, ?_⟩

  have hz : z = C.isoSpec.hom ≫ Spec.map φ := by
    rw [hφ, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hFin
  haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hFlat

  obtain ⟨s⟩ := (inferInstance : Nonempty ↥(Spec (CommRingCat.of k)))
  have h1 := hrank s
  rw [hz, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hFin hFlat] at h1

  have h2 : φ.hom.finrank s = Module.finrank k Γ(C, ⊤) := by
    have : φ.hom = algebraMap k Γ(C, ⊤) := rfl
    rw [this, RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    rfl
  rw [← h2, h1]

theorem finite_algHom (B : Type u) [CommRing B] [Algebra k B] [Module.Finite k B] : Finite (B →ₐ[k] k) := by
  classical
  haveI : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let F : (B →ₐ[k] k) → MaximalSpectrum B := fun φ =>
    ⟨RingHom.ker φ.toRingHom, RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun x => ⟨algebraMap k B x, by simp⟩)⟩
  refine Finite.of_injective F ?_
  intro φ ψ h
  have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg MaximalSpectrum.asIdeal h
  apply AlgHom.ext
  intro x

  have h1 : x - algebraMap k B (φ x) ∈ RingHom.ker φ.toRingHom := by simp [RingHom.mem_ker]
  rw [hker] at h1
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes] at h1
  exact (sub_eq_zero.1 h1).symm

theorem natCard_algHom_ge {C : Scheme.{u}} (z : C ⟶ Spec (CommRingCat.of k)) [IsAffine C]
    (hfin : letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra; Module.Finite k Γ(C, ⊤))
    (ι : Type) (e : ι ↪ {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _}) [Finite ι] :
    letI : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
    Nat.card ι ≤ Nat.card (Γ(C, ⊤) →ₐ[k] k) := by
  letI alg : Algebra k Γ(C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  haveI := hfin
  haveI : Finite (Γ(C, ⊤) →ₐ[k] k) := finite_algHom Γ(C, ⊤)

  let Φ : {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} → (Γ(C, ⊤) →ₐ[k] k) := fun x =>
    { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      commutes' := by
        intro c
        change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
        rw [← Scheme.Hom.comp_appTop_assoc, x.2]
        simp }
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    have happ : x.1.appTop = y.1.appTop := by
      have := congrArg (fun φ : Γ(C, ⊤) →ₐ[k] k => φ.toRingHom) hxy
      have h2 : (x.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) = (y.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) := by
        ext1; exact this
      simpa [← Iso.eq_comp_inv] using h2
    apply Subtype.ext
    have hx := Scheme.isoSpec_hom_naturality x.1
    have hy := Scheme.isoSpec_hom_naturality y.1
    rw [happ] at hx
    rw [← cancel_mono C.isoSpec.hom, ← hx, hy]
  calc Nat.card ι ≤ Nat.card {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := by
          haveI : Finite {x : Spec (CommRingCat.of k) ⟶ C // x ≫ z = 𝟙 _} := Finite.of_injective Φ hΦ
          exact Nat.card_le_card_of_injective e e.injective
    _ ≤ Nat.card (Γ(C, ⊤) →ₐ[k] k) := Nat.card_le_card_of_injective Φ hΦ

end LEVRED

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] [IsAlgClosed k] (E : FakeEllipticCurve Λ N k) (hNk : (N : k) ≠ 0) :
    IsReduced E.C := by
  classical
  set z : E.C ⟶ Spec (CommRingCat.of k) := E.lev ≫ E.f with hz
  haveI : IsFinite z := E.lev_finite
  haveI : Flat z := E.lev_flat
  haveI : IsAffine E.C := isAffine_of_isAffineHom z
  letI alg : Algebra k Γ(E.C, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ z.appTop).hom.toAlgebra
  obtain ⟨hfin, hrank⟩ := LEVRED.finrank_sections_eq z (N ^ 2) E.lev_rank
  haveI := hfin

  have hgp : geomPoint (S := k) k (RingHom.id k) = 𝟙 (Spec (CommRingCat.of k)) := by simp [geomPoint]
  obtain ⟨eN, -⟩ := E.lev_fibre k (RingHom.id k) hNk
  haveI : NeZero N := ⟨by rintro rfl; exact hNk (by simp)⟩

  have emb : ZMod N × ZMod N ↪ {x : Spec (CommRingCat.of k) ⟶ E.C // x ≫ z = 𝟙 _} := by
    refine ⟨fun v => ⟨(eN v).2.choose, ?_⟩, ?_⟩
    · have h := (eN v).2.choose_spec
      rw [hz, ← Category.assoc, h, ← hgp]; exact (eN v).1.2
    · intro v w hvw
      apply eN.injective
      apply Subtype.ext; apply Subtype.ext
      have := congrArg (fun x : {x : Spec (CommRingCat.of k) ⟶ E.C // x ≫ z = 𝟙 _} => x.1 ≫ E.lev) hvw
      simp only at this
      rw [(eN v).2.choose_spec, (eN w).2.choose_spec] at this
      exact this
  have hpts : N ^ 2 ≤ Nat.card (Γ(E.C, ⊤) →ₐ[k] k) := by
    have := LEVRED.natCard_algHom_ge z hfin (ZMod N × ZMod N) emb
    simpa [Nat.card_prod, Nat.card_zmod, pow_two] using this
  have hB : IsReduced Γ(E.C, ⊤) := IsReduced.of_finrank_le_natCard_algHom k _ (hrank ▸ hpts)
  haveI : IsReduced (Spec (CommRingCat.of Γ(E.C, ⊤))) := inferInstance
  exact isReduced_of_isOpenImmersion E.C.isoSpec.hom

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero (solution)
