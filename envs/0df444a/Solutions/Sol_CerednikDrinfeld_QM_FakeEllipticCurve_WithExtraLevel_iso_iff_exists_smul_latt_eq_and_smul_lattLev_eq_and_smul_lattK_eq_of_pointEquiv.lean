-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel.iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f3b560ba-0d63-51a7-bbc3-7b5544048998

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_isReduced_K_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace K2Iso48

variable {R : Type} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem mapPt_id {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {h : 𝟙 A ≫ f = f}
    {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) : mapPt (𝟙 A) h P = P := by
  apply Subtype.ext; simp [mapPt]

theorem eq_of_mapPt_id_eq {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {φ ψ : A ⟶ A'} {hφ : φ ≫ f' = f} {hψ : ψ ≫ f' = f}
    (h : mapPt φ hφ (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = mapPt ψ hψ ⟨𝟙 A, Category.id_comp f⟩) : φ = ψ := by
  have := congrArg Subtype.val h
  simpa [mapPt] using this

def IsHom {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (LX : RelativeGroupLaw R gX) (LY : RelativeGroupLaw R gY) (α : X ⟶ Y) (hα : α ≫ gY = gX) : Prop :=
  ∀ ⦃T : Scheme.{0}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t gX),
    mapPt α hα (LX.mul t u v) = LY.mul t (mapPt α hα u) (mapPt α hα v)

theorem IsHom.comp {X Y Z : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {gZ : Z ⟶ Spec (CommRingCat.of R)} {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {LZ : RelativeGroupLaw R gZ}
    {α : X ⟶ Y} {hα : α ≫ gY = gX} {β : Y ⟶ Z} {hβ : β ≫ gZ = gY} (h₁ : IsHom LX LY α hα) (h₂ : IsHom LY LZ β hβ)
    {h : (α ≫ β) ≫ gZ = gX} : IsHom LX LZ (α ≫ β) h := by
  intro T t u v
  rw [mapPt_comp α hα β hβ, h₁, h₂, ← mapPt_comp α hα β hβ, ← mapPt_comp α hα β hβ]

theorem IsHom.map_one {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt α hα (LX.one t) = LY.one t := by
  have h' := h t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h'
  have := congrArg (LY.mul t (LY.inv t (mapPt α hα (LX.one t)))) h'
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at this
  exact this.symm

theorem IsHom.map_inv {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gX) :
    mapPt α hα (LX.inv t P) = LY.inv t (mapPt α hα P) := by
  letI := LY.pointGroup t
  have h' := h t (LX.inv t P) P
  rw [LX.inv_mul_cancel, h.map_one] at h'
  exact (inv_eq_of_mul_eq_one_left h'.symm).symm

theorem IsHom.map_nsmulPt {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : X ⟶ Y} {hα : α ≫ gY = gX} (h : IsHom LX LY α hα)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t gX) :
    mapPt α hα (nsmulPt LX t n P) = nsmulPt LY t n (mapPt α hα P) := by
  induction n with
  | zero => exact h.map_one t
  | succ n ih => simp only [nsmulPt]; rw [h, ih]

theorem mapPt_iso_eq_iff {X Y : Scheme.{0}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (e : X ≅ Y) (he : e.hom ≫ gY = gX) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P Q : SchemeHomOver t gX) :
    mapPt e.hom he P = mapPt e.hom he Q ↔ P = Q := by
  constructor
  · intro h
    have := congrArg (fun S : SchemeHomOver t gY => S.1 ≫ e.inv) h
    simp only [mapPt, Category.assoc, e.hom_inv_id, Category.comp_id] at this
    exact Subtype.ext this
  · rintro rfl; rfl

theorem inv_unique {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) (h : L.mul t y x = L.one t) :
    y = L.inv t x := by
  have := congrArg (fun z => L.mul t z (L.inv t x)) h
  rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one, L.one_mul] at this
  exact this

theorem mapPt_invHom {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    mapPt (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 (L.inv f ⟨𝟙 A, Category.id_comp f⟩).2 P = L.inv t P := by
  apply inv_unique
  have hn := L.mul_natural f t P.1 P.2 (L.inv f ⟨𝟙 A, Category.id_comp f⟩) ⟨𝟙 A, Category.id_comp f⟩
  rw [L.inv_mul_cancel, L.one_natural] at hn
  have e1 : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (L.inv f ⟨𝟙 A, Category.id_comp f⟩) =
      mapPt (L.inv f ⟨𝟙 A, Category.id_comp f⟩).1 (L.inv f ⟨𝟙 A, Category.id_comp f⟩).2 P := by
    apply Subtype.ext; rfl
  have e2 : GoodReductionJacobian.schemeHomOverComp P.1 P.2 (⟨𝟙 A, Category.id_comp f⟩ : SchemeHomOver f f) = P := by
    apply Subtype.ext; show P.1 ≫ 𝟙 A = P.1; exact Category.comp_id _
  rw [e1, e2] at hn
  exact hn.symm

theorem factorsThrough_transfer {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hN : (N : ℂ) ≠ 0)
    (E E' : FakeEllipticCurve Λ N ℂ) (g : E.A ⟶ E'.A) (hg : g ≫ E'.f = E.f)
    (hk : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, FactorsThrough E.lev P →
      FactorsThrough E'.lev (mapPt g hg P))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P : SchemeHomOver t E.f) (hP : FactorsThrough E.lev P) :
    FactorsThrough E'.lev (mapPt g hg P) := by
  haveI : IsReduced E.C := FakeEllipticCurve.isReduced_C_of_natCast_ne_zero ℂ E hN
  haveI : IsClosedImmersion E'.lev := E'.lev_closed
  haveI : IsFinite (E.lev ≫ E.f) := E.lev_finite
  haveI : LocallyOfFiniteType (E.lev ≫ E.f) := inferInstance
  obtain ⟨φ₀, hφ₀⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced ℂ (E.lev ≫ E.f) E'.f
    E'.lev (E.lev ≫ g) (by rw [Category.assoc, hg]) (fun z => by
      have hz : FactorsThrough E.lev (⟨z.1 ≫ E.lev, by rw [Category.assoc]; exact z.2⟩ :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) := ⟨z.1, rfl⟩
      obtain ⟨w, hw⟩ := hk _ hz
      exact ⟨w, by rw [hw]; simp [mapPt]⟩)
  obtain ⟨P₀, hP₀⟩ := hP
  exact ⟨P₀ ≫ φ₀, by simp [mapPt, hφ₀, ← hP₀]⟩

theorem not_forall_smul_mem (L : Submodule ℤ (Fin 2 → ℂ)) (b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ))
    (hL : L = Submodule.span ℤ (Set.range b₀)) {d : ℂ} (hd : d ≠ 0) : ¬ ∀ v : Fin 2 → ℂ, d • v ∈ L := by
  intro h
  have hmem : ((1 / 2 : ℝ) • b₀ 0 : Fin 2 → ℂ) ∈ Submodule.span ℤ (Set.range b₀) := by
    rw [← hL]
    have := h (d⁻¹ • ((1 / 2 : ℝ) • b₀ 0))
    rwa [smul_smul, mul_inv_cancel₀ hd, one_smul] at this
  rw [Module.Basis.mem_span_iff_repr_mem] at hmem
  obtain ⟨n, hn⟩ := hmem 0
  rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same] at hn
  have hn' : (n : ℝ) = 1 / 2 := hn
  have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast (by rw [hn']; norm_num : (2 : ℝ) * n = 1)
  omega

theorem factorsThroughK_transfer {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N ℓ : ℕ} (hℓ : (ℓ : ℂ) ≠ 0)
    (E E' : FakeEllipticCurve Λ N ℂ) (K : E.ExtraLevel ℓ) (K' : E'.ExtraLevel ℓ) (g : E.A ⟶ E'.A) (hg : g ≫ E'.f = E.f)
    (hk : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, FactorsThrough K.levK P →
      FactorsThrough K'.levK (mapPt g hg P))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P : SchemeHomOver t E.f) (hP : FactorsThrough K.levK P) :
    FactorsThrough K'.levK (mapPt g hg P) := by
  haveI : IsReduced K.K := FakeEllipticCurve.ExtraLevel.isReduced_K_of_natCast_ne_zero ℂ E K hℓ
  haveI : IsClosedImmersion K'.levK := K'.levK_closed
  haveI : IsFinite (K.levK ≫ E.f) := K.levK_finite
  haveI : LocallyOfFiniteType (K.levK ≫ E.f) := inferInstance
  obtain ⟨φ₀, hφ₀⟩ := CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced ℂ (K.levK ≫ E.f) E'.f
    K'.levK (K.levK ≫ g) (by rw [Category.assoc, hg]) (fun z => by
      have hz : FactorsThrough K.levK (⟨z.1 ≫ K.levK, by rw [Category.assoc]; exact z.2⟩ :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) := ⟨z.1, rfl⟩
      obtain ⟨w, hw⟩ := hk _ hz
      exact ⟨w, by rw [hw]; simp [mapPt]⟩)
  obtain ⟨P₀, hP₀⟩ := hP
  exact ⟨P₀ ≫ φ₀, by simp [mapPt, hφ₀, ← hP₀]⟩

end K2Iso48

open K2Iso48 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)

    (latt : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ N ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))

    (hL1 : ∀ E : FakeEllipticCurve Λ N ℂ,
        (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
        (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))

    (hE1 : ∀ (E : FakeEllipticCurve Λ N ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
        e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)

    (hE2 : ∀ (E : FakeEllipticCurve Λ N ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
        e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
        e E (pushPt (E.act x) (E.act_over x) P) =
          ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH2 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
      ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH3 : ∀ (E E' : FakeEllipticCurve Λ N ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ)

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)

    (ℓ : ℕ) (lattK : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLK : ∀ (u : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ) (v : Fin 2 → ℂ),
      v ∈ lattK u ↔ FactorsThrough u.2.levK ((e u.1).symm (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup))) :
    (∀ u u' : FakeEllipticCurve.WithExtraLevel Λ N ℓ ℂ,
        FakeEllipticCurve.WithExtraLevel.Iso u u' ↔
          ∃ c : ℂ, c ≠ 0 ∧ c • latt u.1 = latt u'.1 ∧ c • lattLev u.1 = lattLev u'.1 ∧ c • lattK u = lattK u') := by
  classical
  intro u u'
  obtain ⟨E, K⟩ := u
  obtain ⟨E', K'⟩ := u'
  dsimp only
  have hLK_E : ∀ v : Fin 2 → ℂ, v ∈ lattK ⟨E, K⟩ ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) :=
    fun v => hLK ⟨E, K⟩ v
  have hLK_E' : ∀ v : Fin 2 → ℂ, v ∈ lattK ⟨E', K'⟩ ↔ FactorsThrough K'.levK ((e E').symm (v : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup)) :=
    fun v => hLK ⟨E', K'⟩ v

  have hsurj : ∀ (X : FakeEllipticCurve Λ N ℂ) (v : Fin 2 → ℂ), ∃ P, e X P = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) :=
    fun X v => ⟨(e X).symm v, (e X).apply_symm_apply _⟩
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)

  have hmemtr : ∀ (X Y : FakeEllipticCurve Λ N ℂ) (g : X.A ⟶ Y.A) (hg : g ≫ Y.f = X.f) (d : ℂ),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f, FactorsThrough X.lev P → FactorsThrough Y.lev (mapPt g hg P)) →
      (∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f) (v : Fin 2 → ℂ),
        e X P = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) →
        e Y (mapPt g hg P) = ((d • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup)) →
      ∀ v ∈ lattLev X, d • v ∈ lattLev Y := by
    intro X Y g hg d hlg hge v hv
    obtain ⟨P, hP, hPe⟩ := ((hLev X).1 v).1 hv
    exact ((hLev Y).1 (d • v)).2 ⟨mapPt g hg P, hlg P hP, hge P v hPe⟩

  have hkpt : ∀ (X Y : FakeEllipticCurve Λ N ℂ) (g : X.A ⟶ Y.A) (hg : g ≫ Y.f = X.f) (d : ℂ),
      (∀ v ∈ lattLev X, d • v ∈ lattLev Y) →
      (∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f) (v : Fin 2 → ℂ),
        e X P = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) →
        e Y (mapPt g hg P) = ((d • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup)) →
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f, FactorsThrough X.lev P → FactorsThrough Y.lev (mapPt g hg P) := by
    intro X Y g hg d hd hge P hP
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (e X P)
    have hwmem : w ∈ lattLev X := ((hLev X).1 w).2 ⟨P, hP, hw.symm⟩
    obtain ⟨P'', hP'', hP''e⟩ := ((hLev Y).1 (d • w)).1 (hd w hwmem)
    have : P'' = mapPt g hg P := (e Y).injective (by rw [hP''e, hge P w hw.symm])
    exact this ▸ hP''

  have hmemtrK : ∀ (X Y : FakeEllipticCurve Λ N ℂ) (KX : X.ExtraLevel ℓ) (KY : Y.ExtraLevel ℓ)
      (hX : ∀ v : Fin 2 → ℂ, v ∈ lattK ⟨X, KX⟩ ↔ FactorsThrough KX.levK ((e X).symm (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup)))
      (hY : ∀ v : Fin 2 → ℂ, v ∈ lattK ⟨Y, KY⟩ ↔ FactorsThrough KY.levK ((e Y).symm (v : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup)))
      (g : X.A ⟶ Y.A) (hg : g ≫ Y.f = X.f) (d : ℂ),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f, FactorsThrough KX.levK P → FactorsThrough KY.levK (mapPt g hg P)) →
      (∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f) (v : Fin 2 → ℂ),
        e X P = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) →
        e Y (mapPt g hg P) = ((d • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup)) →
      ∀ v ∈ lattK ⟨X, KX⟩, d • v ∈ lattK ⟨Y, KY⟩ := by
    intro X Y KX KY hX hY g hg d hlg hge v hv
    have hP := (hX v).1 hv
    have hPe : e X ((e X).symm (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup)) = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) :=
      (e X).apply_symm_apply _
    have h2 := hge _ v hPe
    apply (hY (d • v)).2
    have : (e Y).symm ((d • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup) = mapPt g hg ((e X).symm (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup)) := by
      rw [← h2, Equiv.symm_apply_apply]
    rw [this]
    exact hlg _ hP
  have hkptK : ∀ (X Y : FakeEllipticCurve Λ N ℂ) (KX : X.ExtraLevel ℓ) (KY : Y.ExtraLevel ℓ)
      (hX : ∀ v : Fin 2 → ℂ, v ∈ lattK ⟨X, KX⟩ ↔ FactorsThrough KX.levK ((e X).symm (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup)))
      (hY : ∀ v : Fin 2 → ℂ, v ∈ lattK ⟨Y, KY⟩ ↔ FactorsThrough KY.levK ((e Y).symm (v : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup)))
      (g : X.A ⟶ Y.A) (hg : g ≫ Y.f = X.f) (d : ℂ),
      (∀ v ∈ lattK ⟨X, KX⟩, d • v ∈ lattK ⟨Y, KY⟩) →
      (∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f) (v : Fin 2 → ℂ),
        e X P = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) →
        e Y (mapPt g hg P) = ((d • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup)) →
      ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) X.f, FactorsThrough KX.levK P → FactorsThrough KY.levK (mapPt g hg P) := by
    intro X Y KX KY hX hY g hg d hd hge P hP
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective (e X P)
    have hPw : (e X).symm (w : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) = P := by rw [hw, Equiv.symm_apply_apply]
    have hwmem : w ∈ lattK ⟨X, KX⟩ := (hX w).2 (hPw ▸ hP)
    have h2 := (hY (d • w)).1 (hd w hwmem)
    have : (e Y).symm ((d • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt Y).toAddSubgroup) = mapPt g hg P := by
      rw [← hge P w hw.symm, Equiv.symm_apply_apply]
    rwa [this] at h2
  constructor
  · rintro ⟨eI, he, hadd, hact, hlev, hlevK⟩
    have he' : eI.inv ≫ E.f = E'.f := by rw [← he, eI.inv_hom_id_assoc]
    have hcomp : ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f), mapPt eI.inv he' (mapPt eI.hom he P) = P := by
      intro P; rw [← mapPt_comp eI.hom he eI.inv he' (h := by rw [eI.hom_inv_id]; exact Category.id_comp _)]
      apply Subtype.ext; simp [mapPt]
    have hcomp' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P : SchemeHomOver t E'.f),
        mapPt eI.hom he (mapPt eI.inv he' P) = P := by
      intro T t P; rw [← mapPt_comp eI.inv he' eI.hom he (h := by rw [eI.inv_hom_id]; exact Category.id_comp _)]
      apply Subtype.ext; simp [mapPt]
    have hadd' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E'.f),
        mapPt eI.inv he' (E'.L.mul t P Q) = E.L.mul t (mapPt eI.inv he' P) (mapPt eI.inv he' Q) := by
      intro T t P Q
      apply (mapPt_iso_eq_iff eI he _ _).1
      rw [hcomp', hadd, hcomp', hcomp']
    have hact' : ∀ x : ↥Λ, E'.act x ≫ eI.inv = eI.inv ≫ E.act x := by
      intro x
      rw [← cancel_mono eI.hom, Category.assoc, eI.inv_hom_id, Category.comp_id, Category.assoc, hact x,
        eI.inv_hom_id_assoc]
    obtain ⟨c, hc, hce⟩ := hH1 E E' eI.hom he hadd hact
    obtain ⟨c', hc', hce'⟩ := hH1 E' E eI.inv he' hadd' hact'

    have hkey : ∀ v : Fin 2 → ℂ, (c' * c - 1) • v ∈ latt E := by
      intro v
      obtain ⟨P, hP⟩ := hsurj E v
      have h1 := hce' (mapPt eI.hom he P) (c • v) (hce P v hP)
      rw [hcomp, hP, smul_smul] at h1
      rw [sub_smul, one_smul]
      have := (QuotientAddGroup.eq.1 h1)
      rw [Submodule.mem_toAddSubgroup] at this
      have : -( -v + (c' * c) • v) ∈ latt E → (c' * c) • v - v ∈ latt E := fun h => by
        rw [neg_add, neg_neg, ← sub_eq_add_neg] at h
        rwa [← neg_sub, Submodule.neg_mem_iff] at h
      exact this ((latt E).neg_mem ‹_›)
    obtain ⟨b₀, hb₀⟩ := (hL1 E).1
    have hcc : c' * c = 1 := by
      by_contra hne
      exact not_forall_smul_mem (latt E) b₀ hb₀ (sub_ne_zero.2 hne) hkey
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hcc; exact zero_ne_one hcc
    refine ⟨c, hc0, le_antisymm ?_ ?_, le_antisymm ?_ ?_, le_antisymm ?_ ?_⟩
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w c (latt E)).1 hw
      exact hc v hv
    · intro w hw
      refine (Submodule.mem_smul_pointwise_iff_exists w c (latt E)).2 ⟨c' • w, hc' w hw, ?_⟩
      rw [smul_smul, mul_comm, hcc, one_smul]
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w c (lattLev E)).1 hw
      exact hmemtr E E' eI.hom he c (fun P hP => (hlev _ P).1 hP) hce v hv
    · intro w hw
      refine (Submodule.mem_smul_pointwise_iff_exists w c (lattLev E)).2 ⟨c' • w, ?_, by rw [smul_smul, mul_comm, hcc, one_smul]⟩
      exact hmemtr E' E eI.inv he' c' (fun P hP => by rw [hlev _ (mapPt eI.inv he' P), hcomp']; exact hP) hce' w hw
    · intro w hw
      obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w c (lattK ⟨E, K⟩)).1 hw
      exact hmemtrK E E' K K' hLK_E hLK_E' eI.hom he c (fun P hP => (hlevK _ P).1 hP) hce v hv
    · intro w hw
      refine (Submodule.mem_smul_pointwise_iff_exists w c (lattK ⟨E, K⟩)).2 ⟨c' • w, ?_, by rw [smul_smul, mul_comm, hcc, one_smul]⟩
      exact hmemtrK E' E K' K hLK_E' hLK_E eI.inv he' c' (fun P hP => by rw [hlevK _ (mapPt eI.inv he' P), hcomp']; exact hP) hce' w hw
  · rintro ⟨c, hc0, hcl, hclL, hclK⟩

    have hℓ : (ℓ : ℂ) ≠ 0 := by
      intro h0
      have hℓ0 : ℓ = 0 := by exact_mod_cast h0
      obtain ⟨P₀, -⟩ := K.levK_one (𝟙 (Spec (CommRingCat.of ℂ)))
      haveI := K.levK_flat
      haveI := K.levK_finite
      have h1 := Scheme.Hom.one_le_finrank_map (K.levK ≫ E.f) (P₀.base (IsLocalRing.closedPoint ℂ))
      rw [K.levK_rank, hℓ0] at h1
      simp at h1
    have hsub : ∀ v ∈ latt E, c • v ∈ latt E' := fun v hv => hcl ▸ Submodule.smul_mem_pointwise_smul v c _ hv
    have hsub' : ∀ w ∈ latt E', c⁻¹ • w ∈ latt E := by
      intro w hw
      rw [← hcl] at hw
      obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w c (latt E)).1 hw
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    obtain ⟨φ, hφ, haddφ, hactφ, heφ⟩ := hH2 E E' c hsub
    obtain ⟨ψ, hψ, haddψ, hactψ, heψ⟩ := hH2 E' E c⁻¹ hsub'
    have hφψ : (φ ≫ ψ) ≫ E.f = E.f := by rw [Category.assoc, hψ, hφ]
    have hψφ : (ψ ≫ φ) ≫ E'.f = E'.f := by rw [Category.assoc, hφ, hψ]
    have h1 : φ ≫ ψ = 𝟙 E.A := by
      refine hH3 E E (φ ≫ ψ) (𝟙 E.A) hφψ (Category.id_comp _) (fun P => ?_)
      obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective ((e E) P)
      apply (e E).injective
      rw [mapPt_comp φ hφ ψ hψ, heψ _ _ (heφ P w hw.symm), mapPt_id, ← hw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have h2 : ψ ≫ φ = 𝟙 E'.A := by
      refine hH3 E' E' (ψ ≫ φ) (𝟙 E'.A) hψφ (Category.id_comp _) (fun P => ?_)
      obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective ((e E') P)
      apply (e E').injective
      rw [mapPt_comp ψ hψ φ hφ, heφ _ _ (heψ P w hw.symm), mapPt_id, ← hw, smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have hsubL' : ∀ w ∈ lattLev E', c⁻¹ • w ∈ lattLev E := by
      intro w hw
      rw [← hclL] at hw
      obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w c (lattLev E)).1 hw
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hkφ := hkpt E E' φ hφ c (fun w hw => hclL ▸ Submodule.smul_mem_pointwise_smul w c _ hw) heφ
    have hkψ := hkpt E' E ψ hψ c⁻¹ hsubL' heψ
    have hsubK' : ∀ w ∈ lattK ⟨E', K'⟩, c⁻¹ • w ∈ lattK ⟨E, K⟩ := by
      intro w hw
      rw [← hclK] at hw
      obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists w c (lattK ⟨E, K⟩)).1 hw
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hkKφ := hkptK E E' K K' hLK_E hLK_E' φ hφ c (fun w hw => hclK ▸ Submodule.smul_mem_pointwise_smul w c _ hw) heφ
    have hkKψ := hkptK E' E K' K hLK_E' hLK_E ψ hψ c⁻¹ hsubK' heψ
    refine ⟨⟨φ, ψ, h1, h2⟩, hφ, haddφ, hactφ, fun t P => ⟨fun hP => factorsThrough_transfer hN E E' φ hφ hkφ t P hP, fun hP => ?_⟩,
      fun t P => ⟨fun hP => factorsThroughK_transfer hℓ E E' K K' φ hφ hkKφ t P hP, fun hP => ?_⟩⟩
    · have hback := factorsThrough_transfer hN E' E ψ hψ hkψ t _ hP
      rw [← mapPt_comp φ hφ ψ hψ (h := hφψ)] at hback
      obtain ⟨P₀, hP₀⟩ := hback
      exact ⟨P₀, by rw [hP₀]; simp [mapPt, h1]⟩
    · have hback := factorsThroughK_transfer hℓ E' E K' K ψ hψ hkKψ t _ hP
      rw [← mapPt_comp φ hφ ψ hψ (h := hφψ)] at hback
      obtain ⟨P₀, hP₀⟩ := hback
      exact ⟨P₀, by rw [hP₀]; simp [mapPt, h1]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithExtraLevel_iso_iff_exists_smul_latt_eq_and_smul_lattLev_eq_and_smul_lattK_eq_of_pointEquiv (solution)
