-- Prove2me | solution 1 for CerednikDrinfeld.QM.WithFullLevel.iso_of_smul_latt_subset_of_level_iff_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ab621779-1e23-5e65-9d0f-9a2af6cf5523

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isReduced_C_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

namespace IsoHom16

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

end IsoHom16

open IsoHom16 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

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

    (hAN : ∀ (E : FakeEllipticCurve Λ N ℂ) (U : E.A.Opens) (f : Γ(E.A, U)),
        IsOpen {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∃ F : (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {v : Fin 2 → ℂ | ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U} ∧
          ∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f))

    (hCOV : ∀ (E : FakeEllipticCurve Λ N ℂ) (v₀ : Fin 2 → ℂ),
        ∃ (U : E.A.Opens) (f₁ f₂ : Γ(E.A, U)) (ε : ℝ) (D : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
          (F : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
          0 < ε ∧
          (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U) ∧
          (∀ (v : Fin 2 → ℂ) (h : ⊤ ≤ ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1 ⁻¹ᵁ U),
            v ∈ Metric.ball v₀ ε →
            F v = ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₁),
                    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
                      ((((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)).1.appLE U ⊤ h) f₂)]) ∧
          HasFDerivAt F (D : (Fin 2 → ℂ) →L[ℂ] (Fin 2 → ℂ)) v₀)
    (m : ℕ)
    (uu uu' : FakeEllipticCurve.WithFullLevel Λ N m ℂ) (H : ℂ) (hH : H ≠ 0)
    (hL : ∀ w ∈ latt uu.1, H • w ∈ latt uu'.1)
    (hL' : ∀ w ∈ latt uu'.1, H⁻¹ • w ∈ latt uu.1)
    (hlev : ∀ w : Fin 2 → ℂ,
      (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uu.1.f,
          FactorsThrough uu.1.lev P ∧ e uu.1 P = ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu.1).toAddSubgroup)) ↔
      (∃ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uu'.1.f,
          FactorsThrough uu'.1.lev P' ∧ e uu'.1 P' = ((H • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu'.1).toAddSubgroup)))
    (hgen : ∀ w₀ : Fin 2 → ℂ, e uu.1 uu.2.P = ((w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu.1).toAddSubgroup) →
      e uu'.1 uu'.2.P = ((H • w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu'.1).toAddSubgroup)) :
    FakeEllipticCurve.WithFullLevel.Iso uu uu' := by
  classical
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)

  obtain ⟨φ, hφ, haddφ, hactφ, heφ⟩ := hH2 uu.1 uu'.1 H hL
  obtain ⟨ψ, hψ, haddψ, hactψ, heψ⟩ := hH2 uu'.1 uu.1 H⁻¹ hL'
  have hφψ : (φ ≫ ψ) ≫ uu.1.f = uu.1.f := by rw [Category.assoc, hψ, hφ]
  have hψφ : (ψ ≫ φ) ≫ uu'.1.f = uu'.1.f := by rw [Category.assoc, hφ, hψ]
  have h1 : φ ≫ ψ = 𝟙 uu.1.A := by
    refine hH3 uu.1 uu.1 (φ ≫ ψ) (𝟙 uu.1.A) hφψ (Category.id_comp _) (fun P => ?_)
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective ((e uu.1) P)
    apply (e uu.1).injective
    rw [mapPt_comp φ hφ ψ hψ, heψ _ _ (heφ P w hw.symm), mapPt_id, ← hw, smul_smul, inv_mul_cancel₀ hH, one_smul]
  have h2 : ψ ≫ φ = 𝟙 uu'.1.A := by
    refine hH3 uu'.1 uu'.1 (ψ ≫ φ) (𝟙 uu'.1.A) hψφ (Category.id_comp _) (fun P => ?_)
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective ((e uu'.1) P)
    apply (e uu'.1).injective
    rw [mapPt_comp ψ hψ φ hφ, heφ _ _ (heψ P w hw.symm), mapPt_id, ← hw, smul_smul, mul_inv_cancel₀ hH, one_smul]

  have hkφ : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uu.1.f, FactorsThrough uu.1.lev P →
      FactorsThrough uu'.1.lev (mapPt φ hφ P) := by
    intro P hP
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_surjective ((e uu.1) P)
    obtain ⟨P', hP', hP'e⟩ := (hlev w).1 ⟨P, hP, hw.symm⟩
    have : P' = mapPt φ hφ P := (e uu'.1).injective (by rw [hP'e, heφ P w hw.symm])
    exact this ▸ hP'
  have hkψ : ∀ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) uu'.1.f, FactorsThrough uu'.1.lev P' →
      FactorsThrough uu.1.lev (mapPt ψ hψ P') := by
    intro P' hP'
    obtain ⟨w', hw'⟩ := QuotientAddGroup.mk_surjective ((e uu'.1) P')
    have hw'' : (e uu'.1) P' = ((H • (H⁻¹ • w') : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt uu'.1).toAddSubgroup) := by
      rw [smul_smul, mul_inv_cancel₀ hH, one_smul]; exact hw'.symm
    obtain ⟨P, hP, hPe⟩ := (hlev (H⁻¹ • w')).2 ⟨P', hP', hw''⟩
    have : P = mapPt ψ hψ P' := (e uu.1).injective (by rw [hPe, heψ P' w' hw'.symm])
    exact this ▸ hP

  have hgen' : mapPt φ hφ uu.2.P = uu'.2.P := by
    obtain ⟨w₀, hw₀⟩ := QuotientAddGroup.mk_surjective ((e uu.1) uu.2.P)
    apply (e uu'.1).injective
    rw [heφ uu.2.P w₀ hw₀.symm, hgen w₀ hw₀.symm]
  refine ⟨⟨φ, ψ, h1, h2⟩, hφ, haddφ, hactφ, fun t P =>
    ⟨fun hP => factorsThrough_transfer hN0 uu.1 uu'.1 φ hφ hkφ t P hP, fun hP => ?_⟩, hgen'⟩
  have hback := factorsThrough_transfer hN0 uu'.1 uu.1 ψ hψ hkψ t _ hP
  rw [← mapPt_comp φ hφ ψ hψ (h := hφψ)] at hback
  obtain ⟨P₀, hP₀⟩ := hback
  exact ⟨P₀, by rw [hP₀]; simp [mapPt, h1]⟩

end S_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator
end P2MW
export P2MW.S_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator (solution)
