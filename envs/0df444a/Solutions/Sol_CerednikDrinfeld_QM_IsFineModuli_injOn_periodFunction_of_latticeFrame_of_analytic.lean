-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.injOn_periodFunction_of_latticeFrame_of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/a84df8a0-4bf0-5ddf-ba5d-71d2d2139045

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame
import Theorems.Thm_CerednikDrinfeld_QM_WithFullLevel_iso_of_smul_latt_subset_of_level_iff_of_generator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_injOn_periodFunction_of_latticeFrame_of_analytic

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

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

    (m : ℕ) (hm : 3 ≤ m) (hmc : m.Coprime (N * q * q'))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℂ)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ N m M πM ptF) (hsm : SmoothOfRelativeDimension 1 πM)

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (j : Spec (CommRingCat.of Sc) ⟶ M) [IsOpenImmersion j]
    (hj : j ≫ πM = Spec.map (CommRingCat.ofHom (algebraMap ℂ Sc)))
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ r)
    (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (κ : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
    (T : Set (Fin 4 → ℤ)) (a₀ : Fin 4 → ℤ)
    (hκ : ∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0)
    (hPT : ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε →
        ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) πM,
          x.1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j →
          ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)) = x)
    (hBASIS : ∀ z ∈ Metric.ball (σ₀ t) ε,
        (∀ i : Fin 4, v i z ∈ κ z • latt (u z).1) ∧
        ∀ x ∈ κ z • latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x)
    (hLEVN : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ w : Fin 2 → ℂ,
        (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
            FactorsThrough (u z).1.lev P ∧ e (u z).1 P = (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
          ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) =
            (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup))
    (hLEVM : ∀ z ∈ Metric.ball (σ₀ t) ε,
        e (u z).1 (u z).2.P =
          (((κ z)⁻¹ • (((m : ℂ)⁻¹) • ∑ i, (a₀ i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup))

    (τ : ℂ → UpperHalfPlane) (c : ℂ → ℂ) (y : Fin 4 → ℍ[ℚ, a, b])
    (hc : ∀ z ∈ Metric.ball (σ₀ t) ε, c z ≠ 0)
    (hper : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i)) :
    Set.InjOn (fun z : ℂ => τ z) (Metric.ball (σ₀ t) ε) := by
  intro z hz z' hz' hτ

  obtain ⟨hH, hL, hL', hlev, hgen⟩ := CerednikDrinfeld.QM.smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV m hm hmc M πM ptF hM hsm Sc j hj t σ₀ r 𝒰 hr hσ₀ hbij hhol ε hε hεr u κ v T a₀ hκ hPT hBASIS hLEVN hLEVM τ c y hc hper z z' hz hz' hτ

  have hiso : FakeEllipticCurve.WithFullLevel.Iso (u z) (u z') :=
    CerednikDrinfeld.QM.WithFullLevel.iso_of_smul_latt_subset_of_level_iff_of_generator hB Λ hΛ ι hι hqq' hqN hq'N hN R hR hRΛ latt e hL1 hE1 hE2 hH1 hH2 hH3 hAN hCOV m (u z) (u z') _ hH hL hL' hlev hgen

  have hpt := hM.ptF_iso ℂ (𝟙 _) (u z) (u z') hiso

  obtain ⟨σ, hσ, hσz⟩ := hbij.surjOn (Metric.ball_subset_ball hεr hz)
  obtain ⟨σ', hσ', hσz'⟩ := hbij.surjOn (Metric.ball_subset_ball hεr hz')
  simp only at hσz hσz'

  have hover : ∀ ρ : Sc →ₐ[ℂ] ℂ, (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ j) ≫ πM = 𝟙 (Spec (CommRingCat.of ℂ)) := by
    intro ρ
    have hcomp : (ρ.toRingHom).comp (algebraMap ℂ Sc) = RingHom.id ℂ := RingHom.ext fun x => by simp
    rw [Category.assoc, hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hof : CommRingCat.ofHom ((ρ.toRingHom).comp (algebraMap ℂ Sc)) = 𝟙 (CommRingCat.of ℂ) := by
      rw [hcomp]; rfl
    first
      | (rw [hof, Spec.map_id])
      | (erw [hof, Spec.map_id])
      | (simp only [hcomp, CommRingCat.ofHom_id, Spec.map_id])
  have hx : ∀ ρ ∈ 𝒰, ρ t ∈ Metric.ball (σ₀ t) ε →
      ptF ℂ (𝟙 (Spec (CommRingCat.of ℂ))) (u (ρ t)) = ⟨Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ j, hover ρ⟩ :=
    fun ρ hρ hρε => hPT ρ hρ hρε _ rfl
  have h1 := hx σ hσ (hσz ▸ hz)
  have h2 := hx σ' hσ' (hσz' ▸ hz')
  rw [hσz] at h1
  rw [hσz'] at h2
  have h12 : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j = Spec.map (CommRingCat.ofHom σ'.toRingHom) ≫ j := by
    have := congrArg Subtype.val (h1.symm.trans (hpt.trans h2))
    exact this
  have hsp : Spec.map (CommRingCat.ofHom σ.toRingHom) = Spec.map (CommRingCat.ofHom σ'.toRingHom) :=
    (cancel_mono j).1 h12
  have hrh : σ.toRingHom = σ'.toRingHom := by
    have := Spec.map_injective hsp
    exact congrArg CommRingCat.Hom.hom this
  have hσσ : σ = σ' := AlgHom.ext fun s => by
    have := congrArg (fun f : Sc →+* ℂ => f s) hrh
    exact this
  rw [← hσz, ← hσz', hσσ]

end S_CerednikDrinfeld_QM_IsFineModuli_injOn_periodFunction_of_latticeFrame_of_analytic
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_injOn_periodFunction_of_latticeFrame_of_analytic (solution)
