-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_lambdaAction_frameCoords_of_uniformization_family_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0882af83-a9f0-5167-a180-462342d815c2

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent
import Theorems.Thm_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_lambdaAction_frameCoords_of_uniformization_family_of_smooth

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

    (Sc : Type) [CommRing Sc] [IsDomain Sc] [Algebra ℂ Sc] [Algebra.FiniteType ℂ Sc]
    (hSc : Algebra.Smooth ℂ Sc) (hΩ : Module.rank Sc (KaehlerDifferential ℂ Sc) = 1)
    (t : Sc) (σ₀ : Sc →ₐ[ℂ] ℂ) (r : ℝ) (𝒰 : Set (Sc →ₐ[ℂ] ℂ)) (hr : 0 < r) (hσ₀ : σ₀ ∈ 𝒰)
    (hbij : Set.BijOn (fun σ : Sc →ₐ[ℂ] ℂ => σ t) 𝒰 (Metric.ball (σ₀ t) r))
    (hhol : ∀ s : Sc, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (Metric.ball (σ₀ t) r) ∧ ∀ σ ∈ 𝒰, σ s = F (σ t))

    (m : ℕ) (𝒰𝒜 : FakeEllipticCurve.WithFullLevel Λ N m Sc)
    (u : ℂ → FakeEllipticCurve.WithFullLevel Λ N m ℂ) (g : ∀ z : ℂ, (u z).1.A ⟶ 𝒰𝒜.1.A)
    (hg : ∀ σ ∈ 𝒰,
      ∃ hc : CategoryTheory.IsPullback (g (σ t)) (u (σ t)).1.f 𝒰𝒜.1.f (Spec.map (CommRingCat.ofHom σ.toRingHom)),

      (∀ (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f),
        ((u (σ t)).1.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q).1 ≫ g (σ t) =
          (𝒰𝒜.1.L.mul (𝟙 (Spec (CommRingCat.of ℂ)) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom))
            ⟨P.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g (σ t), by rw [Category.assoc, hc.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, (u (σ t)).1.act x ≫ g (σ t) = g (σ t) ≫ 𝒰𝒜.1.act x) ∧

      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f,
        FactorsThrough (u (σ t)).1.lev P → ∃ P₀ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.C, P₀ ≫ 𝒰𝒜.1.lev = P.1 ≫ g (σ t)) ∧

      ((u (σ t)).2.P).1 ≫ g (σ t) = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1)

    (ε : ℝ) (κ : ℂ → ℂ) (hε : 0 < ε) (hεr : ε ≤ r) (hκ : ∀ z ∈ Metric.ball (σ₀ t) ε, κ z ≠ 0)
    (hRELAN :
      (∀ (V : 𝒰𝒜.1.A.Opens) (f : Γ(𝒰𝒜.1.A, V)),
        IsOpen {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
          ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                  g (σ t)) ⁻¹ᵁ V} ∧
        ∃ F : ℂ × (Fin 2 → ℂ) → ℂ,
          DifferentiableOn ℂ F {p : ℂ × (Fin 2 → ℂ) | p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V} ∧
          ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₀ t) ε → ∀ (w : Fin 2 → ℂ)
            (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                    g (σ t)) ⁻¹ᵁ V),
            F (σ t, w) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
              (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫
                  g (σ t)).appLE V ⊤ hV) f)))
    (hRELCOV :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ w₁ w₁' : Fin 2 → ℂ,
        (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) =
          (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) →
        ∃ (V : 𝒰𝒜.1.A.Opens) (f₂ f₃ : Γ(𝒰𝒜.1.A, V)) (δ : ℝ)
          (D D' : (ℂ × (Fin 2 → ℂ)) ≃L[ℂ] (ℂ × (Fin 2 → ℂ))) (Φ : ℂ × (Fin 2 → ℂ) → ℂ × (Fin 2 → ℂ)),
          0 < δ ∧
          ⊤ ≤ (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ p ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ, p.1 ∈ Metric.ball (σ₀ t) ε ∧ ∃ σ ∈ 𝒰, σ t = p.1 ∧
            ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • p.2 : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V) ∧
          (∀ σ ∈ 𝒰, ∀ (w : Fin 2 → ℂ),
            (((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ ∨ ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ) →
            ∀ (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
            Φ (σ t, w) = (σ t, ![(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂),
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃)])) ∧
          HasFDerivAt Φ (D : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁) ∧
          HasFDerivAt Φ (D' : (ℂ × (Fin 2 → ℂ)) →L[ℂ] (ℂ × (Fin 2 → ℂ))) (σ₁ t, w₁') ∧
          (∀ σ ∈ 𝒰, ∀ (w w' : Fin 2 → ℂ),
            ((σ t, w) : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁) : ℂ × (Fin 2 → ℂ)) δ →
            ((σ t, w') : ℂ × (Fin 2 → ℂ)) ∈ Metric.ball ((σ₁ t, w₁') : ℂ × (Fin 2 → ℂ)) δ →
            ∀ (hV : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V)
              (hV' : ⊤ ≤ (((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) ⁻¹ᵁ V),
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₂) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₂) →
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV) f₃) =
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)).appLE V ⊤ hV') f₃) →
              (((e (u (σ t)).1).symm ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)) =
                (((e (u (σ t)).1).symm ((κ (σ t) • w' : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)).1 ≫ g (σ t)))))
    (hKCL :
      (∀ w : Fin 2 → ℂ, κ (σ₀ t) • w ∉ latt (u (σ₀ t)).1 →
        ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball (σ₀ t) δ, ∀ w' : Fin 2 → ℂ,
          κ z • w' ∈ latt (u z).1 → δ ≤ ‖w' - w‖))
    (hRELSURJ :
      (∀ σ₁ ∈ 𝒰, σ₁ t ∈ Metric.ball (σ₀ t) ε → ∀ (w₁ : Fin 2 → ℂ) (ρ : ℝ), 0 < ρ →
        ∃ (V : 𝒰𝒜.1.A.Opens) (fs : Finset ↑(Γ(𝒰𝒜.1.A, V))) (ε₁ : ℝ)
          (h₁ : ⊤ ≤ (((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)) ⁻¹ᵁ V),
          0 < ε₁ ∧ ∀ σ ∈ 𝒰, σ t ∈ Metric.ball (σ₁ t) ε₁ →
            ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u (σ t)).1.f)
              (hP : ⊤ ≤ (P.1 ≫ g (σ t)) ⁻¹ᵁ V),
              (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P.1 ≫ g (σ t)).appLE V ⊤ hP) φ) -
                  (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((((e (u (σ₁ t)).1).symm ((κ (σ₁ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₁ t)).1).toAddSubgroup)).1 ≫ g (σ₁ t)).appLE V ⊤ h₁) φ)‖ < ε₁) →
              ∃ w ∈ Metric.ball w₁ ρ,
                e (u (σ t)).1 P = ((κ (σ t) • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ t)).1).toAddSubgroup)))

    (ε' : ℝ) (v : Fin 4 → ℂ → (Fin 2 → ℂ)) (hε' : 0 < ε') (hε'ε : ε' ≤ ε)
    (hv : ∀ i : Fin 4, DifferentiableOn ℂ (v i) (Metric.ball (σ₀ t) ε'))
    (hbasis : ∀ z ∈ Metric.ball (σ₀ t) ε',
        (∀ i : Fin 4, κ z • v i z ∈ latt (u z).1) ∧
        ∀ x ∈ latt (u z).1, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = (κ z)⁻¹ • x) :
    ∃ (ε'' : ℝ) (A : ℍ[ℚ, a, b] → Fin 4 → Fin 4 → ℤ), 0 < ε'' ∧ ε'' ≤ ε' ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε'', ∀ lam ∈ Λ, ∀ j₀ : Fin 4,
        ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z) = ∑ i, (A lam i j₀ : ℂ) • v i z) := by
  classical
  set S : Set ℂ := Metric.ball (σ₀ t) ε' with hS
  have hSpre : IsPreconnected S := (convex_ball (σ₀ t) ε').isPreconnected
  have hκ' : ∀ z ∈ S, κ z ≠ 0 := fun z hz => hκ z (Metric.ball_subset_ball hε'ε hz)

  have hvc : ∀ i, ContinuousOn (v i) S := fun i => (hv i).continuousOn

  have hlin : ∀ z ∈ S, LinearIndependent ℝ (fun i => v i z) := by
    intro z hz
    obtain ⟨b₀, hb₀⟩ := (hL1 (u z).1).1
    have hgen : ∀ x ∈ Submodule.span ℤ (Set.range b₀), ∃ n : Fin 4 → ℤ, (∑ i, n i • (κ z • v i z)) = x := by
      intro x hx
      rw [← hb₀] at hx
      obtain ⟨n, hn, -⟩ := (hbasis z hz).2 x hx
      refine ⟨n, ?_⟩
      have : (∑ i, n i • (κ z • v i z)) = κ z • ∑ i, ((n i : ℂ) • v i z) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_comm]
      rw [this, hn, smul_inv_smul₀ (hκ' z hz)]
    have hli := LinearIndependent.of_forall_mem_span_exists_sum_zsmul_eq b₀ (fun i => κ z • v i z) hgen
    let f : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) :=
      ((LinearEquiv.smulOfNeZero ℂ (Fin 2 → ℂ) (κ z) (hκ' z hz)).restrictScalars ℝ).toLinearMap
    refine LinearIndependent.of_comp f ?_
    convert hli using 1
    rfl
    rfl

  have key : ∀ (lam : ℍ[ℚ, a, b]) (j₀ : Fin 4), ∃ n : Fin 4 → ℤ, lam ∈ Λ →
      ∀ z ∈ S, ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z) = ∑ i, n i • v i z := by
    intro lam j₀
    by_cases hlam : lam ∈ Λ
    swap
    · exact ⟨0, fun h => absurd h hlam⟩
    have hxc : ContinuousOn (fun z => ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z)) S :=
      (Continuous.matrix_mulVec continuous_const continuous_id).comp_continuousOn (hvc j₀)
    have hmem : ∀ z ∈ S, ∃ n : Fin 4 → ℤ, ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z) = ∑ i, n i • v i z := by
      intro z hz
      have h1 : κ z • v j₀ z ∈ latt (u z).1 := (hbasis z hz).1 j₀
      have h2 := (hL1 (u z).1).2 lam hlam _ h1
      obtain ⟨n, hn, -⟩ := (hbasis z hz).2 _ h2
      refine ⟨n, ?_⟩
      rw [Matrix.mulVec_smul, inv_smul_smul₀ (hκ' z hz)] at hn
      rw [← hn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
    obtain ⟨n, hn⟩ := IsPreconnected.exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent hSpre v hvc hlin
      (fun z => ((ι lam).map (algebraMap ℝ ℂ)).mulVec (v j₀ z)) hxc hmem
    exact ⟨n, fun _ => hn⟩
  choose Af hAf using key
  refine ⟨ε', fun lam i j₀ => Af lam j₀ i, hε', le_rfl, ?_⟩
  intro z hz lam hlam j₀
  rw [hAf lam j₀ hlam z hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Int.cast_smul_eq_zsmul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_lambdaAction_frameCoords_of_uniformization_family_of_smooth
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_lambdaAction_frameCoords_of_uniformization_family_of_smooth (solution)
