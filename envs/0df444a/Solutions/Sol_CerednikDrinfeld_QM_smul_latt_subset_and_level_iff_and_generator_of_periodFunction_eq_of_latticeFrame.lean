-- Prove2me | solution 1 for CerednikDrinfeld.QM.smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/60303835-e8d8-54fd-8956-b5dcc87aa64b

import Definitions.Def_CerednikDrinfeld_QMModuli
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

namespace P2MW.S_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame

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
    (hper : ∀ z ∈ Metric.ball (σ₀ t) ε, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i))
    (z z' : ℂ) (hz : z ∈ Metric.ball (σ₀ t) ε) (hz' : z' ∈ Metric.ball (σ₀ t) ε) (hτ : τ z = τ z') :
    let H : ℂ := (c z * κ z) / (c z' * κ z')
    H ≠ 0 ∧
    (∀ w ∈ latt (u z).1, H • w ∈ latt (u z').1) ∧
    (∀ w ∈ latt (u z').1, H⁻¹ • w ∈ latt (u z).1) ∧
    (∀ w : Fin 2 → ℂ,
      (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
          FactorsThrough (u z).1.lev P ∧ e (u z).1 P = ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
      (∃ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z').1.f,
          FactorsThrough (u z').1.lev P' ∧ e (u z').1 P' = ((H • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup))) ∧
    (∀ w₀ : Fin 2 → ℂ, e (u z).1 (u z).2.P = ((w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) →
      e (u z').1 (u z').2.P = ((H • w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup)) := by
  intro H
  have hz0 := hz; have hz0' := hz'
  have hκz := hκ z hz; have hκz' := hκ z' hz'; have hcz := hc z hz; have hcz' := hc z' hz'
  have hH0 : H ≠ 0 := div_ne_zero (mul_ne_zero hcz hκz) (mul_ne_zero hcz' hκz')

  have hV' : ∀ i : Fin 4, v i z' = (c z / c z') • v i z := by
    intro i
    have h1 := hper z hz i; have h2 := hper z' hz' i
    rw [hτ] at h1
    have : c z' • v i z' = c z • v i z := by rw [h2, h1]
    calc v i z' = (c z')⁻¹ • (c z' • v i z') := by rw [smul_smul, inv_mul_cancel₀ hcz', one_smul]
      _ = (c z / c z') • v i z := by rw [this, smul_smul, div_eq_inv_mul]
  have hsum' : ∀ n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z') = (c z / c z') • ∑ i, (n i : ℂ) • v i z := by
    intro n; rw [Finset.smul_sum]; congr 1; funext i; rw [hV', smul_comm]

  have hHκ : ∀ X : Fin 2 → ℂ, H • ((κ z)⁻¹ • X) = (κ z')⁻¹ • ((c z / c z') • X) := by
    intro X; simp only [smul_smul]; congr 1; show (c z * κ z) / (c z' * κ z') * (κ z)⁻¹ = (κ z')⁻¹ * (c z / c z'); field_simp
  have hHκ' : ∀ X : Fin 2 → ℂ, H⁻¹ • ((κ z')⁻¹ • ((c z / c z') • X)) = (κ z)⁻¹ • X := by
    intro X; rw [← hHκ X, smul_smul, inv_mul_cancel₀ hH0, one_smul]

  have memS : ∀ zz ∈ Metric.ball (σ₀ t) ε, ∀ n : Fin 4 → ℤ,
      (∑ i, (n i : ℂ) • v i zz) ∈ κ zz • latt (u zz).1 := by
    intro zz hzz n
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ ((hBASIS zz hzz).1 i)

  have down : ∀ zz ∈ Metric.ball (σ₀ t) ε, ∀ x : Fin 2 → ℂ, x ∈ κ zz • latt (u zz).1 → (κ zz)⁻¹ • x ∈ latt (u zz).1 := by
    intro zz hzz x hx
    obtain ⟨y0, hy0, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x (κ zz) _).1 hx
    rwa [smul_smul, inv_mul_cancel₀ (hκ zz hzz), one_smul]

  have coords : ∀ w ∈ latt (u z).1, ∃ n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = κ z • w := by
    intro w hw
    obtain ⟨n, hn, -⟩ := (hBASIS z hz).2 _ (Submodule.smul_mem_pointwise_smul w (κ z) _ hw)
    exact ⟨n, hn⟩
  have coords' : ∀ w ∈ latt (u z').1, ∃ n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z') = κ z' • w := by
    intro w hw
    obtain ⟨n, hn, -⟩ := (hBASIS z' hz').2 _ (Submodule.smul_mem_pointwise_smul w (κ z') _ hw)
    exact ⟨n, hn⟩

  have G1 : ∀ w ∈ latt (u z).1, H • w ∈ latt (u z').1 := by
    intro w hw
    obtain ⟨n, hn⟩ := coords w hw
    have : H • w = (κ z')⁻¹ • ∑ i, (n i : ℂ) • v i z' := by
      rw [hsum' n, ← hHκ, hn, smul_smul (κ z)⁻¹ (κ z) w, inv_mul_cancel₀ hκz, one_smul]
    rw [this]
    exact down z' hz' _ (memS z' hz' n)

  have G2 : ∀ w ∈ latt (u z').1, H⁻¹ • w ∈ latt (u z).1 := by
    intro w hw
    obtain ⟨n, hn⟩ := coords' w hw
    have : H⁻¹ • w = (κ z)⁻¹ • ∑ i, (n i : ℂ) • v i z := by
      rw [← hHκ', ← hsum' n, hn, smul_smul (κ z')⁻¹ (κ z') w, inv_mul_cancel₀ hκz', one_smul]
    rw [this]
    exact down z hz _ (memS z hz n)

  have hHX : ∀ (r : ℂ) (n : Fin 4 → ℤ),
      H • ((κ z)⁻¹ • (r • ∑ i, (n i : ℂ) • v i z)) = (κ z')⁻¹ • (r • ∑ i, (n i : ℂ) • v i z') := by
    intro r n; rw [hHκ, smul_comm (c z / c z') r, ← hsum']

  have hq : ∀ (S : Submodule ℤ (Fin 2 → ℂ)) (x y : Fin 2 → ℂ),
      ((x : (Fin 2 → ℂ) ⧸ S.toAddSubgroup) = (y : (Fin 2 → ℂ) ⧸ S.toAddSubgroup)) ↔ -x + y ∈ S := by
    intro S x y; exact QuotientAddGroup.eq

  have hcls : ∀ w x : Fin 2 → ℂ, ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) = ((x : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) →
      ((H • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup) = ((H • x : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup) := by
    intro w x h
    rw [hq] at h ⊢
    have := G1 _ h
    simpa only [smul_add, smul_neg] using this
  have hcls' : ∀ w x : Fin 2 → ℂ, ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup) = ((x : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup) →
      ((H⁻¹ • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) = ((H⁻¹ • x : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) := by
    intro w x h
    rw [hq] at h ⊢
    have := G2 _ h
    simpa only [smul_add, smul_neg] using this

  have G3 : ∀ w : Fin 2 → ℂ,
      (∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z).1.f,
          FactorsThrough (u z).1.lev P ∧ e (u z).1 P = ((w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) ↔
      (∃ P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) (u z').1.f,
          FactorsThrough (u z').1.lev P' ∧ e (u z').1 P' = ((H • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup)) := by
    intro w
    rw [hLEVN z hz w, hLEVN z' hz' (H • w)]
    constructor
    · rintro ⟨n, hnT, hwn⟩
      refine ⟨n, hnT, ?_⟩
      rw [← hHX]; exact hcls _ _ hwn
    · rintro ⟨n, hnT, hwn⟩
      refine ⟨n, hnT, ?_⟩
      have h1 := hcls' _ _ hwn
      rw [← hHX, smul_smul, smul_smul, inv_mul_cancel₀ hH0, one_smul, one_smul] at h1
      exact h1

  have G4 : ∀ w₀ : Fin 2 → ℂ, e (u z).1 (u z).2.P = ((w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) →
      e (u z').1 (u z').2.P = ((H • w₀ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z').1).toAddSubgroup) := by
    intro w₀ hw₀
    rw [hLEVM z' hz', ← hHX]
    rw [hLEVM z hz] at hw₀
    exact (hcls _ _ hw₀.symm).symm
  exact ⟨hH0, G1, G2, G3, G4⟩

end S_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame
end P2MW
export P2MW.S_CerednikDrinfeld_QM_smul_latt_subset_and_level_iff_and_generator_of_periodFunction_eq_of_latticeFrame (solution)
