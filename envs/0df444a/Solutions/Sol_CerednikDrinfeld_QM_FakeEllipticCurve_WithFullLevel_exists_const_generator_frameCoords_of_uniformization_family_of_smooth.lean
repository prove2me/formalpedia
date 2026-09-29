-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_const_generator_frameCoords_of_uniformization_family_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/93b4c2cb-860d-5968-84e6-beede2f3f5e3

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_isOpen_and_exists_differentiableOn_appLE_of_forall_section
import Theorems.Thm_AlgebraicGeometry_exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_generator_frameCoords_of_uniformization_family_of_smooth

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise BigOperators

namespace C5C48

open Topology Filter Set

theorem not_countable_quotient (S : AddSubgroup (Fin 2 → ℂ)) (hS : (S : Set (Fin 2 → ℂ)).Countable) :
    ¬ Countable ((Fin 2 → ℂ) ⧸ S) := by
  intro hQ
  apply not_countable_complex
  have hV : (Set.univ : Set (Fin 2 → ℂ)).Countable := by
    have hcov : (Set.univ : Set (Fin 2 → ℂ)) ⊆
        ⋃ q : (Fin 2 → ℂ) ⧸ S, (fun s : Fin 2 → ℂ => Quotient.out q + s) '' (S : Set (Fin 2 → ℂ)) := by
      intro x _
      refine Set.mem_iUnion.2 ⟨QuotientAddGroup.mk x, ?_⟩
      refine ⟨-(Quotient.out (QuotientAddGroup.mk x : (Fin 2 → ℂ) ⧸ S)) + x, ?_, by abel⟩
      rw [SetLike.mem_coe, ← QuotientAddGroup.eq]
      exact QuotientAddGroup.out_eq' _
    exact (Set.countable_iUnion fun q => hS.image _).mono hcov
  have : (Set.univ : Set ℂ) = (fun v : Fin 2 → ℂ => v 0) '' Set.univ := by
    ext z; simp only [Set.mem_univ, Set.image_univ, Set.mem_range, true_iff]; exact ⟨fun _ => z, rfl⟩
  rw [this]; exact hV.image _

theorem countable_span_range {ι : Type} [Fintype ι] (b : ι → (Fin 2 → ℂ)) :
    ((Submodule.span ℤ (Set.range b) : Submodule ℤ (Fin 2 → ℂ)) : Set (Fin 2 → ℂ)).Countable := by
  have : ((Submodule.span ℤ (Set.range b) : Submodule ℤ (Fin 2 → ℂ)) : Set (Fin 2 → ℂ)) ⊆
      Set.range (fun n : ι → ℤ => ∑ i, n i • b i) := by
    intro x hx
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx
    exact ⟨n, hn⟩
  exact (Set.countable_range _).mono this

theorem exists_lattice_gap (v : Fin 4 → ℂ → (Fin 2 → ℂ)) (z₀ : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hv : ∀ i, ContinuousOn (v i) (Metric.ball z₀ δ))
    (hli : LinearIndependent ℝ (fun i => v i z₀)) :
    ∃ (c η : ℝ), 0 < c ∧ 0 < η ∧ η ≤ δ ∧ ∀ z ∈ Metric.ball z₀ η, ∀ d : Fin 4 → ℤ, d ≠ 0 →
      c ≤ ‖∑ i, ((d i : ℤ) : ℂ) • v i z‖ := by
  classical

  set T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 2 → ℂ) := Fintype.linearCombination ℝ (fun i => v i z₀) with hT
  have hTinj : Function.Injective T := hli.fintypeLinearCombination_injective
  obtain ⟨K, hK, hAL⟩ := T.injective_iff_antilipschitz.1 hTinj

  have hKpos : (0 : ℝ) < K := hK
  obtain ⟨η, hη, hηδ, hηv⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ z ∈ Metric.ball z₀ η, ∀ i, ‖v i z - v i z₀‖ ≤ (8 * (K : ℝ))⁻¹ := by
    have hε : (0 : ℝ) < (8 * (K : ℝ))⁻¹ := by positivity
    have hall : ∀ i, ∃ ηi > 0, ∀ z ∈ Metric.ball z₀ ηi, z ∈ Metric.ball z₀ δ → ‖v i z - v i z₀‖ ≤ (8 * (K : ℝ))⁻¹ := by
      intro i
      have hc := (hv i) z₀ (Metric.mem_ball_self hδ)
      have := Metric.continuousWithinAt_iff.1 hc _ hε
      obtain ⟨ηi, hηi, h⟩ := this
      exact ⟨ηi, hηi, fun z hz hzδ => by rw [← dist_eq_norm]; exact (h hzδ hz).le⟩
    choose ηi hηi hηiv using hall
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min ηi
    refine ⟨min (ηi i₀) δ, lt_min (hηi i₀) hδ, min_le_right _ _, fun z hz i => ?_⟩
    exact hηiv i z (Metric.ball_subset_ball ((min_le_left _ _).trans (hi₀ i)) hz) (Metric.ball_subset_ball (min_le_right _ _) hz)
  refine ⟨(2 * K)⁻¹, η, by positivity, hη, hηδ, fun z hz d hd => ?_⟩

  set dr : Fin 4 → ℝ := fun i => (d i : ℝ) with hdr
  have hdr1 : 1 ≤ ‖dr‖ := by
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h; push Not at h; exact hd (funext h)
    calc (1 : ℝ) ≤ |(d i : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hi
      _ = ‖dr i‖ := by rw [hdr, Real.norm_eq_abs]
      _ ≤ ‖dr‖ := norm_le_pi_norm dr i
  have hTd : T dr = ∑ i, ((d i : ℤ) : ℂ) • v i z₀ := by
    simp only [hT, Fintype.linearCombination_apply, hdr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.coe_smul]; norm_cast
  have hlow : ‖dr‖ ≤ K * ‖∑ i, ((d i : ℤ) : ℂ) • v i z₀‖ := by
    have := hAL.le_mul_dist dr 0
    simp only [dist_zero_right, map_zero] at this
    rw [hTd] at this; exact this

  have hpert : ‖∑ i, ((d i : ℤ) : ℂ) • v i z - ∑ i, ((d i : ℤ) : ℂ) • v i z₀‖ ≤ 4 * ‖dr‖ * (8 * (K : ℝ))⁻¹ := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ i, (((d i : ℤ) : ℂ) • v i z - ((d i : ℤ) : ℂ) • v i z₀)‖
        ≤ ∑ i, ‖((d i : ℤ) : ℂ) • v i z - ((d i : ℤ) : ℂ) • v i z₀‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 4, ‖dr‖ * (8 * (K : ℝ))⁻¹ := Finset.sum_le_sum fun i _ => by
          rw [← smul_sub, norm_smul]
          refine mul_le_mul ?_ (hηv z hz i) (norm_nonneg _) (norm_nonneg _)
          rw [Complex.norm_intCast, ← Real.norm_eq_abs]
          have : ‖(d i : ℝ)‖ = ‖dr i‖ := by rw [hdr]
          rw [this]; exact norm_le_pi_norm dr i
      _ = 4 * ‖dr‖ * (8 * (K : ℝ))⁻¹ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  have hK' : (K : ℝ) ≠ 0 := hKpos.ne'
  have h1 : ‖dr‖ / K ≤ ‖∑ i, ((d i : ℤ) : ℂ) • v i z₀‖ := by
    rw [div_le_iff₀ hKpos]; linarith [hlow]
  have h2 : ‖∑ i, ((d i : ℤ) : ℂ) • v i z₀‖ ≤ ‖∑ i, ((d i : ℤ) : ℂ) • v i z‖ + 4 * ‖dr‖ * (8 * (K : ℝ))⁻¹ := by
    have := norm_sub_norm_le (∑ i, ((d i : ℤ) : ℂ) • v i z₀) (∑ i, ((d i : ℤ) : ℂ) • v i z)
    rw [← norm_neg, neg_sub] at hpert
    linarith [abs_le.1 (abs_norm_sub_norm_le (∑ i, ((d i : ℤ) : ℂ) • v i z₀) (∑ i, ((d i : ℤ) : ℂ) • v i z))]
  have h3 : 4 * ‖dr‖ * (8 * (K : ℝ))⁻¹ = ‖dr‖ / K / 2 := by simp only [mul_inv, div_eq_mul_inv]; ring
  have h4 : (2 * (K : ℝ))⁻¹ ≤ ‖dr‖ / K / 2 := by
    rw [show (2 * (K : ℝ))⁻¹ = 1 / K / 2 by simp only [mul_inv, div_eq_mul_inv, one_mul]; ring]
    gcongr
  linarith

end C5C48

open C5C48 in
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
    ∃ (ε'' : ℝ) (a₀ : Fin 4 → ℤ), 0 < ε'' ∧ ε'' ≤ ε' ∧

      (∀ z ∈ Metric.ball (σ₀ t) ε'',
        e (u z).1 (u z).2.P =
          ((κ z • (((m : ℂ)⁻¹) • ∑ i, (a₀ i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup)) := by
  classical
  set z₀ : ℂ := σ₀ t with hz₀
  set E₀ := (u z₀).1 with hE₀

  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · exfalso
    subst hm0
    haveI : Countable ℍ[ℚ, a, b] := Countable.of_equiv _ (QuaternionAlgebra.equivTuple _ _ _).symm
    have hgp : geomPoint ℂ (RingHom.id ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
      show Spec.map (CommRingCat.ofHom (RingHom.id ℂ)) = 𝟙 _
      rw [CommRingCat.ofHom_id]; exact Spec.map_id _
    have hsurj : Function.Surjective (fun x : ↥Λ =>
        pushPt ((u z₀).1.act x) ((u z₀).1.act_over x) (FakeEllipticCurve.sectionAt (u z₀).2.P ℂ (RingHom.id ℂ))) := by
      intro Q
      exact (u z₀).2.generates ℂ (RingHom.id ℂ) Q rfl
    have hc : Countable (SchemeHomOver (geomPoint ℂ (RingHom.id ℂ)) (u z₀).1.f) := hsurj.countable
    rw [hgp] at hc
    have hcT : Countable ((Fin 2 → ℂ) ⧸ (latt (u z₀).1).toAddSubgroup) := Countable.of_equiv _ (e (u z₀).1)
    obtain ⟨b₀, hb₀⟩ := (hL1 (u z₀).1).1
    refine not_countable_quotient (latt (u z₀).1).toAddSubgroup ?_ hcT
    show ((latt (u z₀).1 : Submodule ℤ (Fin 2 → ℂ)) : Set (Fin 2 → ℂ)).Countable
    rw [hb₀]; exact countable_span_range b₀

  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'

  have he_one : ∀ E : FakeEllipticCurve Λ N ℂ, e E (E.L.one (𝟙 (Spec (CommRingCat.of ℂ)))) = 0 := by
    intro E
    have h := hE1 E (E.L.one _) (E.L.one _)
    rw [E.L.one_mul] at h
    exact left_eq_add.1 h
  have he_nsmul : ∀ (E : FakeEllipticCurve Λ N ℂ) (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      e E (nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) n P) = n • e E P := by
    intro E n P
    induction n with
    | zero => rw [zero_smul]; exact he_one E
    | succ n ih =>
      show e E (E.L.mul _ (nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) n P) P) = (n + 1) • e E P
      rw [hE1, ih, add_smul, one_smul]

  have htor : ∀ (z : ℂ) (w : Fin 2 → ℂ),
      e (u z).1 (u z).2.P = ((κ z • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) →
      (m : ℂ) • (κ z • w) ∈ latt (u z).1 := by
    intro z w hw
    have h1 := he_nsmul (u z).1 m (u z).2.P
    rw [(u z).2.torsion, he_one, hw] at h1
    have h2 : (((m • (κ z • w) : Fin 2 → ℂ)) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) = 0 := by
      rw [QuotientAddGroup.mk_nsmul]; exact h1.symm
    rw [QuotientAddGroup.eq_zero_iff] at h2
    rw [← Nat.cast_smul_eq_nsmul ℂ] at h2
    exact h2

  have hcoord : ∀ z ∈ Metric.ball z₀ ε', ∀ (w : Fin 2 → ℂ),
      e (u z).1 (u z).2.P = ((κ z • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z).1).toAddSubgroup) →
      ∃ n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = (m : ℂ) • w := by
    intro z hz w hw
    obtain ⟨n, hn, -⟩ := (hbasis z hz).2 _ (htor z w hw)
    refine ⟨n, ?_⟩
    rw [hn, smul_smul, smul_smul, mul_assoc, mul_comm (m : ℂ) (κ z), ← mul_assoc,
      inv_mul_cancel₀ (hκ z (Metric.ball_subset_ball hε'ε hz)), one_mul]

  have hz₀ε' : z₀ ∈ Metric.ball z₀ ε' := Metric.mem_ball_self hε'
  have hz₀ε : z₀ ∈ Metric.ball z₀ ε := Metric.mem_ball_self hε
  set y₀ : Fin 2 → ℂ := Quotient.out (e (u z₀).1 (u z₀).2.P) with hy₀
  set w₁ : Fin 2 → ℂ := (κ z₀)⁻¹ • y₀ with hw₁
  have hw₁ : e (u z₀).1 (u z₀).2.P = ((κ z₀ • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z₀).1).toAddSubgroup) := by
    rw [hw₁, smul_smul, mul_inv_cancel₀ (hκ z₀ hz₀ε), one_smul, hy₀]
    exact (QuotientAddGroup.out_eq' _).symm
  obtain ⟨a₀, ha₀⟩ := hcoord z₀ hz₀ε' w₁ hw₁
  have hP₀ : (e (u z₀).1).symm ((κ z₀ • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z₀).1).toAddSubgroup) = (u z₀).2.P := by
    rw [← hw₁, Equiv.symm_apply_apply]

  have hli : LinearIndependent ℝ (fun i => v i z₀) := by
    obtain ⟨b₀, hb₀⟩ := (hL1 (u z₀).1).1
    set uu : Fin 4 → (Fin 2 → ℂ) := fun i => κ z₀ • v i z₀ with huu
    have hspan : (⊤ : Submodule ℝ (Fin 2 → ℂ)) ≤ Submodule.span ℝ (Set.range uu) := by
      rw [← b₀.span_eq]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      have hbj : b₀ j ∈ latt (u z₀).1 := by rw [hb₀]; exact Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨n, hn, -⟩ := (hbasis z₀ hz₀ε').2 _ hbj
      have : b₀ j = ∑ i, (n i : ℝ) • uu i := by
        have h2 : κ z₀ • (∑ i, (n i : ℂ) • v i z₀) = b₀ j := by
          rw [hn, smul_smul, mul_inv_cancel₀ (hκ z₀ hz₀ε), one_smul]
        rw [← h2, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [huu, smul_comm, ← Complex.coe_smul]; norm_cast
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (Fin 2 → ℂ) := by
      rw [Module.finrank_eq_card_basis b₀]
    have hliu : LinearIndependent ℝ uu := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
    rw [Fintype.linearIndependent_iff] at hliu ⊢
    intro g hg i
    refine hliu g ?_ i
    have : ∑ i, g i • uu i = κ z₀ • ∑ i, g i • v i z₀ := by
      rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [huu, smul_comm]
    rw [this, hg, smul_zero]

  obtain ⟨c, η, hc, hη, hηε', hgap⟩ := exists_lattice_gap v z₀ hε' (fun i => (hv i).continuousOn) hli

  set Ma : ℝ := ∑ i, ‖((a₀ i : ℤ) : ℂ)‖ with hMa
  set ρ : ℝ := c / (4 * ((m : ℝ) + 1)) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity

  obtain ⟨V, fs, ε₁, h₁, hε₁, hSURJ⟩ := hRELSURJ σ₀ hσ₀ hz₀ε w₁ ρ hρpos

  have hgen : ∀ σ ∈ 𝒰, ((u (σ t)).2.P).1 ≫ g (σ t) = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (𝒰𝒜.2.P).1 :=
    fun σ hσ => (hg σ hσ).2.2.2.2
  have hPi0 : ((e (u (σ₀ t)).1).symm ((κ (σ₀ t) • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u (σ₀ t)).1).toAddSubgroup)).1 ≫ g (σ₀ t) =
      Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ (𝒰𝒜.2.P).1 := by
    rw [← hgen σ₀ hσ₀]
    show ((e (u z₀).1).symm ((κ z₀ • w₁ : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt (u z₀).1).toAddSubgroup)).1 ≫ g z₀ = ((u z₀).2.P).1 ≫ g z₀
    rw [hP₀]
  have hvalcongr : ∀ (f₁ f₂ : Spec (CommRingCat.of ℂ) ⟶ 𝒰𝒜.1.A), f₁ = f₂ → ∀ (W : 𝒰𝒜.1.A.Opens) (φ : Γ(𝒰𝒜.1.A, W))
      (k₁ : ⊤ ≤ f₁ ⁻¹ᵁ W) (k₂ : ⊤ ≤ f₂ ⁻¹ᵁ W),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((f₁.appLE W ⊤ k₁) φ) = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((f₂.appLE W ⊤ k₂) φ) := by
    intro f₁ f₂ h; subst h; intro W φ k₁ k₂; rfl
  have h₁' : ⊤ ≤ (Spec.map (CommRingCat.ofHom σ₀.toRingHom) ≫ (𝒰𝒜.2.P).1) ⁻¹ᵁ V := by rw [← hPi0]; exact h₁

  have hrat := fun φ : Γ(𝒰𝒜.1.A, V) =>
    AlgebraicGeometry.exists_forall_gammaSpecIso_appLE_specMap_comp_eq_div_pow (K := ℂ) (𝒰𝒜.2.P).1 V φ σ₀ h₁'
  choose s₀ aa kk hs₀ hratval using hrat
  choose Fh hFh hFhval using hhol

  have hcontF : ∀ s : Sc, ContinuousAt (Fh s) z₀ := fun s =>
    ((hFh s).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).continuousAt
  have hFz₀ : ∀ s : Sc, Fh s z₀ = σ₀ s := fun s => (hFhval s σ₀ hσ₀).symm

  have hgood : ∀ᶠ z in 𝓝 z₀, (∀ φ ∈ insert (0 : Γ(𝒰𝒜.1.A, V)) fs, Fh (s₀ φ) z ≠ 0) ∧
      (∀ φ ∈ fs, ‖Fh (aa φ) z / Fh (s₀ φ) z ^ kk φ - Fh (aa φ) z₀ / Fh (s₀ φ) z₀ ^ kk φ‖ < ε₁) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all_finset]
      intro φ _
      have h0 : Fh (s₀ φ) z₀ ≠ 0 := by rw [hFz₀]; exact hs₀ φ
      exact (hcontF (s₀ φ)).eventually_ne h0
    · rw [Filter.eventually_all_finset]
      intro φ _
      have h0 : Fh (s₀ φ) z₀ ≠ 0 := by rw [hFz₀]; exact hs₀ φ
      have hq : ContinuousAt (fun z => Fh (aa φ) z / Fh (s₀ φ) z ^ kk φ) z₀ :=
        (hcontF (aa φ)).div ((hcontF (s₀ φ)).pow _) (pow_ne_zero _ h0)
      have := Metric.tendsto_nhds.1 hq ε₁ hε₁
      filter_upwards [this] with z hz
      rwa [dist_eq_norm] at hz

  have hvsmall : ∀ᶠ z in 𝓝 z₀, ∑ i, ‖((a₀ i : ℤ) : ℂ)‖ * ‖v i z - v i z₀‖ < c / 4 := by
    have hct : Filter.Tendsto (fun z => ∑ i, ‖((a₀ i : ℤ) : ℂ)‖ * ‖v i z - v i z₀‖) (𝓝 z₀)
        (𝓝 (∑ i : Fin 4, ‖((a₀ i : ℤ) : ℂ)‖ * ‖v i z₀ - v i z₀‖)) := by
      refine tendsto_finsetSum _ fun i _ => ?_
      have hci : ContinuousAt (v i) z₀ := ((hv i).differentiableAt (Metric.isOpen_ball.mem_nhds hz₀ε')).continuousAt
      exact (((hci.tendsto).sub tendsto_const_nhds).norm).const_mul _
    have h0 : (∑ i : Fin 4, ‖((a₀ i : ℤ) : ℂ)‖ * ‖v i z₀ - v i z₀‖) < c / 4 := by
      simp only [sub_self, norm_zero, mul_zero, Finset.sum_const_zero]; positivity
    exact hct.eventually (eventually_lt_nhds h0)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hgood.and (hvsmall.and (Metric.ball_mem_nhds z₀ (lt_min (lt_min hε₁ hη) hε'))))

  refine ⟨min δ ε', a₀, lt_min hδ hε', min_le_right _ _, ?_⟩
  intro z hz
  have hzδ : z ∈ Metric.ball z₀ δ := Metric.ball_subset_ball (min_le_left _ _) hz
  obtain ⟨⟨hden, hclose⟩, hvs, hz3⟩ := hδsub hzδ
  have hzε₁ : z ∈ Metric.ball z₀ ε₁ := Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) hz3
  have hzη : z ∈ Metric.ball z₀ η := Metric.ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _)) hz3
  have hzε' : z ∈ Metric.ball z₀ ε' := Metric.ball_subset_ball (min_le_right _ _) hz3
  have hzr : z ∈ Metric.ball z₀ r := Metric.ball_subset_ball (hε'ε.trans hεr) hzε'

  obtain ⟨σ, hσ𝒰, hσz⟩ := hbij.surjOn hzr
  subst hσz

  have hσs : ∀ φ ∈ insert (0 : Γ(𝒰𝒜.1.A, V)) fs, σ (s₀ φ) ≠ 0 := fun φ hφ => by rw [hFhval (s₀ φ) σ hσ𝒰]; exact hden φ hφ
  obtain ⟨hmemV, -⟩ := hratval 0 σ (hσs 0 (Finset.mem_insert_self _ _))
  have hP : ⊤ ≤ (((u (σ t)).2.P).1 ≫ g (σ t)) ⁻¹ᵁ V := by rw [hgen σ hσ𝒰]; exact hmemV
  obtain ⟨w, hw, hew⟩ := hSURJ σ hσ𝒰 hzε₁ (u (σ t)).2.P hP (fun φ hφ => by
    obtain ⟨hmφ, hvφ⟩ := hratval φ σ (hσs φ (Finset.mem_insert_of_mem hφ))
    obtain ⟨hm₀, hv₀⟩ := hratval φ σ₀ (hs₀ φ)
    rw [hvalcongr _ _ (hgen σ hσ𝒰) V φ hP hmφ, hvφ, hvalcongr _ _ hPi0 V φ h₁ hm₀, hv₀,
      hFhval (aa φ) σ hσ𝒰, hFhval (s₀ φ) σ hσ𝒰, ← hFz₀ (aa φ), ← hFz₀ (s₀ φ)]
    exact hclose φ hφ)

  obtain ⟨n, hn⟩ := hcoord (σ t) hzε' w hew
  have hna : n = a₀ := by
    by_contra hne
    have hd : n - a₀ ≠ 0 := sub_ne_zero.2 hne
    have hgap' := hgap (σ t) hzη (n - a₀) hd

    have hid : ∑ i, (((n - a₀) i : ℤ) : ℂ) • v i (σ t) =
        (m : ℂ) • (w - w₁) - ∑ i, ((a₀ i : ℤ) : ℂ) • (v i (σ t) - v i z₀) := by
      have e1 : ∑ i, (((n - a₀) i : ℤ) : ℂ) • v i (σ t) = ∑ i, ((n i : ℤ) : ℂ) • v i (σ t) - ∑ i, ((a₀ i : ℤ) : ℂ) • v i (σ t) := by
        rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.sub_apply, Int.cast_sub, sub_smul]
      rw [e1, hn, smul_sub, ← ha₀]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    have hbound : ‖∑ i, (((n - a₀) i : ℤ) : ℂ) • v i (σ t)‖ < c := by
      rw [hid]
      calc ‖(m : ℂ) • (w - w₁) - ∑ i, ((a₀ i : ℤ) : ℂ) • (v i (σ t) - v i z₀)‖
          ≤ ‖(m : ℂ) • (w - w₁)‖ + ‖∑ i, ((a₀ i : ℤ) : ℂ) • (v i (σ t) - v i z₀)‖ := norm_sub_le _ _
        _ ≤ (m : ℝ) * ρ + ∑ i, ‖((a₀ i : ℤ) : ℂ)‖ * ‖v i (σ t) - v i z₀‖ := by
            gcongr
            · rw [norm_smul, Complex.norm_natCast]
              exact mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hw).le) (Nat.cast_nonneg _)
            · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => by rw [norm_smul])
        _ < c / 4 * 1 + c / 4 := by
            refine add_lt_add ?_ hvs
            rw [hρ]
            have hm1 : (m : ℝ) < (m : ℝ) + 1 := lt_add_one _
            have : (m : ℝ) * (c / (4 * ((m : ℝ) + 1))) = c / 4 * ((m : ℝ) / ((m : ℝ) + 1)) := by
              field_simp
            rw [this]
            gcongr
            rw [div_lt_one (by positivity)]; exact hm1
        _ ≤ c := by linarith
    exact absurd hgap' (not_le.2 hbound)

  rw [hew]
  congr 2
  rw [hna] at hn
  rw [hn, smul_smul, inv_mul_cancel₀ hm0, one_smul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_generator_frameCoords_of_uniformization_family_of_smooth
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_const_generator_frameCoords_of_uniformization_family_of_smooth (solution)
