-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_smul_latt_atkinLehnerQuotient_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f8000295-4f41-54a4-bbb4-e2691526213c

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_int_trd_eq_and_nrd_eq
import Theorems.Thm_QuaternionAlgebra_nrd_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_atkinLehnerQuotient_of_pointEquiv
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace F4AL12

variable {R : Type} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

variable {a b : ℚ}

theorem star_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : star x ∈ Λ := by
  obtain ⟨⟨t, n, ht, -⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hΛ hx
  have h : star x = (t : ℤ) • (1 : ℍ[ℚ, a, b]) - x := by
    have h2 := add_star_eq_coe_trd x
    rw [ht] at h2
    have h3 : star x = ((t : ℚ) : ℍ[ℚ, a, b]) - x := by rw [← h2]; abel
    rw [h3, zsmul_eq_mul, mul_one]
    norm_cast
  rw [h]
  exact Λ.sub_mem (Λ.smul_mem _ hΛ.one_mem) hx

theorem qmPeriodMap_mul (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) (y s : ℍ[ℚ, a, b]) :
    qmPeriodMap ι τ (y * s) = ((ι y).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ s) := by
  simp only [qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

theorem mulVec_coe (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (r : ℚ) (v : Fin 2 → ℂ) :
    ((ι ((r : ℚ) : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v = (r : ℂ) • v := by
  have : ι ((r : ℚ) : ℍ[ℚ, a, b]) = algebraMap ℚ (Matrix (Fin 2) (Fin 2) ℝ) r := by
    rw [← ι.commutes r]; rfl
  rw [this, Algebra.algebraMap_eq_smul_one]
  rw [show ((r • (1 : Matrix (Fin 2) (Fin 2) ℝ)).map (algebraMap ℝ ℂ)) = ((r : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) from by
    ext i j; simp [Matrix.one_apply, Matrix.smul_apply]; split_ifs <;> simp]
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]

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

end F4AL12

open F4AL12 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)

    (latt : FakeEllipticCurve Λ 1 ℂ → Submodule ℤ (Fin 2 → ℂ))
    (e : ∀ E : FakeEllipticCurve Λ 1 ℂ,
      SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f ≃ ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hL1 : ∀ E : FakeEllipticCurve Λ 1 ℂ,
      (∃ b₀ : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), latt E = Submodule.span ℤ (Set.range b₀)) ∧
      (∀ x ∈ Λ, ∀ v ∈ latt E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ latt E))
    (hE1 : ∀ (E : FakeEllipticCurve Λ 1 ℂ) (P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      e E (E.L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e E P + e E Q)
    (hE2 : ∀ (E : FakeEllipticCurve Λ 1 ℂ) (x : ↥Λ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
      e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
      e E (pushPt (E.act x) (E.act_over x) P) =
        ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hH1 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) →
      ∃ c : ℂ, (∀ v ∈ latt E, c • v ∈ latt E') ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH2 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (c : ℂ), (∀ v ∈ latt E, c • v ∈ latt E') →
      ∃ (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (P Q : SchemeHomOver t E.f),
          mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
        (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f) (v : Fin 2 → ℂ),
          e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) →
          e E' (mapPt φ hφ P) = ((c • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E').toAddSubgroup))
    (hH3 : ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (φ ψ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E'.f = E.f),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, mapPt φ hφ P = mapPt ψ hψ P) → φ = ψ) :
    (∀ (r : ℕ), (r = q ∨ r = q') →
        ∀ (E E' : FakeEllipticCurve Λ 1 ℂ) (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 → c • latt E = qmPeriodLattice ι Λ τ →
        E.IsAtkinLehnerQuotient r E' →
        ∀ s ∈ Λ, nrd s = (r : ℚ) →
          ∃ c' : ℂ, c' ≠ 0 ∧ ∀ v : Fin 2 → ℂ, v ∈ c' • latt E' ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) := by
  classical
  intro r hr E E' τ c hc hcL hAL s hs hns
  have hO : IsOrder Λ := hΛ.isOrder
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> exact Fact.out
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  have hrq0 : (r : ℚ) ≠ 0 := by exact_mod_cast hrp.ne_zero
  set φτ := qmPeriodMap ι τ with hφτ

  have he_one : ∀ X : FakeEllipticCurve Λ 1 ℂ, e X (X.L.one (𝟙 _)) = 0 := by
    intro X
    have h := hE1 X (X.L.one (𝟙 _)) (X.L.one (𝟙 _))
    rw [X.L.one_mul] at h
    exact left_eq_add.mp h
  have hsurj : ∀ (X : FakeEllipticCurve Λ 1 ℂ) (v : Fin 2 → ℂ), ∃ P, e X P = (v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) :=
    fun X v => ⟨(e X).symm v, (e X).apply_symm_apply _⟩
  have hmem_iff : ∀ (X : FakeEllipticCurve Λ 1 ℂ) (v : Fin 2 → ℂ), ((v : (Fin 2 → ℂ) ⧸ (latt X).toAddSubgroup) = 0) ↔ v ∈ latt X :=
    fun X v => (QuotientAddGroup.eq_zero_iff v).trans (Submodule.mem_toAddSubgroup _)

  obtain ⟨φ, hφ, ψ, hψ, haddφ, haddψ, hactφ, hactψ, hcomp, hker, -⟩ := hAL
  have hrΛ : ((r : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((r : ℚ) : ℍ[ℚ, a, b]) = (r : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  obtain ⟨hφψ, hψφ⟩ := hcomp hrΛ
  obtain ⟨c₁, hc₁, hce₁⟩ := hH1 E E' φ hφ haddφ hactφ
  obtain ⟨c₂, hc₂, hce₂⟩ := hH1 E' E ψ hψ haddψ hactψ

  have hprod : ∀ v : Fin 2 → ℂ, (c₂ * c₁ - r) • v ∈ latt E := by
    intro v
    obtain ⟨P, hP⟩ := hsurj E v
    have h1 := hce₂ (mapPt φ hφ P) (c₁ • v) (hce₁ P v hP)
    rw [← mapPt_comp φ hφ ψ hψ (h := by rw [Category.assoc, hψ, hφ]), smul_smul] at h1
    have h2 : mapPt (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) P = pushPt (E.act ⟨_, hrΛ⟩) (E.act_over ⟨_, hrΛ⟩) P := by
      apply Subtype.ext; simp [mapPt, hφψ]
    rw [h2] at h1
    have h3 : e E (pushPt (E.act ⟨_, hrΛ⟩) (E.act_over ⟨_, hrΛ⟩) P) = (((r : ℂ) • v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
      rw [hE2 E ⟨_, hrΛ⟩ P v hP, mulVec_coe]; push_cast; rfl
    rw [← hmem_iff, sub_smul, QuotientAddGroup.mk_sub, ← h1, ← h3, sub_self]
  obtain ⟨b₀, hb₀⟩ := (hL1 E).1
  have hcc : c₂ * c₁ = r := by
    by_contra hne
    exact not_forall_smul_mem (latt E) b₀ hb₀ (sub_ne_zero.2 hne) hprod
  have hc₁0 : c₁ ≠ 0 := by rintro rfl; rw [mul_zero] at hcc; exact hr0 hcc.symm
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; rw [zero_mul] at hcc; exact hr0 hcc.symm

  let Sat : (Fin 2 → ℂ) → Prop := fun u =>
    ∀ (m : ↥Λ) (n : ℤ), (m : ℍ[ℚ, a, b]) * star (m : ℍ[ℚ, a, b]) = (((r : ℤ) * n : ℚ) : ℍ[ℚ, a, b]) →
      ((ι (m : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec u ∈ latt E
  have hlatt' : ∀ w : Fin 2 → ℂ, w ∈ latt E' ↔ Sat (c₁⁻¹ • w) := by
    intro w
    constructor
    · intro hw

      obtain ⟨Q, hQ⟩ := hsurj E' ((r : ℂ)⁻¹ • w)
      have hP : e E (mapPt ψ hψ Q) = ((c₂ • (r : ℂ)⁻¹ • w : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := hce₂ Q _ hQ
      have hkerP : mapPt φ hφ (mapPt ψ hψ Q) = E'.L.one (𝟙 _) := by
        rw [← mapPt_comp ψ hψ φ hφ (h := by rw [Category.assoc, hφ, hψ])]
        have h2 : mapPt (ψ ≫ φ) (by rw [Category.assoc, hφ, hψ]) Q = pushPt (E'.act ⟨_, hrΛ⟩) (E'.act_over ⟨_, hrΛ⟩) Q := by
          apply Subtype.ext; simp [mapPt, hψφ]
        rw [h2]
        apply (e E').injective
        rw [hE2 E' ⟨_, hrΛ⟩ Q _ hQ, he_one, mulVec_coe, smul_smul, Rat.cast_natCast, mul_inv_cancel₀ hr0, one_smul]
        exact (hmem_iff E' w).2 hw
      intro m n hmn
      have h3 := (hker (𝟙 _) (mapPt ψ hψ Q)).1 hkerP m n hmn
      have h4 := hE2 E m (mapPt ψ hψ Q) _ hP
      rw [h3, he_one] at h4
      have h5 := (hmem_iff E _).1 h4.symm
      have : c₁⁻¹ • w = c₂ • (r : ℂ)⁻¹ • w := by
        rw [smul_smul]; congr 1; field_simp; rw [mul_comm, hcc]
      rw [this]; exact h5
    · intro hsat
      obtain ⟨P, hP⟩ := hsurj E (c₁⁻¹ • w)
      have hkerP : mapPt φ hφ P = E'.L.one (𝟙 _) := by
        apply (hker (𝟙 _) P).2
        intro m n hmn
        apply (e E).injective
        rw [hE2 E m P _ hP, he_one]
        exact (hmem_iff E _).2 (hsat m n hmn)
      have h1 := hce₁ P _ hP
      rw [hkerP, he_one, smul_smul, mul_inv_cancel₀ hc₁0, one_smul] at h1
      exact (hmem_iff E' w).1 h1.symm

  have hlattE : ∀ v : Fin 2 → ℂ, v ∈ latt E ↔ c • v ∈ qmPeriodLattice ι Λ τ := by
    intro v
    rw [← hcL]
    constructor
    · exact fun hv => Submodule.smul_mem_pointwise_smul v c _ hv
    · intro hv
      obtain ⟨v', hv', h⟩ := (Submodule.mem_smul_pointwise_iff_exists _ c (latt E)).1 hv
      rwa [← smul_right_injective _ hc h]
  have hsbar : star s ∈ Λ := star_mem hO hs
  have hssbar : s * star s = ((r : ℚ) : ℍ[ℚ, a, b]) := by rw [mul_star_eq_coe_nrd, hns]
  have key : ∀ u : Fin 2 → ℂ, Sat u ↔ ∃ y ∈ Λ, φτ (y * s) = ((r : ℂ) * c) • u := by
    intro u
    constructor
    · intro hsat

      have h1 : ((ι (star s)).map (algebraMap ℝ ℂ)).mulVec u ∈ latt E := by
        refine hsat ⟨star s, hsbar⟩ 1 ?_
        show star s * star (star s) = _
        rw [star_star, star_mul_eq_coe_nrd, hns]; push_cast; simp
      rw [hlattE, mem_qmPeriodLattice_iff] at h1
      obtain ⟨z, hz, hzeq⟩ := h1

      obtain ⟨y, hy, hyeq⟩ :=
        QuaternionAlgebra.IsMaximalOrder.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
          hB Λ hΛ r hr s hs (z * star s) (hO.mul_mem hz hsbar) ⟨1, by rw [hns]; ring⟩
          (by
            obtain ⟨⟨_, nz, -, hnz⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hz
            exact ⟨nz, by rw [QuaternionAlgebra.nrd_mul, nrd_star, hns, hnz, mul_comm]⟩)
      refine ⟨y, hy, ?_⟩

      have hys : y * s = s * z := by
        have h3 := congrArg (fun t => t * s) hyeq
        rw [mul_assoc, mul_assoc, star_mul_eq_coe_nrd, hns, mul_coe_eq_smul, mul_smul_comm, smul_mul_assoc,
          ← Int.cast_smul_eq_zsmul ℚ] at h3
        push_cast at h3
        exact (smul_right_injective _ hrq0 h3).symm
      rw [hys, qmPeriodMap_mul, hzeq, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← map_mul, hssbar,
        mulVec_coe, smul_smul, mul_comm c]
      push_cast; rfl
    · rintro ⟨y, hy, hyeq⟩ m n hmn
      rw [hlattE, ← Matrix.mulVec_smul, mem_qmPeriodLattice_iff]

      have hnm : nrd (m : ℍ[ℚ, a, b]) = (r : ℚ) * n := by
        have h := (mul_star_eq_coe_nrd (m : ℍ[ℚ, a, b])).symm.trans hmn
        exact_mod_cast QuaternionAlgebra.coe_injective h
      obtain ⟨⟨_, ny, -, hny⟩, -⟩ := QuaternionAlgebra.IsOrder.exists_int_trd_eq_and_nrd_eq hO hy
      obtain ⟨y', hy', hyeq'⟩ :=
        QuaternionAlgebra.IsMaximalOrder.exists_mul_eq_natCast_smul_of_dvd_nrd_of_dvd_nrd_of_isIndefiniteRamifiedExactlyAt
          hB Λ hΛ r hr (m : ℍ[ℚ, a, b]) m.2 (y * s) (hO.mul_mem hy hs) ⟨n, hnm⟩
          ⟨ny, by rw [QuaternionAlgebra.nrd_mul, hns, hny, mul_comm]⟩
      refine ⟨y', hy', ?_⟩

      have hcu : c • u = (r : ℂ)⁻¹ • φτ (y * s) := by
        rw [hyeq, smul_smul, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
      rw [hcu, Matrix.mulVec_smul, ← qmPeriodMap_mul, hyeq', map_zsmul]
      rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]; push_cast; rw [inv_mul_cancel₀ hr0, one_smul]

  refine ⟨(r : ℂ) * c * c₁⁻¹, mul_ne_zero (mul_ne_zero hr0 hc) (inv_ne_zero hc₁0), fun v => ?_⟩
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, h⟩ := (key _).1 ((hlatt' w).1 hw)
    refine ⟨y, hy, ?_⟩
    rw [h, smul_smul]
  · rintro ⟨y, hy, h⟩
    refine ⟨((r : ℂ) * c * c₁⁻¹)⁻¹ • v, (hlatt' _).2 ((key _).2 ⟨y, hy, ?_⟩), ?_⟩
    · rw [h, smul_smul, smul_smul, mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero hr0 hc) (inv_ne_zero hc₁0)), one_smul]
    · rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero (mul_ne_zero hr0 hc) (inv_ne_zero hc₁0)), one_smul]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_atkinLehnerQuotient_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_smul_latt_atkinLehnerQuotient_of_pointEquiv (solution)
