-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.forall_factorsThrough_lev_imp_eq_one_of_smul_eq_qmPeriodMap_of_nrd_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/99fdc0d7-e959-5d7e-b019-837893ee0a0d

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_lev_imp_eq_one_of_smul_eq_qmPeriodMap_of_nrd_eq
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem TransRead.qmPeriodMap_injective {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) : Function.Injective (qmPeriodMap ι τ) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  set z := x - y with hz
  apply hι
  rw [map_zero]
  have h0 : ((ι z).map (algebraMap ℝ ℂ)).mulVec ![(τ : ℂ), 1] = 0 := by
    rw [← qmPeriodMap_apply]; exact hxy
  have hτ : (τ : ℂ).im ≠ 0 := ne_of_gt τ.im_pos
  have row : ∀ i : Fin 2, ι z i 0 = 0 ∧ ι z i 1 = 0 := by
    intro i
    have hi := congrFun h0 i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at hi

    have him := congrArg Complex.im hi
    have hre := congrArg Complex.re hi
    simp at him hre
    have h00 : ι z i 0 = 0 := by
      rcases him with h | h
      · exact h
      · exact absurd h hτ
    refine ⟨h00, ?_⟩
    simpa [h00] using hre
  ext i j
  fin_cases j
  · exact (row i).1
  · exact (row i).2

open TransRead in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) (hqq' : q' ≠ q)
    {N : ℕ} [NeZero N] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)

    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnrd : nrd t = (ℓ : ℚ))
    (hlev : ∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x)

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

    (lattLev : FakeEllipticCurve Λ N ℂ → Submodule ℤ (Fin 2 → ℂ))
    (hLev : ∀ E : FakeEllipticCurve Λ N ℂ,
      (∀ v : Fin 2 → ℂ, v ∈ lattLev E ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ lattLev E ∧
      (∀ x ∈ Λ, ∀ v ∈ lattLev E, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ lattLev E) ∧
      (∀ v ∈ lattLev E, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex (lattLev E).toAddSubgroup = N ^ 2)

    (m : ℕ) (hm : m ≠ 0) (hℓm : ℓ ∣ m) (E : FakeEllipticCurve Λ N ℂ) (P : E.FullLevel m)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hlatt : c • latt E = qmPeriodLattice ι Λ τ)
    (hlattLev : c • lattLev E = qmPeriodLattice ι J' τ)
    (w : ℍ[ℚ, a, b]) (vP : Fin 2 → ℂ) (hvP : e E P.P = (vP : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))
    (hcvP : c • vP = ((m : ℂ)⁻¹) • qmPeriodMap ι τ w)
    (L₀ : Submodule ℤ ℍ[ℚ, a, b])
    (hLT : ∀ y : ℍ[ℚ, a, b], (∃ z ∈ Λ, z * t = y) ↔ ∃ z ∈ Λ, ∃ x ∈ Λ, x ∈ L₀ ∧ (ℓ : ℚ) • z + x * w = y) :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : ℂ →+* k) (x : ↥Λ), (x : ℍ[ℚ, a, b]) ∈ L₀ →
      FactorsThrough E.lev
        (pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) →
      pushPt (E.act x) (E.act_over x)
          (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) = E.L.one (geomPoint k sk) := by
  classical
  intro k _ _ sk x hxL₀ hfac
  have hO : IsOrder Λ := hΛ.isOrder
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hΦinj := TransRead.qmPeriodMap_injective ι hι τ
  have hℓsmul : ∀ v : Fin 2 → ℂ, (ℓ : ℂ) • v = (ℓ : ℤ) • v := fun v => by
    rw [Nat.cast_smul_eq_nsmul, natCast_zsmul]

  let M' : Submodule ℤ (Fin 2 → ℂ) := (Λ.map (LinearMap.mulRight ℤ t)).map (qmPeriodMap ι τ)
  have hM'mem : ∀ v, v ∈ M' ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v := by
    intro v
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * t, ⟨y, hy, rfl⟩, rfl⟩

  have hlevΦ : ∀ v : Fin 2 → ℂ,
      (∃ w' ∈ qmPeriodLattice ι J' τ, ∃ m' ∈ M', (ℓ : ℂ) • w' + m' = v) ↔ ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v := by
    intro v
    constructor
    · rintro ⟨w', hw', m', hm', rfl⟩
      obtain ⟨j, hj, rfl⟩ := (mem_qmPeriodLattice_iff ι J' τ w').mp hw'
      obtain ⟨y, hy, rfl⟩ := (hM'mem m').mp hm'
      obtain ⟨j₂, hj₂, hj₂eq⟩ := (hlev ((ℓ : ℤ) • j + y * t)).mp ⟨j, hj, y, hy, rfl⟩
      refine ⟨j₂, hj₂, ?_⟩
      rw [hj₂eq, map_add, map_zsmul, hℓsmul]
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨j₁, hj₁, y, hy, heq⟩ := (hlev (j * t)).mpr ⟨j, hj, rfl⟩
      refine ⟨qmPeriodMap ι τ j₁, (mem_qmPeriodLattice_iff ι J' τ _).mpr ⟨j₁, hj₁, rfl⟩,
        qmPeriodMap ι τ (y * t), (hM'mem _).mpr ⟨y, hy, rfl⟩, ?_⟩
      rw [← heq, map_add, map_zsmul, hℓsmul]

  obtain ⟨h7i, -, -⟩ :=
    QuaternionAlgebra.IsEichlerOrder.forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
      hqN hq'N hqq' hB Λ hΛ hN R hR hRΛ ι hι J' hJ' τ ℓ hℓ hℓq hℓq'
  obtain ⟨hM'1, hM'2, hM'3, hM'4, hM'5⟩ := (h7i M').mpr ⟨t, ht, hnrd, fun v => hM'mem v, hlevΦ⟩

  have htrans : ∀ v ∈ lattLev E, ((ℓ : ℂ) * c) • v ∈ M' → v ∈ latt E := by
    intro v hv hvM
    have hcv : c • v ∈ qmPeriodLattice ι J' τ := by
      rw [← hlattLev]; exact Submodule.smul_mem_pointwise_smul _ _ _ hv
    have h1 := hM'5 (c • v) hcv (by rw [smul_smul]; exact hvM)
    rw [← hlatt] at h1
    obtain ⟨v', hv', hcv'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    rw [← smul_right_injective _ hc hcv']
    exact hv'

  obtain ⟨K', hK'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_extraLevel_forall_factorsThrough_iff_smul_mem_of_transversal_of_pointEquiv
      hB Λ hΛ ι latt e hL1 hE1 hE2 lattLev hLev ℓ hℓ E τ c hc hlatt M' ⟨hM'1, hM'2, hM'3, hM'4, htrans⟩

  have he_one : e E (E.L.one (𝟙 _)) = 0 := by
    have h := hE1 E (E.L.one (𝟙 _)) (E.L.one (𝟙 _))
    rw [E.L.one_mul] at h
    have := congrArg (fun z => z - e E (E.L.one (𝟙 _))) h
    simpa using this.symm
  have he_nsmul : ∀ n : ℕ, e E (nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) n P.P) =
      ((n • vP : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := by
    intro n
    induction n with
    | zero =>
      show e E (E.L.one _) = _
      rw [he_one, zero_smul, QuotientAddGroup.mk_zero]
    | succ n ih =>
      show e E (E.L.mul _ (nsmulPt E.L _ n P.P) P.P) = _
      rw [hE1, ih, hvP, succ_nsmul, QuotientAddGroup.mk_add]
  let Q₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f :=
    pushPt (E.act x) (E.act_over x) (nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) (m / ℓ) P.P)
  have heQ₁ : e E Q₁ = ((((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP) : Fin 2 → ℂ) :
      (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) :=
    hE2 E x _ _ (he_nsmul (m / ℓ))
  have hcomp : (c * (ℓ : ℂ)) • ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP) =
      qmPeriodMap ι τ ((x : ℍ[ℚ, a, b]) * w) := by
    have hw : (c * (ℓ : ℂ)) • ((m / ℓ : ℕ) • vP) = qmPeriodMap ι τ w := by
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      have : c * (ℓ : ℂ) * ((m / ℓ : ℕ) : ℂ) = (m : ℂ) * c := by
        rw [mul_assoc, ← Nat.cast_mul, Nat.mul_div_cancel' hℓm, mul_comm]
      rw [this, mul_smul, hcvP, smul_smul, mul_inv_cancel₀ hm0, one_smul]
    rw [← Matrix.mulVec_smul, hw, qmPeriodMap_apply, qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]

  obtain ⟨z, hz, hzt⟩ := (hLT ((x : ℍ[ℚ, a, b]) * w)).mpr ⟨0, Λ.zero_mem, x, x.2, hxL₀, by rw [smul_zero, zero_add]⟩
  have hQ₁K : FactorsThrough K'.levK Q₁ := by
    have h1 := (hK' (((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec ((m / ℓ : ℕ) • vP))).mpr
      (by rw [hcomp, hM'mem]; exact ⟨z, hz, by rw [hzt]⟩)
    rwa [← heQ₁, Equiv.symm_apply_apply] at h1

  have hσ : geomPoint k sk ≫ 𝟙 (Spec (CommRingCat.of ℂ)) = geomPoint k sk := Category.comp_id _
  let H : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f → SchemeHomOver (geomPoint k sk) E.f :=
    fun Q => schemeHomOverComp (geomPoint k sk) hσ Q
  have H_coe : ∀ Q, (H Q).1 = geomPoint k sk ≫ Q.1 := fun _ => rfl
  have H_mul : ∀ P' Q', H (E.L.mul _ P' Q') = E.L.mul _ (H P') (H Q') := fun P' Q' => E.L.mul_natural _ _ _ hσ P' Q'
  have H_one : H (E.L.one _) = E.L.one _ := E.L.one_natural _ _ _ hσ
  have H_nsmul : ∀ (j : ℕ) Q', H (nsmulPt E.L _ j Q') = nsmulPt E.L _ j (H Q') := by
    intro j Q'
    induction j with
    | zero => exact H_one
    | succ j ih =>
      show H (E.L.mul _ (nsmulPt E.L _ j Q') Q') = E.L.mul _ (nsmulPt E.L _ j (H Q')) (H Q')
      rw [H_mul, ih]
  have H_act : ∀ (y : ↥Λ) Q', H (pushPt (E.act y) (E.act_over y) Q') = pushPt (E.act y) (E.act_over y) (H Q') := by
    intro y Q'
    apply Subtype.ext
    simp only [H_coe, pushPt, mapPt_coe, Category.assoc]
  have key : H Q₁ = pushPt (E.act x) (E.act_over x)
      (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk)) := by
    show H (pushPt (E.act x) (E.act_over x) (nsmulPt E.L (𝟙 (Spec (CommRingCat.of ℂ))) (m / ℓ) P.P)) = _
    rw [H_act, H_nsmul]
    rfl
  have hfacK : FactorsThrough K'.levK (pushPt (E.act x) (E.act_over x)
      (nsmulPt E.L (geomPoint k sk) (m / ℓ) (FakeEllipticCurve.sectionAt P.P k sk))) := by
    rw [← key]
    obtain ⟨P₀, hP₀⟩ := hQ₁K
    exact ⟨geomPoint k sk ≫ P₀, by rw [Category.assoc, hP₀, H_coe]⟩
  exact K'.levK_disjoint (geomPoint k sk) _ hfacK hfac

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_lev_imp_eq_one_of_smul_eq_qmPeriodMap_of_nrd_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_forall_factorsThrough_lev_imp_eq_one_of_smul_eq_qmPeriodMap_of_nrd_eq (solution)
