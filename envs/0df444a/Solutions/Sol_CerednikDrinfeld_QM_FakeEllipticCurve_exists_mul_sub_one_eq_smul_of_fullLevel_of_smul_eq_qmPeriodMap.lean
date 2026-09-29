-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b9c51482-be45-5c9e-a439-2c36e2f65f47

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

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

theorem X0Unit.qmPeriodMap_injective {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
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

open X0Unit in
theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    {N : ℕ}

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
    (m : ℕ) [NeZero m] (u : FakeEllipticCurve.WithFullLevel Λ N m ℂ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hlatt : c • latt u.1 = qmPeriodLattice ι Λ τ)
    (x₀ : ↥Λ) (v : Fin 2 → ℂ) (hv : e u.1 u.2.P = (v : (Fin 2 → ℂ) ⧸ (latt u.1).toAddSubgroup))
    (hx₀ : c • v = ((m : ℂ)⁻¹) • qmPeriodMap ι τ (x₀ : ℍ[ℚ, a, b])) :
    ∃ y : ↥Λ,
      (∃ z : ↥Λ, (x₀ : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (z : ℍ[ℚ, a, b])) ∧
      (∃ z : ↥Λ, (y : ℍ[ℚ, a, b]) * (x₀ : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (z : ℍ[ℚ, a, b])) := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder

  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hgid : geomPoint (S := ℂ) ℂ (RingHom.id ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
    unfold geomPoint
    have : CommRingCat.ofHom (RingHom.id ℂ) = 𝟙 (CommRingCat.of ℂ) := rfl
    rw [this, Spec.map_id]
  have he_one : e u.1 (u.1.L.one (𝟙 _)) = 0 := by
    have h := hE1 u.1 (u.1.L.one (𝟙 _)) (u.1.L.one (𝟙 _))
    rw [u.1.L.one_mul] at h
    have := congrArg (fun z => z - e u.1 (u.1.L.one (𝟙 _))) h
    simpa using this.symm

  have hann : ∀ x : ↥Λ, pushPt (u.1.act x) (u.1.act_over x) u.2.P = u.1.L.one (𝟙 _) →
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro x h
    apply (u.2.annihilator ℂ (RingHom.id ℂ) x).mp
    apply Subtype.ext
    have h1 : u.2.P.1 ≫ u.1.act x = (u.1.L.one (𝟙 _)).1 := congrArg Subtype.val h
    have h2 := congrArg Subtype.val (u.1.L.one_natural (𝟙 (Spec (CommRingCat.of ℂ))) (geomPoint ℂ (RingHom.id ℂ))
      (geomPoint ℂ (RingHom.id ℂ)) (Category.comp_id _))

    rw [schemeHomOverComp_coe] at h2
    show (geomPoint ℂ (RingHom.id ℂ) ≫ u.2.P.1) ≫ u.1.act x = (u.1.L.one (geomPoint ℂ (RingHom.id ℂ))).1
    rw [Category.assoc, h1, h2]

  have hmem : ∀ x : ↥Λ, ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v ∈ latt u.1 →
      pushPt (u.1.act x) (u.1.act_over x) u.2.P = u.1.L.one (𝟙 _) := by
    intro x hx
    apply (e u.1).injective
    rw [hE2 u.1 x u.2.P v hv, he_one]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hx

  have hΦmul : ∀ x : ↥Λ, ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec (qmPeriodMap ι τ (x₀ : ℍ[ℚ, a, b])) =
      qmPeriodMap ι τ ((x : ℍ[ℚ, a, b]) * (x₀ : ℍ[ℚ, a, b])) := by
    intro x
    rw [qmPeriodMap_apply, qmPeriodMap_apply, map_mul, Matrix.map_mul, Matrix.mulVec_mulVec]
  have hkey : ∀ x : ↥Λ, (∃ z : ↥Λ, (x : ℍ[ℚ, a, b]) * (x₀ : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b])) →
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b]) := by
    intro x ⟨z, hz⟩
    apply hann x
    apply hmem x

    have hcw : c • (((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v) ∈ qmPeriodLattice ι Λ τ := by
      rw [← Matrix.mulVec_smul, hx₀, Matrix.mulVec_smul, hΦmul, hz, mem_qmPeriodLattice_iff]
      refine ⟨(z : ℍ[ℚ, a, b]), z.2, ?_⟩
      rw [Nat.cast_smul_eq_nsmul ℚ, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hm0, one_smul]
    rw [← hlatt] at hcw
    obtain ⟨w, hw, hcw'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hcw
    have : w = ((ι (x : ℍ[ℚ, a, b])).map (algebraMap ℝ ℂ)).mulVec v := smul_right_injective _ hc hcw'
    rw [← this]; exact hw

  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hO.fg
  let R : ↥Λ →ₗ[ℤ] ↥Λ :=
    { toFun := fun l => ⟨(l : ℍ[ℚ, a, b]) * (x₀ : ℍ[ℚ, a, b]), hO.mul_mem l.2 x₀.2⟩
      map_add' := fun l l' => Subtype.ext (by
        show ((l + l' : ↥Λ) : ℍ[ℚ, a, b]) * x₀ = (l : ℍ[ℚ, a, b]) * x₀ + (l' : ℍ[ℚ, a, b]) * x₀
        rw [Submodule.coe_add, add_mul])
      map_smul' := fun n l => Subtype.ext (by
        show ((n • l : ↥Λ) : ℍ[ℚ, a, b]) * x₀ = n • ((l : ℍ[ℚ, a, b]) * x₀)
        rw [Submodule.coe_smul, smul_mul_assoc]) }
  let S : Submodule ℤ ↥Λ := LinearMap.range ((m : ℤ) • (LinearMap.id : ↥Λ →ₗ[ℤ] ↥Λ))
  have hSmem : ∀ l : ↥Λ, l ∈ S ↔ ∃ z : ↥Λ, (l : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b]) := by
    intro l
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have := congrArg (fun t : ↥Λ => (t : ℍ[ℚ, a, b])) hz
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul] at this
      rw [← this, ← Int.cast_smul_eq_zsmul ℚ]; norm_cast
    · rintro ⟨z, hz⟩
      refine ⟨z, Subtype.ext ?_⟩
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul]
      rw [hz, ← Int.cast_smul_eq_zsmul ℚ]; norm_cast
  have hRS : S ≤ S.comap R := by
    rintro l hl
    obtain ⟨z, hz⟩ := (hSmem l).mp hl
    show R l ∈ S
    rw [hSmem]
    exact ⟨⟨(z : ℍ[ℚ, a, b]) * x₀, hO.mul_mem z.2 x₀.2⟩, by
      show (l : ℍ[ℚ, a, b]) * x₀ = (m : ℚ) • ((z : ℍ[ℚ, a, b]) * x₀); rw [hz, smul_mul_assoc]⟩
  let Rbar : (↥Λ ⧸ S) →ₗ[ℤ] (↥Λ ⧸ S) := S.mapQ S R hRS
  have hRbar_inj : Function.Injective Rbar := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective S q
    rw [LinearMap.mem_ker] at hq
    change S.mapQ S R hRS (Submodule.Quotient.mk l) = 0 at hq
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hSmem] at hq
    rw [Submodule.Quotient.mk_eq_zero, hSmem]
    exact hkey l hq

  haveI hfinQ : Module.Finite ℤ (↥Λ ⧸ S) := Module.Finite.quotient ℤ S
  haveI : AddGroup.FG (↥Λ ⧸ S) := Module.Finite.iff_addGroup_fg.mp hfinQ
  haveI : Finite (↥Λ ⧸ S) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective S q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), ?_⟩
    rw [show (m • Submodule.Quotient.mk l : ↥Λ ⧸ S) = S.mkQ (m • l) from (map_nsmul S.mkQ m l).symm,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨l, by show ((m : ℤ) • (LinearMap.id (R := ℤ) (M := ↥Λ)) l) = m • l; rw [LinearMap.id_apply, natCast_zsmul]⟩
  have hRbar_surj : Function.Surjective Rbar := Finite.surjective_of_injective hRbar_inj

  let one' : ↥Λ := ⟨1, hO.one_mem⟩
  obtain ⟨qy, hqy⟩ := hRbar_surj (Submodule.Quotient.mk one')
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S qy
  change S.mapQ S R hRS (Submodule.Quotient.mk y) = Submodule.Quotient.mk one' at hqy
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq, hSmem] at hqy
  obtain ⟨z₁, hz₁⟩ := hqy
  have hyx : (y : ℍ[ℚ, a, b]) * x₀ - 1 = (m : ℚ) • (z₁ : ℍ[ℚ, a, b]) := by
    simp at hz₁
    exact hz₁

  let Lx : ↥Λ →ₗ[ℤ] ↥Λ :=
    { toFun := fun l => ⟨(x₀ : ℍ[ℚ, a, b]) * (l : ℍ[ℚ, a, b]), hO.mul_mem x₀.2 l.2⟩
      map_add' := fun l l' => Subtype.ext (by
        show (x₀ : ℍ[ℚ, a, b]) * ((l + l' : ↥Λ) : ℍ[ℚ, a, b]) = (x₀ : ℍ[ℚ, a, b]) * l + (x₀ : ℍ[ℚ, a, b]) * l'
        rw [Submodule.coe_add, mul_add])
      map_smul' := fun n l => Subtype.ext (by
        show (x₀ : ℍ[ℚ, a, b]) * ((n • l : ↥Λ) : ℍ[ℚ, a, b]) = n • ((x₀ : ℍ[ℚ, a, b]) * l)
        rw [Submodule.coe_smul, mul_smul_comm]) }
  have hLS : S ≤ S.comap Lx := by
    rintro l hl
    obtain ⟨z, hz⟩ := (hSmem l).mp hl
    show Lx l ∈ S
    rw [hSmem]
    exact ⟨⟨(x₀ : ℍ[ℚ, a, b]) * z, hO.mul_mem x₀.2 z.2⟩, by
      show (x₀ : ℍ[ℚ, a, b]) * l = (m : ℚ) • ((x₀ : ℍ[ℚ, a, b]) * z); rw [hz, mul_smul_comm]⟩
  let Lbar : (↥Λ ⧸ S) →ₗ[ℤ] (↥Λ ⧸ S) := S.mapQ S Lx hLS
  have hLbar_inj : Function.Injective Lbar := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective S q
    rw [LinearMap.mem_ker] at hq
    change S.mapQ S Lx hLS (Submodule.Quotient.mk l) = 0 at hq
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hSmem] at hq
    rw [Submodule.Quotient.mk_eq_zero, hSmem]
    obtain ⟨z, hz⟩ := hq

    refine ⟨⟨(y : ℍ[ℚ, a, b]) * z - (z₁ : ℍ[ℚ, a, b]) * l, Λ.sub_mem (hO.mul_mem y.2 z.2) (hO.mul_mem z₁.2 l.2)⟩, ?_⟩
    show (l : ℍ[ℚ, a, b]) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * z - (z₁ : ℍ[ℚ, a, b]) * l)
    have e1 : (y : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * l) = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * z) := by
      rw [show (x₀ : ℍ[ℚ, a, b]) * (l : ℍ[ℚ, a, b]) = (m : ℚ) • (z : ℍ[ℚ, a, b]) from hz, mul_smul_comm]
    have e2 : ((y : ℍ[ℚ, a, b]) * x₀ - 1) * l = (m : ℚ) • ((z₁ : ℍ[ℚ, a, b]) * l) := by
      rw [hyx, smul_mul_assoc]
    calc (l : ℍ[ℚ, a, b]) = (y : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * l) - ((y : ℍ[ℚ, a, b]) * x₀ - 1) * l := by
          rw [sub_mul, one_mul, mul_assoc]; abel
      _ = (m : ℚ) • ((y : ℍ[ℚ, a, b]) * z - (z₁ : ℍ[ℚ, a, b]) * l) := by rw [e1, e2, smul_sub]
  have hLbar_surj : Function.Surjective Lbar := Finite.surjective_of_injective hLbar_inj
  obtain ⟨qy', hqy'⟩ := hLbar_surj (Submodule.Quotient.mk one')
  obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective S qy'
  change S.mapQ S Lx hLS (Submodule.Quotient.mk y') = Submodule.Quotient.mk one' at hqy'
  rw [Submodule.mapQ_apply, Submodule.Quotient.eq, hSmem] at hqy'
  obtain ⟨z₂, hz₂⟩ := hqy'
  have hxy' : (x₀ : ℍ[ℚ, a, b]) * y' - 1 = (m : ℚ) • (z₂ : ℍ[ℚ, a, b]) := by
    simp at hz₂
    exact hz₂

  refine ⟨y, ⟨⟨(x₀ : ℍ[ℚ, a, b]) * ((z₁ : ℍ[ℚ, a, b]) * y' - (y : ℍ[ℚ, a, b]) * z₂) + z₂,
    Λ.add_mem (hO.mul_mem x₀.2 (Λ.sub_mem (hO.mul_mem z₁.2 y'.2) (hO.mul_mem y.2 z₂.2))) z₂.2⟩, ?_⟩, ⟨z₁, hyx⟩⟩
  show (x₀ : ℍ[ℚ, a, b]) * y - 1 = (m : ℚ) • ((x₀ : ℍ[ℚ, a, b]) * ((z₁ : ℍ[ℚ, a, b]) * y' - (y : ℍ[ℚ, a, b]) * z₂) + z₂)
  have e3 : (y : ℍ[ℚ, a, b]) - y' = ((y : ℍ[ℚ, a, b]) * x₀ - 1) * y' - (y : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * y' - 1) := by
    noncomm_ring
  calc (x₀ : ℍ[ℚ, a, b]) * y - 1 = (x₀ : ℍ[ℚ, a, b]) * ((y : ℍ[ℚ, a, b]) - y') + ((x₀ : ℍ[ℚ, a, b]) * y' - 1) := by noncomm_ring
    _ = (x₀ : ℍ[ℚ, a, b]) * (((y : ℍ[ℚ, a, b]) * x₀ - 1) * y' - (y : ℍ[ℚ, a, b]) * ((x₀ : ℍ[ℚ, a, b]) * y' - 1)) +
          ((x₀ : ℍ[ℚ, a, b]) * y' - 1) := by rw [← e3]
    _ = (m : ℚ) • ((x₀ : ℍ[ℚ, a, b]) * ((z₁ : ℍ[ℚ, a, b]) * y' - (y : ℍ[ℚ, a, b]) * z₂) + z₂) := by
          rw [hyx, hxy', smul_mul_assoc, mul_smul_comm, ← smul_sub, mul_smul_comm, ← smul_add]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_mul_sub_one_eq_smul_of_fullLevel_of_smul_eq_qmPeriodMap (solution)
