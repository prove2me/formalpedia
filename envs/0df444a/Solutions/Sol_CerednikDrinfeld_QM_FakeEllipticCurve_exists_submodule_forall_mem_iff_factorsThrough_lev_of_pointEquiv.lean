-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/466a6c38-0dda-5643-992f-ff2c1cef8c8e

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

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
    (E : FakeEllipticCurve Λ N ℂ) :
    ∃ ME : Submodule ℤ (Fin 2 → ℂ),
      (∀ v : Fin 2 → ℂ, v ∈ ME ↔
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
          FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) ∧
      latt E ≤ ME ∧
      (∀ x ∈ Λ, ∀ v ∈ ME, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ ME) ∧
      (∀ v ∈ ME, (N : ℤ) • v ∈ latt E) ∧
      (latt E).toAddSubgroup.relIndex ME.toAddSubgroup = N ^ 2 := by
  classical

  have he_one : e E (E.L.one (𝟙 _)) = 0 := by
    have h1 := hE1 E (E.L.one (𝟙 _)) (E.L.one (𝟙 _))
    rw [E.L.one_mul] at h1
    simpa using h1
  have he_inv : ∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f, e E (E.L.inv (𝟙 _) P) = - e E P := by
    intro P
    have h1 := hE1 E P (E.L.inv (𝟙 _) P)
    rw [E.L.mul_inv_cancel, he_one] at h1
    exact (neg_eq_of_add_eq_zero_right h1.symm).symm
  have he_nsmul : ∀ (n : ℕ) (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f),
      e E (nsmulPt E.L (𝟙 _) n P) = n • e E P := by
    intro n P
    induction n with
    | zero => simp [nsmulPt, he_one]
    | succ n ih => rw [nsmulPt, hE1, ih, succ_nsmul]

  let M0 : AddSubgroup (Fin 2 → ℂ) :=
    { carrier := {v | ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
        FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)}
      zero_mem' := ⟨E.L.one _, E.lev_one _, by rw [he_one, QuotientAddGroup.mk_zero]⟩
      add_mem' := by
        rintro v w ⟨P, hP, hPv⟩ ⟨Q, hQ, hQw⟩
        exact ⟨E.L.mul _ P Q, (E.lev_sub _ P Q hP hQ).1, by rw [hE1, hPv, hQw, QuotientAddGroup.mk_add]⟩
      neg_mem' := by
        rintro v ⟨P, hP, hPv⟩
        exact ⟨E.L.inv _ P, (E.lev_sub _ P P hP hP).2, by rw [he_inv, hPv, QuotientAddGroup.mk_neg]⟩ }
  have hmem : ∀ v : Fin 2 → ℂ, v ∈ M0 ↔ ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f,
      FactorsThrough E.lev P ∧ e E P = (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := fun v => Iff.rfl
  refine ⟨AddSubgroup.toIntSubmodule M0, fun v => hmem v, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    refine (hmem v).mpr ⟨E.L.one _, E.lev_one _, ?_⟩
    rw [he_one]
    exact ((QuotientAddGroup.eq_zero_iff v).mpr hv).symm
  ·
    intro x hx v hv
    obtain ⟨P, hP, hPv⟩ := (hmem v).mp hv
    exact (hmem _).mpr ⟨pushPt (E.act ⟨x, hx⟩) (E.act_over ⟨x, hx⟩) P, E.lev_stable ⟨x, hx⟩ _ P hP,
      hE2 E ⟨x, hx⟩ P v hPv⟩
  ·
    intro v hv
    obtain ⟨P, hP, hPv⟩ := (hmem v).mp hv
    have h1 := he_nsmul N P
    rw [E.lev_torsion _ P hP, he_one, hPv] at h1
    show (N : ℤ) • v ∈ (latt E).toAddSubgroup
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul, natCast_zsmul]
    exact h1.symm
  ·
    show (latt E).toAddSubgroup.relIndex M0 = N ^ 2
    let φ : ↥M0 →+ (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup :=
      (QuotientAddGroup.mk' (latt E).toAddSubgroup).comp M0.subtype
    have hφ : ∀ v : ↥M0, φ v = ((v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) := fun v => rfl
    have hker : φ.ker = (latt E).toAddSubgroup.addSubgroupOf M0 := by
      ext v
      rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, hφ, QuotientAddGroup.eq_zero_iff]
    have hrange : ∀ y : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup,
        y ∈ φ.range ↔ y ∈ e E '' {P | FactorsThrough E.lev P} := by
      intro y
      constructor
      · rintro ⟨⟨v, P, hP, hPv⟩, rfl⟩
        exact ⟨P, hP, hPv⟩
      · rintro ⟨P, hP, rfl⟩
        obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective (e E P)
        exact ⟨⟨v, P, hP, hv.symm⟩, hv⟩
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker, Nat.card_congr (Equiv.subtypeEquivRight hrange)]
    rw [Nat.card_image_of_injective (e E).injective]

    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    obtain ⟨eN, -⟩ := E.lev_fibre ℂ (RingHom.id ℂ) hN
    have hg : geomPoint ℂ (RingHom.id ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
      simp [geomPoint]
    have hc := Nat.card_congr eN
    rw [hg] at hc
    show Nat.card {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f // FactorsThrough E.lev P} = N ^ 2
    rw [← hc, Nat.card_prod, Nat.card_zmod, pow_two]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_submodule_forall_mem_iff_factorsThrough_lev_of_pointEquiv (solution)
