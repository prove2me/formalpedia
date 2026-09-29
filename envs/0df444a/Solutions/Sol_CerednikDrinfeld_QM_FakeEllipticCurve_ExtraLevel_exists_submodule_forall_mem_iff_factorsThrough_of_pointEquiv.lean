-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e29748d3-aaea-5a6a-9a56-c2009d44e126

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

import Theorems.Thm_QuaternionAlgebra_IsOrder_relIndex_span_smul_eq_pow_four
import Theorems.Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
import Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_isUnit_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField MatrixGroups Topology Pointwise

namespace F3a13

variable {a b : ℚ}

theorem ne_zero_and_ne_zero {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hB : IsIndefiniteRamifiedExactlyAt a b q q') :
    a ≠ 0 ∧ b ≠ 0 := by
  have key : ∀ y : ℍ[ℚ, a, b], y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.isUnit_of_ne_zero hB y hy
    apply hy
    calc (u : ℍ[ℚ, a, b]) = ↑u⁻¹ * (↑u * ↑u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hyy, mul_zero]
  refine ⟨fun h0 => key ⟨0, 1, 0, 0⟩ ?_ ?_, fun h0 => key ⟨0, 0, 1, 0⟩ ?_ ?_⟩
  · intro h; simpa using congrArg QuaternionAlgebra.imI h
  · ext <;> simp [h0]
  · intro h; simpa using congrArg QuaternionAlgebra.imJ h
  · ext <;> simp [h0]

theorem mem_span_smul_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (m : ℕ) (x : ℍ[ℚ, a, b]) :
    x ∈ Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (m : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b])) ↔
      ∃ y ∈ Λ, x = (m : ℤ) • y := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx; obtain ⟨v, hv, rfl⟩ := hy
      exact ⟨u + v, Λ.add_mem hu hv, by simp [smul_add]⟩
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      exact ⟨c • u, Λ.smul_mem c hu, by rw [smul_comm]⟩
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

section Lattices

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem smul_toAddSubgroup (c : ℂ) (A : Submodule ℤ V) :
    (c • A).toAddSubgroup = A.toAddSubgroup.map (DistribSMul.toAddMonoidHom V c) := by
  ext v
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists, AddSubgroup.mem_map,
    DistribSMul.toAddMonoidHom_apply]

theorem relIndex_smul {c : ℂ} (hc : c ≠ 0) (A B : Submodule ℤ V) :
    (c • A).toAddSubgroup.relIndex (c • B).toAddSubgroup = A.toAddSubgroup.relIndex B.toAddSubgroup := by
  rw [smul_toAddSubgroup, smul_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (smul_right_injective V hc)

theorem smul_mono {c : ℂ} {A B : Submodule ℤ V} (h : A ≤ B) : c • A ≤ c • B := by
  intro v hv
  rw [Submodule.mem_smul_pointwise_iff_exists] at hv ⊢
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨w, h hw, rfl⟩

end Lattices

end F3a13

open F3a13 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)

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
    (ℓ : ℕ) (hℓ : ℓ.Prime) (E : FakeEllipticCurve Λ 1 ℂ) (K : E.ExtraLevel ℓ)
    (τ : UpperHalfPlane) (c : ℂ) (hc : c ≠ 0) (hcL : c • latt E = qmPeriodLattice ι Λ τ) :
    ∃ LK : Submodule ℤ (Fin 2 → ℂ),
      (∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup))) ∧
      latt E ≤ LK ∧
      (c * ℓ) • LK ≤ qmPeriodLattice ι Λ τ ∧
      (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ (c * ℓ) • LK) ∧
      (∀ y ∈ Λ, ∀ v ∈ (c * ℓ) • LK, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ (c * ℓ) • LK) ∧
      ((c * ℓ) • LK).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 := by
  classical
  obtain ⟨ha, hb⟩ := ne_zero_and_ne_zero hB
  have hO : IsOrder Λ := hΛ.isOrder
  have hℓC : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hcℓ : (c * ℓ : ℂ) ≠ 0 := mul_ne_zero hc hℓC

  have e_one : e E (E.L.one (𝟙 _)) = 0 := by
    have h := hE1 E (E.L.one _) (E.L.one _)
    rw [E.L.one_mul] at h
    exact (add_left_cancel (h.symm.trans (add_zero _).symm))
  have e_inv : ∀ P, e E (E.L.inv (𝟙 _) P) = - e E P := fun P => by
    have h := hE1 E (E.L.inv _ P) P
    rw [E.L.inv_mul_cancel, e_one] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  have e_nsmul : ∀ (n : ℕ) P, e E (nsmulPt E.L (𝟙 _) n P) = n • e E P := by
    intro n P
    induction n with
    | zero => simp only [nsmulPt, zero_smul]; exact e_one
    | succ n ih => simp only [nsmulPt]; rw [hE1, ih, succ_nsmul]
  have es_add : ∀ y y', (e E).symm (y + y') = E.L.mul (𝟙 _) ((e E).symm y) ((e E).symm y') := fun y y' => by
    apply (e E).injective; rw [hE1, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have es_zero : (e E).symm 0 = E.L.one (𝟙 _) := by
    apply (e E).injective; rw [e_one, Equiv.apply_symm_apply]
  have es_neg : ∀ y, (e E).symm (-y) = E.L.inv (𝟙 _) ((e E).symm y) := fun y => by
    apply (e E).injective; rw [e_inv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

  let KQ : AddSubgroup ((Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) :=
    { carrier := {y | FactorsThrough K.levK ((e E).symm y)}
      add_mem' := fun {y y'} hy hy' => by
        simp only [Set.mem_setOf_eq] at hy hy' ⊢
        rw [es_add]; exact (K.levK_sub _ _ _ hy hy').1
      zero_mem' := by simp only [Set.mem_setOf_eq]; rw [es_zero]; exact K.levK_one _
      neg_mem' := fun {y} hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        rw [es_neg]; exact (K.levK_sub _ _ _ hy hy).2 }
  let πq : (Fin 2 → ℂ) →+ (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup := QuotientAddGroup.mk' (latt E).toAddSubgroup
  let LKs : AddSubgroup (Fin 2 → ℂ) := KQ.comap πq
  let LK : Submodule ℤ (Fin 2 → ℂ) := AddSubgroup.toIntSubmodule LKs
  have memLK : ∀ v : Fin 2 → ℂ, v ∈ LK ↔ FactorsThrough K.levK ((e E).symm (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup)) :=
    fun v => Iff.rfl
  have hLKs : LK.toAddSubgroup = LKs := AddSubgroup.toIntSubmodule_toAddSubgroup LKs

  have hLle : latt E ≤ LK := by
    intro v hv
    rw [memLK]
    have : (v : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) = 0 := (QuotientAddGroup.eq_zero_iff v).2 hv
    rw [this, es_zero]; exact K.levK_one _

  have hℓLK : (ℓ : ℂ) • LK ≤ latt E := by
    intro v hv
    rw [Submodule.mem_smul_pointwise_iff_exists] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [memLK] at hw
    have ht := K.levK_torsion _ _ hw
    have h2 := congrArg (e E) ht
    rw [e_nsmul, e_one, Equiv.apply_symm_apply, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h2
    rw [Nat.cast_smul_eq_nsmul]; exact h2

  have hstab : ∀ y ∈ Λ, ∀ v ∈ LK, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ LK := by
    intro y hy v hv
    rw [memLK] at hv ⊢
    have h := hE2 E ⟨y, hy⟩ ((e E).symm v) v (Equiv.apply_symm_apply _ _)
    have : (e E).symm ((((ι y).map (algebraMap ℝ ℂ)).mulVec v : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (latt E).toAddSubgroup) =
        pushPt (E.act ⟨y, hy⟩) (E.act_over ⟨y, hy⟩) ((e E).symm v) := by
      apply (e E).injective; rw [Equiv.apply_symm_apply]; exact h.symm
    rw [this]; exact K.levK_stable ⟨y, hy⟩ _ _ hv

  have hcardKQ : Nat.card KQ = ℓ ^ 2 := by
    obtain ⟨eK, -⟩ := K.levK_fibre ℂ (RingHom.id ℂ) hℓC
    have hgp : geomPoint ℂ (RingHom.id ℂ) = 𝟙 (Spec (CommRingCat.of ℂ)) := by
      rw [geomPoint, CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [hgp] at eK
    have e2 : KQ ≃ {P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) E.f // FactorsThrough K.levK P} :=
      { toFun := fun y => ⟨(e E).symm y.1, y.2⟩
        invFun := fun P => ⟨e E P.1, by show FactorsThrough K.levK ((e E).symm (e E P.1)); rw [Equiv.symm_apply_apply]; exact P.2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun P => Subtype.ext (by simp) }
    rw [Nat.card_congr (e2.trans eK.symm), Nat.card_prod, Nat.card_zmod, pow_two]
  have hidx1 : (latt E).toAddSubgroup.relIndex LK.toAddSubgroup = ℓ ^ 2 := by
    rw [hLKs]
    have hker : (latt E).toAddSubgroup = (⊥ : AddSubgroup _).comap πq := by
      rw [AddMonoidHom.comap_bot, QuotientAddGroup.ker_mk']
    rw [hker, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective _),
      AddSubgroup.relIndex_bot_left, hcardKQ]

  set φ := qmPeriodMap ι τ with hφdef
  have hφ : Function.Injective φ :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ).1
  have hLτ : qmPeriodLattice ι Λ τ = Λ.map φ := rfl
  have hℓLτ : ((ℓ : ℂ) • qmPeriodLattice ι Λ τ).toAddSubgroup =
      ((Submodule.span ℤ ((fun y : ℍ[ℚ, a, b] => (ℓ : ℤ) • y) '' (Λ : Set ℍ[ℚ, a, b]))).toAddSubgroup).map
        (φ : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ)) := by
    ext v
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists, AddSubgroup.mem_map,
      LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hLτ, Submodule.mem_map] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      refine ⟨(ℓ : ℤ) • y, (mem_span_smul_iff ℓ _).2 ⟨y, hy, rfl⟩, ?_⟩
      rw [map_zsmul, natCast_zsmul, Nat.cast_smul_eq_nsmul]; rfl
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := (mem_span_smul_iff ℓ x).1 hx
      refine ⟨φ y, by rw [hLτ]; exact Submodule.mem_map_of_mem hy, ?_⟩
      rw [map_zsmul, natCast_zsmul, Nat.cast_smul_eq_nsmul]; rfl
  have hidx4τ : ((ℓ : ℂ) • qmPeriodLattice ι Λ τ).toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 4 := by
    rw [hℓLτ, hLτ, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective (f := (φ : ℍ[ℚ, a, b] →+ (Fin 2 → ℂ))) _ _ hφ]
    exact QuaternionAlgebra.IsOrder.relIndex_span_smul_eq_pow_four hO ℓ hℓ.pos
  have hidx4 : ((ℓ : ℂ) • latt E).toAddSubgroup.relIndex (latt E).toAddSubgroup = ℓ ^ 4 := by
    rw [← relIndex_smul hc, smul_comm, hcL, hidx4τ]

  have hidx2 : ((ℓ : ℂ) • LK).toAddSubgroup.relIndex (latt E).toAddSubgroup = ℓ ^ 2 := by
    have h1 : ((ℓ : ℂ) • latt E).toAddSubgroup.relIndex ((ℓ : ℂ) • LK).toAddSubgroup = ℓ ^ 2 := by
      rw [relIndex_smul hℓC, hidx1]
    have hle1 : ((ℓ : ℂ) • latt E).toAddSubgroup ≤ ((ℓ : ℂ) • LK).toAddSubgroup := fun v hv => smul_mono hLle hv
    have hle2 : ((ℓ : ℂ) • LK).toAddSubgroup ≤ (latt E).toAddSubgroup := fun v hv => hℓLK hv
    have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
    rw [h1, hidx4, show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring] at hmul
    exact mul_left_cancel₀ (pow_ne_zero 2 hℓ.ne_zero) hmul
  refine ⟨LK, memLK, hLle, ?_, ?_, ?_, ?_⟩
  ·
    rw [← hcL, mul_smul]
    exact smul_mono hℓLK
  ·
    intro v hv
    rw [← hcL, Submodule.mem_smul_pointwise_iff_exists] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [Submodule.mem_smul_pointwise_iff_exists]
    refine ⟨w, hLle hw, ?_⟩
    rw [mul_comm, mul_smul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  ·
    intro y hy v hv
    rw [Submodule.mem_smul_pointwise_iff_exists] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨_, hstab y hy w hw, by rw [Matrix.mulVec_smul]⟩
  ·
    rw [← hcL, mul_smul, relIndex_smul hc, hidx2]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_exists_submodule_forall_mem_iff_factorsThrough_of_pointEquiv (solution)
