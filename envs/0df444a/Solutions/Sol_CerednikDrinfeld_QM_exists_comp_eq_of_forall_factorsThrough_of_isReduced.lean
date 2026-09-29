-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_comp_eq_of_forall_factorsThrough_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/49fce61d-6773-56e4-9c67-b5f496655576

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open CerednikDrinfeld CerednikDrinfeld.QM

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {Z A C : Scheme.{u}}
    (g : Z ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] [IsReduced Z]
    (f : A ⟶ Spec (CommRingCat.of k)) (i : C ⟶ A) [IsClosedImmersion i]
    (φ : Z ⟶ A) (hφ : φ ≫ f = g)
    (h : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g, FactorsThrough i (mapPt φ hφ z)) :
    ∃ φ₀ : Z ⟶ C, φ₀ ≫ i = φ := by
  have hJ : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace g

  have hcl : closedPoints Z ⊆ (φ : Z → A) ⁻¹' (i.ker.support : Set A) := by
    intro x hx
    have hx0 := h ⟨pointOfClosedPoint g x hx, pointOfClosedPoint_comp g x hx⟩
    unfold FactorsThrough at hx0
    obtain ⟨P₀, hP₀⟩ := hx0
    rw [mapPt_coe] at hP₀
    have hx' : φ x = i (P₀ (IsLocalRing.closedPoint k)) := by
      rw [← Scheme.Hom.comp_apply, hP₀, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
    show φ x ∈ (i.ker.support : Set A)
    rw [hx']
    exact i.range_subset_ker_support ⟨_, rfl⟩

  have hall : (φ : Z → A) ⁻¹' (i.ker.support : Set A) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints (X := Z)]
    exact (i.ker.support.isClosed.preimage φ.continuous).closure_subset_iff.mpr hcl

  have key : i.ker ≤ φ.ker := by
    rw [← Scheme.IdealSheafData.map_bot φ, Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff,
      ← Scheme.IdealSheafData.support_eq_top_iff, ← SetLike.coe_set_eq,
      Scheme.IdealSheafData.support_comap]
    simpa using hall
  exact ⟨IsClosedImmersion.lift i φ key, IsClosedImmersion.lift_fac i φ key⟩

end S_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_comp_eq_of_forall_factorsThrough_of_isReduced (solution)
