-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_le_section_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/07ad1dfe-68e0-5411-930f-e52c2f362c50

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_section_comp_eq
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

open CategoryTheory.Limits in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (L : Type) [CommRing L] (R : Subalgebra ℤ L) (hR : R.FG) (ER : FakeEllipticCurve Λ N ↥R)
    (σ₁ σ₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥R))) ER.f)
    (h : Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ σ₁.1 = Spec.map (CommRingCat.ofHom R.val.toRingHom) ≫ σ₂.1)
    (s : Finset L) :
    ∃ (R' : Subalgebra ℤ L) (_ : R'.FG) (hRR' : R ≤ R') (_ : (↑s : Set L) ⊆ R'),
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom) ≫ σ₁.1 =
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom) ≫ σ₂.1 := by
  classical

  haveI : Smooth ER.f := ER.bundle.smooth
  haveI : LocallyOfFiniteType ER.f := inferInstance

  have halg : algebraMap (↥R) L = R.val.toRingHom := rfl
  have hab : pullback.fst (𝟙 (Spec (CommRingCat.of ↥R))) (Spec.map (CommRingCat.ofHom (algebraMap (↥R) L))) ≫ σ₁.1 =
      pullback.fst (𝟙 (Spec (CommRingCat.of ↥R))) (Spec.map (CommRingCat.ofHom (algebraMap (↥R) L))) ≫ σ₂.1 := by
    have hc := pullback.condition (f := 𝟙 (Spec (CommRingCat.of ↥R))) (g := Spec.map (CommRingCat.ofHom (algebraMap (↥R) L)))
    rw [Category.comp_id] at hc
    rw [hc, Category.assoc, Category.assoc, halg, h]
  obtain ⟨T, hTfg, hsT, hT⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      (𝟙 (Spec (CommRingCat.of ↥R))) ER.f σ₁.1 σ₂.1 σ₁.2 σ₂.2 hab s

  let R' : Subalgebra ℤ L := T.restrictScalars ℤ
  have hRR' : R ≤ R' := fun x hx => by
    show x ∈ T
    have : algebraMap (↥R) L ⟨x, hx⟩ ∈ T := T.algebraMap_mem _
    simpa [halg] using this

  have hR'fg : R'.FG := by
    rw [Subalgebra.fg_iff_finiteType]
    haveI : Algebra.FiniteType ℤ ↥R := (Subalgebra.fg_iff_finiteType R).mp hR
    haveI : Algebra.FiniteType (↥R) ↥T := (Subalgebra.fg_iff_finiteType T).mp hTfg
    have : Algebra.FiniteType ℤ ↥T := Algebra.FiniteType.trans (S := ↥R) inferInstance inferInstance
    exact this
  refine ⟨R', hR'fg, hRR', hsT, ?_⟩

  have hc := pullback.condition (f := 𝟙 (Spec (CommRingCat.of ↥R))) (g := Spec.map (CommRingCat.ofHom (algebraMap (↥R) ↥T)))
  rw [Category.comp_id] at hc
  rw [hc, Category.assoc, Category.assoc] at hT
  have hT' := (cancel_epi (pullback.snd (𝟙 (Spec (CommRingCat.of ↥R))) (Spec.map (CommRingCat.ofHom (algebraMap (↥R) ↥T))))).mp hT
  have hincl : CommRingCat.ofHom (Subalgebra.inclusion hRR').toRingHom = CommRingCat.ofHom (algebraMap (↥R) ↥T) := by
    congr 1
  rw [hincl]
  exact hT'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_section_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_le_section_comp_eq (solution)
