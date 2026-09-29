-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4342486f-6bb8-51b5-aee0-06c451d9845e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (a : ℕ → Fin 2 → B) (ha : a 0 0 * a 0 1 = (p : B)) :
    ∃ (X : CerednikDrinfeld.FormalODModule p B)
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
      X.IsHomogeneousVBasis j γ ∧ X.HasStructureConstants γ a := by
  classical
  obtain ⟨XU, γU, hγU, haU⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar p

  let I : Ideal (MvPolynomial (ℕ × Fin 2) (Zp2 p)) :=
    Ideal.span {CartierLift.liftRel p (Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)}
  let e : MvPolynomial (ℕ × Fin 2) (Zp2 p) →+* B :=
    MvPolynomial.eval₂Hom j (fun b => a b.1 b.2)
  have he : ∀ x ∈ I, e x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, CartierLift.liftRel, map_sub, map_mul, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, map_natCast]
    simp [ha]
  let φ : CartierLift.LiftRing p (Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1) →+* B :=
    Ideal.Quotient.lift I e he
  have hφj : φ.comp (algebraMap (Zp2 p) (CartierLift.LiftRing p (Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1))) = j := by
    ext r
    show φ (Ideal.Quotient.mk I (MvPolynomial.C r)) = j r
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
  have hφX : ∀ (m : ℕ) (i : Fin 2),
      φ (CartierLift.liftVar (p := p) (R := Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1) (m, i)) = a m i := by
    intro m i
    show φ (Ideal.Quotient.mk I (MvPolynomial.X (m, i))) = a m i
    rw [Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_X']
  refine ⟨XU.map φ, fun i => CartierModule.baseChange φ (γU i), ?_, ?_⟩
  · have h := hγU.map φ
    rwa [hφj] at h
  · have h := haU.map φ
    have hfun : (fun m i => φ (CartierLift.liftVar (p := p) (R := Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1) (m, i))) = a :=
      funext fun m => funext fun i => hφX m i
    rw [hfun] at h
    exact h

end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq (solution)
