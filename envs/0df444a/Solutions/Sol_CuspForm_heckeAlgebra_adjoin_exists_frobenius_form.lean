-- Prove2me | solution 1 for CuspForm.heckeAlgebra_adjoin_exists_frobenius_form
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/bc97b561-a444-538f-bab2-8262266ae68b

import Theorems.Thm_CuspForm_eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero
import Theorems.Thm_CuspForm_exists_cyclic_span_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeAlgebra_adjoin_exists_frobenius_form
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

noncomputable section

namespace GorAux1

open ModularFormClass

variable (M : ℕ)

local notation "S₂" => CuspForm (CongruenceSubgroup.Gamma0 M) 2

def qCoeffOne : S₂ →ₗ[ℂ] ℂ where
  toFun f := qCoeff f 1
  map_add' f g := by
    simp only [qCoeff, CuspForm.coe_add]
    rw [ModularForm.qExpansion_add one_pos (by simp) f g, map_add]
  map_smul' c f := by
    simp only [qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos (by simp) c f, map_smul, smul_eq_mul]

variable {M} in
@[scoped simp] theorem qCoeffOne_apply (f : S₂) : qCoeffOne M f = qCoeff f 1 := rfl

variable {M} in

def evalAt (f₀ : S₂) : Module.End ℂ S₂ →ₗ[ℂ] S₂ where
  toFun T := T f₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {M} in
@[scoped simp] theorem evalAt_apply (f₀ : S₂) (T : Module.End ℂ S₂) : evalAt f₀ T = T f₀ := rfl

variable [NeZero M]

theorem adjoin_toSubmodule_eq_span :
    Subalgebra.toSubmodule (Algebra.adjoin ℂ
        ((CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂))))
      = Submodule.span ℂ ((CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂))) := by
  refine Algebra.adjoin_eq_span_of_subset ℂ ?_
  intro x hx
  have hx' : x ∈ (CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂)) := by
    have := Submonoid.closure_le (s := (CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂)))
      (S := (CuspForm.heckeAlgebra M 2 ∅).toSubsemiring.toSubmonoid)
    exact this.mpr (fun y hy => hy) hx
  exact Submodule.subset_span hx'

variable {M} in
theorem mem_adjoin_iff_mem_span (T : Module.End ℂ S₂) :
    T ∈ Algebra.adjoin ℂ ((CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂)))
      ↔ T ∈ Submodule.span ℂ ((CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂))) := by
  rw [← Subalgebra.mem_toSubmodule, adjoin_toSubmodule_eq_span]

variable {M} in

def frobForm (f₀ : S₂) :
    (Algebra.adjoin ℂ ((CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂)))) →ₗ[ℂ] ℂ :=
  (qCoeffOne M) ∘ₗ (evalAt f₀) ∘ₗ (Subalgebra.val _).toLinearMap

variable {M} in
theorem frobForm_apply (f₀ : S₂)
    (a : Algebra.adjoin ℂ ((CuspForm.heckeAlgebra M 2 ∅ : Set (Module.End ℂ S₂)))) :
    frobForm f₀ a = qCoeff ((a : Module.End ℂ S₂) f₀) 1 := rfl

end GorAux1
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_adjoin_exists_frobenius_form.GorAux1"

end
p2m_reactivate "P2MW.S_CuspForm_heckeAlgebra_adjoin_exists_frobenius_form.GorAux1"

open GorAux1 in
theorem solution (M : ℕ) [NeZero M] :
    ∃ l : (Algebra.adjoin ℂ
        ((CuspForm.heckeAlgebra M 2 ∅ : Set
          (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2))))) →ₗ[ℂ] ℂ,
      ∀ a, (∀ b, l (a * b) = 0) → a = 0 := by
  obtain ⟨f₀, hf₀⟩ := CuspForm.exists_cyclic_span_heckeAlgebra M
  refine ⟨frobForm f₀, ?_⟩
  intro a ha
  have key : (a : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) = 0 := by
    refine CuspForm.eq_zero_of_mem_span_heckeAlgebra_of_forall_qCoeff_one_eq_zero M _
      ((mem_adjoin_iff_mem_span _).mp a.2) ?_
    intro g
    obtain ⟨T, hT, hTg⟩ := hf₀ g
    obtain ⟨b, rfl⟩ :
        ∃ b : Algebra.adjoin ℂ ((CuspForm.heckeAlgebra M 2 ∅ : Set
          (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)))),
          (b : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) = T :=
      ⟨⟨T, (mem_adjoin_iff_mem_span T).mpr hT⟩, rfl⟩
    have h := ha b
    rw [frobForm_apply, Subalgebra.coe_mul, Module.End.mul_apply, hTg] at h
    exact h
  exact ZeroMemClass.coe_eq_zero.mp key

end S_CuspForm_heckeAlgebra_adjoin_exists_frobenius_form
end P2MW
export P2MW.S_CuspForm_heckeAlgebra_adjoin_exists_frobenius_form (solution)
