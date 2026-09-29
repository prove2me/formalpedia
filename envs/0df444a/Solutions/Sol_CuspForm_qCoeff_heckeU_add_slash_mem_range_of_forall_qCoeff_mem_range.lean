-- Prove2me | solution 1 for CuspForm.qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/23ac231e-a83c-550c-a547-31670eef9dac

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Theorems.Thm_CuspForm_stableT
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH
import Theorems.Thm_ModularCurve_exists_ratCast_qExpansion_slash_of_mem_Gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range
p2m_attr_erase "instance" "ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv"
p2m_attr_erase "simp" "ModularCurve.intSeriesC_one ModularCurve.JOne.torsionGaloisRep_apply ModularCurve.coe_restrictForm ModularCurve.intSeriesC_zero ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring"

set_option autoImplicit false

open scoped MatrixGroups ModularForm

namespace TFunRatIhl

theorem gamma1_le_gammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : CongruenceSubgroup.Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma0_mem.mpr h10
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, CongruenceSubgroup.Gamma0Map]
    exact h11
  rw [this]
  exact one_mem H

def toGamma1 {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ} (f : CuspForm (CohCarrier.GammaH M H) k) :
    ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑f
  slash_action_eq' A hA := SlashInvariantFormClass.slash_action_eq f A (Subgroup.map_mono (gamma1_le_gammaH M H) hA)
  holo' := ModularFormClass.holo f
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f (hc.mono (Subgroup.map_mono (gamma1_le_gammaH M H)))

@[scoped simp] theorem coe_toGamma1 {M : ℕ} {H : Subgroup (ZMod M)ˣ} {k : ℤ} (f : CuspForm (CohCarrier.GammaH M H) k) :
    (⇑(toGamma1 f) : UpperHalfPlane → ℂ) = ⇑f := rfl

end TFunRatIhl
p2m_reactivate "P2MW.S_CuspForm_qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range.TFunRatIhl"

open TFunRatIhl in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (ρ : SL(2, ℤ)) (hρ : ρ ∈ CongruenceSubgroup.Gamma0 M)
    (hρℓ : (((ρ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod M) = ℓ)
    (g : CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ (algebraMap ℚ ℂ).range) :
    ∀ n : ℕ, ModularFormClass.qCoeff
        (ModularForm.heckeU k ℓ ⇑g +
          (⇑g ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ ρ : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) n ∈ (algebraMap ℚ ℂ).range := by
  intro n
  have hT := CuspForm.stableT M H k hℓ hℓM
  have hD := CuspForm.stableD M H k

  have hfun := CuspForm.coe_heckeTLinH_eq (M := M) (H := H) k hℓ hℓM hT ⟨ρ, hρ⟩ hρℓ g
  rw [← hfun, CuspForm.qCoeff_heckeTLinH_eq_qCoeff_mul_add_pow_mul_qCoeff_diamondLinH M H k hℓ hℓM g n]
  have hgrat : ∀ m : ℕ, ∃ q : ℚ, (UpperHalfPlane.qExpansion 1 (⇑(toGamma1 g) : UpperHalfPlane → ℂ)).coeff m = (q : ℂ) := by
    intro m
    obtain ⟨q, hq⟩ := hg m
    exact ⟨q, by rw [← eq_ratCast (algebraMap ℚ ℂ) q, hq]; rfl⟩
  refine Subring.add_mem _ (hg _) (Subring.mul_mem _ ⟨(ℓ : ℚ) ^ (k - 1), by push_cast; rfl⟩ ?_)
  by_cases hdvd : ℓ ∣ n
  · rw [if_pos hdvd, CuspForm.coe_diamondLinH_apply (M := M) (H := H) k hD]
    obtain ⟨q, hq⟩ := ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 M (toGamma1 g) hgrat
      (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ))
      (CuspForm.gammaLift M (CuspForm.unitOfPrimeNotDvd hℓ hℓM)).2 (n / ℓ)
    refine ⟨q, ?_⟩
    rw [eq_ratCast, ← hq]
    rfl
  · rw [if_neg hdvd]
    exact Subring.zero_mem _

end S_CuspForm_qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range
end P2MW
export P2MW.S_CuspForm_qCoeff_heckeU_add_slash_mem_range_of_forall_qCoeff_mem_range (solution)
