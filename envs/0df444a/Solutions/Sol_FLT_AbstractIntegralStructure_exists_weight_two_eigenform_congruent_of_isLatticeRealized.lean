-- Prove2me | solution 1 for FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_isLatticeRealized
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1b5b4d81-cde0-59ea-b62b-c86990374f9d

import Mathlib
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_PowerSeries_FormalHeckeOperators
import Theorems.Thm_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_heckeT_congr
import Theorems.Thm_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"

open CuspForm EisensteinWeightOne CongruenceSubgroup ModularFormClass

theorem solution
    {N : ℕ} [NeZero N] (h : CuspForm.HasIntegralBasis N) {a : ℕ → ℤ}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a)
    (hreal : CuspForm.IsLatticeRealized N a) :
    ∃ (f : CuspForm (Gamma0 N) 2) (_ : f.IsNormalizedEigenform)
      (𝔪' : Ideal (integralClosure ℤ ℂ)), 𝔪'.IsMaximal ∧
      ((3 : ℕ) : integralClosure ℤ ℂ) ∈ 𝔪' ∧
      ∀ (ℓ : ℕ) (_ : ℓ.Prime) (_ : ¬ ℓ ∣ N),
        ∃ c : integralClosure ℤ ℂ, (c : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          c - (a ℓ : integralClosure ℤ ℂ) ∈ 𝔪' :=
  FLT.AbstractIntegralStructure.exists_weight_two_eigenform_congruent_of_heckeT_congr h heig.1
    (fun ℓ hℓ hℓN n =>
      FLT.OccurrenceStatement.three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd heig hℓ hℓN n)
    hreal

end S_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized
end P2MW
export P2MW.S_FLT_AbstractIntegralStructure_exists_weight_two_eigenform_congruent_of_isLatticeRealized (solution)
