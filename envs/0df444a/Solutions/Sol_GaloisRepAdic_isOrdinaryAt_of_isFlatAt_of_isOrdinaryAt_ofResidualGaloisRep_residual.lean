-- Prove2me | solution 1 for GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1007bf01-b111-5881-9cf1-579f5c69b326

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_forall_quotient
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isFlatAt_baseChangeAlong_of_finite_residueField
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_ofResidualGaloisRep_residual_baseChangeAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
p2m_attr_erase "instance" "instIsScalarTowerTensorProduct_definitions AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree"
p2m_attr_erase "simp" "closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open IsLocalRing

theorem solution {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpA : (p : A) ∈ maximalIdeal A)
    (ρ : GaloisRepAdic A) (hdet : ρ.DetIsCyclotomic p) (hflat : ρ.IsFlatAt p)
    (hres : (GaloisRepAdic.ofResidualGaloisRep ρ.residual).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by
  haveI hk : Finite (A ⧸ maximalIdeal A) := hflat.1
  refine GaloisRepAdic.isOrdinaryAt_of_forall_quotient ρ (Fact.out) hp2 (fun m => ?_) (fun m => ?_)
  · letI : Nontrivial (A ⧸ maximalIdeal A ^ (m + 1)) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
        (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
    letI : IsLocalRing (A ⧸ maximalIdeal A ^ (m + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    exact GaloisRepAdic.detIsCyclotomic_baseChangeAlong _ _ ρ hdet
  · letI : Nontrivial (A ⧸ maximalIdeal A ^ (m + 1)) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
        (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
    letI : IsLocalRing (A ⧸ maximalIdeal A ^ (m + 1)) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI hfinq : Finite (A ⧸ maximalIdeal A ^ (m + 1)) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian _) (m + 1)
    haveI : Finite (ResidueField (A ⧸ maximalIdeal A ^ (m + 1))) :=
      Finite.of_surjective _ (IsLocalRing.residue_surjective)
    exact GaloisRepAdic.isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual_of_finite
      p hp2 _ (GaloisRepAdic.detIsCyclotomic_baseChangeAlong _ _ ρ hdet)
      (GaloisRepAdic.isFlatAt_baseChangeAlong_of_finite_residueField _ _ ρ hflat)
      (GaloisRepAdic.isOrdinaryAt_ofResidualGaloisRep_residual_baseChangeAlong _ _ ρ p hres)

end S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual
end P2MW
export P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isFlatAt_of_isOrdinaryAt_ofResidualGaloisRep_residual (solution)
