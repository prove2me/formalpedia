-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.primeCoeffsIntegral_of_neZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ce774acc-23f5-55b2-8b4a-b2d4902a92fb

import Mathlib
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

open scoped CongruenceSubgroup

theorem solution {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform) :
    g.PrimeCoeffsIntegral := by
  intro ℓ
  haveI : Module.Finite ℤ (CuspForm.heckeAlgebra M 2 (∅ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two M ∅
  haveI hint : Algebra.IsIntegral ℤ (CuspForm.heckeAlgebra M 2 (∅ : Set ℕ)) :=
    Algebra.IsIntegral.of_finite ℤ _
  obtain ⟨χ, -, hT, hU⟩ := hg.exists_ringHom_heckeAlgebra (∅ : Set ℕ)
  by_cases hℓM : (ℓ : ℕ) ∣ M
  · refine ⟨⟨ModularFormClass.qCoeff g ℓ, ?_⟩, rfl⟩
    rw [← hU ℓ ℓ.2 hℓM (Set.notMem_empty _)]
    exact (hint.isIntegral _).map χ.toIntAlgHom
  · refine ⟨⟨ModularFormClass.qCoeff g ℓ, ?_⟩, rfl⟩
    rw [← hT ℓ ℓ.2 hℓM (Set.notMem_empty _)]
    exact (hint.isIntegral _).map χ.toIntAlgHom

end S_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_primeCoeffsIntegral_of_neZero (solution)
