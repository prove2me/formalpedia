-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.eigenCoeffRing_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8360aaec-8bdc-5c62-862f-fe0c5cc810c2

import Mathlib
import Definitions.Def_CuspForm_EigenformCoefficientRing
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_ringHom_heckeAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite
p2m_attr_erase "simp" "PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option Elab.async false

open scoped CongruenceSubgroup

namespace CuspForm
p2m_export "CuspForm" "PrimeCoeffsIntegral eigenLift_coe eigenCoeffRing IsNormalizedEigenform moduleFinite_heckeAlgebra_two heckeAlgebra heckeAlgebra.T heckeAlgebra.U"
p2m_open "CuspForm"

namespace IsNormalizedEigenform p2m_export "CuspForm.IsNormalizedEigenform" "exists_ringHom_heckeAlgebra" end IsNormalizedEigenform
p2m_open_scoped "CuspForm.IsNormalizedEigenform" in
private theorem IsNormalizedEigenform.eigenCoeffRing_moduleFinite {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (hint : g.PrimeCoeffsIntegral) : Module.Finite ℤ (eigenCoeffRing hint) := by

  haveI hA : Module.Finite ℤ (CuspForm.heckeAlgebra M 2 (∅ : Set ℕ)) :=
    CuspForm.moduleFinite_heckeAlgebra_two M (∅ : Set ℕ)

  obtain ⟨χ, -, hT, hU⟩ := hg.exists_ringHom_heckeAlgebra (∅ : Set ℕ)

  haveI hSc : Module.Finite ℤ χ.toIntAlgHom.range :=
    Module.Finite.of_surjective χ.toIntAlgHom.rangeRestrict.toLinearMap
      χ.toIntAlgHom.rangeRestrict_surjective

  have hmem : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff g ℓ ∈ χ.toIntAlgHom.range := by
    intro ℓ
    by_cases hdvd : (ℓ : ℕ) ∣ M
    · exact ⟨CuspForm.heckeAlgebra.U ℓ.2 hdvd (Set.notMem_empty _),
        hU ℓ.1 ℓ.2 hdvd (Set.notMem_empty _)⟩
    · exact ⟨CuspForm.heckeAlgebra.T ℓ.2 hdvd (Set.notMem_empty _),
        hT ℓ.1 ℓ.2 hdvd (Set.notMem_empty _)⟩

  have hadj : Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => ModularFormClass.qCoeff g ℓ)
      ≤ χ.toIntAlgHom.range := by
    refine Algebra.adjoin_le ?_
    rintro x ⟨ℓ, rfl⟩
    exact hmem ℓ

  have hmap : (eigenCoeffRing hint).map (integralClosure ℤ ℂ).val
      = Algebra.adjoin ℤ (Set.range fun ℓ : Nat.Primes => ModularFormClass.qCoeff g ℓ) := by
    rw [eigenCoeffRing, AlgHom.map_adjoin, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext fun ℓ => eigenLift_coe hint ℓ))

  have hfgSc : (Subalgebra.toSubmodule χ.toIntAlgHom.range).FG := Module.Finite.iff_fg.mp hSc
  haveI : IsNoetherian ℤ (Subalgebra.toSubmodule χ.toIntAlgHom.range) :=
    isNoetherian_of_fg_of_noetherian _ hfgSc
  have hVW : Subalgebra.toSubmodule ((eigenCoeffRing hint).map (integralClosure ℤ ℂ).val)
      ≤ Subalgebra.toSubmodule χ.toIntAlgHom.range := fun x hx => hadj (hmap ▸ hx)
  have hVfg : (Subalgebra.toSubmodule
      ((eigenCoeffRing hint).map (integralClosure ℤ ℂ).val)).FG := by
    have h1 := (IsNoetherian.noetherian (Submodule.comap
      (Subalgebra.toSubmodule χ.toIntAlgHom.range).subtype
      (Subalgebra.toSubmodule ((eigenCoeffRing hint).map (integralClosure ℤ ℂ).val)))).map
      (Subalgebra.toSubmodule χ.toIntAlgHom.range).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hVW] at h1
  haveI hVfin : Module.Finite ℤ ((eigenCoeffRing hint).map (integralClosure ℤ ℂ).val) :=
    Module.Finite.iff_fg.mpr hVfg

  exact Module.Finite.equiv
    (Subalgebra.equivMapOfInjective (eigenCoeffRing hint) (integralClosure ℤ ℂ).val
      Subtype.coe_injective).symm.toLinearEquiv

end CuspForm

set_option autoImplicit false
p2m_open "CuspForm P2MW.S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite.CuspForm CuspForm.IsNormalizedEigenform P2MW.S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite.CuspForm.IsNormalizedEigenform"

theorem solution {M : ℕ} [NeZero M]
    {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNormalizedEigenform)
    (hint : g.PrimeCoeffsIntegral) : Module.Finite ℤ (CuspForm.eigenCoeffRing hint) := by
  exact CuspForm.IsNormalizedEigenform.eigenCoeffRing_moduleFinite hg hint

end S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_eigenCoeffRing_moduleFinite (solution)
