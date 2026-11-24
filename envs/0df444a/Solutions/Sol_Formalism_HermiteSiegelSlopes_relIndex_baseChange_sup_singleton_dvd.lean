-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.relIndex_baseChange_sup_singleton_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:33.778083+00:00
-- url     : https://prove2.me/submissions/dbfd599e-b8ec-42e3-ac4f-f232e8f56055

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_sup_singleton_eq_absNorm
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_smul_integers
import Theorems.Thm_Formalism_HermiteSiegelSlopes_finrank_ringOfIntegers_eq
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_span
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_sup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution (A : Submodule (𝓞 F) (ι → F)) (m : ι → F) :
    (bcLat (E := E) A).toAddSubgroup.relIndex
        (bcLat (E := E) (A ⊔ Submodule.span (𝓞 F) {m})).toAddSubgroup ∣
      (A.toAddSubgroup.relIndex (A ⊔ Submodule.span (𝓞 F) {m}).toAddSubgroup) ^ finrank F E := by
  rw [baseChangeLattice_sup, baseChangeLattice_span, Set.image_singleton, relIndex_sup_singleton_eq_absNorm,
    relIndex_sup_singleton_eq_absNorm, ← finrank_ringOfIntegers_eq, ← Ideal.absNorm_algebraMap]
  apply Ideal.absNorm_dvd_absNorm_of_le
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, ← baseChangeMap_smul_integers]
  exact Submodule.subset_span ⟨_, hr, rfl⟩
end Formalism.HermiteSiegelSlopes
