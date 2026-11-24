-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.relIndex_baseChange_dvd_pow_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:30.180876+00:00
-- url     : https://prove2.me/submissions/7c0a6f1f-eba2-4f72-ba90-a6807a816004

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_mono
import Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_baseChange_sup_singleton_dvd

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
theorem _root_.solution (A : Submodule (𝓞 F) (ι → F)) (s : Finset (ι → F)) :
    (bcLat (E := E) A).toAddSubgroup.relIndex
        (bcLat (E := E) (A ⊔ Submodule.span (𝓞 F) (s : Set (ι → F)))).toAddSubgroup ∣
      (A.toAddSubgroup.relIndex
        (A ⊔ Submodule.span (𝓞 F) (s : Set (ι → F))).toAddSubgroup) ^ finrank F E := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro m s hm ih
    have hU : A ⊔ Submodule.span (𝓞 F) ((insert m s : Finset (ι → F)) : Set (ι → F)) =
        (A ⊔ Submodule.span (𝓞 F) (s : Set (ι → F))) ⊔ Submodule.span (𝓞 F) {m} := by
      rw [Finset.coe_insert, Submodule.span_insert, sup_left_comm, sup_comm (Submodule.span (𝓞 F) {m})]
    rw [hU]
    have h1 : A ≤ A ⊔ Submodule.span (𝓞 F) (s : Set (ι → F)) := le_sup_left
    have h2 : A ⊔ Submodule.span (𝓞 F) (s : Set (ι → F)) ≤
        (A ⊔ Submodule.span (𝓞 F) (s : Set (ι → F))) ⊔ Submodule.span (𝓞 F) {m} := le_sup_left
    have e1 := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 h1)
      ((Submodule.toAddSubgroup_le _ _).2 h2)
    have e2 := AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).2 (baseChangeLattice_mono (E := E) h1))
      ((Submodule.toAddSubgroup_le _ _).2 (baseChangeLattice_mono (E := E) h2))
    calc _ = _ * _ := e2.symm
      _ ∣ _ := mul_dvd_mul ih (relIndex_baseChange_sup_singleton_dvd _ m)
      _ = _ := by rw [← mul_pow, e1]
end Formalism.HermiteSiegelSlopes
