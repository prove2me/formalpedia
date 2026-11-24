-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeMap_mem_span_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:32.684974+00:00
-- url     : https://prove2.me/submissions/9cb2278c-4230-4b58-a241-1e6c20d20997

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_add_vectors
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_smul_field
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bcMap_zero

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
theorem _root_.solution {j : ℕ} (e : Fin j → ι → F) (m : ι → F)
    (hm : m ∈ Submodule.span F (Set.range e)) :
    bcMap (E := E) m ∈ Submodule.span E (Set.range fun a => bcMap (E := E) (e a)) := by
  let N : Submodule F (ι → F) :=
    { carrier := {x | bcMap (E := E) x ∈ Submodule.span E (Set.range fun a => bcMap (E := E) (e a))}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, baseChangeMap_add_vectors] at *
        exact Submodule.add_mem _ ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, bcMap_zero]
        exact Submodule.zero_mem _
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq, baseChangeMap_smul_field] at *
        exact Submodule.smul_mem _ _ hx }
  have hle : Submodule.span F (Set.range e) ≤ N :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact Submodule.subset_span ⟨a, rfl⟩)
  exact hle hm
end Formalism.HermiteSiegelSlopes
