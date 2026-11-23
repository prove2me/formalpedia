-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.baseChangeLattice_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:02.775609+00:00
-- url     : https://prove2.me/submissions/214bb47b-b0b2-4b36-ad25-be3dc4f66839

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_map_add
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_smul_integers

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
theorem _root_.solution (s : Set (ι → F)) :
    bcLat (E := E) (Submodule.span (𝓞 F) s) = Submodule.span (𝓞 E) (bcMap '' s) := by
  unfold bcLat
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    let N : Submodule (𝓞 F) (ι → F) :=
      { carrier := {x | bcMap (E := E) x ∈ Submodule.span (𝓞 E) (bcMap (E := E) '' s)}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, baseChangeMap_map_add] at *
          exact Submodule.add_mem _ ha hb
        zero_mem' := by
          simp only [Set.mem_setOf_eq]
          have h0 : bcMap (E := E) (0 : ι → F) = 0 := by funext i; simp [bcMap]
          rw [h0]
          exact Submodule.zero_mem _
        smul_mem' := fun c {x} hx => by
          simp only [Set.mem_setOf_eq, baseChangeMap_smul_integers] at *
          exact Submodule.smul_mem _ _ hx }
    have hsN : Submodule.span (𝓞 F) s ≤ N :=
      Submodule.span_le.2 fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
    exact hsN hz
  · exact Submodule.span_mono (fun _ ⟨z, hz, hze⟩ => ⟨z, Submodule.subset_span hz, hze⟩)
end Formalism.HermiteSiegelSlopes
