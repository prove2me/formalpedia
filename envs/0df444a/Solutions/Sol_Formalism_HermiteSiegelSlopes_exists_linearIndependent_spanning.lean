-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.exists_linearIndependent_spanning
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:06.01954+00:00
-- url     : https://prove2.me/submissions/a3eb1d75-1196-4581-a8c3-b891695e7c50

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent

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
theorem _root_.solution (M : Submodule (𝓞 F) (ι → F)) [Finite ι] :
    ∃ (j : ℕ) (e : Fin j → ι → F), LinearIndependent F e ∧ (∀ a, e a ∈ M) ∧
      (M : Set (ι → F)) ⊆ Submodule.span F (Set.range e) := by
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent F (M : Set (ι → F))
  have hfin : b.Finite := hli.setFinite
  have : Finite b := hfin.to_subtype
  obtain ⟨j, ⟨eqv⟩⟩ := Finite.exists_equiv_fin b
  refine ⟨j, fun a => (eqv.symm a : ι → F), hli.comp _ eqv.symm.injective, fun a => hbs (eqv.symm a).2, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span F (M : Set (ι → F)) := Submodule.subset_span hx
  rw [← hspan] at hx'
  have hr : Set.range (fun a => (eqv.symm a : ι → F)) = b := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact (eqv.symm a).2
    · intro hz
      exact ⟨eqv ⟨z, hz⟩, by simp⟩
  rw [hr]
  exact hx'
end Formalism.HermiteSiegelSlopes
