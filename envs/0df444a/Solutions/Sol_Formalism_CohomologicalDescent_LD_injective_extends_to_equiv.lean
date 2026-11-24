-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.injective_extends_to_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:18:22.375901+00:00
-- url     : https://prove2.me/submissions/baf177ca-2f0e-4051-910f-4f50d2df633c

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r s t : ℕ} (h : s + t = r) (f : Fin s → Fin r) (hf : Function.Injective f) :
    ∃ ρ : Fin s ⊕ Fin t ≃ Fin r, ∀ p, ρ (Sum.inl p) = f p := by
  classical
  have hc : Fintype.card ↥(Set.range f)ᶜ = t := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective hf]
    simp
    omega
  let e1 : Fin s ≃ ↥(Set.range f) := Equiv.ofInjective f hf
  let e2 : Fin t ≃ ↥(Set.range f)ᶜ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨(Equiv.sumCongr e1 e2).trans (Equiv.Set.sumCompl (Set.range f)), fun p => ?_⟩
  simp [e1]
end Formalism.CohomologicalDescent.LD
