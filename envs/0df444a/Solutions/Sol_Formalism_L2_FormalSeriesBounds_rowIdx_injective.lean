-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.rowIdx_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:27:41.868888+00:00
-- url     : https://prove2.me/submissions/5f34d848-f24e-4358-a191-4ea627da8a57

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowIdx_self
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_rowIdx_other

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (g : Fin 2) : Function.Injective (rowIdx g : WV I → I g ⊕ I (1 - g)) := by
  rintro ⟨g1, x1⟩ ⟨g2, x2⟩ h
  rcases finset_fin_two_eq_cases g g1 with h1 | h1 <;> rcases finset_fin_two_eq_cases g g2 with h2 | h2
  · subst h1; subst h2
    rw [rowIdx_self, rowIdx_self] at h
    rw [Sum.inl.inj h]
  · subst h1; subst h2
    rw [rowIdx_self, rowIdx_other] at h
    exact absurd h (by simp)
  · subst h1; subst h2
    rw [rowIdx_other, rowIdx_self] at h
    exact absurd h (by simp)
  · subst h1; subst h2
    rw [rowIdx_other, rowIdx_other] at h
    rw [Sum.inr.inj h]
end Formalism.L2.FormalSeriesBounds
