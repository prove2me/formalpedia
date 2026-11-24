-- Prove2me | solution 1 for Formalism.HC.D7.exists_prime_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:30.096796+00:00
-- url     : https://prove2.me/submissions/e662c1a0-69af-4c8b-9524-7c36fde2e23a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EqOfPowEqOne
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_intCast_mem_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} (hH : HostHyp q d) {L : Type} [Field L] [NumberField L] {ζ a b : L}
  (h : IsLayer (e + 2) q d ζ a b)
namespace Formalism.HC.D7
theorem _root_.solution (M : Type) [Field M] [NumberField M] (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 M), P.IsPrime ∧ P.LiesOver (span {(p : ℤ)}) ∧ ((p : ℤ) : 𝓞 M) ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨P, h1, h2⟩⟩ : Nonempty ((span {(p : ℤ)}).primesOver (𝓞 M)) := inferInstance
  exact ⟨P, h1, h2, (odd_intCast_mem_iff p P _).mpr dvd_rfl⟩
end Formalism.HC.D7
