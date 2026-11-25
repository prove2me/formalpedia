-- Prove2me | solution 1 for Formalism.HC.D7.principal_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:27:22.603128+00:00
-- url     : https://prove2.me/submissions/1c1011e8-7442-4fca-97ad-a03a156429c5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_EqOfPowEqOne
import Theorems.Thm_Formalism_HC_D7_exists_prime_mem
import Theorems.Thm_Formalism_HermitianLattices_FiltrationBoundaryCriterion_PfN_principalStable


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
include hH h
namespace Formalism.HC.D7
theorem _root_.solution (c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) (hc : galE e ζ a b c = cc e) :
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧ 𝔟 ⊔ c • 𝔟 = ⊤ ∧
      ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟 := by
  obtain ⟨P2, h2, -, m2⟩ := exists_prime_mem (KinE ζ a b) 2 Nat.prime_two
  obtain ⟨Pq, hq, -, mq⟩ := exists_prime_mem (KinE ζ a b) q hH.1
  obtain ⟨B, h1, -, h3, h4, -⟩ := Formalism.HermitianLattices.FiltrationBoundaryCriterion.PfN.principalStable e q d hH L ζ a b h c hc P2 Pq h2 hq
    (by exact_mod_cast m2) mq
  exact ⟨B, h1, h3, h4⟩
end Formalism.HC.D7
