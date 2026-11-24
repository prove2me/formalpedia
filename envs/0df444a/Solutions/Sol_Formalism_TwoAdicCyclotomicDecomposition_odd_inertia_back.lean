-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_inertia_back
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:08.837359+00:00
-- url     : https://prove2.me/submissions/da4870ca-2aef-4808-8739-b313b6781d83

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {G : Type*} [One G]
    (f : Gal(L/ℚ) → G) (hinj : Function.Injective f) (h1 : f 1 = 1) (t : G)
    (r : ℕ) [Fact r.Prime] (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(r : ℤ)})]
    (hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) → f τ = 1 ∨ f τ = t)
    (hram : P.ramificationIdx ℤ ≠ 1) (σ : Gal(L/ℚ)) (hσ : f σ = t) :
    ∀ x : 𝓞 L, σ • x - x ∈ P := by
  by_contra hn
  have hbot : P.inertia Gal(L/ℚ) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    rw [Subgroup.mem_bot]
    rcases hfwd τ hτ with h' | h'
    · exact hinj (h'.trans h1.symm)
    · have := hinj (h'.trans hσ.symm)
      subst this
      exact absurd hτ hn
  have hc := odd_card L r P
  rw [hbot, Subgroup.card_bot] at hc
  exact hram hc.symm
end Formalism.TwoAdicCyclotomicDecomposition
