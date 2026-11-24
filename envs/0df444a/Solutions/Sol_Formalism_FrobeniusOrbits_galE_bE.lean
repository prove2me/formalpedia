-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.galE_bE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:43:32.476825+00:00
-- url     : https://prove2.me/submissions/decb7dce-a933-4a43-af69-1e82829d15d7

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply

set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b)
    (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    ((σ (bE ζ a b) : hostE ζ a b) : L) = ((((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) : L) * b := by
  have ha : (bE ζ a b) ^ 2 = -((d : ℕ) : hostE ζ a b) := by
    apply Subtype.ext
    simp [bE, h.2.2.1]
  have hs : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
    rw [← map_pow, ha, map_neg, map_natCast]
  have hor : σ (bE ζ a b) = bE ζ a b ∨ σ (bE ζ a b) = -bE ζ a b :=
    sq_eq_sq_iff_eq_or_eq_neg.mp hs
  unfold galE
  dsimp only
  unfold Formalism.TwoAdicCyclotomicDecomposition.sgn
  by_cases hx : σ (bE ζ a b) = bE ζ a b
  · rw [if_pos hx, hx]
    simp [bE]
  · rw [if_neg hx]
    rcases hor with h1 | h1
    · exact absurd h1 hx
    · rw [h1]
      simp [bE]
end Formalism.FrobeniusOrbits
