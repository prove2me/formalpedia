-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.isConj_iff_galE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:12.549331+00:00
-- url     : https://prove2.me/submissions/ea6803e2-9c60-45eb-8de1-0947c724b448

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_eq_conjE_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_conjE_apply
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
    (φ : hostE ζ a b →+* ℂ) (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b) :
    (∀ x, φ (σ x) = starRingEnd ℂ (φ x)) ↔ galE e ζ a b σ = cc e := by
  rw [← eq_conjE_iff hqd h]
  constructor
  · intro hσ
    exact AlgEquiv.ext fun x => φ.injective (by rw [hσ, conjE_apply hqd h])
  · rintro rfl x
    exact conjE_apply hqd h φ x
end Formalism.FrobeniusOrbits
