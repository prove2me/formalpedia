-- Prove2me | solution 1 for Formalism.L2.NG.IsLabelOf.at_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:32:34.573141+00:00
-- url     : https://prove2.me/submissions/873af2a4-03cc-4a60-813c-4a6d326fbf56

import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsLab
import Theorems.Thm_Formalism_L2_NG_labPol_one
import Theorems.Thm_Formalism_L2_NG_exists_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.L2 Formalism.L2.NG
variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {p : ℕ} [Fact p.Prime]
variable {A : ValuationSubring Ω} {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {ζ : ℕ → Formalism.CyclotomicNorms.Fbar p}
  {teich : Formalism.CyclotomicNorms.Fbar p →* ℂ} {I : Set (Ω ≃ₐ[E] Ω)} {n : ℕ} {P : (Ω ≃ₐ[E] Ω) → ℂ[X]} {f f' : (ZMod p)[X]}
namespace Formalism.L2.NG
namespace IsLabelOf
theorem _root_.solution (h : IsLabelOf A κ ζ teich I n P f) {σ : Ω ≃ₐ[E] Ω} (hσ : σ ∈ I) (hc : NT.TameCoupled A κ σ ζ) :
    P σ = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod := by
  obtain ⟨d, hd⟩ := exists_level f h.2.2.1
  rw [← labPol_one]
  exact h.2.2.2 σ hσ d 1 hd (by rw [pow_one]; exact hc d hd.1)
end IsLabelOf
end Formalism.L2.NG
