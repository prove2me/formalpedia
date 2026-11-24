-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Galois.hPart_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:58.670795+00:00
-- url     : https://prove2.me/submissions/15f54166-c7c4-4ec9-834c-9144dfb34be1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_trace_eq_iff_units
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_hcl_eq_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_apply_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Galois
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Galois
theorem _root_.solution (h : IsLayer (e + 2) q d ζ a b) {σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b}
    {τ : Gal(L/ℚ)} (hστ : ∀ x : hostE ζ a b, ((σ x : hostE ζ a b) : L) = τ x) :
    hPart e ζ a b σ = hcl e (h.1.autToPow ℚ τ) := by
  have hθ : ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ (h.1.autToPow ℚ τ : ZMod (2 ^ (e + 2))).val +
        ζ⁻¹ ^ (h.1.autToPow ℚ τ : ZMod (2 ^ (e + 2))).val := by
    rw [hστ]; exact apply_theta h.1 τ
  have hex : ∃ u : (ZMod (2 ^ (e + 2)))ˣ, ((σ (thE ζ a b) : hostE ζ a b) : L) =
      ζ ^ (u : ZMod (2 ^ (e + 2))).val + ζ⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val := ⟨_, hθ⟩
  unfold hPart
  rw [dif_pos hex, hcl_eq_iff]
  have hs := hθ.symm.trans hex.choose_spec
  exact (trace_eq_iff_units h.1 _ _).mp hs.symm
end Formalism.FrobeniusOrbits.Galois
