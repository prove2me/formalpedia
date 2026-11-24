-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.allBut_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:37.833963+00:00
-- url     : https://prove2.me/submissions/10814da4-1209-4669-8735-cab2bbf73c7d

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers

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
open Formalism Formalism.G0
open Formalism.G0.LengthLayersP
variable {O : Type} [CommRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution {M : Type} [AddCommGroup M] [Module O M] (π : O) (P : Submodule O M)
    (E : ℕ) (h : AllButLE π ⊤ P 0 E) : ∀ y : M, π ^ E • y ∈ P := by
  intro y
  obtain ⟨C, -, hcard, hC⟩ := h
  have hC0 : C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
  have h1 := hC y Submodule.mem_top
  rwa [hC0, Finset.coe_empty, Submodule.span_empty, sup_bot_eq] at h1
end Formalism.G0.LengthLayersP
