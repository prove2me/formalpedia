-- Prove2me | solution 1 for Formalism.G0.LengthLayersP.length_le_of_span_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:37.296235+00:00
-- url     : https://prove2.me/submissions/5d9b2acc-45bd-4bbb-9702-2d41aae12941

import Definitions.Def_Formalism_SubspaceCounting_Statement
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Theorems.Thm_Formalism_G0_LengthLayersP_length_span_finset_le

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
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.G0.LengthLayersP
theorem _root_.solution (π : O) (hπ : Irreducible π) {X : Type} [AddCommGroup X]
    [Module O X] (s : ℕ) (D : Finset X) (hD : ∀ x ∈ D, π ^ s • x = 0)
    (htop : Submodule.span O (D : Set X) = ⊤) :
    Module.length O X ≤ ((D.card * s : ℕ) : ℕ∞) := by
  have h := length_span_finset_le π hπ s D hD
  rw [htop] at h
  rwa [(Submodule.topEquiv).length_eq] at h
end Formalism.G0.LengthLayersP
