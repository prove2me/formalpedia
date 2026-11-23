-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.sum_pts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:18.246525+00:00
-- url     : https://prove2.me/submissions/bdcee054-4c3b-4f6d-8a98-17b78b03ed83

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockStartPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BlockStartPoints
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
open Classical
noncomputable section
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.BlockStartPoints
theorem _root_.solution {β : Type} [AddCommMonoid β] (Y : Finset (Pt E)) (s : ℕ) (S : Finset E)
    (F : Pt E → β) : ∑ p ∈ pts Y s S, F p = ∑ t ∈ S, ∑ h ∈ Y, F (join h s t) := by
  unfold pts
  rw [Finset.sum_image, Finset.sum_product_right]
  rintro ⟨h, t⟩ _ ⟨h', t'⟩ _ e
  simp only [join] at e
  have h2 := List.append_inj' e rfl
  simpa using h2
end Formalism.FourierDecayAlt.P.BlockStartPoints
