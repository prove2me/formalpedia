-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cx1.psd_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:22:55.961858+00:00
-- url     : https://prove2.me/submissions/70cd027a-b03a-41e7-9265-c2b5e203bba1

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
open Formalism.FourierDecayAlt.P.Cx1
namespace Formalism.FourierDecayAlt.P.Cx1
theorem _root_.solution {α β : Type} (Y : Finset α) (φ : α → β) (k : β → β → ℂ) (Z : Finset β)
    (hZ : ∀ x ∈ Y, φ x ∈ Z) (h : TB.PSDOn Z k) : TB.PSDOn Y (fun x y => k (φ x) (φ y)) := by
  simp only [TB.PSDOn] at h ⊢
  exact h.submatrix (fun x : Y => (⟨φ x, hZ x x.2⟩ : Z))
end Formalism.FourierDecayAlt.P.Cx1
