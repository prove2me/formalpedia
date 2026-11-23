-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BlockStartPoints.psd_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:17.625037+00:00
-- url     : https://prove2.me/submissions/02523482-e966-4222-9dcb-faad4bfbf1bf

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
theorem _root_.solution {α β : Type} (Y : Finset α) (Z : Finset β) (φ : α → β) (hφ : ∀ a ∈ Y, φ a ∈ Z)
    (k : β → β → ℂ) (hk : PSDOn Z k) : PSDOn Y (fun a b => k (φ a) (φ b)) :=
  Matrix.PosSemidef.submatrix hk (fun a : Y => (⟨φ a, hφ a a.2⟩ : Z))
end Formalism.FourierDecayAlt.P.BlockStartPoints
