-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StrictBoxOrder.sup_pres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:36.256466+00:00
-- url     : https://prove2.me/submissions/d2574bc6-11bb-45db-bb67-ba37801fdbe2

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictBoxOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StrictBoxOrder
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.StrictBoxOrder
theorem _root_.solution {ι : Type} (f : Module.End ℂ V) (F : ι → Submodule ℂ V) (p : ι → Prop)
    (h : ∀ j, ∀ v ∈ F j, f v ∈ F j) : ∀ v ∈ ⨆ (j) (_ : p j), F j, f v ∈ ⨆ (j) (_ : p j), F j := by
  have hle : (⨆ (j) (_ : p j), F j) ≤ (⨆ (j) (_ : p j), F j).comap f := by
    refine iSup₂_le (fun j hj => ?_)
    intro v hv
    exact (le_iSup₂ (f := fun j (_ : p j) => F j) j hj) (h j v hv)
  intro v hv
  exact hle hv
end Formalism.FourierDecayAlt.P.StrictBoxOrder
