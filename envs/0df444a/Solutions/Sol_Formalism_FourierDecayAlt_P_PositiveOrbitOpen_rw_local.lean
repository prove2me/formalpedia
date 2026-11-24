-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rw_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:46:37.456516+00:00
-- url     : https://prove2.me/submissions/141ae200-9790-457e-892f-530896677315

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_rdV_local

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveOrbitOpen
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen
theorem _root_.solution {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) (w : List (Mat k r)) (hw : ∀ X ∈ w, inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → Rw w f₁ x = Rw w f₂ x := by
  induction w with
  | nil => exact h
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local hV (ih (fun Y hY => hw Y (List.mem_cons_of_mem X hY))) (hw X (by simp)) x hx hxG
end Formalism.FourierDecayAlt.P.PositiveOrbitOpen
