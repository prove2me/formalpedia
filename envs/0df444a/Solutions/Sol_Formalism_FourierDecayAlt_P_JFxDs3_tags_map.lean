-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs3.tags_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:19:46.712806+00:00
-- url     : https://prove2.me/submissions/11d69b10-ac7c-4a3e-8f15-ce432b724a75

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxDs3
theorem _root_.solution (φ : Bool × Mat k r → Bool × Mat k r) :
    ∀ l : List (Bool × Mat k r), (∀ y ∈ l, (φ y).1 = y.1) → (l.map φ).map Prod.fst = l.map Prod.fst := by
  intro l hl
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hl y (List.mem_cons_self ..), ih fun z hz => hl z (List.mem_cons_of_mem _ hz)⟩
end Formalism.FourierDecayAlt.P.JFxDs3
