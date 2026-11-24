-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs3.le_sum_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:35.338943+00:00
-- url     : https://prove2.me/submissions/6bfed78b-82c9-409f-aec1-041b44a4cc02

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
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JFxDs3
theorem _root_.solution {α : Type*} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (l : List α) {x : α} (hx : x ∈ l) :
    f x ≤ (l.map f).sum := by
  exact List.single_le_sum (fun y hy => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hy
    exact hf z) _ (List.mem_map_of_mem hx)
end Formalism.FourierDecayAlt.P.JFxDs3
