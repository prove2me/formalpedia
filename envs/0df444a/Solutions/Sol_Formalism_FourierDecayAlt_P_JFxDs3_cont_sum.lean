-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs3.cont_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:34.554887+00:00
-- url     : https://prove2.me/submissions/263256f1-adf6-463e-b0d2-c8a792b32ce1

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
theorem _root_.solution {α : Type*} (S : Set (SS k r)) (f : α → SS k r → ℝ) :
    ∀ l : List α, (∀ x ∈ l, ContinuousOn (f x) S) → ContinuousOn (fun p => (l.map (fun x => f x p)).sum) S := by
  intro l hl
  induction l with
  | nil => simpa using continuousOn_const
  | cons y l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hl y (List.mem_cons_self ..)).add (ih fun z hz => hl z (List.mem_cons_of_mem _ hz))
end Formalism.FourierDecayAlt.P.JFxDs3
