-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameEntries.foldl_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:38:53.851054+00:00
-- url     : https://prove2.me/submissions/78fcd722-de5c-4a21-8f5d-b8068c4a018c

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.FrameEntries
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FrameEntries
theorem _root_.solution (L : List ((Mx k r → E) → Mx k r → E)) (c : ℂ)
    (hL : ∀ T ∈ L, ∀ f, T (fun x => c • f x) = fun x => c • T f x) (f : Mx k r → E) :
    L.foldl (fun h T => T h) (fun x => c • f x) = fun x => c • L.foldl (fun h T => T h) f x := by
  induction L generalizing f with
  | nil => rfl
  | cons T L ih =>
    simp only [List.foldl_cons]
    rw [hL T (by simp) f]
    exact ih (fun T' hT' => hL T' (by simp [hT'])) (T f)
end Formalism.FourierDecayAlt.P.FrameEntries
