-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.Comm.lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:13.333106+00:00
-- url     : https://prove2.me/submissions/882f92a7-cad8-4d31-82a5-eb5cc51d21c3

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
namespace Comm
theorem _root_.solution {T₁ T₂ S : (Mx k r → E) → Mx k r → E} (hS : Good k r i D S) (hT₁ : Good k r i D T₁)
    (hT₂ : Good k r i D T₂) (h₁ : Comm k r i D T₁ S) (h₂ : Comm k r i D T₂ S) (c : ℂ) :
    Comm k r i D (fun f x => T₁ f x + c • T₂ f x) S := by
  intro f hf x hx
  show T₁ (S f) x + c • T₂ (S f) x = S (fun y => T₁ f y + c • T₂ f y) x
  rw [hS.lin _ _ c (hT₁.sm f hf) (hT₂.sm f hf) x hx, h₁ f hf x hx, h₂ f hf x hx]
end Comm
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
