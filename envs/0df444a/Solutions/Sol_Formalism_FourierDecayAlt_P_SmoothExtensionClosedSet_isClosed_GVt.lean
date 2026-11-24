-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet.isClosed_GVt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:58:55.688018+00:00
-- url     : https://prove2.me/submissions/020a3597-8dfc-43a7-b9a7-8dafb3bd1166

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsSmoothExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter Topology
open scoped Manifold ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
theorem _root_.solution (k r : ℕ) : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := by
  have h0 : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hc : Continuous (fun x : Mt k r => (Matrix.of x)ᴴ * Hpk k r * Matrix.of x) :=
    ((h0.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h0
  exact isClosed_eq hc continuous_const
end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
