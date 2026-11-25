-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx1.TC.CW.coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:51:41.373342+00:00
-- url     : https://prove2.me/submissions/edd01f5d-6610-4299-bbc1-56a2f6c5f4d9

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute

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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx1 Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.NFx1.TC
namespace CW
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (h : CW k r i T) (a : Mx k r → ℂ) :
    CW k r i (fun f x => a x • T f x) := by
  refine ⟨fun U₀ hU₀ Φ hΦ x hx hg => (h.diff U₀ hU₀ Φ hΦ x hx hg).const_smul (a x.2), ?_⟩
  intro U₀ hU₀ Φ hΦ x hx hg v
  have h1 := h.diff U₀ hU₀ Φ hΦ x hx hg
  show fderiv ℝ (fun c' => a x.2 • T (Φ c') x.2) x.1 v = a x.2 • T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2
  rw [show (fun c' => a x.2 • T (Φ c') x.2) = a x.2 • (fun c' => T (Φ c') x.2) from rfl,
    (h1.hasFDerivAt.const_smul (a x.2)).fderiv, _root_.smul_apply, h.comm U₀ hU₀ Φ hΦ x hx hg v]
end CW
end Formalism.FourierDecayAlt.P.NFx1.TC
