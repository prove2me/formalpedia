-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct.vdm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:40:24.946345+00:00
-- url     : https://prove2.me/submissions/0ff9fd18-de96-448b-9aa1-275814e42ed6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCTheta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
theorem _root_.solution (N : ℕ) : ∃ W : Matrix (Fin N) (Fin N) ℂ,
    W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1 := by
  refine ⟨(Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)))⁻¹, Matrix.nonsing_inv_mul _ ?_⟩
  rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
  intro a b h
  exact Fin.ext (Nat.cast_injective h)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
