-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct.interp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:03.517969+00:00
-- url     : https://prove2.me/submissions/ae2005dc-400a-45f1-a080-e4b740460b90

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCTheta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActCut

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] (N : ℕ) (W : Matrix (Fin N) (Fin N) ℂ)
    (hW : W * Matrix.vandermonde (fun i : Fin N => ((i : ℕ) : ℂ)) = 1) (p : ℂ → V) (a : ℕ → V)
    (ha : ∀ Y, p Y = ∑ j ∈ Finset.range N, Y ^ j • a j) (j : Fin N) :
    ∑ i : Fin N, W j i • p ((i : ℕ) : ℂ) = a j := by
  have key : ∀ l : Fin N, ∑ i : Fin N, W j i * ((i : ℕ) : ℂ) ^ (l : ℕ) = if j = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hW j) l
    simpa [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.one_apply] using h
  simp_rw [ha, Finset.sum_range, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key, ite_smul, one_smul, zero_smul]
  simp
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAct
