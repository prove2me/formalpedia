-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.opNormAt_le_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:31.929969+00:00
-- url     : https://prove2.me/submissions/5d85c25c-34fc-4d39-9bd1-673c8eb525da

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_normAt_eq_norm
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_fcoord_map
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_dense_fcoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.BlockMetrics
namespace Formalism.IndefR.LatticeTransfer.BlockMetrics
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] V) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b X v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b X v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v)) with hTd
  refine ContinuousLinearMap.opNorm_le_bound T hC fun u => ?_
  refine (dense_fcoord b X hX v).induction_on (p := fun w => ‖T w‖ ≤ C * ‖w‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hT : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)) =
        WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (φ f)) := by
      rw [fcoord_map b X v hX φ f]; rfl
    show ‖T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f))‖ ≤ C * ‖WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)‖
    rw [hT, ← normAt_eq_norm, ← normAt_eq_norm]
    exact h f
end Formalism.IndefR.LatticeTransfer.BlockMetrics
