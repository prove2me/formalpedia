-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.dense_fcoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:46.311429+00:00
-- url     : https://prove2.me/submissions/9b22b455-1ef2-40e9-9643-0079d3fd1f03

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_BlockMetrics_dense_emb

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
theorem _root_.solution {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have hemb : DenseRange v.embedding := dense_emb v (IsTotallyComplex.isComplex v)
  have h1 : DenseRange fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x := by
    have hpi : DenseRange (Pi.map fun _ : ι => v.embedding) := DenseRange.piMap fun _ => hemb
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (Pi.map fun _ : ι => v.embedding) := by
      ext u; constructor
      · rintro ⟨x, rfl⟩; exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨c, rfl⟩
        refine ⟨b.equivFun.symm c, ?_⟩
        funext i
        have hc := congr_fun (b.equivFun.apply_symm_apply c) i
        rw [Basis.equivFun_apply] at hc
        show v.embedding (b.repr (b.equivFun.symm c) i) = v.embedding (c i)
        rw [hc]
    rw [DenseRange, hr]; exact hpi
  have h2 : Continuous fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have h3 : Function.Surjective fun u : ι → ℂ =>
      (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    intro w
    refine ⟨(X v).mulVec (WithLp.ofLp w), ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]
  exact h3.denseRange.comp h1 h2
end Formalism.IndefR.LatticeTransfer.BlockMetrics
