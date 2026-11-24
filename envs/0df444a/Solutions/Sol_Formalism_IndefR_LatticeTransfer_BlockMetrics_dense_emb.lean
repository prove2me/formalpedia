-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.dense_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.927354+00:00
-- url     : https://prove2.me/submissions/a8722b5b-76c0-4e96-a387-4973147829f1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_OpNormAtLeOfPoints

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  rcases Complex.subfield_eq_of_closed (v.embedding.fieldRange.isClosed_topologicalClosure) with h | h
  · exfalso
    have hr : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure :=
        v.embedding.fieldRange.le_topologicalClosure (RingHom.mem_fieldRange.2 ⟨x, rfl⟩)
      rw [h] at hx
      obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.1 hx
      rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
      simp
    exact (InfinitePlace.isComplex_iff.1 hv) hr
  · intro z
    have hz : z ∈ v.embedding.fieldRange.topologicalClosure := by
      rw [h]; exact Subfield.mem_top z
    have hc : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (Set.range v.embedding) := by
      rw [← RingHom.coe_fieldRange]; rfl
    rw [← hc]; exact hz
end Formalism.IndefR.LatticeTransfer.BlockMetrics
