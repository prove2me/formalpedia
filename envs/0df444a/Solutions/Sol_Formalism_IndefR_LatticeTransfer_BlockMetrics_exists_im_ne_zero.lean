-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.BlockMetrics.exists_im_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:00.927044+00:00
-- url     : https://prove2.me/submissions/c3874267-049e-4b6c-bf06-4c6e0ee30419

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (v : InfinitePlace K) : ∃ a : K, (v.embedding a).im ≠ 0 := by
  have hv := IsTotallyComplex.isComplex v
  rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hv
  by_contra hcon
  push_neg at hcon
  apply hv
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)
end Formalism.IndefR.LatticeTransfer.BlockMetrics
