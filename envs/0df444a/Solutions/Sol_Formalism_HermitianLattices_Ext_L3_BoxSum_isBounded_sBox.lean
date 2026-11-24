-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.isBounded_sBox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:47.128363+00:00
-- url     : https://prove2.me/submissions/58ce0d92-c709-424c-856a-e4db6dfde480

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoTsumDivPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology MeasureTheory Pointwise
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution [IsTotallyReal F] : Bornology.IsBounded (sBox F) := by
  refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff]
  constructor
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    rw [Real.norm_eq_abs, abs_of_pos (hx w).1]
    exact (hx w).2
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro w
    exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)
end Formalism.HermitianLattices.Ext.L3.BoxSum
