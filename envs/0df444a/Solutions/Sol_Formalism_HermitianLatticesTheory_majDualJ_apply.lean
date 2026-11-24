-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDualJ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:53.094803+00:00
-- url     : https://prove2.me/submissions/0536fdd2-71f9-447e-85a5-c6d3aaa309c0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    majDualJ h b X u = jW h b X u := rfl
end Formalism.HermitianLatticesTheory
