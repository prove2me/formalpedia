-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_realize_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.610169+00:00
-- url     : https://prove2.me/submissions/f69ce279-47e2-4105-9653-281f5be5b24d

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
theorem _root_.solution (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    realize b X x p = if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re
      else (fcoord b X p.1 x p.2.1).im := rfl
end Formalism.HermitianLatticesTheory
