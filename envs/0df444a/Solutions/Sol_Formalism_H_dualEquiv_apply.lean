-- Prove2me | solution 1 for Formalism.H.dualEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:49.604072+00:00
-- url     : https://prove2.me/submissions/4ce5cd25-8fb4-405d-bfcd-ad705f4482e1

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_InnerDualVecBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Complex
open scoped RealInnerProductSpace
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.H
theorem _root_.solution (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    ((dualEquiv e m : dual (Submodule.span ℤ (Set.range e))) : V) = dualVec e m := rfl
end Formalism.H
