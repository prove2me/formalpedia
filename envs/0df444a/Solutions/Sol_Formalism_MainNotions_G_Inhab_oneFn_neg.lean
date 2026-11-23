-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.oneFn_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:50.036247+00:00
-- url     : https://prove2.me/submissions/97f2ea51-ecce-4100-aa8b-8006268be17d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf) (C : Level P)
variable (h0 : ∀ v, P.lam0 v = fun _ _ => 0)
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution {L : P.Tup} (h : ¬ P.IsLatTup L) : oneFn P L = 0 := by simp [oneFn, h]
end Formalism.MainNotions.G.Inhab
