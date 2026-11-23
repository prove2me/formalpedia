-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_tenV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:57.888693+00:00
-- url     : https://prove2.me/submissions/eead7306-d071-40cf-8aa3-059f65502301

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
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (M : ∀ v, Submodule O (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf))
    (h : ∀ v, (1 : MvPolynomial _ Kf) ∈ M v) : (1 : P.Xsp) ∈ P.tenV M := Submodule.subset_span ⟨fun _ => 1, h, by simp⟩
end Formalism.MainNotions.G.Inhab
