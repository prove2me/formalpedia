-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.one_mem_HtupW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:15.403104+00:00
-- url     : https://prove2.me/submissions/b462872b-3246-44bd-b3d8-275dbc98cb15

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_lattice_degree_zero
import Theorems.Thm_Formalism_MainNotions_G_Inhab_lamAt_zero
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_tensorLat
import Theorems.Thm_Formalism_MainNotions_G_Inhab_one_mem_tenV
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
include h0
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (L : P.Tup) : (1 : P.Xsp) ∈ P.HtupW L := by
  unfold Places.HtupW
  apply one_mem_tenV
  intro v
  unfold HtenW
  apply one_mem_tensorLat
  intro s
  simp only [h0 v, lamAt_zero]
  exact one_mem_lattice_degree_zero O Kf _ _
end Formalism.MainNotions.G.Inhab
