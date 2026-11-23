-- Prove2me | solution 1 for Formalism.L2.SG.PoincareSeriesSquareIntegrable.mem_stab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:52.379298+00:00
-- url     : https://prove2.me/submissions/a35785ef-5570-4c6e-a2bd-3961d5009d94

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.dupNamespace false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PoincareSeriesSquareIntegrable
open Formalism.L2.SG.FoldBound
namespace Formalism.L2.SG.PoincareSeriesSquareIntegrable
theorem _root_.solution {G : Type*} [Group G] (S S' : Subgroup G) (γ g : G) :
    g ∈ stab S S' γ ↔ g ∈ S ∧ γ⁻¹ * g * γ ∈ S' := by
  unfold stab
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
end Formalism.L2.SG.PoincareSeriesSquareIntegrable
