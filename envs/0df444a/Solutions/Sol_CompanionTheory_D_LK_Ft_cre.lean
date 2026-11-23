-- Prove2me | solution 1 for CompanionTheory.D.LK.Ft_cre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:57.490472+00:00
-- url     : https://prove2.me/submissions/90101263-3e1d-4a55-bbcd-aa972aa36fab

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialBoundedSupport
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_DifferentialCommutesWeightOperator
import Theorems.Thm_CompanionTheory_D_LK_wt_insert
import Theorems.Thm_CompanionTheory_D_LK_Ft_apply
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_LK_Car_cre_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Car Formalism.REAL
open CompanionTheory.D.DSIC (KRel)
variable {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace CompanionTheory.D.LK
theorem _root_.solution {ε : Fin n → Bool} (E : Fin n → Fin n → Module.End ℂ V) (c : Fin n) {i : Pos n} (hi : cpt ε i)
    (x : Cn n V) : Ft ε E c (cre i x) = cre i (Ft ε E c x) + (al i c : ℂ) • cre i x := by
  funext A
  simp only [Ft_apply, cre_apply, Pi.add_apply, Pi.smul_apply]
  by_cases h : i ∈ A
  · have e : A.filter (cpt ε) = insert i ((A.erase i).filter (cpt ε)) := by
      conv_lhs => rw [← insert_erase h, filter_insert, if_pos hi]
    rw [if_pos h, if_pos h, e, wt_insert (fun hh => notMem_erase i A (mem_filter.1 hh).1), map_smul]
    push_cast
    module
  · simp [h]
end CompanionTheory.D.LK
