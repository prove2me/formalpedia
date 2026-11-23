-- Prove2me | solution 1 for Formalism.D5.Bal.sum_S_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:24.63346+00:00
-- url     : https://prove2.me/submissions/d0ffff53-31af-40c1-af77-9aea36f11a55

import Definitions.Def_Formalism_ThickAverageLoss_PartnersToFactorsAt
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Theorems.Thm_Formalism_D5_Bal_inPhi_add_topPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset ArithmeticFunction
noncomputable section
namespace Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
namespace Bal
section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private lemma prod_add_fst_fst (x y : E0 × H) : (x + y).1.1 = x.1.1 + y.1.1 := rfl
private lemma topPl_fst_fst_eq_zero (t : H) : (topPl t).1.1 = 0 := rfl
private lemma cconj_fst_fst_eq_one : (cconj : E0 × H).1.1 = 1 := rfl
private lemma prod_sub_fst_fst (x y : E0 × H) : (x - y).1.1 = x.1.1 - y.1.1 := rfl
end
end Bal
end Formalism.D5
end
end

set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.D5
open Formalism Formalism.CMTypeGaloisData Formalism.WT Formalism.WeightedSieveThreeParameter
open Formalism.D5.Bal
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.D5.Bal
theorem _root_.solution {β : Type*} [AddCommMonoid β] (t : H) (F : E0 × H → β) :
    ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t)), F (cconj + g + topPl t)
      = ∑ ρ ∈ PhiSet (H := H), F ρ := by
  refine Finset.sum_nbij' (fun g => cconj + g + topPl t) (fun ρ => ρ - cconj - topPl t) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    have hg' : ¬ InPhi (g + topPl t) := (Finset.mem_filter.mp hg).2
    have h1 : ¬ g.1.1 = 0 := fun h => hg' ((inPhi_add_topPl g t).mpr h)
    show cconj + g + topPl t ∈ PhiSet (H := H)
    rw [PhiSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (cconj + g + topPl t).1.1 = 0
    rw [prod_add_fst_fst, prod_add_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]
    revert h1
    generalize g.1.1 = e
    revert e
    decide
  · intro ρ hρ
    rw [PhiSet, Finset.mem_filter] at hρ
    have h1 : ρ.1.1 = 0 := hρ.2
    show ρ - cconj - topPl t ∈ univ.filter (fun g : E0 × H => ¬ InPhi (g + topPl t))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [inPhi_add_topPl]
    show ¬ (ρ - cconj - topPl t).1.1 = 0
    rw [prod_sub_fst_fst, prod_sub_fst_fst, cconj_fst_fst_eq_one, topPl_fst_fst_eq_zero]
    revert h1
    generalize ρ.1.1 = e
    revert e
    decide
  · intro g _
    show cconj + g + topPl t - cconj - topPl t = g
    abel
  · intro ρ _
    show cconj + (ρ - cconj - topPl t) + topPl t = ρ
    abel
  · intro g _
    rfl
end Formalism.D5.Bal
