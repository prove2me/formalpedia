-- Prove2me | solution 1 for FairSelling.untouched_mms_part_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:31.805807+00:00
-- url     : https://prove2.me/submissions/45228099-f3bc-487c-af66-d383db7a1df3

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_restrictVal_nonneg
import Theorems.Thm_FairSelling_le_MMS_of_outcome
import Theorems.Thm_FairSelling_vbarSum_restrict_subset
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome

attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
    (hcfg : ConfigN 3 w p (MMS 3 w p) A s q)
    (lost j k : Fin 3) (hlj : lost ≠ j) (hlk : lost ≠ k) (hjk : j ≠ k)
    (g : G) (hg : g ∈ A lost) :
    MMS 3 w p ≤ MMS 2 (restrictVal (Finset.univ \ {g}) w)
      (restrictVal (Finset.univ \ {g}) p) := by
  apply le_MMS_of_outcome;
  bv_decide;
  exact fun _ => restrictVal_nonneg _ hw _;
  exact fun _ => restrictVal_nonneg _ hp _;
  rotate_right;
  exact unifiedOutcome ( fun i => restrictVal ( Finset.univ \ { g } ) w ) ( restrictVal ( Finset.univ \ { g } ) p ) ( fun i => if i = 0 then A j else A k ) s ( fun i => if i = 0 then q j else q k );
  · apply unifiedOutcome_valid;
    · exact fun _ => restrictVal_nonneg _ hp _;
    · have := hcfg.1;
      grind;
    · exact fun i => by fin_cases i <;> [ exact hcfg.2.1 j; exact hcfg.2.1 k ] ;
    · exact fun i => by split_ifs <;> [ exact hcfg.2.2.2.1 j; exact hcfg.2.2.2.1 k ] ;
    · have := hcfg.2.2.2.2.1; simp_all +decide [ Fin.sum_univ_three ] ;
      fin_cases lost <;> fin_cases j <;> fin_cases k <;> simp +decide at hlj hlk hjk hg ⊢;
      all_goals rw [ show ∑ g_1 ∈ s, restrictVal ( Finset.univ \ { g } ) p g_1 = ∑ g_1 ∈ s, p g_1 from ?_ ] ; linarith [ hcfg.2.2.2.1 0, hcfg.2.2.2.1 1, hcfg.2.2.2.1 2 ];
      all_goals refine' Finset.sum_congr rfl fun x hx => _; simp +decide [ restrictVal ] ;
      all_goals intro hx'; have := hcfg.2.1 0; have := hcfg.2.1 1; have := hcfg.2.1 2; simp_all +decide [ Finset.disjoint_left ] ;
  · intro i
    have h_util : util (restrictVal (Finset.univ \ {g}) w) (unifiedOutcome (fun i => restrictVal (Finset.univ \ {g}) w) (restrictVal (Finset.univ \ {g}) p) (fun i => if i = 0 then A j else A k) s (fun i => if i = 0 then q j else q k)) i = vbarSum w p (if i = 0 then A j else A k) + (if i = 0 then q j else q k) := by
      rw [util_unifiedOutcome (fun _ => restrictVal (Finset.univ \ {g}) w) (restrictVal (Finset.univ \ {g}) p) (fun i => if i = 0 then A j else A k) s (fun i => if i = 0 then q j else q k) i]
      congr 1
      rw [vbarSum_restrict_subset]
      intro x hx; have := hcfg.1; simp_all +decide [ Finset.disjoint_left ] ;
      grind;
    fin_cases i <;> simp_all +decide [ ConfigN ]
end FairSelling
