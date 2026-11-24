-- Prove2me | solution 1 for FairSelling.MMS2_cash_of_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:57:29.609138+00:00
-- url     : https://prove2.me/submissions/585fe43e-a359-4dfb-8710-85e0ad9e9d80

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_ThreeAgentCash
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_MMS2_cash_of_two_bundles
import Theorems.Thm_FairSelling_bagfill
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R : Finset G) (cash τ : ℝ) (hcash : 0 ≤ cash) (hτ : 0 ≤ τ)
    (hsmall : ∀ g ∈ R, vbar w p g ≤ τ)
    (htotal : 3 * τ ≤ vbarSum w p R + cash) :
    τ ≤ MMS 2 (cashVal R w) (cashPrice R p cash) := by
  by_cases hcase : τ ≤ ∑ g ∈ R, vbar w p g;
  · -- Use `bagfill` to select $C$ with $\tau \leq \text{value}(C) \leq 2\tau$.
    obtain ⟨C, hC⟩ : ∃ C ⊆ R, τ ≤ vbarSum w p C ∧ vbarSum w p C ≤ 2 * τ := by
      have := bagfill ( fun g => vbar w p g ) τ ( 2 * τ ) hτ ( by linarith ) R ?_ hcase;
      · exact this;
      · exact fun g hg => by linarith [ hsmall g hg ] ;
    convert MMS2_cash_of_two_bundles w p hw hp R C ( R \ C ) cash 0 cash _ _ _ _ _ _ using 1;
    any_goals tauto;
    · simp +decide [ vbarSum_sdiff, hC.1 ];
      grind;
    · exact Finset.disjoint_sdiff;
    · grind +splitImp;
  · apply MMS2_cash_of_two_bundles;
    any_goals tauto;
    · linarith!;
    · simp +decide [ vbarSum ];
    · exact le_add_of_nonneg_left ( Finset.sum_nonneg fun _ _ => le_max_of_le_left ( hp _ ) )
end FairSelling
