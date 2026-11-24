-- Prove2me | solution 1 for FairSelling.restricted_MMS2_ge_of_slack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:40:19.877448+00:00
-- url     : https://prove2.me/submissions/9efa8d12-9122-425e-9d6e-6f508b963eb0

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restricted_MMS2_ge
import Theorems.Thm_FairSelling_bagfill
import Theorems.Thm_FairSelling_vbarSum_sdiff


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (R : Finset G) (τ : ℝ) (hτ : 0 ≤ τ) (hR2 : 2 * τ ≤ vbarSum w p R)
    (hslack : ∀ g ∈ R, vbar w p g ≤ vbarSum w p R - 2 * τ) :
    τ ≤ MMS 2 (restrictVal R w) (restrictVal R p) := by
  classical
  have hsumR : vbarSum w p R = ∑ g ∈ R, vbar w p g := rfl
  have hbnd : ∀ g ∈ R, vbar w p g ≤ (vbarSum w p R - τ) - τ := by
    intro g hg; have := hslack g hg; linarith
  have htot : τ ≤ ∑ g ∈ R, vbar w p g := by rw [← hsumR]; linarith
  obtain ⟨B1, hB1sub, hB1lo, hB1hi⟩ :=
    bagfill (fun g => vbar w p g) τ (vbarSum w p R - τ) hτ (by linarith) R hbnd htot
  refine restricted_MMS2_ge w p hw hp R B1 (R \ B1) τ
    (Finset.disjoint_sdiff) hB1sub (Finset.sdiff_subset) hB1lo ?_
  have hsdiff : vbarSum w p (R \ B1) = vbarSum w p R - vbarSum w p B1 :=
    vbarSum_sdiff w p hB1sub
  have hval : vbarSum w p B1 = ∑ g ∈ B1, vbar w p g := rfl
  rw [hsdiff]; linarith [hB1hi]
end FairSelling
