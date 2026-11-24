-- Prove2me | solution 1 for FairSelling.pure_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:20.130711+00:00
-- url     : https://prove2.me/submissions/f8b05d6d-4aa7-4106-a04f-05e269050a17

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restricted_MMS2_ge
import Theorems.Thm_FairSelling_three_MMS_le_vbarSum_univ
import Theorems.Thm_FairSelling_bagfill
import Theorems.Thm_FairSelling_MMS_nonneg
import Theorems.Thm_FairSelling_vbarSum_sdiff


set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3/4) * MMS 3 w p)
    (B : Finset G) (hBrej : vbarSum w p B ≤ (3/4) * MMS 3 w p) :
    (3/4) * MMS 3 w p ≤
      MMS 2 (restrictVal (Finset.univ \ B) w) (restrictVal (Finset.univ \ B) p) := by
  classical
  set M : ℝ := MMS 3 w p with hM
  have hM0 : 0 ≤ M := MMS_nonneg (by norm_num) w p hw hp
  set R : Finset G := Finset.univ \ B with hR
  -- Total `v̄`-value of the remaining goods.
  have hBsub : B ⊆ Finset.univ := Finset.subset_univ _
  have hRval : vbarSum w p R = vbarSum w p Finset.univ - vbarSum w p B := by
    rw [hR]; exact vbarSum_sdiff w p hBsub
  have hunivge : 3 * M ≤ vbarSum w p Finset.univ := three_MMS_le_vbarSum_univ w p hw hp
  have hRge : (9/4) * M ≤ vbarSum w p R := by rw [hRval]; linarith
  -- Bag-fill the first sub-bundle.
  have hsumR : vbarSum w p R = ∑ g ∈ R, vbar w p g := rfl
  have hlo0 : (0 : ℝ) ≤ (3/4) * M := by positivity
  have hlohi : (3/4) * M ≤ vbarSum w p R - (3/4) * M := by linarith
  have hbnd : ∀ g ∈ R, vbar w p g ≤ (vbarSum w p R - (3/4) * M) - (3/4) * M := by
    intro g _; have := hnobig g; linarith
  have htot : (3/4) * M ≤ ∑ g ∈ R, vbar w p g := by rw [← hsumR]; linarith
  obtain ⟨B1, hB1sub, hB1lo, hB1hi⟩ :=
    bagfill (fun g => vbar w p g) ((3/4) * M) (vbarSum w p R - (3/4) * M) hlo0 hlohi R hbnd htot
  -- The two sub-bundles.
  refine restricted_MMS2_ge w p hw hp R B1 (R \ B1) ((3/4) * M)
    (Finset.disjoint_sdiff) hB1sub (Finset.sdiff_subset) hB1lo ?_
  have hsdiff : vbarSum w p (R \ B1) = vbarSum w p R - vbarSum w p B1 :=
    vbarSum_sdiff w p hB1sub
  have hval : vbarSum w p B1 = ∑ g ∈ B1, vbar w p g := rfl
  rw [hsdiff]; linarith [hB1hi]
end FairSelling
